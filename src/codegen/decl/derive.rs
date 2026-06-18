//! Derived-instance codegen (`derive instance …`, `derive newtype instance …`).
//!
//! Generates the dictionary object directly from the data type's constructors.
//! Field instances are obtained via the field type's resolved dictionary and
//! invoked through the dict object itself (`fieldDict.eq(a)(b)`), so we never
//! need to import the class's method accessor.
//!
//! Currently supports `Eq`, `Ord`, and `derive newtype instance` (which reuses
//! the representation type's dictionary). Other classes produce an empty dict
//! object (valid JS that only fails if a missing method is actually called).

use crate::codegen::js_ast::{JsBinaryOp, JsExpr, JsStmt};
use crate::typecheck_db::ir;
use crate::typecheck_db::types::Type;

use super::expr::Cg;
use super::{dict_param_names, instance_js_name, type_expr_head_name, DeclCgCtx, GenDecl, GenUnit};

/// One constructor of a type being derived for.
#[derive(Clone)]
pub struct DerivedCtor {
    pub js_name: String,
    pub fields: Vec<Type>,
}

/// Constructor layout of a local data/newtype, keyed (in the driver) by the
/// type's simple name.
#[derive(Clone)]
pub struct DerivedTypeInfo {
    pub ctors: Vec<DerivedCtor>,
    /// The type's declared type variables, in order (last is the Functor param).
    pub type_vars: Vec<String>,
}

pub fn codegen_derive_decl(
    decl: &ir::Decl,
    ctx: &DeclCgCtx,
    info: Option<&DerivedTypeInfo>,
) -> GenDecl {
    let mut out = GenDecl::default();
    let ir::Decl::Derive { newtype, class_name, types, constraints, .. } = decl else {
        return out;
    };
    let class_simple = class_name.name.resolve().unwrap_or_default();
    let heads: Vec<String> = types.iter().map(type_expr_head_name).collect();
    let inst_name = instance_js_name(&class_simple, &heads);

    // Context dictionaries (e.g. `Eq a => Eq (Foo a)`) become leading params,
    // available as givens while resolving field dictionaries.
    let params = dict_param_names(constraints);
    let scope: Vec<(String, String)> = constraints
        .iter()
        .zip(params.iter())
        .map(|(c, p)| (c.class.name.resolve().unwrap_or_default(), p.clone()))
        .collect();
    let empty_cd = std::collections::HashMap::new();
    let mut cg = Cg::new(ctx, &empty_cd, scope);

    let dict = if *newtype {
        derive_newtype(&mut cg, &class_simple, info)
    } else {
        match class_simple.as_str() {
            "Eq" => derive_eq_like(&mut cg, info, "eq", false),
            "Eq1" => derive_eq_like(&mut cg, info, "eq1", true),
            "Ord" => derive_ord_like(&mut cg, info, "compare", false),
            "Ord1" => derive_ord_like(&mut cg, info, "compare1", true),
            "Functor" => derive_functor(&mut cg, info),
            // Unknown class: emit an empty dict — valid JS that only errors if a
            // missing method is actually invoked at runtime.
            _ => JsExpr::ObjectLit(vec![]),
        }
    };

    out.external_refs = cg.take_external_refs();
    let mut body = dict;
    for p in params.iter().rev() {
        body = JsExpr::Function(None, vec![p.clone()], vec![JsStmt::Return(body)]);
    }
    out.exports.push((inst_name.clone(), None));
    out.units.push(GenUnit {
        js_name: inst_name.clone(),
        stmts: vec![JsStmt::VarDecl(inst_name, Some(body))],
    });
    out
}

/// `derive newtype instance C NT` reuses the representation type's `C` dict
/// (the newtype is erased at runtime, so the dictionaries are interchangeable).
fn derive_newtype(cg: &mut Cg, class_simple: &str, info: Option<&DerivedTypeInfo>) -> JsExpr {
    let inner = info
        .and_then(|i| i.ctors.first())
        .and_then(|c| c.fields.first());
    match inner {
        Some(ty) => cg.dict_for_type(class_simple, ty),
        None => JsExpr::ObjectLit(vec![]),
    }
}

/// `eq`/`eq1`: `x => y => <all ctors compared field-by-field>`. For `eq1` (`hk`),
/// the method takes the element's `Eq` dict as a leading `dictEq` param and the
/// functor param's fields compare through it.
fn derive_eq_like(
    cg: &mut Cg,
    info: Option<&DerivedTypeInfo>,
    method_name: &str,
    hk: bool,
) -> JsExpr {
    let Some(info) = info else { return JsExpr::ObjectLit(vec![]) };
    if hk {
        cg.push_scope("Eq", "dictEq");
    }
    let x = || JsExpr::Var("x".to_string());
    let y = || JsExpr::Var("y".to_string());

    let mut stmts: Vec<JsStmt> = Vec::new();
    let multi = info.ctors.len() > 1;
    for ctor in &info.ctors {
        let test = JsExpr::Binary(
            JsBinaryOp::And,
            Box::new(JsExpr::InstanceOf(Box::new(x()), Box::new(JsExpr::Var(ctor.js_name.clone())))),
            Box::new(JsExpr::InstanceOf(Box::new(y()), Box::new(JsExpr::Var(ctor.js_name.clone())))),
        );
        // Conjoin field comparisons: fieldDict.eq(x.valueI)(y.valueI).
        let mut conj = JsExpr::BoolLit(true);
        let mut first = true;
        for (i, fty) in ctor.fields.iter().enumerate() {
            let fdict = cg.dict_for_type("Eq", fty);
            let cmp = call2(method(fdict, "eq"), field(x(), i), field(y(), i));
            conj = if first { first = false; cmp } else {
                JsExpr::Binary(JsBinaryOp::And, Box::new(conj), Box::new(cmp))
            };
        }
        stmts.push(JsStmt::If(test, vec![JsStmt::Return(conj)], None));
    }
    if multi {
        stmts.push(JsStmt::Return(JsExpr::BoolLit(false)));
    } else if stmts.is_empty() {
        stmts.push(JsStmt::Return(JsExpr::BoolLit(true)));
    }
    let mut eq_fn = curry2(stmts);
    if hk {
        eq_fn = JsExpr::Function(None, vec!["dictEq".to_string()], vec![JsStmt::Return(eq_fn)]);
    }
    JsExpr::ObjectLit(vec![(method_name.to_string(), eq_fn)])
}

/// `compare`/`compare1`: `x => y => <lexicographic over ctor index then fields>`.
/// Requires the `Data.Ordering` constructors. For `compare1` (`hk`), the method
/// takes the element's `Ord` dict as a leading `dictOrd` param.
fn derive_ord_like(
    cg: &mut Cg,
    info: Option<&DerivedTypeInfo>,
    method_name: &str,
    hk: bool,
) -> JsExpr {
    let Some(info) = info else { return JsExpr::ObjectLit(vec![]) };
    if hk {
        cg.push_scope("Ord", "dictOrd");
    }
    let x = || JsExpr::Var("x".to_string());
    let y = || JsExpr::Var("y".to_string());

    // Ordering constructors live in Data.Ordering.
    cg.note_external("Data.Ordering");
    let ord = |c: &str| JsExpr::Indexer(
        Box::new(JsExpr::ModuleAccessor("Data_Ordering".to_string(), c.to_string())),
        Box::new(JsExpr::StringLit("value".to_string())),
    );

    let mut stmts: Vec<JsStmt> = Vec::new();
    // Phase 1: same-constructor — compare fields lexicographically.
    for ctor in &info.ctors {
        let same = JsExpr::Binary(
            JsBinaryOp::And,
            Box::new(JsExpr::InstanceOf(Box::new(x()), Box::new(JsExpr::Var(ctor.js_name.clone())))),
            Box::new(JsExpr::InstanceOf(Box::new(y()), Box::new(JsExpr::Var(ctor.js_name.clone())))),
        );
        let mut body: Vec<JsStmt> = Vec::new();
        for (i, fty) in ctor.fields.iter().enumerate() {
            let fdict = cg.dict_for_type("Ord", fty);
            let cmp = call2(method(fdict, "compare"), field(x(), i), field(y(), i));
            let o = format!("$o{i}");
            body.push(JsStmt::VarDecl(o.clone(), Some(cmp)));
            let not_eq = JsExpr::Binary(
                JsBinaryOp::StrictNeq,
                Box::new(JsExpr::Var(o.clone())),
                Box::new(ord("EQ")),
            );
            body.push(JsStmt::If(not_eq, vec![JsStmt::Return(JsExpr::Var(o))], None));
        }
        body.push(JsStmt::Return(ord("EQ")));
        stmts.push(JsStmt::If(same, body, None));
    }
    // Phase 2: different constructors — order by declaration index. Iterating in
    // order, the first ctor matching x (→ LT) or y (→ GT) decides.
    if info.ctors.len() > 1 {
        for ctor in &info.ctors {
            let x_is = JsExpr::InstanceOf(Box::new(x()), Box::new(JsExpr::Var(ctor.js_name.clone())));
            stmts.push(JsStmt::If(x_is, vec![JsStmt::Return(ord("LT"))], None));
            let y_is = JsExpr::InstanceOf(Box::new(y()), Box::new(JsExpr::Var(ctor.js_name.clone())));
            stmts.push(JsStmt::If(y_is, vec![JsStmt::Return(ord("GT"))], None));
        }
    }
    stmts.push(JsStmt::Return(ord("EQ")));
    let mut compare_fn = curry2(stmts);
    if hk {
        compare_fn =
            JsExpr::Function(None, vec!["dictOrd".to_string()], vec![JsStmt::Return(compare_fn)]);
    }
    JsExpr::ObjectLit(vec![(method_name.to_string(), compare_fn)])
}

/// `map: f => x => <rebuild each ctor, mapping the functor param>`.
fn derive_functor(cg: &mut Cg, info: Option<&DerivedTypeInfo>) -> JsExpr {
    let Some(info) = info else { return JsExpr::ObjectLit(vec![]) };
    let Some(a) = info.type_vars.last().cloned() else { return JsExpr::ObjectLit(vec![]) };
    let x = || JsExpr::Var("x".to_string());

    let mut stmts: Vec<JsStmt> = Vec::new();
    for ctor in &info.ctors {
        let test = JsExpr::InstanceOf(Box::new(x()), Box::new(JsExpr::Var(ctor.js_name.clone())));
        let rebuilt = if ctor.fields.is_empty() {
            // Nullary ctor — unchanged.
            x()
        } else {
            // Ctor.create(map(field0))(map(field1))...
            let mut call = JsExpr::Indexer(
                Box::new(JsExpr::Var(ctor.js_name.clone())),
                Box::new(JsExpr::StringLit("create".to_string())),
            );
            for (i, fty) in ctor.fields.iter().enumerate() {
                let mapped = map_field(cg, fty, &a, field(x(), i));
                call = JsExpr::App(Box::new(call), vec![mapped]);
            }
            call
        };
        stmts.push(JsStmt::If(test, vec![JsStmt::Return(rebuilt)], None));
    }
    stmts.push(JsStmt::Return(x()));
    let map_fn = JsExpr::Function(
        None,
        vec!["f".to_string()],
        vec![JsStmt::Return(JsExpr::Function(None, vec!["x".to_string()], stmts))],
    );
    JsExpr::ObjectLit(vec![("map".to_string(), map_fn)])
}

/// Map the functor parameter `a` within a field of type `fty`, applied to `value`.
fn map_field(cg: &mut Cg, fty: &Type, a: &str, value: JsExpr) -> JsExpr {
    if is_var(fty, a) {
        // The param itself — apply `f`.
        return JsExpr::App(Box::new(JsExpr::Var("f".to_string())), vec![value]);
    }
    if !contains_var(fty, a) {
        // No occurrence — unchanged.
        return value;
    }
    // `G inner` where `a` occurs in the last argument: map through G's Functor.
    if let Type::App(g, inner) = fty {
        let container = (**g).clone();
        let fdict = cg.dict_for_type("Functor", &container);
        let inner_mapper = JsExpr::Function(
            None,
            vec!["$v".to_string()],
            vec![JsStmt::Return(map_field(cg, inner, a, JsExpr::Var("$v".to_string())))],
        );
        return JsExpr::App(
            Box::new(JsExpr::App(Box::new(method(fdict, "map")), vec![inner_mapper])),
            vec![value],
        );
    }
    // Unsupported shape — leave unchanged (best effort).
    value
}

fn is_var(t: &Type, a: &str) -> bool {
    matches!(t, Type::Var(v) if v == a)
}

fn contains_var(t: &Type, a: &str) -> bool {
    match t {
        Type::Var(v) => v == a,
        Type::App(f, x) => contains_var(f, a) || contains_var(x, a),
        Type::Fun(x, y) => contains_var(x, a) || contains_var(y, a),
        Type::Kinded(inner, _) => contains_var(inner, a),
        _ => false,
    }
}

// -- small JS builders ------------------------------------------------------

fn field(obj: JsExpr, i: usize) -> JsExpr {
    JsExpr::Indexer(Box::new(obj), Box::new(JsExpr::StringLit(format!("value{i}"))))
}

fn method(dict: JsExpr, name: &str) -> JsExpr {
    JsExpr::Indexer(Box::new(dict), Box::new(JsExpr::StringLit(name.to_string())))
}

fn call2(f: JsExpr, a: JsExpr, b: JsExpr) -> JsExpr {
    JsExpr::App(Box::new(JsExpr::App(Box::new(f), vec![a])), vec![b])
}

/// `function (x) { return function (y) { <stmts> }; }`
fn curry2(stmts: Vec<JsStmt>) -> JsExpr {
    let inner = JsExpr::Function(None, vec!["y".to_string()], stmts);
    JsExpr::Function(None, vec!["x".to_string()], vec![JsStmt::Return(inner)])
}
