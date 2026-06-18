//! Per-declaration JavaScript codegen driven by the typecheck_db IR.
//!
//! This is a *fresh* codegen (distinct from the legacy whole-module
//! `crate::codegen::js`): it consumes the lowered IR (`typecheck_db::ir`)
//! plus per-declaration typecheck results, and emits one independent JS
//! unit per PureScript declaration so the output can be cached per-decl.

mod derive;
mod expr;

pub use derive::{codegen_derive_decl, DerivedCtor, DerivedTypeInfo};

use std::collections::{HashMap, HashSet};

use crate::codegen::common::ident_to_js;
use crate::codegen::js_ast::{JsExpr, JsStmt};
use crate::cst::TypeExpr;
use crate::span::Span;
use crate::typecheck_db::ir;
use crate::typecheck_db::passes::constraints::ResolvedDict;
use crate::typecheck_db::types::Type;

/// Empty per-decl dict map (for decls with no resolved constraints).
fn no_dicts() -> HashMap<Span, Vec<ResolvedDict>> {
    HashMap::new()
}

/// Deterministic JS name for a type-class dictionary instance, shared by the
/// instance declaration and call sites: `lowerFirst(Class)` followed by each
/// head type's name (e.g. `ToInt Color` → `toIntColor`, `Eq (Maybe a)` →
/// `eqMaybe`). Must agree on both sides so references resolve.
pub fn instance_js_name(
    class_module: Option<&str>,
    class_simple: &str,
    type_heads: &[String],
) -> String {
    // NOTE: the class's defining module is threaded here to disambiguate
    // same-named classes from different modules, but isn't yet folded into the
    // name: the reference side derives the class module from the InstanceIndex
    // QName while the declaration side uses the resolved defining module, and
    // those two sources currently disagree (e.g. `Data.Eq` vs none), so
    // prefixing would break cross-module instance references. Reconciling those
    // module sources is a prerequisite for true disambiguation.
    let _ = class_module;
    let mut s = String::new();
    for (i, c) in class_simple.chars().enumerate() {
        if i == 0 {
            s.extend(c.to_lowercase());
        } else {
            s.push(c);
        }
    }
    // `Generic`'s second parameter is the (fundep-determined) representation
    // type, written `_` at the declaration. Name by the data type only so the
    // declaration and call sites (which see the concrete Rep) agree.
    let heads: &[String] = if class_simple == "Generic" && !type_heads.is_empty() {
        &type_heads[..1]
    } else {
        type_heads
    };
    for h in heads {
        s.push_str(h);
    }
    ident_to_js(crate::interner::intern(&s))
}

/// Head constructor name of a CST type expression (`Maybe a` → "Maybe",
/// `Color` → "Color"). Used for instance naming from declaration syntax.
pub(crate) fn type_expr_head_name(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Constructor { name, .. } => {
            crate::interner::resolve(name.name.symbol()).unwrap_or_default()
        }
        TypeExpr::Var { name, .. } => {
            crate::interner::resolve(name.value.symbol()).unwrap_or_default()
        }
        TypeExpr::App { constructor, .. } => type_expr_head_name(constructor),
        TypeExpr::Parens { ty, .. } => type_expr_head_name(ty),
        _ => String::new(),
    }
}

/// Head constructor name of a solved instance type (`Maybe a` → "Maybe",
/// `Color` → "Color"). Type variables / non-constructor heads yield "".
pub(crate) fn type_head_name(t: &Type) -> String {
    match t {
        Type::Con(q) => q.name.clone(),
        Type::App(f, _) => type_head_name(f),
        Type::Kinded(inner, _) => type_head_name(inner),
        _ => String::new(),
    }
}

/// Module-global information needed while translating declarations:
/// constructor arities, which constructors are newtypes (identity), and
/// which local names are foreign imports (`$foreign.x`).
pub struct DeclCgCtx<'a> {
    /// The dotted name of the module being compiled (e.g. "Data.Maybe").
    pub module: &'a str,
    /// Data-constructor name → field count (local constructors).
    pub ctor_arity: &'a HashMap<String, usize>,
    /// Names of newtype constructors (compiled as identity).
    pub newtype_ctors: &'a HashSet<String>,
    /// Local names that are `foreign import`s (referenced as `$foreign.x`).
    pub foreign_names: &'a HashSet<String>,
    /// Class-method (raw PS) name → class simple name. Lets codegen pull a
    /// dictionary from an in-scope parameter when the solver discharged the
    /// constraint via a *given* (no `constraint_dicts` entry recorded).
    pub class_methods: &'a HashMap<String, String>,
    /// Instance index, consulted to resolve a constrained instance's context
    /// dictionaries (the `ResolvedDict.context` is stored unsubstituted).
    pub instances: &'a crate::typecheck_db::passes::instance_index::InstanceIndex,
    /// Instance dictionary JS name → defining module (dotted). Lets a dict
    /// reference to an imported instance be emitted as `Module.name`. Names
    /// absent from this map (or mapped to the current module) are local.
    pub instance_modules: &'a HashMap<String, String>,
}

/// One emitted JS binding (a value, or a single data constructor).
#[derive(Debug, Clone, PartialEq)]
pub struct GenUnit {
    pub js_name: String,
    pub stmts: Vec<JsStmt>,
}

/// Result of translating a single PureScript declaration (or equation group).
#[derive(Debug, Clone, Default, PartialEq)]
pub struct GenDecl {
    pub units: Vec<GenUnit>,
    /// Module parts of every external module this decl references.
    pub external_refs: Vec<Vec<String>>,
    /// Local (same-module) JS names referenced — for topological ordering.
    pub local_refs: Vec<String>,
    /// (js_name, optional original-PS-name for `as` rename) to export.
    pub exports: Vec<(String, Option<String>)>,
    /// `$foreign` members referenced / re-exported.
    pub foreign_refs: Vec<String>,
}

/// Translate a group of value-declaration equations that share a name.
/// Phase 1 only supports a single equation per name; multi-equation groups
/// are handled in Phase 3.
pub fn codegen_value_group(
    equations: &[&ir::Decl],
    ctx: &DeclCgCtx,
    constraint_dicts: &HashMap<Span, Vec<ResolvedDict>>,
    leading_constraints: &[crate::typecheck_db::types::Constraint],
) -> GenDecl {
    let mut out = GenDecl::default();
    let first = match equations.first() {
        Some(d) => d,
        None => return out,
    };
    let name_sym = match first {
        ir::Decl::Value { name, .. } => name.value,
        _ => return out,
    };
    let js_name = ident_to_js(name_sym.symbol());

    // Givens in scope for the body: one (class, dictParam) per leading constraint.
    let params = dict_param_names_types(leading_constraints);
    let scope: Vec<(String, String)> = leading_constraints
        .iter()
        .zip(params.iter())
        .map(|(c, p)| (c.class.name.clone(), p.clone()))
        .collect();

    let mut cg = expr::Cg::new(ctx, constraint_dicts, scope);
    let mut body_expr = cg.value_group_body(equations);
    out.external_refs = cg.take_external_refs();
    out.local_refs = cg.take_local_refs();

    // A constrained value (`f :: Eq a => ...`) takes its dictionaries as
    // leading curried parameters; the body resolves givens to these names.
    for p in params.iter().rev() {
        body_expr = JsExpr::Function(None, vec![p.clone()], vec![JsStmt::Return(body_expr)]);
    }

    let stmt = JsStmt::VarDecl(js_name.clone(), Some(body_expr));
    out.exports.push((js_name.clone(), None));
    out.units.push(GenUnit { js_name, stmts: vec![stmt] });
    out
}

/// Peel `Forall`/`Constrained` layers off a scheme type to collect the leading
/// (given) constraints a value is parameterised over.
pub fn leading_constraints(ty: &Type) -> Vec<crate::typecheck_db::types::Constraint> {
    match ty {
        Type::Forall(_, inner) => leading_constraints(inner),
        Type::Constrained(cs, inner) => {
            let mut v = cs.clone();
            v.extend(leading_constraints(inner));
            v
        }
        _ => Vec::new(),
    }
}

/// Dict parameter names for solver-`Constraint`s, numbering duplicate classes.
pub(crate) fn dict_param_names_types(
    constraints: &[crate::typecheck_db::types::Constraint],
) -> Vec<String> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    let mut names = Vec::with_capacity(constraints.len());
    for c in constraints {
        let class = &c.class.name;
        let n = counts.entry(class.clone()).or_insert(0);
        let name = if *n == 0 {
            format!("dict{class}")
        } else {
            format!("dict{class}{n}")
        };
        *n += 1;
        names.push(name);
    }
    names
}

/// Translate a `class` declaration into one method-accessor per member:
/// `var method = function (dict) { return dict["method"]; };`. The dict key is
/// the raw PureScript method name (matching the instance dict object keys).
pub fn codegen_class_decl(decl: &ir::Decl) -> GenDecl {
    let mut out = GenDecl::default();
    let ir::Decl::Class { members, .. } = decl else { return out };
    for member in members {
        let method_js = ident_to_js(member.name.value.symbol());
        let method_ps = member.name.value.resolve().unwrap_or_default();
        let accessor = JsExpr::Function(
            None,
            vec!["dict".to_string()],
            vec![JsStmt::Return(JsExpr::Indexer(
                Box::new(JsExpr::Var("dict".to_string())),
                Box::new(JsExpr::StringLit(method_ps)),
            ))],
        );
        out.exports.push((method_js.clone(), None));
        out.units.push(GenUnit {
            js_name: method_js.clone(),
            stmts: vec![JsStmt::VarDecl(method_js, Some(accessor))],
        });
    }
    out
}

/// Translate an `instance` declaration into a dictionary object. Each method is
/// compiled from its equation group. Instance context constraints (e.g.
/// `Eq a => Eq (Maybe a)`) become leading dict parameters; the dict object is
/// then a function of those params.
pub fn codegen_instance_decl(
    decl: &ir::Decl,
    ctx: &DeclCgCtx,
    method_dicts: &HashMap<String, HashMap<Span, Vec<ResolvedDict>>>,
    method_leading: &HashMap<String, Vec<String>>,
) -> GenDecl {
    let mut out = GenDecl::default();
    let ir::Decl::Instance { class_name, types, members, constraints, .. } = decl else {
        return out;
    };

    let class_simple = class_name.name.resolve().unwrap_or_default();
    let class_module = class_name.module.resolve();
    let heads: Vec<String> = types.iter().map(type_expr_head_name).collect();
    let inst_name = instance_js_name(class_module.as_deref(), &class_simple, &heads);

    // Group instance methods by name (preserving source order).
    let mut order: Vec<crate::interner::Symbol> = Vec::new();
    let mut groups: HashMap<crate::interner::Symbol, Vec<&ir::Decl>> = HashMap::new();
    for m in members {
        if let ir::Decl::Value { name, .. } = m {
            let sym = name.value.symbol();
            if !groups.contains_key(&sym) {
                order.push(sym);
            }
            groups.entry(sym).or_default().push(m);
        }
    }

    // The instance context provides given dictionaries to every method body.
    let ctx_params = dict_param_names(constraints);
    let scope: Vec<(String, String)> = constraints
        .iter()
        .zip(ctx_params.iter())
        .map(|(c, p)| (c.class.name.resolve().unwrap_or_default(), p.clone()))
        .collect();

    let mut external_refs: Vec<Vec<String>> = Vec::new();
    let mut local_refs: Vec<String> = Vec::new();
    let mut fields: Vec<(String, JsExpr)> = Vec::new();
    for sym in &order {
        let eqs = &groups[sym];
        let method_ps = crate::interner::resolve(*sym).unwrap_or_default();
        let cds = method_dicts.get(&method_ps).cloned().unwrap_or_default();

        // The class method's signature may carry its own constraints (e.g.
        // `eq1 :: Eq a => f a -> f a -> Boolean`). Those become leading dict
        // params on the *method* value, layered over the instance context.
        let method_classes = method_leading.get(&method_ps).cloned().unwrap_or_default();
        let method_params = dict_param_names_from_classes(&method_classes);
        let mut method_scope = scope.clone();
        for (c, p) in method_classes.iter().zip(method_params.iter()) {
            method_scope.push((c.clone(), p.clone()));
        }

        let mut cg = expr::Cg::new(ctx, &cds, method_scope);
        let mut body = cg.value_group_body(eqs);
        for r in cg.take_external_refs() {
            if !external_refs.contains(&r) {
                external_refs.push(r);
            }
        }
        for r in cg.take_local_refs() {
            if !local_refs.contains(&r) {
                local_refs.push(r);
            }
        }
        for p in method_params.iter().rev() {
            body = JsExpr::Function(None, vec![p.clone()], vec![JsStmt::Return(body)]);
        }
        fields.push((method_ps, body));
    }

    // Superclass-accessor fields (e.g. `Semigroup0: () => semigroupX` on a
    // Monoid instance). Resolved with the instance context in scope.
    let inst_types: Vec<Type> = types
        .iter()
        .map(|t| crate::typecheck_db::types::convert_type_expr(t, &Default::default()))
        .collect();
    {
        let nd = no_dicts();
        let mut sc_cg = expr::Cg::new(ctx, &nd, scope.clone());
        let sc_fields = sc_cg.superclass_fields(&class_simple, &inst_types);
        if !sc_fields.is_empty() {
            for r in sc_cg.take_external_refs() {
                if !external_refs.contains(&r) {
                    external_refs.push(r);
                }
            }
            for r in sc_cg.take_local_refs() {
                if !local_refs.contains(&r) {
                    local_refs.push(r);
                }
            }
            // Prepend so superclass accessors precede methods (matches reference).
            let mut all = sc_fields;
            all.append(&mut fields);
            fields = all;
        }
    }

    let dict_obj = JsExpr::ObjectLit(fields);

    // Wrap with one parameter per (runtime) context constraint. Phase 5: the
    // dict-param names follow the `dict<Class>` convention so the body's call
    // sites can find them. Context constraints with the same class get numbered.
    let mut body = dict_obj;
    if !constraints.is_empty() {
        let params = dict_param_names(constraints);
        for p in params.iter().rev() {
            body = JsExpr::Function(None, vec![p.clone()], vec![JsStmt::Return(body)]);
        }
    }

    out.external_refs = external_refs;
    out.local_refs = local_refs;
    out.exports.push((inst_name.clone(), None));
    out.units.push(GenUnit {
        js_name: inst_name.clone(),
        stmts: vec![JsStmt::VarDecl(inst_name, Some(body))],
    });
    out
}

/// Dict parameter names from class simple names, numbering duplicates.
pub(crate) fn dict_param_names_from_classes(classes: &[String]) -> Vec<String> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    let mut names = Vec::with_capacity(classes.len());
    for class in classes {
        let n = counts.entry(class.clone()).or_insert(0);
        names.push(if *n == 0 { format!("dict{class}") } else { format!("dict{class}{n}") });
        *n += 1;
    }
    names
}

/// The class simple-names of the leading constraints in a (class-member) type
/// signature — i.e. the method's own dictionary parameters, e.g.
/// `eq1 :: Eq a => f a -> f a -> Boolean` → `["Eq"]`.
pub fn method_dict_classes(ty: &TypeExpr) -> Vec<String> {
    match ty {
        TypeExpr::Forall { ty, .. } => method_dict_classes(ty),
        TypeExpr::Constrained { constraints, ty, .. } => {
            let mut v: Vec<String> = constraints
                .iter()
                .map(|c| c.class.name.resolve().unwrap_or_default())
                .collect();
            v.extend(method_dict_classes(ty));
            v
        }
        _ => Vec::new(),
    }
}

/// Compute dict parameter names for a constraint list, numbering duplicates of
/// the same class: `[Eq a, Eq b, Show c]` → `["dictEq", "dictEq1", "dictShow"]`.
pub(crate) fn dict_param_names(constraints: &[crate::cst::Constraint]) -> Vec<String> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    let mut names = Vec::with_capacity(constraints.len());
    for c in constraints {
        let class = c.class.name.resolve().unwrap_or_default();
        let n = counts.entry(class.clone()).or_insert(0);
        let name = if *n == 0 {
            format!("dict{class}")
        } else {
            format!("dict{class}{n}")
        };
        *n += 1;
        names.push(name);
    }
    names
}

/// Translate a `data` declaration: one JS unit per constructor, matching the
/// legacy runtime ABI (`new Ctor(value0, ...)` + curried `.create`; nullary →
/// `.value` singleton).
pub fn codegen_data_decl(decl: &ir::Decl) -> GenDecl {
    let mut out = GenDecl::default();
    let ir::Decl::Data { constructors, .. } = decl else { return out };
    for ctor in constructors {
        let ctor_js = ident_to_js(ctor.name.value.symbol());
        let n_fields = ctor.fields.len();
        let stmt = constructor_stmt(&ctor_js, n_fields);
        out.exports.push((ctor_js.clone(), None));
        out.units.push(GenUnit { js_name: ctor_js, stmts: vec![stmt] });
    }
    out
}

/// Translate a `newtype` declaration: the constructor is the identity
/// function (the wrapper is erased at runtime).
pub fn codegen_newtype_decl(decl: &ir::Decl) -> GenDecl {
    let mut out = GenDecl::default();
    let ir::Decl::Newtype { constructor, .. } = decl else { return out };
    let ctor_js = ident_to_js(constructor.value.symbol());
    let identity = JsExpr::Function(
        None,
        vec!["x".to_string()],
        vec![JsStmt::Return(JsExpr::Var("x".to_string()))],
    );
    out.exports.push((ctor_js.clone(), None));
    out.units.push(GenUnit {
        js_name: ctor_js.clone(),
        stmts: vec![JsStmt::VarDecl(ctor_js, Some(identity))],
    });
    out
}

/// Translate a `foreign import`: no body is generated — the value lives in the
/// FFI companion module and is re-exported from there. The member is recorded
/// under its *raw* PureScript name (the FFI file uses that name verbatim) so
/// the assembler emits `import * as $foreign` + `export { x } from "./foreign.js"`.
pub fn codegen_foreign_decl(decl: &ir::Decl) -> GenDecl {
    let mut out = GenDecl::default();
    let ir::Decl::Foreign { name, .. } = decl else { return out };
    let raw = name.value.resolve().unwrap_or_default();
    out.foreign_refs.push(raw);
    out
}

/// Build the `var Ctor = (function(){ ... })();` statement for a data
/// constructor with `n_fields` fields.
fn constructor_stmt(ctor_js: &str, n_fields: usize) -> JsStmt {
    if n_fields == 0 {
        // Nullary: singleton stored at `Ctor.value`.
        let iife_body = vec![
            JsStmt::Expr(JsExpr::Function(Some(ctor_js.to_string()), vec![], vec![])),
            JsStmt::Assign(
                JsExpr::Indexer(
                    Box::new(JsExpr::Var(ctor_js.to_string())),
                    Box::new(JsExpr::StringLit("value".to_string())),
                ),
                JsExpr::New(Box::new(JsExpr::Var(ctor_js.to_string())), vec![]),
            ),
            JsStmt::Return(JsExpr::Var(ctor_js.to_string())),
        ];
        let iife = JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], iife_body)),
            vec![],
        );
        return JsStmt::VarDecl(ctor_js.to_string(), Some(iife));
    }

    let field_names: Vec<String> = (0..n_fields).map(|i| format!("value{i}")).collect();
    let ctor_body: Vec<JsStmt> = field_names
        .iter()
        .map(|f| {
            JsStmt::Assign(
                JsExpr::Indexer(
                    Box::new(JsExpr::Var("this".to_string())),
                    Box::new(JsExpr::StringLit(f.clone())),
                ),
                JsExpr::Var(f.clone()),
            )
        })
        .collect();

    let mut create_func = JsExpr::New(
        Box::new(JsExpr::Var(ctor_js.to_string())),
        field_names.iter().map(|f| JsExpr::Var(f.clone())).collect(),
    );
    for f in field_names.iter().rev() {
        create_func = JsExpr::Function(None, vec![f.clone()], vec![JsStmt::Return(create_func)]);
    }

    let iife_body = vec![
        JsStmt::Expr(JsExpr::Function(
            Some(ctor_js.to_string()),
            field_names.clone(),
            ctor_body,
        )),
        JsStmt::Assign(
            JsExpr::Indexer(
                Box::new(JsExpr::Var(ctor_js.to_string())),
                Box::new(JsExpr::StringLit("create".to_string())),
            ),
            create_func,
        ),
        JsStmt::Return(JsExpr::Var(ctor_js.to_string())),
    ];
    let iife = JsExpr::App(
        Box::new(JsExpr::Function(None, vec![], iife_body)),
        vec![],
    );
    JsStmt::VarDecl(ctor_js.to_string(), Some(iife))
}

/// A throwing JS expression used as a placeholder for not-yet-supported
/// constructs. Calling it at runtime makes the gap obvious in tests.
pub(crate) fn unsupported(what: &str) -> JsExpr {
    JsExpr::App(
        Box::new(JsExpr::Function(
            None,
            vec![],
            vec![JsStmt::Throw(JsExpr::App(
                Box::new(JsExpr::Var("Error".to_string())),
                vec![JsExpr::StringLit(format!("codegen: unsupported {what}"))],
            ))],
        )),
        vec![],
    )
}
