/// Convert PureScript internal types to TypeScript type annotations.

use crate::codegen::js_ast::TsType;
use crate::interner::{self, Symbol};
use crate::typechecker::types::{Type, Scheme};

/// Convert a PureScript Type to a TsType for TypeScript output.
pub fn ps_type_to_ts(ty: &Type) -> TsType {
    match ty {
        Type::Con(qi) => con_to_ts(qi.name),
        Type::Fun(from, to) => {
            let param_ty = ps_type_to_ts(from);
            let ret_ty = ps_type_to_ts(to);
            TsType::Function(vec![("x".to_string(), param_ty)], Box::new(ret_ty))
        }
        Type::App(f, arg) => {
            // Collect spine: f a b c → (f, [a, b, c])
            let (head, args) = collect_app_spine(ty);
            match head {
                Type::Con(qi) => {
                    let name = symbol_to_string(qi.name);
                    match name.as_str() {
                        "Array" if args.len() == 1 => {
                            TsType::Array(Box::new(ps_type_to_ts(&args[0])))
                        }
                        "Effect" | "Aff" if args.len() == 1 => {
                            // Effect a → () => a
                            let ret = ps_type_to_ts(&args[0]);
                            TsType::Function(vec![], Box::new(ret))
                        }
                        _ => {
                            let ts_args: Vec<TsType> = args.iter().map(|a| ps_type_to_ts(a)).collect();
                            TsType::TypeRef(name, ts_args)
                        }
                    }
                }
                _ => {
                    // HKT or complex application — fall back to any
                    TsType::Any
                }
            }
        }
        Type::Var(sym) => {
            let name = symbol_to_string(*sym);
            // Strip leading $ from internal names
            let clean = if name.starts_with('$') { &name[1..] } else { &name };
            // Uppercase first letter for TypeScript convention
            let ts_name = {
                let mut chars = clean.chars();
                match chars.next() {
                    Some(c) => format!("{}{}", c.to_uppercase(), chars.as_str()),
                    None => clean.to_string(),
                }
            };
            TsType::TypeVar(ts_name)
        }
        Type::Forall(vars, body) => {
            // Just convert the body — generic params are handled at the declaration site
            ps_type_to_ts(body)
        }
        Type::Record(fields, _tail) => {
            let ts_fields: Vec<(String, TsType)> = fields
                .iter()
                .map(|(label, ty)| (symbol_to_string(*label), ps_type_to_ts(ty)))
                .collect();
            TsType::Object(ts_fields)
        }
        Type::Unif(_) => TsType::Any,
        Type::TypeString(_) => TsType::String,
        Type::TypeInt(_) => TsType::Number,
    }
}

/// Convert a curried function type into a multi-param TypeScript function type.
/// PureScript: a -> b -> c → TS: (x: a, y: b) => c
pub fn uncurry_function_type(ty: &Type) -> Option<(Vec<TsType>, TsType)> {
    let mut params = Vec::new();
    let mut current = ty;

    // Skip forall
    if let Type::Forall(_, body) = current {
        current = body;
    }

    while let Type::Fun(from, to) = current {
        params.push(ps_type_to_ts(from));
        current = to;
    }

    if params.is_empty() {
        return None;
    }

    Some((params, ps_type_to_ts(current)))
}

/// Convert a Scheme to a TsType, stripping forall vars.
pub fn scheme_to_ts(scheme: &Scheme) -> TsType {
    ps_type_to_ts(&scheme.ty)
}

/// Extract generic type parameter names from a Scheme's forall vars.
pub fn scheme_type_params(scheme: &Scheme) -> Vec<String> {
    let mut params = Vec::new();
    collect_forall_params(&scheme.ty, &mut params);
    // Also include forall_vars from the scheme itself
    for var in &scheme.forall_vars {
        let name = symbol_to_string(*var);
        let clean = if name.starts_with('$') { name[1..].to_string() } else { name };
        let ts_name = uppercase_first(&clean);
        if !params.contains(&ts_name) {
            params.push(ts_name);
        }
    }
    params
}

fn collect_forall_params(ty: &Type, params: &mut Vec<String>) {
    if let Type::Forall(vars, body) = ty {
        for (var, _visible) in vars {
            let name = symbol_to_string(*var);
            let clean = if name.starts_with('$') { name[1..].to_string() } else { name };
            let ts_name = uppercase_first(&clean);
            if !params.contains(&ts_name) {
                params.push(ts_name);
            }
        }
        collect_forall_params(body, params);
    }
}

fn uppercase_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => format!("{}{}", c.to_uppercase(), chars.as_str()),
        None => s.to_string(),
    }
}

/// Collect type application spine: `App(App(f, a), b)` → `(f, [a, b])`
fn collect_app_spine(ty: &Type) -> (&Type, Vec<&Type>) {
    let mut args = Vec::new();
    let mut current = ty;
    while let Type::App(f, arg) = current {
        args.push(arg.as_ref());
        current = f;
    }
    args.reverse();
    (current, args)
}

fn con_to_ts(name: Symbol) -> TsType {
    let s = symbol_to_string(name);
    match s.as_str() {
        "Int" | "Number" => TsType::Number,
        "String" | "Char" => TsType::String,
        "Boolean" => TsType::Boolean,
        "Unit" => TsType::Void,
        _ => TsType::TypeRef(s, vec![]),
    }
}

fn symbol_to_string(sym: Symbol) -> String {
    interner::resolve(sym).unwrap_or_else(|| format!("unknown_{:?}", sym))
}

/// Convert a CST TypeExpr directly to TsType (for instance heads/constraints
/// where we don't have the internal Type representation).
pub fn cst_type_expr_to_ts(ty: &crate::cst::TypeExpr) -> TsType {
    use crate::cst::TypeExpr;
    match ty {
        TypeExpr::Constructor { name, .. } => con_to_ts(name.name),
        TypeExpr::Var { name, .. } => {
            let s = symbol_to_string(name.value);
            let clean = if s.starts_with('$') { &s[1..] } else { &s };
            TsType::TypeVar(uppercase_first(clean))
        }
        TypeExpr::App { constructor, arg, .. } => {
            // Collect spine
            let (head, args) = collect_cst_app_spine(ty);
            if let TypeExpr::Constructor { name, .. } = head {
                let s = symbol_to_string(name.name);
                match s.as_str() {
                    "Array" if args.len() == 1 => TsType::Array(Box::new(cst_type_expr_to_ts(args[0]))),
                    _ => {
                        let ts_args: Vec<TsType> = args.iter().map(|a| cst_type_expr_to_ts(a)).collect();
                        match con_to_ts(name.name) {
                            TsType::TypeRef(n, _) => TsType::TypeRef(n, ts_args),
                            simple => simple, // Int, String, etc — ignore args
                        }
                    }
                }
            } else {
                TsType::Any
            }
        }
        TypeExpr::Function { from, to, .. } => {
            let param = cst_type_expr_to_ts(from);
            let ret = cst_type_expr_to_ts(to);
            TsType::Function(vec![("x".to_string(), param)], Box::new(ret))
        }
        TypeExpr::Record { fields, .. } => {
            let ts_fields: Vec<(String, TsType)> = fields.iter().map(|f| {
                (symbol_to_string(f.label.value), cst_type_expr_to_ts(&f.ty))
            }).collect();
            TsType::Object(ts_fields)
        }
        TypeExpr::Forall { ty, .. } => cst_type_expr_to_ts(ty),
        TypeExpr::Constrained { ty, .. } => cst_type_expr_to_ts(ty),
        TypeExpr::Parens { ty, .. } => cst_type_expr_to_ts(ty),
        _ => TsType::Any,
    }
}

fn collect_cst_app_spine(ty: &crate::cst::TypeExpr) -> (&crate::cst::TypeExpr, Vec<&crate::cst::TypeExpr>) {
    use crate::cst::TypeExpr;
    let mut args = Vec::new();
    let mut current = ty;
    while let TypeExpr::App { constructor, arg, .. } = current {
        args.push(arg.as_ref());
        current = constructor;
    }
    args.reverse();
    (current, args)
}
