use crate::cst::TypeExpr;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;

/// Convert a CST TypeExpr (parsed surface syntax) into the internal Type representation.
/// Used for type annotations like `(expr :: Type)`.
pub fn convert_type_expr(ty: &TypeExpr) -> Result<Type, TypeError> {
    match ty {
        TypeExpr::Constructor { name, .. } => Ok(Type::Con(name.name)),

        TypeExpr::Var { name, .. } => Ok(Type::Var(name.value)),

        TypeExpr::Function { from, to, .. } => {
            let from_ty = convert_type_expr(from)?;
            let to_ty = convert_type_expr(to)?;
            Ok(Type::fun(from_ty, to_ty))
        }

        TypeExpr::App { constructor, arg, .. } => {
            let f = convert_type_expr(constructor)?;
            let a = convert_type_expr(arg)?;
            Ok(Type::app(f, a))
        }

        TypeExpr::Forall { vars, ty, .. } => {
            let var_symbols: Vec<_> = vars.iter().map(|v| v.value).collect();
            let body = convert_type_expr(ty)?;
            Ok(Type::Forall(var_symbols, Box::new(body)))
        }

        TypeExpr::Parens { ty, .. } => convert_type_expr(ty),

        other => Err(TypeError::NotImplemented {
            span: other.span(),
            feature: format!("type conversion for this type expression form"),
        }),
    }
}
