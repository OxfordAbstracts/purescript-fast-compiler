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

        // Strip constraints for now (no typeclass solving yet)
        TypeExpr::Constrained { ty, .. } => convert_type_expr(ty),

        TypeExpr::Record { fields, .. } => {
            let field_types: Vec<_> = fields
                .iter()
                .map(|f| {
                    let ty = convert_type_expr(&f.ty)?;
                    Ok((f.label.value, ty))
                })
                .collect::<Result<_, TypeError>>()?;
            Ok(Type::Record(field_types, None))
        }

        TypeExpr::Row { fields, tail, .. } => {
            let field_types: Vec<_> = fields
                .iter()
                .map(|f| {
                    let ty = convert_type_expr(&f.ty)?;
                    Ok((f.label.value, ty))
                })
                .collect::<Result<_, TypeError>>()?;
            let tail_ty = tail
                .as_ref()
                .map(|t| convert_type_expr(t))
                .transpose()?
                .map(Box::new);
            Ok(Type::Record(field_types, tail_ty))
        }

        TypeExpr::Wildcard { .. } => {
            // Wildcard types become a fresh type — but we don't have access to InferCtx here.
            // Use Type::Var with a special name that will be instantiated later.
            Ok(Type::Var(crate::interner::intern("_")))
        }

        TypeExpr::Hole { name, .. } => {
            Ok(Type::Var(*name))
        }

        other => Err(TypeError::NotImplemented {
            span: other.span(),
            feature: format!("type conversion for this type expression form"),
        }),
    }
}
