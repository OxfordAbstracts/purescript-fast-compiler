use std::collections::{HashMap, HashSet};

use crate::ast::span::Span;
use crate::cst::{TypeExpr, TypeField};
use crate::interner::Symbol;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;

/// Check for duplicate labels in a list of type fields, returning a DuplicateLabel error if found.
fn check_duplicate_type_fields(record_span: Span, fields: &[TypeField]) -> Result<(), TypeError> {
    let mut label_spans: HashMap<Symbol, Vec<Span>> = HashMap::new();
    for field in fields {
        label_spans.entry(field.label.value).or_default().push(field.span);
    }
    for (name, spans) in &label_spans {
        if spans.len() > 1 {
            return Err(TypeError::DuplicateLabel {
                record_span,
                field_spans: spans.clone(),
                name: *name,
            });
        }
    }
    Ok(())
}

/// Convert a CST TypeExpr (parsed surface syntax) into the internal Type representation.
/// Used for type annotations like `(expr :: Type)`.
///
/// `type_ops` maps type-level operator symbols to their target type constructor names,
/// populated from `infixr N type TypeName as op` declarations.
///
/// `known_types` is the set of type constructor names currently in scope.
/// If a `TypeExpr::Constructor` name is not in this set, an `UnknownType` error
/// is returned.
pub fn convert_type_expr(ty: &TypeExpr, type_ops: &HashMap<Symbol, Symbol>, known_types: &HashSet<Symbol>) -> Result<Type, TypeError> {
    match ty {
        TypeExpr::Constructor { span, name } => {
            if !known_types.is_empty() && !known_types.contains(&name.name) {
                return Err(TypeError::UnknownType {
                    span: *span,
                    name: name.name,
                });
            }
            Ok(Type::Con(name.name))
        }

        TypeExpr::Var { name, .. } => Ok(Type::Var(name.value)),

        TypeExpr::Function { from, to, .. } => {
            let from_ty = convert_type_expr(from, type_ops, known_types)?;
            let to_ty = convert_type_expr(to, type_ops, known_types)?;
            Ok(Type::fun(from_ty, to_ty))
        }

        TypeExpr::App { constructor, arg, .. } => {
            let f = convert_type_expr(constructor, type_ops, known_types)?;
            let a = convert_type_expr(arg, type_ops, known_types)?;
            Ok(Type::app(f, a))
        }

        TypeExpr::Forall { vars, ty, .. } => {
            let var_symbols: Vec<_> = vars.iter().map(|v| v.value).collect();
            let body = convert_type_expr(ty, type_ops, known_types)?;
            Ok(Type::Forall(var_symbols, Box::new(body)))
        }

        TypeExpr::Parens { ty, .. } => convert_type_expr(ty, type_ops, known_types),

        // Strip constraints for now (no typeclass solving yet)
        TypeExpr::Constrained { ty, .. } => convert_type_expr(ty, type_ops, known_types),

        TypeExpr::Record { span, fields } => {
            // Check for duplicate labels
            check_duplicate_type_fields(*span, fields)?;
            let field_types: Vec<_> = fields
                .iter()
                .map(|f| {
                    let ty = convert_type_expr(&f.ty, type_ops, known_types)?;
                    Ok((f.label.value, ty))
                })
                .collect::<Result<_, TypeError>>()?;
            Ok(Type::Record(field_types, None))
        }

        TypeExpr::Row { span, fields, tail } => {
            // Check for duplicate labels
            check_duplicate_type_fields(*span, fields)?;
            let field_types: Vec<_> = fields
                .iter()
                .map(|f| {
                    let ty = convert_type_expr(&f.ty, type_ops, known_types)?;
                    Ok((f.label.value, ty))
                })
                .collect::<Result<_, TypeError>>()?;
            let tail_ty = tail
                .as_ref()
                .map(|t| convert_type_expr(t, type_ops, known_types))
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

        // Kind annotations: just strip the kind and convert the inner type
        TypeExpr::Kinded { ty, .. } => convert_type_expr(ty, type_ops, known_types),

        // Type-level string literal
        TypeExpr::StringLiteral { value, .. } => {
            Ok(Type::TypeString(crate::interner::intern(value)))
        }

        // Type-level integer literal
        TypeExpr::IntLiteral { value, .. } => {
            Ok(Type::TypeInt(*value))
        }

        // Type-level operators: desugar `left op right` to `App(App(Con(target), left), right)`
        // where `target` is resolved from the type operator map if available.
        TypeExpr::TypeOp { left, op, right, .. } => {
            let left_ty = convert_type_expr(left, type_ops, known_types)?;
            let right_ty = convert_type_expr(right, type_ops, known_types)?;
            let op_name = op.value.name;
            let resolved = type_ops.get(&op_name).copied().unwrap_or(op_name);
            let op_ty = Type::Con(resolved);
            Ok(Type::app(Type::app(op_ty, left_ty), right_ty))
        }
    }
}
