use std::collections::{HashMap, HashSet};

use crate::ast::TypeExpr;
use crate::cst::{QualifiedIdent, unqualified_ident};
use crate::interner::Symbol;
use crate::names::{TypeVarName, LabelName};
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;

/// Convert an AST TypeExpr into the internal Type representation.
/// Used for type annotations like `(expr :: Type)`.
///
/// `type_ops` maps type-level operator symbols to their target type constructor names,
/// populated from `infixr N type TypeName as op` declarations.
///
/// Type name validation is handled by the AST converter (src/ast.rs) during CST→AST
/// conversion. By the time a TypeExpr reaches this function, all Constructor names
/// have already been verified to be in scope.
pub fn convert_type_expr(ty: &TypeExpr, type_ops: &HashMap<QualifiedIdent, QualifiedIdent>) -> Result<Type, TypeError> {
    match ty {
        TypeExpr::Constructor { name, .. } => {
            // Check if this is a type operator used as a constructor (e.g. `(/\)`)
            if let Some(&target) = type_ops.get(&name) {
                return Ok(Type::Con(target));
            }
            Ok(Type::Con(*name))
        }

        TypeExpr::Var { name, .. } => Ok(Type::Var(TypeVarName::new(name.value))),

        TypeExpr::Function { from, to, .. } => {
            let from_ty = convert_type_expr(from, type_ops)?;
            let to_ty = convert_type_expr(to, type_ops)?;
            Ok(Type::fun(from_ty, to_ty))
        }

        TypeExpr::App { constructor, arg, .. } => {
            let f = convert_type_expr(constructor, type_ops)?;
            let a = convert_type_expr(arg, type_ops)?;
            // Normalize `Record (row)` where the row is a CST Row type (parsed as Record)
            // to unwrap the redundant `App(Con("Record"), Record(...))`.
            // This only handles the case where the argument is already a Record type
            // (i.e., it came from a `TypeExpr::Row`). Type variables like `Record r` are
            // left as `App(Con("Record"), Var("r"))` to avoid issues with type alias expansion.
            if let Type::Con(sym) = &f {
                if sym == &unqualified_ident("Record") {
                    if let Type::Record(fields, tail) = a {
                        return Ok(Type::Record(fields, tail));
                    }
                }
            }
            // Normalize `(->) a b` to `Fun(a, b)` — the function type constructor
            // applied to two arguments should become the function type.
            if let Type::App(inner_f, inner_a) = &f {
                if let Type::Con(sym) = inner_f.as_ref() {
                    if crate::interner::resolve(sym.name).unwrap_or_default() == "->" {
                        return Ok(Type::fun(inner_a.as_ref().clone(), a));
                    }
                }
            }
            Ok(Type::app(f, a))
        }

        TypeExpr::Forall { vars, ty, .. } => {
            let var_symbols: Vec<_> = vars.iter().map(|(v, visible, _kind)| (TypeVarName::new(v.value), *visible)).collect();
            // Collect all vars declared in this forall for ordering validation
            let all_forall_vars: HashSet<Symbol> = vars.iter().map(|(v, _, _)| v.value).collect();
            let mut bound_in_forall: HashSet<Symbol> = HashSet::new();
            // Validate kind annotations left-to-right:
            // 1. Check unknown type constructors (e.g. `forall (a :: Typ)` where Typ is undefined)
            // 2. Check forward references within forall (e.g. `forall (a :: k) k.` uses k before declaring it)
            for (v, _visible, kind) in vars {
                if let Some(kind_expr) = kind {
                    convert_type_expr(kind_expr, type_ops)?;
                    // Check for forward references: kind vars that are declared later in this forall
                    check_forall_kind_ordering(kind_expr, &bound_in_forall, &all_forall_vars)?;
                }
                bound_in_forall.insert(v.value);
            }
            let body = convert_type_expr(ty, type_ops)?;
            Ok(Type::Forall(var_symbols, Box::new(body)))
        }

        // Strip constraints for now (no typeclass solving yet)
        TypeExpr::Constrained { ty, .. } => convert_type_expr(ty, type_ops),

        TypeExpr::Record { fields, .. } => {
            let field_types: Vec<_> = fields
                .iter()
                .map(|f| {
                    let ty = convert_type_expr(&f.ty, type_ops)?;
                    Ok((LabelName::new(f.label.value), ty))
                })
                .collect::<Result<_, TypeError>>()?;
            Ok(Type::Record(field_types, None))
        }

        TypeExpr::Row { fields, tail, is_record, .. } => {
            let field_types: Vec<_> = fields
                .iter()
                .map(|f| {
                    let ty = convert_type_expr(&f.ty, type_ops)?;
                    Ok((LabelName::new(f.label.value), ty))
                })
                .collect::<Result<_, TypeError>>()?;
            // Normalize bare row `(| r)` (not record `{ | r }`) with no fields to
            // just the tail variable. This ensures that `IProp (| r) i` passes the
            // row variable directly to the alias, rather than wrapping it in an extra
            // Record layer that prevents unification with bare type variables.
            if !*is_record && field_types.is_empty() {
                if let Some(t) = tail {
                    return convert_type_expr(t, type_ops);
                }
            }
            let tail_ty = tail
                .as_ref()
                .map(|t| convert_type_expr(t, type_ops))
                .transpose()?
                .map(Box::new);
            Ok(Type::Record(field_types, tail_ty))
        }

        TypeExpr::Wildcard { .. } => {
            // Wildcard types become a fresh type — but we don't have access to InferCtx here.
            // Use Type::Var with a special name that will be instantiated later.
            Ok(Type::Var(TypeVarName::new(crate::interner::intern("_"))))
        }

        TypeExpr::Hole { name, .. } => {
            Ok(Type::Var(TypeVarName::new(*name)))
        }

        // Kind annotations: just strip the kind and convert the inner type
        TypeExpr::Kinded { ty, .. } => convert_type_expr(ty, type_ops),

        // Type-level string literal
        TypeExpr::StringLiteral { value, .. } => {
            Ok(Type::TypeString(crate::interner::intern(value)))
        }

        // Type-level integer literal
        TypeExpr::IntLiteral { value, .. } => {
            Ok(Type::TypeInt(*value))
        }

        // These are only used for as-pattern parsing through VTA; they should
        // never reach type conversion (they're converted to binders instead).
        TypeExpr::ArrayPattern { .. } | TypeExpr::AsPattern { .. } => {
            Ok(Type::Var(TypeVarName::new(crate::interner::intern("_"))))
        }

    }
}

/// Check if a type expression references any names that are in scope conflict.
/// Returns the first conflicting name found, if any.
pub fn find_type_scope_conflict(ty: &TypeExpr, conflicts: &HashSet<Symbol>) -> Option<(crate::span::Span, Symbol)> {
    match ty {
        TypeExpr::Constructor { name, span, .. } => {
            if name.module.is_none() && conflicts.contains(&name.name) {
                return Some((*span, name.name));
            }
            None
        }
        TypeExpr::App { constructor, arg, .. } => {
            find_type_scope_conflict(constructor, conflicts)
                .or_else(|| find_type_scope_conflict(arg, conflicts))
        }
        TypeExpr::Function { from, to, .. } => {
            find_type_scope_conflict(from, conflicts)
                .or_else(|| find_type_scope_conflict(to, conflicts))
        }
        TypeExpr::Forall { ty, vars, .. } => {
            for (_, _, kind) in vars {
                if let Some(k) = kind {
                    if let Some(r) = find_type_scope_conflict(k, conflicts) {
                        return Some(r);
                    }
                }
            }
            find_type_scope_conflict(ty, conflicts)
        }
        TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for arg in &c.args {
                    if let Some(r) = find_type_scope_conflict(arg, conflicts) {
                        return Some(r);
                    }
                }
            }
            find_type_scope_conflict(ty, conflicts)
        }
        TypeExpr::Kinded { ty, .. } => {
            find_type_scope_conflict(ty, conflicts)
        }
        TypeExpr::Record { fields, .. } => {
            for f in fields {
                if let Some(r) = find_type_scope_conflict(&f.ty, conflicts) {
                    return Some(r);
                }
            }
            None
        }
        TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                if let Some(r) = find_type_scope_conflict(&f.ty, conflicts) {
                    return Some(r);
                }
            }
            if let Some(t) = tail {
                return find_type_scope_conflict(t, conflicts);
            }
            None
        }
        _ => None,
    }
}

/// Check that kind annotations in forall vars don't forward-reference variables
/// declared later in the same forall. E.g. `forall (a :: k) k.` is invalid because
/// `k` is used before it's declared.
fn check_forall_kind_ordering(
    kind_expr: &TypeExpr,
    bound: &HashSet<Symbol>,
    all_forall_vars: &HashSet<Symbol>,
) -> Result<(), TypeError> {
    match kind_expr {
        TypeExpr::Var { span, name } => {
            // If the var is declared in this forall but not yet bound (forward reference)
            if all_forall_vars.contains(&name.value) && !bound.contains(&name.value) {
                return Err(TypeError::UndefinedTypeVariable {
                    span: *span,
                    name: TypeVarName::new(name.value),
                });
            }
            Ok(())
        }
        TypeExpr::App { constructor, arg, .. } => {
            check_forall_kind_ordering(constructor, bound, all_forall_vars)?;
            check_forall_kind_ordering(arg, bound, all_forall_vars)
        }
        TypeExpr::Function { from, to, .. } => {
            check_forall_kind_ordering(from, bound, all_forall_vars)?;
            check_forall_kind_ordering(to, bound, all_forall_vars)
        }
        TypeExpr::Forall { ty, .. } => {
            check_forall_kind_ordering(ty, bound, all_forall_vars)
        }
        _ => Ok(()),
    }
}
