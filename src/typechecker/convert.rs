use std::collections::{HashMap, HashSet};

use crate::cst::TypeExpr;
use crate::interner::Symbol;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;

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
    super::check_deadline();
    match ty {
        TypeExpr::Constructor { span, name } => {
            // Check if this is a type operator used as a constructor (e.g. `(/\)`)
            if let Some(&target) = type_ops.get(&name.name) {
                return Ok(Type::Con(target));
            }
            if !known_types.is_empty() {
                // Check both unqualified and qualified name (e.g. RL.Cons)
                let found = known_types.contains(&name.name) || name.module.map_or(false, |m| {
                    let mod_str = crate::interner::resolve(m).unwrap_or_default();
                    let name_str = crate::interner::resolve(name.name).unwrap_or_default();
                    known_types.contains(&crate::interner::intern(&format!("{}.{}", mod_str, name_str)))
                });
                if !found {
                    return Err(TypeError::UnknownType {
                        span: *span,
                        name: name.name,
                    });
                }
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
            // Normalize `Record (row)` where the row is a CST Row type (parsed as Record)
            // to unwrap the redundant `App(Con("Record"), Record(...))`.
            // This only handles the case where the argument is already a Record type
            // (i.e., it came from a `TypeExpr::Row`). Type variables like `Record r` are
            // left as `App(Con("Record"), Var("r"))` to avoid issues with type alias expansion.
            if let Type::Con(sym) = &f {
                if crate::interner::resolve(*sym).unwrap_or_default() == "Record" {
                    if let Type::Record(fields, tail) = a {
                        return Ok(Type::Record(fields, tail));
                    }
                }
            }
            Ok(Type::app(f, a))
        }

        TypeExpr::Forall { vars, ty, .. } => {
            let var_symbols: Vec<_> = vars.iter().map(|(v, visible, _kind)| (v.value, *visible)).collect();
            // Collect all vars declared in this forall for ordering validation
            let all_forall_vars: HashSet<Symbol> = vars.iter().map(|(v, _, _)| v.value).collect();
            let mut bound_in_forall: HashSet<Symbol> = HashSet::new();
            // Validate kind annotations left-to-right:
            // 1. Check unknown type constructors (e.g. `forall (a :: Typ)` where Typ is undefined)
            // 2. Check forward references within forall (e.g. `forall (a :: k) k.` uses k before declaring it)
            for (v, _visible, kind) in vars {
                if let Some(kind_expr) = kind {
                    convert_type_expr(kind_expr, type_ops, known_types)?;
                    // Check for forward references: kind vars that are declared later in this forall
                    check_forall_kind_ordering(kind_expr, &bound_in_forall, &all_forall_vars)?;
                }
                bound_in_forall.insert(v.value);
            }
            let body = convert_type_expr(ty, type_ops, known_types)?;
            Ok(Type::Forall(var_symbols, Box::new(body)))
        }

        TypeExpr::Parens { ty, .. } => convert_type_expr(ty, type_ops, known_types),

        // Strip constraints for now (no typeclass solving yet)
        TypeExpr::Constrained { ty, .. } => convert_type_expr(ty, type_ops, known_types),

        TypeExpr::Record { fields, .. } => {
            let field_types: Vec<_> = fields
                .iter()
                .map(|f| {
                    let ty = convert_type_expr(&f.ty, type_ops, known_types)?;
                    Ok((f.label.value, ty))
                })
                .collect::<Result<_, TypeError>>()?;
            Ok(Type::Record(field_types, None))
        }

        TypeExpr::Row { fields, tail, .. } => {
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
                    name: name.value,
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
        TypeExpr::Parens { ty, .. } => {
            check_forall_kind_ordering(ty, bound, all_forall_vars)
        }
        _ => Ok(()),
    }
}
