use std::collections::HashMap;

use crate::ast::span::Span;
use crate::cst::TypeExpr;
use crate::interner::{self, Symbol};
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;
use crate::typechecker::unify::UnifyState;

/// Kind-checking state: a separate UnifyState for kind unification,
/// plus a mapping from type constructor names to their kinds.
pub struct KindState {
    pub state: UnifyState,
    /// Maps type constructor names (e.g. "Array", "Maybe") to their kinds.
    pub type_kinds: HashMap<Symbol, Type>,
}

impl KindState {
    /// Create a new KindState pre-populated with built-in (Prim) kinds.
    pub fn new() -> Self {
        let mut type_kinds = HashMap::new();
        let k_type = Type::kind_type();

        // Prim types with kind Type
        for name in &[
            "Int", "Number", "String", "Char", "Boolean", "Unit",
        ] {
            type_kinds.insert(interner::intern(name), k_type.clone());
        }

        // Array :: Type -> Type
        type_kinds.insert(
            interner::intern("Array"),
            Type::fun(k_type.clone(), k_type.clone()),
        );

        // Record :: Row Type -> Type
        type_kinds.insert(
            interner::intern("Record"),
            Type::fun(Type::kind_row_of(k_type.clone()), k_type.clone()),
        );

        // Function ((->) :: Type -> Type -> Type
        type_kinds.insert(
            interner::intern("->"),
            Type::fun(k_type.clone(), Type::fun(k_type.clone(), k_type.clone())),
        );
        type_kinds.insert(
            interner::intern("Function"),
            Type::fun(k_type.clone(), Type::fun(k_type.clone(), k_type.clone())),
        );

        // Prim.Row.Union :: forall k. Row k -> Row k -> Row k -> Constraint
        // (we don't need this for basic kind checking)

        // Type :: Type (kind of kinds — self-referential, but fine for our purposes)
        type_kinds.insert(interner::intern("Type"), k_type.clone());
        type_kinds.insert(interner::intern("Constraint"), k_type.clone());
        type_kinds.insert(interner::intern("Symbol"), k_type.clone());
        // Row :: Type -> Type (Row is a kind constructor)
        type_kinds.insert(
            interner::intern("Row"),
            Type::fun(k_type.clone(), k_type.clone()),
        );

        KindState {
            state: UnifyState::new(),
            type_kinds,
        }
    }

    /// Create a fresh kind unification variable.
    pub fn fresh_kind_var(&mut self) -> Type {
        Type::Unif(self.state.fresh_var())
    }

    /// Unify two kinds, mapping unification errors to kind-specific errors.
    pub fn unify_kinds(&mut self, span: Span, expected: &Type, found: &Type) -> Result<(), TypeError> {
        self.state.unify(span, expected, found).map_err(|e| match e {
            TypeError::UnificationError { span, expected, found } => {
                TypeError::KindMismatch { span, expected, found }
            }
            TypeError::InfiniteType { span, var, ty } => {
                TypeError::InfiniteKind { span, var, ty }
            }
            other => other,
        })
    }

    /// Zonk a kind (resolve solved unification variables).
    pub fn zonk_kind(&mut self, k: Type) -> Type {
        self.state.zonk(k)
    }

    /// Register a type constructor with its kind.
    pub fn register_type(&mut self, name: Symbol, kind: Type) {
        self.type_kinds.insert(name, kind);
    }

    /// Look up the kind of a type constructor, freshening unsolved unification
    /// variables so that each usage gets its own copy (prevents cross-contamination
    /// between declarations that share kind variables).
    pub fn lookup_type_fresh(&mut self, name: Symbol) -> Option<Type> {
        let kind = self.type_kinds.get(&name)?.clone();
        let zonked = self.zonk_kind(kind);
        Some(self.freshen_unif_vars(&zonked))
    }

    /// Replace unsolved unification variables in a kind with fresh ones.
    /// This is like instantiation for polymorphic kinds but for unif vars.
    fn freshen_unif_vars(&mut self, ty: &Type) -> Type {
        let mut mapping = HashMap::new();
        self.freshen_unif_vars_inner(ty, &mut mapping)
    }

    fn freshen_unif_vars_inner(&mut self, ty: &Type, mapping: &mut HashMap<crate::typechecker::types::TyVarId, Type>) -> Type {
        match ty {
            Type::Unif(id) => {
                if let Some(solved) = self.state.probe(*id) {
                    self.freshen_unif_vars_inner(&solved, mapping)
                } else {
                    mapping.entry(*id).or_insert_with(|| self.fresh_kind_var()).clone()
                }
            }
            Type::Fun(from, to) => {
                Type::fun(
                    self.freshen_unif_vars_inner(from, mapping),
                    self.freshen_unif_vars_inner(to, mapping),
                )
            }
            Type::App(f, a) => {
                Type::app(
                    self.freshen_unif_vars_inner(f, mapping),
                    self.freshen_unif_vars_inner(a, mapping),
                )
            }
            Type::Forall(vars, body) => {
                Type::Forall(vars.clone(), Box::new(self.freshen_unif_vars_inner(body, mapping)))
            }
            _ => ty.clone(),
        }
    }

    /// Look up the kind of a type constructor (immutable reference).
    pub fn lookup_type(&self, name: Symbol) -> Option<&Type> {
        self.type_kinds.get(&name)
    }
}

/// Convert a CST TypeExpr used as a kind annotation into a Type representing a kind.
/// E.g., `Type -> Type` becomes `Fun(Con("Type"), Con("Type"))`.
pub fn convert_kind_expr(kind_expr: &TypeExpr) -> Type {
    match kind_expr {
        TypeExpr::Constructor { name, .. } => {
            Type::Con(name.name)
        }
        TypeExpr::Var { name, .. } => {
            Type::Var(name.value)
        }
        TypeExpr::Function { from, to, .. } => {
            Type::fun(convert_kind_expr(from), convert_kind_expr(to))
        }
        TypeExpr::App { constructor, arg, .. } => {
            Type::app(convert_kind_expr(constructor), convert_kind_expr(arg))
        }
        TypeExpr::Forall { vars, ty, .. } => {
            let var_symbols: Vec<_> = vars.iter().map(|(v, vis, _kind)| (v.value, *vis)).collect();
            Type::Forall(var_symbols, Box::new(convert_kind_expr(ty)))
        }
        TypeExpr::Parens { ty, .. } => convert_kind_expr(ty),
        TypeExpr::Kinded { ty, .. } => convert_kind_expr(ty),
        // Fallback for anything else (shouldn't appear in kind annotations)
        _ => Type::kind_type(),
    }
}

/// Infer the kind of a CST TypeExpr.
///
/// `ks` — the KindState with type constructor kinds and unification state
/// `type_var_kinds` — mapping from type variable names to their kinds
/// `type_ops` — mapping from type-level operator symbols to their target type constructor names
/// `self_type` — if Some, the name of the type currently being defined (used to avoid
///   freshening kind vars for self-referencing types, enabling infinite kind detection)
pub fn infer_kind(
    ks: &mut KindState,
    te: &TypeExpr,
    type_var_kinds: &HashMap<Symbol, Type>,
    type_ops: &HashMap<Symbol, Symbol>,
    self_type: Option<Symbol>,
) -> Result<Type, TypeError> {
    match te {
        TypeExpr::Constructor { name, .. } => {
            // Check if this is a type operator used as a constructor
            if let Some(&target) = type_ops.get(&name.name) {
                let lookup = if self_type == Some(target) {
                    ks.lookup_type(target).cloned()
                } else {
                    ks.lookup_type_fresh(target)
                };
                if let Some(kind) = lookup {
                    return Ok(kind);
                }
            }
            // For self-referencing types, don't freshen — this enables infinite kind detection
            let lookup = if self_type == Some(name.name) {
                ks.lookup_type(name.name).cloned()
            } else {
                ks.lookup_type_fresh(name.name)
            };
            match lookup {
                Some(kind) => Ok(kind),
                None => {
                    // Check for qualified name
                    if let Some(m) = name.module {
                        let mod_str = interner::resolve(m).unwrap_or_default();
                        let name_str = interner::resolve(name.name).unwrap_or_default();
                        let qualified = interner::intern(&format!("{}.{}", mod_str, name_str));
                        if let Some(kind) = ks.lookup_type_fresh(qualified) {
                            return Ok(kind);
                        }
                    }
                    // Unknown type constructor — use a fresh kind variable so its kind
                    // is inferred from usage. UnknownType errors are handled separately
                    // during the type conversion pass.
                    Ok(ks.fresh_kind_var())
                }
            }
        }

        TypeExpr::Var { name, .. } => {
            match type_var_kinds.get(&name.value) {
                Some(kind) => Ok(kind.clone()),
                None => {
                    // Unknown type variable — produce a fresh kind var
                    // This handles implicit kind polymorphism
                    Ok(ks.fresh_kind_var())
                }
            }
        }

        TypeExpr::App { span, constructor, arg } => {
            let f_kind = infer_kind(ks, constructor, type_var_kinds, type_ops, self_type)?;
            // Instantiate polymorphic (Forall) kinds before application
            let f_kind = instantiate_kind(ks, &f_kind);
            let a_kind = infer_kind(ks, arg, type_var_kinds, type_ops, self_type)?;

            // f_kind should be k1 -> k2; unify k1 with a_kind, return k2
            let result_kind = ks.fresh_kind_var();
            let expected_f_kind = Type::fun(a_kind, result_kind.clone());
            ks.unify_kinds(*span, &expected_f_kind, &f_kind)?;
            Ok(result_kind)
        }

        TypeExpr::Function { span, from, to } => {
            let k_type = Type::kind_type();
            let from_kind = infer_kind(ks, from, type_var_kinds, type_ops, self_type)?;
            ks.unify_kinds(*span, &k_type, &from_kind)?;
            let to_kind = infer_kind(ks, to, type_var_kinds, type_ops, self_type)?;
            ks.unify_kinds(*span, &k_type, &to_kind)?;
            Ok(k_type)
        }

        TypeExpr::Forall { vars, ty, .. } => {
            let mut inner_var_kinds = type_var_kinds.clone();
            for (v, _visible, kind_ann) in vars {
                let var_kind = match kind_ann {
                    Some(k) => convert_kind_expr(k),
                    None => ks.fresh_kind_var(),
                };
                inner_var_kinds.insert(v.value, var_kind);
            }
            infer_kind(ks, ty, &inner_var_kinds, type_ops, self_type)
        }

        TypeExpr::Constrained { constraints, ty, .. } => {
            // Check constraint argument kinds
            for constraint in constraints {
                for arg in &constraint.args {
                    infer_kind(ks, arg, type_var_kinds, type_ops, self_type)?;
                }
            }
            infer_kind(ks, ty, type_var_kinds, type_ops, self_type)
        }

        TypeExpr::Record { fields, .. } => {
            // Record fields are typically kind Type, but we just infer each field's
            // kind without constraining — the unification will catch mismatches.
            for field in fields {
                let _field_kind = infer_kind(ks, &field.ty, type_var_kinds, type_ops, self_type)?;
            }
            Ok(Type::kind_type())
        }

        TypeExpr::Row { span, fields, tail, is_record } => {
            // Row fields can have any kind k (polykinded rows: Row k).
            // All fields must have the same kind.
            let elem_kind = if fields.is_empty() {
                ks.fresh_kind_var()
            } else {
                let first_kind = infer_kind(ks, &fields[0].ty, type_var_kinds, type_ops, self_type)?;
                for field in &fields[1..] {
                    let field_kind = infer_kind(ks, &field.ty, type_var_kinds, type_ops, self_type)?;
                    ks.unify_kinds(*span, &first_kind, &field_kind)?;
                }
                first_kind
            };
            if let Some(tail_expr) = tail {
                let tail_kind = infer_kind(ks, tail_expr, type_var_kinds, type_ops, self_type)?;
                if !*is_record {
                    // Bare row: tail should have kind Row k
                    let row_k = Type::kind_row_of(elem_kind.clone());
                    ks.unify_kinds(*span, &row_k, &tail_kind)?;
                }
            }
            if *is_record {
                // { fields | tail } is sugar for Record (fields | tail), kind Type
                Ok(Type::kind_type())
            } else {
                // ( fields | tail ) is a bare row, kind Row k
                Ok(Type::kind_row_of(elem_kind))
            }
        }

        TypeExpr::Parens { ty, .. } => infer_kind(ks, ty, type_var_kinds, type_ops, self_type),

        TypeExpr::Kinded { span, ty, kind } => {
            let inferred_kind = infer_kind(ks, ty, type_var_kinds, type_ops, self_type)?;
            let annotated_kind = convert_kind_expr(kind);
            ks.unify_kinds(*span, &annotated_kind, &inferred_kind)?;
            Ok(annotated_kind)
        }

        TypeExpr::TypeOp { span, left, op, right } => {
            let op_name = op.value.name;
            let resolved = type_ops.get(&op_name).copied().unwrap_or(op_name);
            let op_kind = match ks.lookup_type(resolved) {
                Some(k) => k.clone(),
                None => ks.fresh_kind_var(),
            };
            let left_kind = infer_kind(ks, left, type_var_kinds, type_ops, self_type)?;
            let right_kind = infer_kind(ks, right, type_var_kinds, type_ops, self_type)?;

            // op :: k1 -> k2 -> k3
            let result_kind = ks.fresh_kind_var();
            let k2_to_result = Type::fun(right_kind, result_kind.clone());
            let expected_op_kind = Type::fun(left_kind, k2_to_result);
            ks.unify_kinds(*span, &expected_op_kind, &op_kind)?;
            Ok(result_kind)
        }

        TypeExpr::StringLiteral { .. } => Ok(Type::kind_symbol()),
        TypeExpr::IntLiteral { .. } => Ok(Type::kind_int()),

        TypeExpr::Wildcard { .. } => Ok(ks.fresh_kind_var()),
        TypeExpr::Hole { .. } => Ok(ks.fresh_kind_var()),
    }
}

/// Infer the kind of a data type declaration.
/// Returns the inferred kind (e.g., `Type -> Type -> Type` for `data Pair a b = ...`).
pub fn infer_data_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    type_var_kind_anns: &[Option<Box<TypeExpr>>],
    constructors: &[crate::cst::DataConstructor],
    span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let k_type = Type::kind_type();
    let mut var_kinds = HashMap::new();

    // Assign kind to each type variable (from annotation or fresh)
    for (i, tv) in type_vars.iter().enumerate() {
        let var_kind = if let Some(Some(kind_ann)) = type_var_kind_anns.get(i) {
            convert_kind_expr(kind_ann)
        } else {
            ks.fresh_kind_var()
        };
        var_kinds.insert(tv.value, var_kind);
    }

    // Check each constructor field has kind Type
    // Pass self_type=Some(name) to avoid freshening self-references (enables infinite kind detection)
    for ctor in constructors {
        for field_te in &ctor.fields {
            let field_kind = infer_kind(ks, field_te, &var_kinds, type_ops, Some(name))?;
            ks.unify_kinds(span, &k_type, &field_kind)?;
        }
    }

    // Build the overall kind: k1 -> k2 -> ... -> Type
    let mut result_kind = k_type;
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Infer the kind of a newtype declaration.
pub fn infer_newtype_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    field_ty: &TypeExpr,
    span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let k_type = Type::kind_type();
    let mut var_kinds = HashMap::new();

    for tv in type_vars {
        let var_kind = ks.fresh_kind_var();
        var_kinds.insert(tv.value, var_kind);
    }

    // The single field must have kind Type
    let field_kind = infer_kind(ks, field_ty, &var_kinds, type_ops, Some(name))?;
    ks.unify_kinds(span, &k_type, &field_kind)?;

    // Build kind: k1 -> k2 -> ... -> Type
    let mut result_kind = k_type;
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Infer the kind of a type alias declaration.
pub fn infer_type_alias_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    body: &TypeExpr,
    _span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let mut var_kinds = HashMap::new();

    for tv in type_vars {
        let var_kind = ks.fresh_kind_var();
        var_kinds.insert(tv.value, var_kind);
    }

    let body_kind = infer_kind(ks, body, &var_kinds, type_ops, Some(name))?;

    // Build kind: k1 -> k2 -> ... -> body_kind
    let mut result_kind = body_kind;
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Infer the kind of a class declaration.
/// Classes have kind `k1 -> k2 -> ... -> Constraint`.
pub fn infer_class_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    members: &[crate::cst::ClassMember],
    _span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let mut var_kinds = HashMap::new();

    for tv in type_vars {
        let var_kind = ks.fresh_kind_var();
        var_kinds.insert(tv.value, var_kind);
    }

    // Check member type signatures
    for member in members {
        let _member_kind = infer_kind(ks, &member.ty, &var_kinds, type_ops, Some(name))?;
    }

    // Build kind: k1 -> k2 -> ... -> Constraint
    let mut result_kind = Type::kind_constraint();
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Instantiate a polymorphic kind signature by replacing forall-bound variables
/// with fresh kind unification variables. Returns the instantiated kind.
pub fn instantiate_kind(ks: &mut KindState, kind: &Type) -> Type {
    match kind {
        Type::Forall(vars, body) => {
            let mut subst = HashMap::new();
            for (var, _visible) in vars {
                subst.insert(*var, ks.fresh_kind_var());
            }
            substitute_kind_vars(&subst, body)
        }
        other => other.clone(),
    }
}

/// Substitute kind variables in a type (used for instantiating polymorphic kinds).
fn substitute_kind_vars(subst: &HashMap<Symbol, Type>, ty: &Type) -> Type {
    match ty {
        Type::Var(name) => {
            subst.get(name).cloned().unwrap_or_else(|| ty.clone())
        }
        Type::Fun(from, to) => {
            Type::fun(
                substitute_kind_vars(subst, from),
                substitute_kind_vars(subst, to),
            )
        }
        Type::App(f, a) => {
            Type::app(
                substitute_kind_vars(subst, f),
                substitute_kind_vars(subst, a),
            )
        }
        Type::Forall(vars, body) => {
            // Don't substitute vars that are shadowed by this forall
            let mut inner_subst = subst.clone();
            for (v, _) in vars {
                inner_subst.remove(v);
            }
            Type::Forall(vars.clone(), Box::new(substitute_kind_vars(&inner_subst, body)))
        }
        _ => ty.clone(),
    }
}
