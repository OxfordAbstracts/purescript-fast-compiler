//! Generalization and instantiation.
//!
//! `generalize` promotes every unification variable that's free in `ty`
//! but *not* free in the surrounding [`Env`] into a quantified rigid
//! variable. `instantiate` does the opposite: each quantified variable in
//! a [`Scheme`] is replaced with a fresh unification variable, so a
//! polymorphic binding can be used with different types at different use
//! sites.

use std::collections::HashMap;

use crate::typecheck_db::env::Env;
use crate::typecheck_db::types::{Constraint, Scheme, Type};
use crate::typecheck_db::unify::UnifyState;

/// Generate a fresh Scheme from `ty` by quantifying over unif vars not in
/// `env`.
pub fn generalize(state: &UnifyState, env: &Env, ty: &Type) -> Scheme {
    generalize_with_constraints(state, env, ty, &[])
}

/// Like `generalize`, but also folds a list of pending constraints into
/// the resulting scheme as a `Type::Constrained` layer. Both the body's
/// unif vars and the constraints' unif vars share the *same* unif→typevar
/// substitution, so `Eq α` and the body's `α` end up referring to the
/// same `Type::Var("a")`. Without this, importers re-instantiate the
/// scheme and the constraint args carry orphan unif ids that never
/// connect to the use-site type.
pub fn generalize_with_constraints(
    state: &UnifyState,
    env: &Env,
    ty: &Type,
    constraints: &[Constraint],
) -> Scheme {
    let zonked_ty = state.zonk(ty);
    let zonked_constraints: Vec<Constraint> = constraints
        .iter()
        .map(|c| Constraint {
            class: c.class.clone(),
            args: c.args.iter().map(|a| state.zonk(a)).collect(),
        })
        .collect();

    let env_free = env.free_unif_vars(state);
    let mut all_free: std::collections::HashSet<u32> =
        state.free_unif_vars(&zonked_ty);
    for c in &zonked_constraints {
        for a in &c.args {
            all_free.extend(state.free_unif_vars(a));
        }
    }
    let mut to_generalize: Vec<u32> =
        all_free.difference(&env_free).copied().collect();
    to_generalize.sort();

    let mut subst: HashMap<u32, Type> = HashMap::new();
    let mut names: Vec<String> = Vec::new();
    for (i, id) in to_generalize.iter().enumerate() {
        let name = var_name(i);
        names.push(name.clone());
        subst.insert(*id, Type::Var(name));
    }
    let body = apply_unif_subst(&zonked_ty, &subst);
    if zonked_constraints.is_empty() {
        return Scheme { vars: names, ty: body };
    }
    let lifted_constraints: Vec<Constraint> = zonked_constraints
        .iter()
        .map(|c| Constraint {
            class: c.class.clone(),
            args: c.args.iter().map(|a| apply_unif_subst(a, &subst)).collect(),
        })
        .collect();
    Scheme {
        vars: names,
        ty: Type::Constrained(lifted_constraints, Box::new(body)),
    }
}

/// Instantiate a scheme: replace each quantified variable with a fresh
/// unification variable. Also rewrites any stray `Type::Unif(id)` in
/// the scheme body — those can appear when a cached scheme carries
/// unif vars from the state that produced it, and blindly reusing
/// those ids would panic later when we try to `assign` against a
/// different state's shorter bindings vec. We give every such stray
/// id a fresh local unif var in the new state.
pub fn instantiate(state: &mut UnifyState, scheme: &Scheme) -> Type {
    let mut var_subst: HashMap<String, Type> = HashMap::new();
    for v in &scheme.vars {
        var_subst.insert(v.clone(), state.fresh());
    }
    let body = if var_subst.is_empty() {
        scheme.ty.clone()
    } else {
        apply_var_subst(&scheme.ty, &var_subst)
    };

    // Collect stray `Unif` ids in the body (ids the body carries
    // that weren't introduced by the quantifier substitution above).
    let mut stray_ids: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    collect_stray_unif(&body, &mut stray_ids);
    if stray_ids.is_empty() {
        return body;
    }
    let mut unif_subst: HashMap<u32, Type> = HashMap::new();
    for id in stray_ids {
        unif_subst.insert(id, state.fresh());
    }
    apply_unif_subst(&body, &unif_subst)
}

fn collect_stray_unif(ty: &Type, out: &mut std::collections::HashSet<u32>) {
    match ty {
        Type::Unif(id) => {
            out.insert(*id);
        }
        Type::App(f, a) => {
            collect_stray_unif(f, out);
            collect_stray_unif(a, out);
        }
        Type::Fun(a, b) => {
            collect_stray_unif(a, out);
            collect_stray_unif(b, out);
        }
        Type::Forall(_, body) => collect_stray_unif(body, out),
        Type::Constrained(cs, body) => {
            for c in cs {
                for a in &c.args {
                    collect_stray_unif(a, out);
                }
            }
            collect_stray_unif(body, out);
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            for (_, t) in fs {
                collect_stray_unif(t, out);
            }
            if let Some(t) = tail {
                collect_stray_unif(t, out);
            }
        }
        Type::Kinded(t, k) => {
            collect_stray_unif(t, out);
            collect_stray_unif(k, out);
        }
        _ => {}
    }
}

/// Produce a readable name for the n-th quantified variable: `a`, `b`, …,
/// `z`, `a1`, `b1`, …
fn var_name(n: usize) -> String {
    let letter = (b'a' + (n % 26) as u8) as char;
    let round = n / 26;
    if round == 0 {
        letter.to_string()
    } else {
        format!("{}{}", letter, round)
    }
}

/// Substitute unification variables using `subst`.
pub fn apply_unif_subst(ty: &Type, subst: &HashMap<u32, Type>) -> Type {
    match ty {
        Type::Unif(id) => subst.get(id).cloned().unwrap_or_else(|| ty.clone()),
        Type::App(f, a) => Type::app(
            apply_unif_subst(f, subst),
            apply_unif_subst(a, subst),
        ),
        Type::Fun(a, b) => Type::Fun(
            Box::new(apply_unif_subst(a, subst)),
            Box::new(apply_unif_subst(b, subst)),
        ),
        Type::Forall(vars, body) => {
            let vars = vars
                .iter()
                .map(|(n, v, k)| {
                    (
                        n.clone(),
                        *v,
                        k.as_ref().map(|k| Box::new(apply_unif_subst(k, subst))),
                    )
                })
                .collect();
            Type::Forall(vars, Box::new(apply_unif_subst(body, subst)))
        }
        Type::Constrained(cs, body) => {
            let cs = cs
                .iter()
                .map(|c| Constraint {
                    class: c.class.clone(),
                    args: c.args.iter().map(|a| apply_unif_subst(a, subst)).collect(),
                })
                .collect();
            Type::Constrained(cs, Box::new(apply_unif_subst(body, subst)))
        }
        Type::Record(fs, tail) => Type::Record(
            fs.iter()
                .map(|(l, t)| (l.clone(), apply_unif_subst(t, subst)))
                .collect(),
            tail.as_ref().map(|t| Box::new(apply_unif_subst(t, subst))),
        ),
        Type::Row(fs, tail) => Type::Row(
            fs.iter()
                .map(|(l, t)| (l.clone(), apply_unif_subst(t, subst)))
                .collect(),
            tail.as_ref().map(|t| Box::new(apply_unif_subst(t, subst))),
        ),
        Type::Kinded(t, k) => Type::Kinded(
            Box::new(apply_unif_subst(t, subst)),
            Box::new(apply_unif_subst(k, subst)),
        ),
        _ => ty.clone(),
    }
}

/// Substitute rigid type variables using `subst` (keyed by variable name).
pub fn apply_var_subst(ty: &Type, subst: &HashMap<String, Type>) -> Type {
    match ty {
        Type::Var(name) => subst.get(name).cloned().unwrap_or_else(|| ty.clone()),
        Type::App(f, a) => Type::app(
            apply_var_subst(f, subst),
            apply_var_subst(a, subst),
        ),
        Type::Fun(a, b) => Type::Fun(
            Box::new(apply_var_subst(a, subst)),
            Box::new(apply_var_subst(b, subst)),
        ),
        Type::Forall(vars, body) => {
            // Quantified vars *shadow* outer bindings — strip them from
            // the substitution while traversing the body.
            let mut inner = subst.clone();
            for (n, _, _) in vars {
                inner.remove(n);
            }
            Type::Forall(vars.clone(), Box::new(apply_var_subst(body, &inner)))
        }
        Type::Constrained(cs, body) => {
            let cs = cs
                .iter()
                .map(|c| Constraint {
                    class: c.class.clone(),
                    args: c.args.iter().map(|a| apply_var_subst(a, subst)).collect(),
                })
                .collect();
            Type::Constrained(cs, Box::new(apply_var_subst(body, subst)))
        }
        Type::Record(fs, tail) => Type::Record(
            fs.iter()
                .map(|(l, t)| (l.clone(), apply_var_subst(t, subst)))
                .collect(),
            tail.as_ref().map(|t| Box::new(apply_var_subst(t, subst))),
        ),
        Type::Row(fs, tail) => Type::Row(
            fs.iter()
                .map(|(l, t)| (l.clone(), apply_var_subst(t, subst)))
                .collect(),
            tail.as_ref().map(|t| Box::new(apply_var_subst(t, subst))),
        ),
        Type::Kinded(t, k) => Type::Kinded(
            Box::new(apply_var_subst(t, subst)),
            Box::new(apply_var_subst(k, subst)),
        ),
        _ => ty.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typecheck_db::types::QName;

    fn int_ty() -> Type {
        Type::Con(QName::unqualified("Int"))
    }

    #[test]
    fn instantiate_fresh_vars_for_each_quantifier() {
        let mut s = UnifyState::new();
        let scheme = Scheme {
            vars: vec!["a".into()],
            ty: Type::fun(Type::Var("a".into()), Type::Var("a".into())),
        };
        let t1 = instantiate(&mut s, &scheme);
        let t2 = instantiate(&mut s, &scheme);
        assert_ne!(t1, t2);
        // Each instantiation's domain and codomain are the same var.
        if let Type::Fun(a, b) = &t1 {
            assert_eq!(**a, **b);
            assert!(matches!(**a, Type::Unif(_)));
        } else {
            panic!();
        }
    }

    #[test]
    fn generalize_identity_lambda_type() {
        // Simulate inferring \x -> x : ?0 -> ?0 with no env constraints.
        let mut s = UnifyState::new();
        let env = Env::new();
        let v = s.fresh();
        let ty = Type::fun(v.clone(), v);
        let scheme = generalize(&s, &env, &ty);
        assert_eq!(scheme.vars, vec!["a".to_string()]);
        assert_eq!(
            scheme.ty,
            Type::fun(Type::Var("a".into()), Type::Var("a".into())),
        );
    }

    #[test]
    fn generalize_skips_vars_free_in_env() {
        let mut s = UnifyState::new();
        let mut env = Env::new();
        let env_var = s.fresh();
        env.bind_local("outer", env_var.clone());

        // Now we want to generalize a type that shares `env_var` with the
        // env — that var must not be quantified.
        let new_var = s.fresh();
        let ty = Type::fun(env_var, new_var);

        let scheme = generalize(&s, &env, &ty);
        assert_eq!(scheme.vars.len(), 1); // only new_var was quantified
    }

    #[test]
    fn generalize_produces_stable_var_names_in_order() {
        let mut s = UnifyState::new();
        let env = Env::new();
        let a = s.fresh();
        let b = s.fresh();
        // a -> b -> a
        let ty = Type::fun(a.clone(), Type::fun(b, a));
        let scheme = generalize(&s, &env, &ty);
        assert_eq!(scheme.vars, vec!["a".to_string(), "b".to_string()]);
        assert_eq!(
            scheme.ty,
            Type::fun(
                Type::Var("a".into()),
                Type::fun(Type::Var("b".into()), Type::Var("a".into())),
            )
        );
    }

    #[test]
    fn instantiated_scheme_unifies_with_concrete() {
        let mut s = UnifyState::new();
        let id_scheme = Scheme {
            vars: vec!["a".into()],
            ty: Type::fun(Type::Var("a".into()), Type::Var("a".into())),
        };
        let inst = instantiate(&mut s, &id_scheme);
        // `id @ Int` → `Int -> Int`
        s.unify(&inst, &Type::fun(int_ty(), int_ty())).unwrap();
    }
}
