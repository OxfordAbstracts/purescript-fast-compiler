use std::collections::{HashMap, HashSet};

use crate::interner::Symbol;
use crate::names::{ClassName, Qualified, TypeName, TypeVarName};
use crate::span::Span;
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;

use super::{apply_var_subst, collect_type_refs};

pub(crate) fn has_synonym_head(ty: &Type, type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>) -> bool {
    match ty {
        Type::Con(name) => type_aliases.contains_key(&Qualified::unqualified(name.name)),
        Type::App(f, _) => has_synonym_head(f, type_aliases),
        _ => false,
    }
}

/// Collect all type constructor names (Con) referenced in a type.
/// Used to determine which type_con_arities entries are needed for
/// alias expansion disambiguation.
pub(crate) fn collect_type_con_names_from_type(ty: &Type, names: &mut HashSet<Symbol>) {
    match ty {
        Type::Con(qi) => { names.insert(qi.name.symbol()); }
        Type::App(f, a) => { collect_type_con_names_from_type(f, names); collect_type_con_names_from_type(a, names); }
        Type::Fun(a, b) => { collect_type_con_names_from_type(a, names); collect_type_con_names_from_type(b, names); }
        Type::Forall(_, body) => { collect_type_con_names_from_type(body, names); }
        Type::Record(fields, tail) => {
            for (_, t) in fields { collect_type_con_names_from_type(t, names); }
            if let Some(t) = tail { collect_type_con_names_from_type(t, names); }
        }
        _ => {}
    }
}

/// Expand type aliases with a depth limit to prevent stack overflow.
/// Uses exact arity matching (args == params) for safety.
pub fn expand_type_aliases_limited(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    depth: u32,
) -> Type {
    let mut expanding = HashSet::new();
    expand_type_aliases_limited_inner(ty, type_aliases, None, depth, &mut expanding, None)
}

/// Expand type aliases with over-saturation support and data-type disambiguation.
/// Look up type constructor arity, falling back to unqualified or name-only match.
/// Needed because alias bodies contain unqualified type references, but
/// type_con_arities stores entries under qualified import keys.
pub(crate) fn lookup_type_con_arity(
    arities: &HashMap<Qualified<TypeName>, usize>,
    name: &Qualified<TypeName>,
) -> Option<usize> {
    // Always return the MAXIMUM arity found across all entries with matching .name.
    // This handles the case where an alias body (from another module) contains an
    // unqualified Con that refers to a type with arity N, but the consuming module
    // also has a local definition with the same name but lower arity
    // (e.g. `Data.Options.Options` arity 1 vs local `data Options` arity 0).
    // Using the max prevents spurious KindArityMismatch errors when the alias
    // body's Con is checked in a context with a lower-arity local definition.
    //
    // For qualified names (e.g. `Opt.Options`), first try exact match, then fall
    // back to unqualified; since there's an exact key we don't need the max trick.
    if name.module.is_some() {
        arities.get(name).copied()
            .or_else(|| arities.get(&Qualified::unqualified(name.name)).copied())
    } else {
        // Unqualified: return max arity across all entries with matching .name
        // (both qualified and unqualified entries in the map).
        arities.iter()
            .filter(|(k, _)| k.name == name.name)
            .map(|(_, &v)| v)
            .max()
    }
}

/// Uses `>=` matching: when args > params, extra args are applied to the expanded result.
/// The `type_con_arities` map prevents incorrect expansion when a name is both an alias
/// and a data type (due to module qualifier stripping): if arg count exceeds alias params
/// but fits the data type arity, the alias expansion is skipped.
pub(crate) fn expand_type_aliases_limited_with_arities(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    type_con_arities: &HashMap<Qualified<TypeName>, usize>,
    depth: u32,
) -> Type {
    let mut expanding = HashSet::new();
    expand_type_aliases_limited_inner(
        ty,
        type_aliases,
        Some(type_con_arities),
        depth,
        &mut expanding,
        None,
    )
}


pub(crate) fn type_contains_con_name(ty: &Type, name: &Qualified<TypeName>) -> bool {
    match ty {
        Type::Con(n) => n.name == name.name,
        Type::App(f, a) => type_contains_con_name(f, name) || type_contains_con_name(a, name),
        Type::Fun(a, b) => type_contains_con_name(a, name) || type_contains_con_name(b, name),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_contains_con_name(t, name))
                || tail.as_ref().map_or(false, |t| type_contains_con_name(t, name))
        }
        Type::Forall(_, body) => type_contains_con_name(body, name),
        _ => false,
    }
}

/// Check if a type contains Con(name) applied to exactly `expected_args` arguments.
/// Arity-aware version for self-referential alias detection at export time.
pub(crate) fn contains_self_referential_usage_in_type(ty: &Type, name: Symbol, expected_args: usize) -> bool {
    match ty {
        Type::Con(n) => n.name.symbol() == name && expected_args == 0,
        Type::App(_, _) => {
            let mut head = ty;
            let mut args: Vec<&Type> = Vec::new();
            while let Type::App(f, a) = head {
                args.push(a.as_ref());
                head = f.as_ref();
            }
            if let Type::Con(n) = head {
                if n.name.symbol() == name && args.len() == expected_args {
                    return true;
                }
            }
            contains_self_referential_usage_in_type(head, name, expected_args)
                || args.iter().any(|a| contains_self_referential_usage_in_type(a, name, expected_args))
        }
        Type::Fun(from, to) => {
            contains_self_referential_usage_in_type(from, name, expected_args)
                || contains_self_referential_usage_in_type(to, name, expected_args)
        }
        Type::Forall(_, body) => contains_self_referential_usage_in_type(body, name, expected_args),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| contains_self_referential_usage_in_type(t, name, expected_args))
                || tail.as_ref().map_or(false, |t| contains_self_referential_usage_in_type(t, name, expected_args))
        }
        _ => false,
    }
}

/// Check if a type alias body is a simple re-export: `type X a b = M.X a b`
/// where M is a qualified import alias and X matches the alias name.
pub(crate) fn is_alias_reexport(body: &Type, alias_name: Symbol, params: &[TypeVarName]) -> bool {
    let mut head = body;
    let mut app_args = Vec::new();
    while let Type::App(f, a) = head {
        app_args.push(a.as_ref());
        head = f.as_ref();
    }
    if let Type::Con(qi_name) = head {
        if qi_name.module.is_some() && qi_name.name.symbol() == alias_name && app_args.len() == params.len() {
            // For zero-param aliases, body is just Con(M.X)
            if params.is_empty() {
                return true;
            }
            // For parameterized aliases, each arg must be a matching Var
            return app_args.iter().rev().zip(params.iter()).all(|(arg, param)| {
                matches!(arg, Type::Var(v) if *v == *param)
            });
        }
    }
    false
}

/// Inner expansion function.
/// When `type_con_arities` is `Some`, over-saturated aliases (args > params) are expanded
/// with extra args applied to the result, but expansion is skipped when the name also
/// exists as a data type with a matching arity (alias/data-type name collision).
/// When `None`, only exact arity matches (args == params) are expanded.
///
/// `con_zero_blockers`: optional set of alias names to block in the zero-arg Con path.
/// Used during export expansion to prevent wrong expansion of alias names that collide
/// with data types from different modules (e.g. `type GqlError = { ... }` alias vs
/// `data GqlError = ...`). Only blocks standalone `Con(X)` expansion, NOT `App(Con(X), ...)`
/// expansion, so over-saturated usage (like `POST url input output`) still works.
pub(crate) fn expand_type_aliases_limited_inner(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
    depth: u32,
    expanding: &mut HashSet<Qualified<TypeName>>,
    con_zero_blockers: Option<&HashSet<Symbol>>,
) -> Type {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    expand_type_aliases_limited_inner_impl(ty, type_aliases, type_con_arities, depth, expanding, con_zero_blockers)
    })
}

pub(crate) fn expand_type_aliases_limited_inner_impl(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    type_con_arities: Option<&HashMap<Qualified<TypeName>, usize>>,
    depth: u32,
    expanding: &mut HashSet<Qualified<TypeName>>,
    con_zero_blockers: Option<&HashSet<Symbol>>,
) -> Type {
    if depth > 200 || type_aliases.is_empty() {
        return ty.clone();
    }

    // For App types, collect the full spine first to determine the total arg count.
    // This prevents inner App nodes from being independently expanded as aliases
    // when they're part of a larger application (e.g., App(App(App(App(App(Con("Codec"),
    // ED), a), b), c), d) where Codec has a 1-param alias but is used here as a
    // 5-param data type).
    if let Type::App(_, _) = ty {
        let mut raw_args: Vec<&Type> = Vec::new();
        let mut head = ty;
        while let Type::App(f, a) = head {
            raw_args.push(a.as_ref());
            head = f.as_ref();
        }
        raw_args.reverse();

        if let Type::Con(name) = head {
            if !expanding.contains(name) {
                // When the type constructor has a module qualifier (e.g. Codec.Codec),
                // prefer the qualified form for alias lookup. If only the unqualified
                // name matches an alias but the qualified form doesn't exist, this might
                // be a data type that happens to share a name with an alias from a
                // different module (e.g. Data.Codec.Codec data type vs Data.Codec.JSON.Codec alias).
                let alias_entry = if let Some(module) = name.module {
                    type_aliases.get(&Qualified::qualified(module, name.name))
                } else {
                    type_aliases.get(&Qualified::unqualified(name.name))
                };
                if let Some((params, body)) = alias_entry {
                    let should_expand = if params.is_empty() {
                        // Zero-arg alias applied to args: expand head, re-apply args
                        true
                    } else if raw_args.len() == params.len() {
                        // Exactly saturated: always expand
                        true
                    } else if raw_args.len() > params.len() && type_con_arities.is_some() {
                        // Over-saturated: only expand when we have arities for disambiguation.
                        // Skip if name is also a data type and arg count fits the data type arity.
                        let arities = type_con_arities.unwrap();
                        !lookup_type_con_arity(arities, name)
                            .map_or(false, |arity| raw_args.len() <= arity)
                    } else {
                        false
                    };
                    if should_expand {
                        let expanded_args: Vec<Type> = raw_args
                            .iter()
                            .map(|a| {
                                expand_type_aliases_limited_inner(
                                    a,
                                    type_aliases,
                                    type_con_arities,
                                    depth + 1,
                                    expanding,
                                    con_zero_blockers,
                                )
                            })
                            .collect();
                        let n_sat = params.len();
                        if n_sat == 0 {
                            // Zero-arg alias: expand body, apply all args
                            expanding.insert(*name);
                            let expanded_head = expand_type_aliases_limited_inner(
                                body,
                                type_aliases,
                                type_con_arities,
                                depth + 1,
                                expanding,
                                con_zero_blockers,
                            );
                            expanding.remove(name);
                            let mut result = expanded_head;
                            for arg in expanded_args {
                                result = Type::app(result, arg);
                            }
                            return result;
                        }
                        // Saturated or over-saturated: substitute first n_sat args, apply extras
                        let (sat_args, extra_args) = expanded_args.split_at(n_sat);
                        let subst: HashMap<TypeVarName, Type> = params
                            .iter()
                            .copied()
                            .zip(sat_args.iter().cloned())
                            .collect();
                        let mut result = apply_var_subst(&subst, body);
                        for extra in extra_args {
                            result = Type::app(result, extra.clone());
                        }
                        // Only add to expanding set if the substituted result might
                        // reference this alias (self-referential). For aliases like
                        // RowApply (body = f a), after substitution the result won't
                        // contain RowApply, so blocking it prevents legitimate nested
                        // uses (e.g. OptionsRow body using RowApply again).
                        let is_self_ref = type_contains_con_name(&result, name);
                        if is_self_ref {
                            expanding.insert(*name);
                        }
                        let expanded = expand_type_aliases_limited_inner(
                            &result,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        );
                        if is_self_ref {
                            expanding.remove(name);
                        }
                        return expanded;
                    }
                }
            }
        }

        // Not an expandable alias — expand each arg independently.
        // For the head: if it's a bare Con, don't try to expand it (it's not saturated).
        // Otherwise (e.g., nested App, Fun, etc.), recurse into it.
        let expanded_args: Vec<Type> = raw_args
            .iter()
            .map(|a| {
                expand_type_aliases_limited_inner(
                    a,
                    type_aliases,
                    type_con_arities,
                    depth + 1,
                    expanding,
                    con_zero_blockers,
                )
            })
            .collect();
        let expanded_head = match head {
            Type::Con(_) => head.clone(),
            _ => expand_type_aliases_limited_inner(
                head,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            ),
        };
        let mut result = expanded_head;
        for arg in expanded_args {
            result = Type::app(result, arg);
        }
        return result;
    }

    match ty {
        Type::Fun(a, b) => Type::fun(
            expand_type_aliases_limited_inner(
                a,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            ),
            expand_type_aliases_limited_inner(
                b,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            ),
        ),
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| {
                    (
                        *l,
                        expand_type_aliases_limited_inner(
                            t,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        ),
                    )
                })
                .collect();
            let tail = tail.as_ref().map(|t| {
                Box::new(expand_type_aliases_limited_inner(
                    t,
                    type_aliases,
                    type_con_arities,
                    depth + 1,
                    expanding,
                    con_zero_blockers,
                ))
            });
            Type::Record(fields, tail)
        }
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(expand_type_aliases_limited_inner(
                body,
                type_aliases,
                type_con_arities,
                depth + 1,
                expanding,
                con_zero_blockers,
            )),
        ),
        Type::Con(name) => {
            // Zero-arg alias expansion
            // Use qualified lookup when a module qualifier is present (matching the App path),
            // so that e.g. Border.Evaluated and Style.Evaluated resolve to different aliases
            // instead of colliding on the unqualified "Evaluated" key.
            let lookup_key = if let Some(module) = name.module {
                Qualified::qualified(module, name.name)
            } else {
                Qualified::unqualified(name.name)
            };
            if !expanding.contains(&lookup_key) {
                if let Some((params, body)) = type_aliases.get(&lookup_key) {
                    if params.is_empty() {
                        // Check zero-arg blockers: skip expansion if this alias name
                        // was marked as colliding with a data type at the call site.
                        if let Some(blockers) = con_zero_blockers {
                            if blockers.contains(&name.name.symbol()) {
                                return ty.clone();
                            }
                        }
                        expanding.insert(lookup_key);
                        let result = expand_type_aliases_limited_inner(
                            body,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        );
                        expanding.remove(&lookup_key);
                        return result;
                    }
                }
                // Do NOT fall back to unqualified lookup when qualified not found.
                // Qualified aliases are always stored under their qualified keys during
                // import (e.g. Border.Evaluated, Tick.Easing). Falling back to unqualified
                // would incorrectly expand data type references (e.g. HATS.Easing) using
                // an alias from a different module with the same unqualified name.
                // Eta-reduce partially applied aliases (unqualified)
                if let Some((params, body)) = type_aliases.get(&lookup_key) {
                    if let Some(reduced) = eta_reduce_alias(params, body) {
                        expanding.insert(lookup_key);
                        let result = expand_type_aliases_limited_inner(
                            &reduced,
                            type_aliases,
                            type_con_arities,
                            depth + 1,
                            expanding,
                            con_zero_blockers,
                        );
                        expanding.remove(&lookup_key);
                        return result;
                    }
                }
            }
            ty.clone()
        }
        _ => ty.clone(),
    }
}

/// Check a type for partially applied type synonyms and over-applied type constructors,
/// using known type constructor arities.
pub(crate) fn check_type_for_partial_synonyms_with_arities(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    type_con_arities: &HashMap<Qualified<TypeName>, usize>,
    record_type_aliases: &HashSet<Qualified<TypeName>>,
    span: Span,
    errors: &mut Vec<TypeError>,
) {
    // Pre-expansion check: detect record-kind type aliases in row tails
    // before they get expanded away by expand_type_aliases_limited.
    check_record_alias_row_tails(ty, record_type_aliases, type_con_arities, span, errors);
    let expanded = expand_type_aliases_limited_with_arities(ty, type_aliases, type_con_arities, 0);
    check_partially_applied_synonyms_inner(
        &expanded,
        type_aliases,
        type_con_arities,
        record_type_aliases,
        span,
        errors,
        false,
    );
}

/// Pre-expansion check: walk a type and detect record-kind type aliases used
/// as row tails (e.g. `{ | Foo }` where `type Foo = { x :: Number }`).
/// This must happen before alias expansion because expansion replaces
/// `Type::Con("Foo")` with `Type::Record(...)` which is indistinguishable from valid rows.
pub(crate) fn check_record_alias_row_tails(
    ty: &Type,
    record_type_aliases: &HashSet<Qualified<TypeName>>,
    type_con_arities: &HashMap<Qualified<TypeName>, usize>,
    span: Span,
    errors: &mut Vec<TypeError>,
) {
    match ty {
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                check_record_alias_row_tails(
                    t,
                    record_type_aliases,
                    type_con_arities,
                    span,
                    errors,
                );
            }
            if let Some(t) = tail {
                if let Type::Con(name) = t.as_ref() {
                    if record_type_aliases.contains(&*name) {
                        errors.push(TypeError::KindsDoNotUnify {
                            span,
                            expected: Type::kind_row_of(Type::kind_type()),
                            found: Type::kind_type(),
                        });
                        return;
                    }
                }
                check_record_alias_row_tails(
                    t,
                    record_type_aliases,
                    type_con_arities,
                    span,
                    errors,
                );
            }
        }
        Type::Fun(a, b) => {
            check_record_alias_row_tails(a, record_type_aliases, type_con_arities, span, errors);
            check_record_alias_row_tails(b, record_type_aliases, type_con_arities, span, errors);
        }
        Type::App(f, a) => {
            check_record_alias_row_tails(f, record_type_aliases, type_con_arities, span, errors);
            check_record_alias_row_tails(a, record_type_aliases, type_con_arities, span, errors);
        }
        Type::Forall(_, body) => {
            check_record_alias_row_tails(body, record_type_aliases, type_con_arities, span, errors);
        }
        _ => {}
    }
}

/// Walk a (post-expansion) type looking for partially applied synonyms
/// and over-applied type constructors.
pub(crate) fn check_partially_applied_synonyms_inner(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    type_con_arities: &HashMap<Qualified<TypeName>, usize>,
    record_type_aliases: &HashSet<Qualified<TypeName>>,
    span: Span,
    errors: &mut Vec<TypeError>,
    is_arg: bool,
) {
    match ty {
        Type::App(_, _) => {
            // Collect the head and all arguments of this application chain
            let mut head = ty;
            let mut args: Vec<&Type> = Vec::new();
            while let Type::App(f, a) = head {
                args.push(a.as_ref());
                head = f.as_ref();
            }
            // Check if head is a partially or over-applied synonym
            if let Type::Con(name) = head {
                // When the name has a module qualifier, use the qualified alias key.
                // This prevents confusing a data type (e.g. Codec.Codec) with
                // an unrelated alias of the same unqualified name (e.g. CJ.Codec alias).
                let alias_entry = if let Some(module) = name.module {
                    type_aliases.get(&Qualified::qualified(module, name.name))
                } else {
                    type_aliases.get(&Qualified::unqualified(name.name))
                };
                if let Some((params, _)) = alias_entry {
                    if args.len() < params.len() {
                        // Before flagging as partially applied, check if the name also refers
                        // to a data type with a compatible arity. If so, the user is referencing
                        // the data type, not the alias (name collision between modules).
                        let is_data_type = lookup_type_con_arity(type_con_arities, name)
                            .map_or(false, |arity| args.len() <= arity);
                        if !is_data_type {
                            errors.push(TypeError::PartiallyAppliedSynonym { span, name: *name });
                            return;
                        }
                    } else if args.len() > params.len() {
                        // Over-saturation: the alias might expand to a type that takes more args.
                        // E.g., `type POST = Route "POST"` where Route is a 2-param data type.
                        // `POST "/path"` expands to `Route "POST" "/path"` which is valid.
                        // Only report KAM if we know this name is a data type with insufficient
                        // arity; otherwise assume the alias expansion will accommodate the args.
                        let arity_ok = lookup_type_con_arity(type_con_arities, name)
                            .map_or(true, |arity| args.len() <= arity);
                        if !arity_ok {
                            errors.push(TypeError::KindArityMismatch {
                                span,
                                name: *name,
                                expected: params.len(),
                                found: args.len(),
                            });
                            return;
                        }
                    }
                }
                // NOTE: Do NOT check over-applied non-alias type constructors here.
                // Foreign data types may have result kinds that are type aliases expanding
                // to function types (e.g., `UseEffect :: Type -> HookType` where
                // `type HookType = HookType' -> HookType'`), allowing more applications
                // than the declared arity suggests. The kind checker handles these cases.
            } else {
                check_partially_applied_synonyms_inner(
                    head,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    false,
                );
            }
            // Recurse into each argument — pass is_arg=true so bare synonyms
            // used as higher-kinded arguments (e.g. `Id` in `ReactAttributesF Id r`)
            // are not flagged as partially applied.
            for arg in args {
                check_partially_applied_synonyms_inner(
                    arg,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    true,
                );
            }
        }
        Type::Con(name) => {
            // When this Con appears as an argument to a type application, it may be
            // a higher-kinded type argument (e.g. `type Id a = a` passed as `f` in
            // `ReactAttributesF f r`). Don't flag these as partially applied.
            if is_arg {
                return;
            }
            // Use qualified lookup when the name has a module qualifier,
            // to avoid false positives (e.g. DOM.Node matching a different Node alias).
            let alias_lookup_key = if let Some(module) = name.module {
                Qualified::qualified(module, name.name)
            } else {
                Qualified::unqualified(name.name)
            };
            let alias_entry = type_aliases.get(&alias_lookup_key);
            if let Some((params, _)) = alias_entry {
                if !params.is_empty() {
                    // Check if the name also refers to a data type (any arity).
                    // Data types can be used bare (partially applied) for higher-kinded
                    // usage, so if the name resolves to a data type, skip the PAS check.
                    let is_data_type = lookup_type_con_arity(type_con_arities, name).is_some();
                    if !is_data_type {
                        errors.push(TypeError::PartiallyAppliedSynonym { span, name: *name });
                    }
                }
            }
        }
        Type::Fun(a, b) => {
            check_partially_applied_synonyms_inner(
                a,
                type_aliases,
                type_con_arities,
                record_type_aliases,
                span,
                errors,
                false,
            );
            check_partially_applied_synonyms_inner(
                b,
                type_aliases,
                type_con_arities,
                record_type_aliases,
                span,
                errors,
                false,
            );
        }
        Type::Record(fields, tail) => {
            for (_, t) in fields {
                check_partially_applied_synonyms_inner(
                    t,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    false,
                );
            }
            if let Some(t) = tail {
                // Check if the row tail has kind Type instead of Row Type.
                // A row tail must have kind `Row Type`. Two cases are invalid:
                // 1. A data type with arity 0 (kind Type), e.g. `{ | Int }`
                // 2. A record-kind type alias (kind Type), e.g. `type Foo = { x :: Number }; { | Foo }`
                if let Type::Con(name) = t.as_ref() {
                    // Case 1: data type with arity 0 (kind Type, not Row)
                    if let Some(&arity) = type_con_arities.get(&*name) {
                        if arity == 0 {
                            errors.push(TypeError::KindsDoNotUnify {
                                span,
                                expected: Type::kind_row_of(Type::kind_type()),
                                found: Type::kind_type(),
                            });
                            return;
                        }
                    }
                    // Case 2: type alias declared with record syntax (kind Type)
                    if record_type_aliases.contains(&*name) {
                        errors.push(TypeError::KindsDoNotUnify {
                            span,
                            expected: Type::kind_row_of(Type::kind_type()),
                            found: Type::kind_type(),
                        });
                        return;
                    }
                }
                check_partially_applied_synonyms_inner(
                    t,
                    type_aliases,
                    type_con_arities,
                    record_type_aliases,
                    span,
                    errors,
                    false,
                );
            }
        }
        Type::Forall(_, body) => {
            check_partially_applied_synonyms_inner(
                body,
                type_aliases,
                type_con_arities,
                record_type_aliases,
                span,
                errors,
                false,
            );
        }
        _ => {}
    }
}

/// Detect cycles in type synonym definitions.
pub(crate) fn check_type_synonym_cycles(
    type_aliases: &HashMap<Symbol, (Span, &crate::ast::TypeExpr)>,
    errors: &mut Vec<TypeError>,
) {
    let alias_names: HashSet<Symbol> = type_aliases.keys().map(|k| *k).collect();

    // Build a Symbol-keyed span lookup for error reporting
    let alias_spans: HashMap<Symbol, Span> =
        type_aliases.iter().map(|(k, (s, _))| (*k, *s)).collect();

    // Build adjacency: alias → set of other aliases it references
    let mut deps: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for (name, (_, ty)) in type_aliases {
        let mut refs = HashSet::new();
        collect_type_refs(ty, &mut refs);
        // Only keep references to other aliases
        refs.retain(|r| alias_names.contains(r));
        deps.insert(*name, refs);
    }

    // DFS cycle detection
    let mut visited: HashSet<Symbol> = HashSet::new();
    let mut on_stack: HashSet<Symbol> = HashSet::new();

    for name in type_aliases.keys() {
        if !visited.contains(&name) {
            let mut path = Vec::new();
            if let Some(cycle) =
                dfs_find_cycle(*name, &deps, &mut visited, &mut on_stack, &mut path)
            {
                let span = alias_spans[&name];
                let cycle_spans: Vec<Span> = cycle
                    .iter()
                    .filter_map(|n| alias_spans.get(n).copied())
                    .collect();
                errors.push(TypeError::CycleInTypeSynonym {
                    name: TypeName::new(name.clone()),
                    span,
                    names_in_cycle: cycle.iter().map(|s| TypeName::new(*s)).collect(),
                    spans: cycle_spans,
                });
            }
        }
    }
}

pub(crate) fn dfs_find_cycle(
    node: Symbol,
    deps: &HashMap<Symbol, HashSet<Symbol>>,
    visited: &mut HashSet<Symbol>,
    on_stack: &mut HashSet<Symbol>,
    path: &mut Vec<Symbol>,
) -> Option<Vec<Symbol>> {
    visited.insert(node);
    on_stack.insert(node);
    path.push(node);

    if let Some(neighbors) = deps.get(&node) {
        for &neighbor in neighbors {
            if !visited.contains(&neighbor) {
                if let Some(cycle) = dfs_find_cycle(neighbor, deps, visited, on_stack, path) {
                    return Some(cycle);
                }
            } else if on_stack.contains(&neighbor) {
                // Found a cycle — extract the cycle from path
                let cycle_start = path.iter().position(|&n| n == neighbor).unwrap();
                return Some(path[cycle_start..].to_vec());
            }
        }
    }

    path.pop();
    on_stack.remove(&node);
    None
}

/// Detect cycles in type class superclass declarations.
/// E.g. `class Foo a <= Bar a` and `class Bar a <= Foo a` form a cycle.
pub(crate) fn check_type_class_cycles(
    class_defs: &HashMap<Symbol, (Span, Vec<Symbol>)>,
    errors: &mut Vec<TypeError>,
) {
    let class_names: HashSet<Symbol> = class_defs.keys().copied().collect();

    // Build adjacency: class → set of superclasses that are also defined locally
    let mut deps: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();
    for (&name, (_, superclasses)) in class_defs {
        let refs: HashSet<Symbol> = superclasses
            .iter()
            .copied()
            .filter(|s| class_names.contains(s))
            .collect();
        deps.insert(name, refs);
    }

    // DFS cycle detection
    let mut visited: HashSet<Symbol> = HashSet::new();
    let mut on_stack: HashSet<Symbol> = HashSet::new();

    for &name in class_defs.keys() {
        if !visited.contains(&name) {
            let mut path = Vec::new();
            if let Some(cycle) = dfs_find_cycle(name, &deps, &mut visited, &mut on_stack, &mut path)
            {
                let (span, _) = class_defs[&name];
                let cycle_spans: Vec<Span> = cycle
                    .iter()
                    .filter_map(|n| class_defs.get(n).map(|(s, _)| *s))
                    .collect();
                errors.push(TypeError::CycleInTypeClassDeclaration {
                    name: ClassName::new(name),
                    span,
                    names_in_cycle: cycle.iter().map(|s| ClassName::new(*s)).collect(),
                    spans: cycle_spans,
                });
            }
        }
    }
}

pub(crate) fn eta_reduce_alias(params: &[TypeVarName], body: &Type) -> Option<Type> {
    if params.is_empty() {
        return None;
    }
    let mut current = body;
    let mut remaining_params: Vec<TypeVarName> = params.to_vec();
    // Strip trailing App(_, Var(param)) from back to front
    let mut stripped = Vec::new();
    while let Type::App(f, a) = current {
        if let Some(&last_param) = remaining_params.last() {
            if let Type::Var(v) = a.as_ref() {
                if *v == last_param {
                    stripped.push(());
                    remaining_params.pop();
                    current = f.as_ref();
                    continue;
                }
            }
        }
        break;
    }
    // Must strip ALL params for full eta-reduction
    if remaining_params.is_empty() {
        Some(current.clone())
    } else {
        None
    }
}

pub(crate) fn expand_type_aliases(ty: &Type, type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>) -> Type {
    let mut expanding = HashSet::new();
    expand_type_aliases_inner(ty, type_aliases, 0, &mut expanding)
}

pub(crate) fn expand_type_aliases_inner(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    depth: u32,
    expanding: &mut HashSet<Qualified<TypeName>>,
) -> Type {
    stacker::maybe_grow(32 * 1024, 2 * 1024 * 1024, || {
    expand_type_aliases_inner_impl(ty, type_aliases, depth, expanding)
    })
}

pub(crate) fn expand_type_aliases_inner_impl(
    ty: &Type,
    type_aliases: &HashMap<Qualified<TypeName>, (Vec<TypeVarName>, Type)>,
    depth: u32,
    expanding: &mut HashSet<Qualified<TypeName>>,
) -> Type {
    if depth > 100 || type_aliases.is_empty() {
        return ty.clone();
    }

    // For App types, collect the full spine first to determine the total arg count.
    // This prevents inner App nodes from being independently expanded as aliases
    // when they're part of a larger application (e.g., Codec with 5 args where
    // Codec also has a 1-param alias — expanding the inner App(Con("Codec"), X)
    // would incorrectly treat it as the alias).
    if let Type::App(_, _) = ty {
        let mut raw_args: Vec<&Type> = Vec::new();
        let mut head = ty;
        while let Type::App(f, a) = head {
            raw_args.push(a.as_ref());
            head = f.as_ref();
        }
        raw_args.reverse();

        if let Type::Con(name) = head {
            if !expanding.contains(name) {
                // Use qualified key for qualified types to avoid expanding a data type
                // (e.g. HATS.Easing) using an alias from a different module with the same
                // unqualified name (e.g. Tick's type Easing = Number -> Number).
                let alias_entry = if let Some(module) = name.module {
                    type_aliases.get(&Qualified::qualified(module, name.name))
                } else {
                    type_aliases.get(&Qualified::unqualified(name.name))
                };
                if let Some((params, body)) = alias_entry {
                    if raw_args.len() == params.len() {
                        // Exactly saturated: expand args, substitute, recurse
                        let expanded_args: Vec<Type> = raw_args
                            .iter()
                            .map(|a| {
                                expand_type_aliases_inner(a, type_aliases, depth + 1, expanding)
                            })
                            .collect();
                        let subst: HashMap<TypeVarName, Type> = params
                            .iter()
                            .copied()
                            .zip(expanded_args.into_iter())
                            .collect();
                        expanding.insert(*name);
                        let result = expand_type_aliases_inner(
                            &apply_var_subst(&subst, body),
                            type_aliases,
                            depth + 1,
                            expanding,
                        );
                        expanding.remove(name);
                        return result;
                    }
                }
            }
        }

        // Not an expandable alias — expand each arg independently.
        // For the head: if it's a bare Con, don't recurse (not saturated).
        let expanded_args: Vec<Type> = raw_args
            .iter()
            .map(|a| expand_type_aliases_inner(a, type_aliases, depth + 1, expanding))
            .collect();
        let expanded_head = match head {
            Type::Con(_) => head.clone(),
            _ => expand_type_aliases_inner(head, type_aliases, depth + 1, expanding),
        };
        let mut result = expanded_head;
        for arg in expanded_args {
            result = Type::app(result, arg);
        }
        return result;
    }

    match ty {
        Type::Fun(a, b) => Type::fun(
            expand_type_aliases_inner(a, type_aliases, depth + 1, expanding),
            expand_type_aliases_inner(b, type_aliases, depth + 1, expanding),
        ),
        Type::Record(fields, tail) => {
            let fields = fields
                .iter()
                .map(|(l, t)| {
                    (
                        *l,
                        expand_type_aliases_inner(t, type_aliases, depth + 1, expanding),
                    )
                })
                .collect();
            let tail = tail.as_ref().map(|t| {
                Box::new(expand_type_aliases_inner(
                    t,
                    type_aliases,
                    depth + 1,
                    expanding,
                ))
            });
            Type::Record(fields, tail)
        }
        Type::Forall(vars, body) => Type::Forall(
            vars.clone(),
            Box::new(expand_type_aliases_inner(
                body,
                type_aliases,
                depth + 1,
                expanding,
            )),
        ),
        Type::Con(name) => {
            // Zero-arg alias expansion — use qualified key for qualified types
            if !expanding.contains(name) {
                let alias_entry = if let Some(module) = name.module {
                    type_aliases.get(&Qualified::qualified(module, name.name))
                } else {
                    type_aliases.get(&Qualified::unqualified(name.name))
                };
                if let Some((params, body)) = alias_entry {
                    if params.is_empty() {
                        expanding.insert(*name);
                        let result =
                            expand_type_aliases_inner(body, type_aliases, depth + 1, expanding);
                        expanding.remove(name);
                        return result;
                    }
                    // Eta-reduce partially applied aliases: `type Tree a = Cofree Array a`
                    // as a bare `Tree` (0 args) → try to produce `Cofree Array`.
                    // This works when the alias body ends with exactly the params in order.
                    if let Some(reduced) = eta_reduce_alias(params, body) {
                        expanding.insert(*name);
                        let result = expand_type_aliases_inner(&reduced, type_aliases, depth + 1, expanding);
                        expanding.remove(name);
                        return result;
                    }
                }
            }
            ty.clone()
        }
        _ => ty.clone(),
    }
}

