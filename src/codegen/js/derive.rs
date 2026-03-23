use std::collections::HashMap;

use crate::interner::{self, Symbol};
// TypeVarName/LabelName used via .symbol() on Type::Var and record fields

use super::*;
use super::super::common::ident_to_js;

/// Known derivable classes from the PureScript standard library.
/// Each variant corresponds to a class that can appear in `derive instance`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum DeriveClass {
    Eq,       // Data.Eq.Eq
    Ord,      // Data.Ord.Ord
    Eq1,      // Data.Eq.Eq1
    Ord1,     // Data.Ord.Ord1
    Functor,     // Data.Functor.Functor
    Foldable,    // Data.Foldable.Foldable
    Traversable, // Data.Traversable.Traversable
    Newtype,     // Data.Newtype.Newtype
    Generic,  // Data.Generic.Rep.Generic
    Unknown,  // Not a known derivable class
}

/// Resolve a class name (+ optional module qualifier) to a known derivable class.
/// Checks module qualification when available, falls back to name-only matching
/// for locally-defined classes (common in tests).
pub(crate) fn resolve_derive_class(class_name: &str, module: Option<&str>) -> DeriveClass {
    match (class_name, module) {
        // Module-qualified matches (canonical)
        ("Eq", Some("Data.Eq")) => DeriveClass::Eq,
        ("Ord", Some("Data.Ord")) => DeriveClass::Ord,
        ("Eq1", Some("Data.Eq")) => DeriveClass::Eq1,
        ("Ord1", Some("Data.Ord")) => DeriveClass::Ord1,
        ("Functor", Some("Data.Functor")) => DeriveClass::Functor,
        ("Foldable", Some("Data.Foldable")) => DeriveClass::Foldable,
        ("Traversable", Some("Data.Traversable")) => DeriveClass::Traversable,
        ("Newtype", Some("Data.Newtype")) => DeriveClass::Newtype,
        ("Generic", Some("Data.Generic.Rep")) => DeriveClass::Generic,
        // Unqualified fallback (for locally-defined classes in single-module tests)
        ("Eq", None) => DeriveClass::Eq,
        ("Ord", None) => DeriveClass::Ord,
        ("Eq1", None) => DeriveClass::Eq1,
        ("Ord1", None) => DeriveClass::Ord1,
        ("Functor", None) => DeriveClass::Functor,
        ("Foldable", None) => DeriveClass::Foldable,
        ("Traversable", None) => DeriveClass::Traversable,
        ("Newtype", None) => DeriveClass::Newtype,
        ("Generic", None) => DeriveClass::Generic,
        _ => DeriveClass::Unknown,
    }
}

/// Generate code for a `derive instance` declaration.
/// Produces actual method implementations based on the class being derived.
pub(crate) fn gen_derive_decl(ctx: &CodegenCtx, decl: &Decl, override_name: Option<String>) -> Vec<JsStmt> {
    let Decl::Derive { name, newtype, constraints, class_name, types, .. } = decl else { return vec![] };

    let instance_name = if let Some(n) = override_name {
        n
    } else {
        match name {
            Some(n) => ident_to_js(n.value),
            None => gen_unnamed_instance_name(class_name, types, &ctx.instance_registry, &ctx.type_op_targets),
        }
    };

    let class_str = interner::resolve(class_name.name).unwrap_or_default();
    // Resolve import alias to actual module name for derive class resolution.
    // E.g., `import Data.Generic.Rep as G` means class_name.module = Some("G"),
    // which needs to be resolved to "Data.Generic.Rep".
    let class_module_resolved: Option<String> = class_name.module.and_then(|m| {
        let alias_str = interner::resolve(m)?;
        // Check if this matches an import alias (e.g., `import Data.Generic.Rep as G`)
        for imp in &ctx.module.imports {
            if let Some(qual) = &imp.qualified {
                // The qualified alias is a ModuleName with parts
                if qual.parts.len() == 1 {
                    let qual_name = interner::resolve(qual.parts[0])?;
                    if qual_name == alias_str {
                        let parts: Vec<String> = imp.module.parts.iter()
                            .filter_map(|p| interner::resolve(*p).map(|s| s.to_string()))
                            .collect();
                        return Some(parts.join("."));
                    }
                }
            }
        }
        Some(alias_str.to_string())
    });
    let derive_kind = resolve_derive_class(&class_str, class_module_resolved.as_deref());

    // For derive newtype: delegate to the underlying type's instance
    if *newtype {
        return gen_derive_newtype_instance(ctx, &instance_name, &class_str, class_name, types, constraints);
    }

    // Extract the target type constructor name
    let target_type = extract_head_type_con_from_cst(types, &ctx.type_op_targets);

    // Look up constructors for the target type (with field types for unconstrained derives)
    let ctors_with_types: Vec<(String, usize, Vec<crate::typechecker::types::Type>)> = target_type.and_then(|t| {
        let qi = unqualified(t);
        ctx.data_constructors.get(&qi).map(|ctor_names| {
            ctor_names.iter().filter_map(|cn| {
                ctx.ctor_details.get(cn).map(|(_, _, field_types)| {
                    let name_str = interner::resolve(cn.name).unwrap_or_default();
                    (name_str, field_types.len(), field_types.clone())
                })
            }).collect::<Vec<_>>()
        })
    }).unwrap_or_default();
    let ctors: Vec<(String, usize)> = ctors_with_types.iter().map(|(n, c, _)| (n.clone(), *c)).collect();

    // Build per-constructor, per-field comparison info for Eq/Ord derives.
    let dict_params_for_all = if !constraints.is_empty() { constraint_dict_params(constraints) } else { vec![] };
    let ctor_fields_for_eq_ord: Vec<CtorFields> = if !constraints.is_empty() {
        // Constrained: build expressions from constraint dict params using type-based field analysis
        let method_name = match derive_kind {
            DeriveClass::Eq => Some("eq"),
            DeriveClass::Ord => Some("compare"),
            _ => None,
        };
        if let Some(mname) = method_name {
            build_constrained_ctor_fields_typed(ctx, &ctors_with_types, constraints, &dict_params_for_all, mname)
        } else {
            vec![]
        }
    } else {
        // Unconstrained: resolve concrete instances per field
        match derive_kind {
            DeriveClass::Eq => build_unconstrained_ctor_fields(ctx, &ctors_with_types, "Eq", "eq", true),
            DeriveClass::Ord => build_unconstrained_ctor_fields(ctx, &ctors_with_types, "Ord", "compare", false),
            _ => vec![],
        }
    };

    let mut fields: Vec<(String, JsExpr)> = match derive_kind {
        DeriveClass::Eq => gen_derive_eq_methods(&ctor_fields_for_eq_ord),
        DeriveClass::Ord => gen_derive_ord_methods(ctx, &ctor_fields_for_eq_ord),
        DeriveClass::Eq1 => gen_derive_eq1_methods(ctx, target_type),
        DeriveClass::Ord1 => gen_derive_ord1_methods(ctx, target_type),
        DeriveClass::Functor => {
            // Build the map_param_expr for parametric functor constraints (e.g. dictFunctor)
            let functor_map_param = if !constraints.is_empty() {
                let dict_params = constraint_dict_params(constraints);
                // Find the Functor constraint's dict param
                constraints.iter().zip(dict_params.iter()).find_map(|(c, dp)| {
                    let class_name = interner::resolve(c.class.name).unwrap_or_default();
                    if class_name == "Functor" {
                        Some(JsExpr::Var(dp.clone()))
                    } else {
                        None
                    }
                })
            } else {
                None
            };
            gen_derive_functor_methods(ctx, &ctors_with_types, functor_map_param)
        },
        DeriveClass::Foldable => {
            let foldable_param = if !constraints.is_empty() {
                let dict_params = constraint_dict_params(constraints);
                constraints.iter().zip(dict_params.iter()).find_map(|(c, dp)| {
                    let class_name = interner::resolve(c.class.name).unwrap_or_default();
                    if class_name == "Foldable" {
                        Some(JsExpr::Var(dp.clone()))
                    } else {
                        None
                    }
                })
            } else {
                None
            };
            gen_derive_foldable_methods(ctx, &ctors_with_types, foldable_param)
        },
        DeriveClass::Traversable => gen_derive_traversable_methods(ctx, &ctors_with_types, &instance_name, &dict_params_for_all),
        DeriveClass::Newtype => gen_derive_newtype_class_methods(),
        DeriveClass::Generic => gen_derive_generic_methods(ctx, &ctors),
        DeriveClass::Unknown => vec![],
    };

    // Add superclass accessors (e.g., Ord needs Eq0)
    // Skip for Eq1/Ord1 — they already generate their own superclass accessors
    if constraints.is_empty() && derive_kind != DeriveClass::Eq1 && derive_kind != DeriveClass::Ord1 {
        // Unconstrained: direct reference to local superclass instance
        gen_superclass_accessors(ctx, class_name, types, constraints, &mut fields);
    } else if derive_kind == DeriveClass::Ord {
        // Constrained Ord: Eq0 references the local Eq instance applied to dictOrd.Eq0().
        // Generate inline — hoist_dict_applications will extract it.
        let dict_params = constraint_dict_params(constraints);
        let eq_sym = interner::intern("Eq");
        let eq_instance_name = find_local_eq_instance_for_type(ctx, target_type, eq_sym);
        if let Some(eq_inst_js) = eq_instance_name {
            // Eq0: function() { return eqMaybe(dictOrd.Eq0()); }
            let eq_accessor = JsExpr::App(
                Box::new(JsExpr::Indexer(
                    Box::new(JsExpr::Var(dict_params[0].clone())),
                    Box::new(JsExpr::StringLit("Eq0".to_string())),
                )),
                vec![],
            );
            let eq_applied = JsExpr::App(
                Box::new(JsExpr::Var(eq_inst_js)),
                vec![eq_accessor],
            );
            fields.push(("Eq0".to_string(), JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(eq_applied)],
            )));
        }
    } else if derive_kind == DeriveClass::Traversable {
        // Constrained Traversable: Functor0 and Foldable1 reference local instances
        // applied to the constraint dict's superclass accessors.
        // e.g., Functor0: function() { return functorM(dictTraversable.Functor0()); }
        //       Foldable1: function() { return foldableM(dictTraversable.Foldable1()); }
        let dict_params = constraint_dict_params(constraints);
        if let Some(target) = target_type {
            let type_str = interner::resolve(target).unwrap_or_default();
            // Functor0: functorM(dictTraversable.Functor0())
            let functor_inst_name = format!("functor{type_str}");
            let functor0_accessor = JsExpr::App(
                Box::new(JsExpr::Indexer(
                    Box::new(JsExpr::Var(dict_params[0].clone())),
                    Box::new(JsExpr::StringLit("Functor0".to_string())),
                )),
                vec![],
            );
            let functor_applied = JsExpr::App(
                Box::new(JsExpr::Var(functor_inst_name)),
                vec![functor0_accessor],
            );
            fields.push(("Functor0".to_string(), JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(functor_applied)],
            )));

            // Foldable1: foldableM(dictTraversable.Foldable1())
            let foldable_inst_name = format!("foldable{type_str}");
            let foldable1_accessor = JsExpr::App(
                Box::new(JsExpr::Indexer(
                    Box::new(JsExpr::Var(dict_params[0].clone())),
                    Box::new(JsExpr::StringLit("Foldable1".to_string())),
                )),
                vec![],
            );
            let foldable_applied = JsExpr::App(
                Box::new(JsExpr::Var(foldable_inst_name)),
                vec![foldable1_accessor],
            );
            fields.push(("Foldable1".to_string(), JsExpr::Function(
                None,
                vec![],
                vec![JsStmt::Return(foldable_applied)],
            )));
        }
    }

    let mut obj: JsExpr = JsExpr::ObjectLit(fields);

    // Wrap in constraint functions with hoisted dict method calls.
    // Use a shared counter across all constraint levels so that vars with the same
    // method name get properly numbered (e.g., eq, eq2 for two Eq constraints).
    // Process outer-to-inner for correct counter ordering, then build the nesting.
    if !constraints.is_empty() {
        let mut shared_counter: HashMap<String, usize> = HashMap::new();
        // First pass: pre-count names outer-to-inner to reserve correct numbering
        let mut hoisted_per_level: Vec<Vec<(JsExpr, String)>> = Vec::new();
        for (ci, _constraint) in constraints.iter().enumerate() {
            let dict_param = &dict_params_for_all[ci];
            let body = vec![JsStmt::Return(obj.clone())];
            let mut hoisted: Vec<(JsExpr, String)> = Vec::new();
            collect_dict_apps_nested(dict_param, &body, &mut hoisted, &mut shared_counter, 0);
            // Exclude self-references: don't hoist expressions that reference the instance being defined
            hoisted.retain(|(expr, _)| {
                !js_expr_contains_var(expr, &instance_name)
            });
            // Deduplicate
            let mut unique: Vec<(JsExpr, String)> = Vec::new();
            for (expr, name) in hoisted {
                if !unique.iter().any(|(e, _)| *e == expr) {
                    unique.push((expr, name));
                }
            }
            // Sort hoisted vars alphabetically to match original compiler ordering
            unique.sort_by(|a, b| a.1.cmp(&b.1));
            hoisted_per_level.push(unique);
        }
        // Second pass: build nested functions inside-out with collected hoisting info
        for ci in (0..constraints.len()).rev() {
            let is_runtime = ctx.known_runtime_classes.contains(&constraints[ci].class.name);
            if is_runtime {
                let dict_param = &dict_params_for_all[ci];
                let mut fn_body: Vec<JsStmt> = Vec::new();
                for (expr, name) in &hoisted_per_level[ci] {
                    fn_body.push(JsStmt::VarDecl(name.clone(), Some(expr.clone())));
                }
                let inner_body = vec![JsStmt::Return(obj)];
                // Replace dict apps in inner body with hoisted var references
                let replaced: Vec<JsStmt> = inner_body.into_iter()
                    .map(|s| replace_dict_apps_stmt(s, &hoisted_per_level[ci]))
                    .collect();
                fn_body.extend(replaced);
                obj = JsExpr::Function(None, vec![dict_param.clone()], fn_body);
            } else {
                // Type-level constraint: no runtime param
                obj = JsExpr::Function(None, vec![], vec![JsStmt::Return(obj)]);
            }
        }
    }

    // Wrap non-function derive instances in IIFE if they reference constructors
    if !matches!(obj, JsExpr::Function(_, _, _)) && references_constructor(&obj) {
        let iife = JsExpr::App(
            Box::new(JsExpr::Function(None, vec![], vec![JsStmt::Return(obj)])),
            vec![],
        );
        vec![JsStmt::VarDecl(instance_name, Some(iife))]
    } else {
        vec![JsStmt::VarDecl(instance_name, Some(obj))]
    }
}

/// Find constructor names for a type from local module declarations.
/// Used when the type exports the type name but not its constructors.
pub(crate) fn find_local_ctor_names(module: &crate::cst::Module, type_name: Symbol) -> Vec<QualifiedIdent> {
    for decl in &module.decls {
        match decl {
            crate::cst::Decl::Data { name, constructors, .. } if name.value == type_name => {
                return constructors.iter().map(|c| unqualified(c.name.value)).collect();
            }
            crate::cst::Decl::Newtype { name, constructor, .. } if name.value == type_name => {
                return vec![unqualified(constructor.value)];
            }
            _ => {}
        }
    }
    Vec::new()
}

/// Find the underlying type head for a constructor from local module declarations.
/// For `newtype Day = Day Int`, returns the head of `Int` (i.e., the `Int` symbol).
pub(crate) fn find_local_ctor_underlying_head(
    module: &crate::cst::Module,
    ctor_name: Symbol,
    type_op_targets: &HashMap<Symbol, Symbol>,
) -> Option<Symbol> {
    for decl in &module.decls {
        match decl {
            crate::cst::Decl::Data { constructors, .. } => {
                for ctor in constructors {
                    if ctor.name.value == ctor_name {
                        if let Some(field_ty) = ctor.fields.first() {
                            return extract_head_from_type_expr(field_ty, type_op_targets);
                        }
                    }
                }
            }
            crate::cst::Decl::Newtype { constructor, ty, .. } if constructor.value == ctor_name => {
                return extract_head_from_type_expr(ty, type_op_targets);
            }
            _ => {}
        }
    }
    None
}

/// Generate derive newtype instance: delegates to the underlying type's instance.
/// `derive newtype instance showName :: Show Name` → uses the Show String instance.
///
/// There are two cases:
/// 1. Underlying type is concrete (e.g., `newtype Name = Name String`, `derive newtype instance Show Name`):
///    → Reference the concrete instance: `var showName = Data_Show.showString;`
/// 2. Underlying type is a type variable (e.g., `newtype Additive a = Additive a`, `derive newtype instance Eq a => Eq (Additive a)`):
///    → Pass constraint dict through: `var eqAdditive = function(dictEq) { return dictEq; };`
pub(crate) fn gen_derive_newtype_instance(
    ctx: &CodegenCtx,
    instance_name: &str,
    _class_str: &str,
    class_name: &QualifiedIdent,
    types: &[crate::cst::TypeExpr],
    constraints: &[Constraint],
) -> Vec<JsStmt> {
    let head_type = extract_head_type_con_from_cst(types, &ctx.type_op_targets);

    // Find the newtype's underlying type
    let underlying_is_type_var = head_type.and_then(|head| {
        let qi = unqualified(head);
        ctx.data_constructors.get(&qi).and_then(|ctor_names| {
            ctor_names.first().and_then(|ctor_qi| {
                ctx.ctor_details.get(ctor_qi).and_then(|(_, _, field_types)| {
                    field_types.first().map(|ty| extract_head_from_type(ty).is_none())
                })
            })
        })
    }).unwrap_or(false);

    if underlying_is_type_var && !constraints.is_empty() {
        // Type variable underlying type with constraints: just pass the dict through.
        // `derive newtype instance Eq a => Eq (Additive a)` → `function(dictEq) { return dictEq; }`
        let mut obj: JsExpr = JsExpr::Var("__placeholder__".to_string());
        for (i, constraint) in constraints.iter().enumerate().rev() {
            let dict_param = constraint_to_dict_param(constraint);
            if i == constraints.len() - 1 {
                // Innermost: return the dict param directly
                obj = JsExpr::Function(
                    None,
                    vec![dict_param.clone()],
                    vec![JsStmt::Return(JsExpr::Var(dict_param))],
                );
            } else {
                obj = JsExpr::Function(
                    None,
                    vec![dict_param.clone()],
                    vec![JsStmt::Return(obj)],
                );
            }
        }
        return vec![JsStmt::VarDecl(instance_name.to_string(), Some(obj))];
    }

    // Concrete underlying type: look up the instance
    let mut obj = if let Some(head) = head_type {
        let qi = unqualified(head);
        // Get constructor names; if exports have empty ctor list (type exported without constructors),
        // look up from local module declarations for same-module derive newtype
        let local_ctors;
        let ctor_names_opt = {
            let exported = ctx.data_constructors.get(&qi);
            if exported.map_or(false, |v| !v.is_empty()) {
                exported
            } else {
                // Fall back: search module declarations for the type's constructors
                local_ctors = find_local_ctor_names(ctx.module, head);
                if local_ctors.is_empty() { exported } else { Some(&local_ctors) }
            }
        };
        if let Some(ctor_names) = ctor_names_opt {
            if let Some(ctor_qi) = ctor_names.first() {
                // Try ctor_details first, then fall back to CST for same-module unexported constructors
                let ctor_details_opt = ctx.ctor_details.get(ctor_qi);
                let underlying_head_from_cst = if ctor_details_opt.is_none() {
                    find_local_ctor_underlying_head(ctx.module, ctor_qi.name, &ctx.type_op_targets)
                } else {
                    None
                };
                let underlying_head = ctor_details_opt
                    .and_then(|(_, _, field_types)| field_types.first())
                    .and_then(|ty| extract_head_from_type(ty))
                    .or(underlying_head_from_cst);
                if let Some(underlying_head) = underlying_head {
                    // For Record underlying types, use the typechecker's dict resolution
                    // to build the full RowList-based constraint chain (e.g., ordRecordCons(...)).
                    let underlying_ty = ctor_details_opt.and_then(|(_, _, ft)| ft.first());
                    let record_sym = interner::intern("Record");
                    if underlying_head == record_sym {
                        if let Some(resolved) = try_resolve_record_dict(ctx, class_name, underlying_ty) {
                            resolved
                        } else {
                            resolve_instance_ref(ctx, class_name.name, underlying_head)
                        }
                    } else {
                    let mut inst_expr = resolve_instance_ref(ctx, class_name.name, underlying_head);

                    // When the derive has no constraints but the underlying instance does,
                    // we need to apply concrete dict arguments.
                    // E.g., `derive newtype instance Show (Y String)` where Y wraps Array
                    // needs `showArray(showString)` — applying the Show String dict.
                    if constraints.is_empty() {
                        let type_vars = ctor_details_opt.map(|(_, tv, _)| tv);
                        let underlying_ty2 = ctor_details_opt.and_then(|(_, _, ft)| ft.first());
                        let underlying_inst_name = ctx.instance_registry.get(&(class_name.name, underlying_head)).copied();
                        let underlying_constraints = underlying_inst_name
                            .and_then(|n| ctx.instance_constraint_classes.get(&n))
                            .cloned()
                            .unwrap_or_default();

                        if !underlying_constraints.is_empty() {
                            if let (Some(type_vars), Some(underlying_ty2)) = (type_vars, underlying_ty2) {
                                let type_var_names: Vec<Symbol> = type_vars.iter().map(|qi| qi.name).collect();
                                let cst_type_args = extract_cst_type_args_for_head(types, head, &ctx.type_op_targets);
                                let mut subst: HashMap<Symbol, Symbol> = HashMap::new();
                                for (i, tv) in type_var_names.iter().enumerate() {
                                    if let Some(cst_arg) = cst_type_args.get(i) {
                                        if let Some(concrete_head) = extract_head_from_type_expr(cst_arg, &ctx.type_op_targets) {
                                            subst.insert(*tv, concrete_head);
                                        }
                                    }
                                }

                                let underlying_type_args = collect_type_args_from_type(underlying_ty2);

                                for (ci, constraint_class) in underlying_constraints.iter().enumerate() {
                                    let concrete_head = if let Some(&arg_ty) = underlying_type_args.get(ci) {
                                        match arg_ty {
                                            crate::typechecker::types::Type::Var(v) => subst.get(&v.symbol()).copied(),
                                            _ => extract_head_from_type(arg_ty),
                                        }
                                    } else {
                                        None
                                    };

                                    if let Some(ch) = concrete_head {
                                        let dict_expr = resolve_instance_ref(ctx, *constraint_class, ch);
                                        inst_expr = JsExpr::App(Box::new(inst_expr), vec![dict_expr]);
                                    }
                                }
                            }
                        }
                    }

                    inst_expr
                    }
                } else {
                    JsExpr::ObjectLit(vec![])
                }
            } else {
                JsExpr::ObjectLit(vec![])
            }
        } else {
            JsExpr::ObjectLit(vec![])
        }
    } else {
        JsExpr::ObjectLit(vec![])
    };

    // Wrap in constraint functions if needed
    if !constraints.is_empty() {
        for constraint in constraints.iter().rev() {
            let dict_param = constraint_to_dict_param(constraint);
            let inner = obj;
            obj = JsExpr::Function(
                None,
                vec![dict_param.clone()],
                vec![JsStmt::Return(JsExpr::App(Box::new(inner), vec![JsExpr::Var(dict_param)]))],
            );
        }
    }

    vec![JsStmt::VarDecl(instance_name.to_string(), Some(obj))]
}

/// Generate `eq` method for derive Eq.
/// `ctor_fields` contains per-constructor, per-field comparison info.
pub(crate) fn gen_derive_eq_methods(
    ctor_fields: &[CtorFields],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    let mut body = Vec::new();
    let is_sum = ctor_fields.len() > 1 || (ctor_fields.len() == 1 && ctor_fields[0].fields.is_empty());

    for cf in ctor_fields {
        if cf.fields.is_empty() {
            // Nullary constructor: instanceof check → return true
            let x_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::Var(cf.ctor_name.clone())),
            );
            let y_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(y.clone())),
                Box::new(JsExpr::Var(cf.ctor_name.clone())),
            );
            let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check), Box::new(y_check));
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(JsExpr::BoolLit(true))],
                None,
            ));
        } else {
            // Constructor with fields: compare each field
            let mut field_eq = JsExpr::BoolLit(true);
            for (i, (field_name, compare)) in cf.fields.iter().enumerate() {
                let x_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let eq_call = match compare {
                    FieldCompare::MethodExpr(expr) => {
                        JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(expr.clone()),
                                vec![x_field],
                            )),
                            vec![y_field],
                        )
                    }
                    FieldCompare::StrictEq => {
                        JsExpr::Binary(JsBinaryOp::StrictEq, Box::new(x_field), Box::new(y_field))
                    }
                    FieldCompare::AlwaysTrue => {
                        JsExpr::BoolLit(true)
                    }
                };
                if i == 0 {
                    field_eq = eq_call;
                } else {
                    field_eq = JsExpr::Binary(JsBinaryOp::And, Box::new(field_eq), Box::new(eq_call));
                }
            }

            if is_sum {
                let x_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::Var(cf.ctor_name.clone())),
                );
                let y_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::Var(cf.ctor_name.clone())),
                );
                let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check), Box::new(y_check));
                body.push(JsStmt::If(
                    both_check,
                    vec![JsStmt::Return(field_eq)],
                    None,
                ));
            } else {
                // Single constructor — no instanceof needed, return directly
                body.push(JsStmt::Return(field_eq));
            }
        }
    }

    // Default: constructors don't match
    if is_sum || ctor_fields.is_empty() {
        body.push(JsStmt::Return(JsExpr::BoolLit(false)));
    }

    let eq_fn = JsExpr::Function(
        None,
        vec![x],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![y],
            body,
        ))],
    );

    vec![("eq".to_string(), eq_fn)]
}

/// Generate `eq1` method for derive Eq1.
/// For newtypes: `{ eq1: function(dictEq) { return Data_Eq.eq(eqF(dictEq)); } }`
pub(crate) fn gen_derive_eq1_methods(ctx: &CodegenCtx, target_type: Option<Symbol>) -> Vec<(String, JsExpr)> {
    // Find the local Eq instance for this type
    let eq_sym = interner::intern("Eq");
    let eq_instance_name = target_type.and_then(|head| {
        ctx.instance_registry.get(&(eq_sym, head)).map(|n| ident_to_js(*n))
    });

    if let Some(eq_inst_js) = eq_instance_name {
        // Resolve Data.Eq.eq
        let eq_qi = QualifiedIdent { module: None, name: interner::intern("eq") };
        let eq_ref = gen_qualified_ref_raw(ctx, &eq_qi);

        // eq1: function(dictEq) { return Data_Eq.eq(eqF(dictEq)); }
        let dict_param = "dictEq".to_string();
        let eq_body = JsExpr::App(
            Box::new(eq_ref),
            vec![JsExpr::App(
                Box::new(JsExpr::Var(eq_inst_js)),
                vec![JsExpr::Var(dict_param.clone())],
            )],
        );
        let eq1_fn = JsExpr::Function(
            None,
            vec![dict_param],
            vec![JsStmt::Return(eq_body)],
        );
        vec![("eq1".to_string(), eq1_fn)]
    } else {
        vec![]
    }
}

/// Generate `compare1` and `Eq10` methods for derive Ord1.
/// For newtypes: `{ compare1: function(dictOrd) { return Data_Ord.compare(ordF(dictOrd)); }, Eq10: function() { return eq1F; } }`
pub(crate) fn gen_derive_ord1_methods(ctx: &CodegenCtx, target_type: Option<Symbol>) -> Vec<(String, JsExpr)> {
    let ord_sym = interner::intern("Ord");
    let ord_instance_name = target_type.and_then(|head| {
        ctx.instance_registry.get(&(ord_sym, head)).map(|n| ident_to_js(*n))
    });

    let mut fields = Vec::new();

    if let Some(ord_inst_js) = ord_instance_name {
        // Resolve Data.Ord.compare
        let compare_qi = QualifiedIdent { module: None, name: interner::intern("compare") };
        let compare_ref = gen_qualified_ref_raw(ctx, &compare_qi);

        // compare1: function(dictOrd) { return Data_Ord.compare(ordF(dictOrd)); }
        let dict_param = "dictOrd".to_string();
        let compare_body = JsExpr::App(
            Box::new(compare_ref),
            vec![JsExpr::App(
                Box::new(JsExpr::Var(ord_inst_js)),
                vec![JsExpr::Var(dict_param.clone())],
            )],
        );
        let compare1_fn = JsExpr::Function(
            None,
            vec![dict_param],
            vec![JsStmt::Return(compare_body)],
        );
        fields.push(("compare1".to_string(), compare1_fn));
    }

    // Eq10: function() { return eq1F; }
    let eq1_sym = interner::intern("Eq1");
    let eq1_instance_name = target_type.and_then(|head| {
        ctx.instance_registry.get(&(eq1_sym, head)).map(|n| ident_to_js(*n))
    });
    if let Some(eq1_inst_js) = eq1_instance_name {
        let eq10_fn = JsExpr::Function(
            None,
            vec![],
            vec![JsStmt::Return(JsExpr::Var(eq1_inst_js))],
        );
        fields.push(("Eq10".to_string(), eq10_fn));
    }

    fields
}

/// Generate `compare` method for derive Ord.
/// Returns Data_Ordering.LT/EQ/GT based on constructor order and field comparison.
/// `ctor_fields` contains per-constructor, per-field comparison info.
pub(crate) fn gen_derive_ord_methods(
    ctx: &CodegenCtx,
    ctor_fields: &[CtorFields],
) -> Vec<(String, JsExpr)> {
    let x = "x".to_string();
    let y = "y".to_string();

    // Resolve Data_Ordering.EQ/LT/GT references
    let ordering_eq = resolve_ordering_ref(ctx, "EQ");
    let ordering_lt = resolve_ordering_ref(ctx, "LT");
    let ordering_gt = resolve_ordering_ref(ctx, "GT");

    let mut body = Vec::new();

    // Void type (no constructors): return EQ (unreachable)
    if ctor_fields.is_empty() {
        body.push(JsStmt::Return(ordering_eq.clone()));

        let compare_fn = JsExpr::Function(
            None,
            vec![x],
            vec![JsStmt::Return(JsExpr::Function(
                None,
                vec![y],
                body,
            ))],
        );
        return vec![("compare".to_string(), compare_fn)];
    }

    for (_i, cf) in ctor_fields.iter().enumerate() {
        let x_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.clone())),
            Box::new(JsExpr::Var(cf.ctor_name.clone())),
        );
        let y_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(y.clone())),
            Box::new(JsExpr::Var(cf.ctor_name.clone())),
        );
        let both_check = JsExpr::Binary(JsBinaryOp::And, Box::new(x_check.clone()), Box::new(y_check.clone()));

        if cf.fields.is_empty() {
            // Both same nullary: return EQ
            body.push(JsStmt::If(
                both_check,
                vec![JsStmt::Return(ordering_eq.clone())],
                None,
            ));
        } else {
            // Both same with fields: compare fields
            let mut inner_body = Vec::new();
            for (field_name, compare) in &cf.fields {
                let x_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(x.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                let y_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(y.clone())),
                    Box::new(JsExpr::StringLit(field_name.clone())),
                );
                match compare {
                    FieldCompare::MethodExpr(expr) => {
                        inner_body.push(JsStmt::Return(JsExpr::App(
                            Box::new(JsExpr::App(
                                Box::new(expr.clone()),
                                vec![x_field],
                            )),
                            vec![y_field],
                        )));
                    }
                    FieldCompare::StrictEq => {
                        // For strict equality in ord, we still need to return an Ordering.
                        // This shouldn't normally happen for Ord (fields should have Ord instances),
                        // but as fallback, return EQ.
                        inner_body.push(JsStmt::Return(ordering_eq.clone()));
                    }
                    FieldCompare::AlwaysTrue => {
                        // Empty record: always equal, return EQ
                        inner_body.push(JsStmt::Return(ordering_eq.clone()));
                    }
                }
            }
            if inner_body.is_empty() {
                inner_body.push(JsStmt::Return(ordering_eq.clone()));
            }
            body.push(JsStmt::If(both_check, inner_body, None));
        }

        // If only x matches this ctor: x comes before y → LT
        // Skip LT/GT for the last constructor — it's the catch-all before the throw
        if ctor_fields.len() > 1 && _i < ctor_fields.len() - 1 {
            body.push(JsStmt::If(
                x_check,
                vec![JsStmt::Return(ordering_lt.clone())],
                None,
            ));
            // If only y matches this ctor: y comes before x → GT
            body.push(JsStmt::If(
                y_check,
                vec![JsStmt::Return(ordering_gt.clone())],
                None,
            ));
        }
    }

    // Fallback: throw error
    body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));

    let compare_fn = JsExpr::Function(
        None,
        vec![x],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![y],
            body,
        ))],
    );

    vec![("compare".to_string(), compare_fn)]
}

/// Resolve a reference to Data.Ordering.X.value (EQ, LT, GT)
pub(crate) fn resolve_ordering_ref(ctx: &CodegenCtx, name: &str) -> JsExpr {
    // Always use Data.Ordering module for derive Ord — even if the module defines a local Ordering type
    let ordering_parts: Vec<Symbol> = vec![interner::intern("Data"), interner::intern("Ordering")];
    if let Some(js_mod) = ctx.import_map.get(&ordering_parts) {
        return JsExpr::Indexer(
            Box::new(JsExpr::ModuleAccessor(js_mod.clone(), name.to_string())),
            Box::new(JsExpr::StringLit("value".to_string())),
        );
    }
    // Fallback: local reference
    JsExpr::Indexer(
        Box::new(JsExpr::Var(name.to_string())),
        Box::new(JsExpr::StringLit("value".to_string())),
    )
}

/// Per-field comparison info for derive Eq/Ord.
/// Each field in a constructor maps to one of these.
pub(crate) enum FieldCompare {
    /// Use a method expression like `Data_Eq.eq(eqInt)` applied as `expr(x.field)(y.field)`
    MethodExpr(JsExpr),
    /// Use strict equality: `x.field === y.field`
    StrictEq,
    /// Always true (for empty records: `{} === {}` is false in JS but should be true)
    AlwaysTrue,
}

/// Per-constructor field info for derive Eq/Ord.
pub(crate) struct CtorFields {
    ctor_name: String,
    /// Each element: (field_accessor_name, comparison)
    fields: Vec<(String, FieldCompare)>,
}

/// Build a method expression for a concrete field type.
/// E.g., for `Type::Con("Int")` and method "eq", returns `Data_Eq.eq(Data_Eq.eqInt)`.
/// For `Type::Con("Int")` and method "compare", returns `Data_Ord.compare(Data_Ord.ordInt)`.
/// Returns None if the instance can't be resolved (falls back to strict equality for eq).
pub(crate) fn resolve_field_method_expr(
    ctx: &CodegenCtx,
    field_type: &crate::typechecker::types::Type,
    class_name: &str,
    method_name: &str,
) -> Option<JsExpr> {
    use crate::typechecker::types::Type;
    let head = match field_type {
        Type::Con(qi) => Some(qi.name),
        Type::App(f, _) => extract_head_from_type(f),
        _ => None,
    }?;
    let class_sym = interner::intern(class_name);
    // Use resolve_instance_ref to get a properly qualified reference
    let inst_ref = resolve_instance_ref(ctx, class_sym, head);
    let method_sym = interner::intern(method_name);
    let method_qi = QualifiedIdent { module: None, name: method_sym };
    let method_ref = gen_qualified_ref_raw(ctx, &method_qi);
    Some(JsExpr::App(
        Box::new(method_ref),
        vec![inst_ref],
    ))
}

/// Check if a type is a primitive that supports strict equality (===) for Eq.
pub(crate) fn is_eq_primitive(ty: &crate::typechecker::types::Type) -> bool {
    use crate::typechecker::types::Type;
    match ty {
        Type::Con(qi) => {
            let name = interner::resolve(qi.name).unwrap_or_default();
            matches!(name.as_str(), "Int" | "Number" | "String" | "Char" | "Boolean")
        }
        _ => false,
    }
}

/// Build per-constructor field comparison info for unconstrained Eq/Ord derives.
pub(crate) fn build_unconstrained_ctor_fields(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    class_name: &str,
    method_name: &str,
    use_strict_eq_for_primitives: bool,
) -> Vec<CtorFields> {
    use crate::typechecker::types::Type;
    let is_single_ctor = ctors_with_types.len() == 1;
    ctors_with_types.iter().map(|(ctor_name, _field_count, field_types)| {
        // Only decompose single-record argument for single-constructor types.
        // For sum types, record is stored at value0, not directly on the object.
        if is_single_ctor && field_types.len() == 1 {
            if let Type::Record(row_fields, _) = &field_types[0] {
                // Record field comparison: compare by named fields
                let fields: Vec<(String, FieldCompare)> = row_fields.iter().map(|(label, ty)| {
                    let label_str = interner::resolve(label.symbol()).unwrap_or_default().to_string();
                    let compare = if matches!(ty, Type::Record(fs, _) if fs.is_empty()) {
                        // Empty record: {} === {} is false in JS, use true instead
                        FieldCompare::AlwaysTrue
                    } else if use_strict_eq_for_primitives && is_eq_primitive(ty) {
                        FieldCompare::StrictEq
                    } else {
                        resolve_field_method_expr(ctx, ty, class_name, method_name)
                            .map(FieldCompare::MethodExpr)
                            .unwrap_or(FieldCompare::StrictEq)
                    };
                    (label_str, compare)
                }).collect();
                return CtorFields { ctor_name: ctor_name.clone(), fields };
            }
        }
        // Positional fields (value0, value1, ...)
        let fields: Vec<(String, FieldCompare)> = field_types.iter().enumerate().map(|(i, ty)| {
            let field_name = format!("value{i}");
            let compare = if matches!(ty, Type::Record(fs, _) if fs.is_empty()) {
                // Empty record: {} === {} is false in JS, use true instead
                FieldCompare::AlwaysTrue
            } else if use_strict_eq_for_primitives && is_eq_primitive(ty) {
                FieldCompare::StrictEq
            } else {
                resolve_field_method_expr(ctx, ty, class_name, method_name)
                    .map(FieldCompare::MethodExpr)
                    .unwrap_or(FieldCompare::StrictEq)
            };
            (field_name, compare)
        }).collect();
        CtorFields { ctor_name: ctor_name.clone(), fields }
    }).collect()
}

/// Build per-constructor field comparison info for constrained Eq/Ord derives.
/// Constrained derives map constraint params to all fields using type variables.
/// Build per-constructor field comparison info for constrained Eq/Ord derives.
/// Uses type-based analysis to determine which comparison method (eq/eq1/===) per field.
/// This handles Eq1/Ord1 constraints properly by analyzing field types.
pub(crate) fn build_constrained_ctor_fields_typed(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    constraints: &[crate::cst::Constraint],
    dict_params: &[String],
    method_name: &str, // "eq" or "compare"
) -> Vec<CtorFields> {
    use crate::typechecker::types::Type;
    use crate::cst::TypeExpr;

    let is_eq = method_name == "eq";
    // The higher-kinded class (Eq1/Ord1) and its method
    let hk_class_name = if is_eq { "Eq1" } else { "Ord1" };
    let hk_method_name = if is_eq { "eq1" } else { "compare1" };

    // Find Eq1/Ord1 constraint index and its type var, if any
    let mut eq1_info: Option<(usize, Symbol)> = None; // (constraint_index, type_var)
    for (i, c) in constraints.iter().enumerate() {
        let cname = interner::resolve(c.class.name).unwrap_or_default();
        if cname == hk_class_name {
            if let Some(TypeExpr::Var { name, .. }) = c.args.first() {
                eq1_info = Some((i, name.value));
            }
            break;
        }
    }

    // Build eq1(dictEq1) partially applied expression (if Eq1 constraint exists)
    let eq1_partial: Option<JsExpr> = eq1_info.map(|(idx, _)| {
        let method_sym = interner::intern(hk_method_name);
        let method_qi = QualifiedIdent { module: None, name: method_sym };
        let method_ref = gen_qualified_ref_raw(ctx, &method_qi);
        JsExpr::App(
            Box::new(method_ref),
            vec![JsExpr::Var(dict_params[idx].clone())],
        )
    });
    let eq1_type_var = eq1_info.map(|(_, tv)| tv);

    // Build mapping: constraint type → dict param expression (for non-Eq1 Eq constraints)
    // This maps the constraint's type argument to the dict param name
    struct ConstraintInfo {
        dict_param: String,
        constraint_type_args: Vec<TypeExpr>,
    }
    let eq_constraints: Vec<ConstraintInfo> = constraints.iter().zip(dict_params.iter())
        .filter(|(c, _)| {
            let cname = interner::resolve(c.class.name).unwrap_or_default();
            let base_class = if is_eq { "Eq" } else { "Ord" };
            cname == base_class
        })
        .map(|(c, dp)| ConstraintInfo {
            dict_param: dp.clone(),
            constraint_type_args: c.args.clone(),
        })
        .collect();

    // Resolve the Eq/Ord dict for a given type, returning a JsExpr for the dict
    // This handles: type vars, concrete types, and type applications
    fn resolve_eq_dict_for_type(
        ctx: &CodegenCtx,
        ty: &Type,
        eq_constraints: &[ConstraintInfo],
        method_name: &str,
    ) -> Option<JsExpr> {
        match ty {
            Type::Var(v) => {
                // Look for a constraint matching this type var
                for ci in eq_constraints {
                    if let Some(TypeExpr::Var { name, .. }) = ci.constraint_type_args.first() {
                        if name.value == v.symbol() {
                            return Some(JsExpr::Var(ci.dict_param.clone()));
                        }
                    }
                }
                None
            }
            Type::Con(qi) => {
                // Concrete type - try to find instance ref
                let class_name = if method_name == "eq" { "Eq" } else { "Ord" };
                let class_sym = interner::intern(class_name);
                let inst = resolve_instance_ref(ctx, class_sym, qi.name);
                Some(inst)
            }
            Type::App(f, arg) => {
                // Type application: e.g. Array a → eqArray(dictForA)
                // or multi-arg: Tuple Int (Array a) → eqTuple(eqInt)(eqArray(dictForA))
                // First, try to resolve the function part as a dict
                let f_dict = match f.as_ref() {
                    Type::Con(qi) => {
                        let class_name = if method_name == "eq" { "Eq" } else { "Ord" };
                        let class_sym = interner::intern(class_name);
                        Some(resolve_instance_ref(ctx, class_sym, qi.name))
                    }
                    Type::App(_, _) => {
                        // Multi-arg application: resolve recursively
                        resolve_eq_dict_for_type(ctx, f, eq_constraints, method_name)
                    }
                    _ => None,
                };
                if let Some(f_expr) = f_dict {
                    if let Some(inner_dict) = resolve_eq_dict_for_type(ctx, arg, eq_constraints, method_name) {
                        return Some(JsExpr::App(Box::new(f_expr), vec![inner_dict]));
                    }
                }
                // Check if it matches an explicit constraint directly
                for ci in eq_constraints {
                    if constraint_type_matches_type(&ci.constraint_type_args, ty) {
                        return Some(JsExpr::Var(ci.dict_param.clone()));
                    }
                }
                None
            }
            _ => {
                // Check if it matches an explicit constraint
                for ci in eq_constraints {
                    if constraint_type_matches_type(&ci.constraint_type_args, ty) {
                        return Some(JsExpr::Var(ci.dict_param.clone()));
                    }
                }
                None
            }
        }
    }

    // Determine the comparison for a single field type
    fn field_compare_for_type(
        ctx: &CodegenCtx,
        ty: &Type,
        eq1_partial: &Option<JsExpr>,
        eq1_type_var: Option<Symbol>,
        eq_constraints: &[ConstraintInfo],
        method_name: &str,
        is_eq: bool,
    ) -> FieldCompare {
        // Primitive types use strict equality for Eq
        if is_eq && is_eq_primitive(ty) {
            return FieldCompare::StrictEq;
        }

        // Check for applied type var: App(Var(f), inner) where f is the Eq1 type var
        if let Type::App(head, inner) = ty {
            if let Type::Var(v) = head.as_ref() {
                if eq1_type_var == Some(v.symbol()) {
                    if let Some(eq1_expr) = eq1_partial {
                        // eq1(dictEq1)(eq_dict_for_inner)
                        if let Some(inner_dict) = resolve_eq_dict_for_type(ctx, inner, eq_constraints, method_name) {
                            let fully_applied = JsExpr::App(
                                Box::new(eq1_expr.clone()),
                                vec![inner_dict],
                            );
                            return FieldCompare::MethodExpr(fully_applied);
                        }
                        // Fallback: check if the whole type matches an explicit constraint
                        for ci in eq_constraints {
                            if constraint_type_matches_type(&ci.constraint_type_args, ty) {
                                let eq_method_sym = interner::intern(method_name);
                                let eq_method_qi = QualifiedIdent { module: None, name: eq_method_sym };
                                let eq_method_ref = gen_qualified_ref_raw(ctx, &eq_method_qi);
                                return FieldCompare::MethodExpr(JsExpr::App(
                                    Box::new(eq_method_ref),
                                    vec![JsExpr::Var(ci.dict_param.clone())],
                                ));
                            }
                        }
                    }
                }
            }
        }

        // Check if the type matches an explicit constraint
        for ci in eq_constraints {
            if constraint_type_matches_type(&ci.constraint_type_args, ty) {
                let eq_method_sym = interner::intern(method_name);
                let eq_method_qi = QualifiedIdent { module: None, name: eq_method_sym };
                let eq_method_ref = gen_qualified_ref_raw(ctx, &eq_method_qi);
                return FieldCompare::MethodExpr(JsExpr::App(
                    Box::new(eq_method_ref),
                    vec![JsExpr::Var(ci.dict_param.clone())],
                ));
            }
        }

        // Type var: find its Eq constraint
        if let Type::Var(v) = ty {
            for ci in eq_constraints {
                if let Some(TypeExpr::Var { name, .. }) = ci.constraint_type_args.first() {
                    if name.value == v.symbol() {
                        let eq_method_sym = interner::intern(method_name);
                        let eq_method_qi = QualifiedIdent { module: None, name: eq_method_sym };
                        let eq_method_ref = gen_qualified_ref_raw(ctx, &eq_method_qi);
                        return FieldCompare::MethodExpr(JsExpr::App(
                            Box::new(eq_method_ref),
                            vec![JsExpr::Var(ci.dict_param.clone())],
                        ));
                    }
                }
            }
        }

        // Record type: generate inline lambda comparison for each field
        if let Type::Record(row_fields, _) = ty {
            if row_fields.is_empty() {
                return FieldCompare::AlwaysTrue;
            }
            // Build: function(x) { return function(y) { return x.f1 === y.f1 && eq(x.f2)(y.f2) && ...; }; }
            let xr = "x$r".to_string();
            let yr = "y$r".to_string();
            let mut and_chain: Option<JsExpr> = None;
            for (label, field_ty) in row_fields {
                let label_str = interner::resolve(label.symbol()).unwrap_or_default().to_string();
                let x_acc = JsExpr::Indexer(
                    Box::new(JsExpr::Var(xr.clone())),
                    Box::new(JsExpr::StringLit(label_str.clone())),
                );
                let y_acc = JsExpr::Indexer(
                    Box::new(JsExpr::Var(yr.clone())),
                    Box::new(JsExpr::StringLit(label_str)),
                );
                let field_cmp = match field_compare_for_type(ctx, field_ty, eq1_partial, eq1_type_var, eq_constraints, method_name, is_eq) {
                    FieldCompare::StrictEq => {
                        JsExpr::Binary(JsBinaryOp::StrictEq, Box::new(x_acc), Box::new(y_acc))
                    }
                    FieldCompare::MethodExpr(expr) => {
                        JsExpr::App(
                            Box::new(JsExpr::App(Box::new(expr), vec![x_acc])),
                            vec![y_acc],
                        )
                    }
                    FieldCompare::AlwaysTrue => JsExpr::BoolLit(true),
                };
                and_chain = Some(match and_chain {
                    None => field_cmp,
                    Some(prev) => JsExpr::Binary(JsBinaryOp::And, Box::new(prev), Box::new(field_cmp)),
                });
            }
            let body = and_chain.unwrap_or(JsExpr::BoolLit(true));
            // function(x$r) { return function(y$r) { return ...; }; }
            let lambda = JsExpr::Function(
                None,
                vec![xr],
                vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![yr],
                    vec![JsStmt::Return(body)],
                ))],
            );
            return FieldCompare::MethodExpr(lambda);
        }

        // Concrete type: try to resolve instance
        if let Some(expr) = resolve_eq_dict_for_type(ctx, ty, &eq_constraints, method_name) {
            let eq_method_sym = interner::intern(method_name);
            let eq_method_qi = QualifiedIdent { module: None, name: eq_method_sym };
            let eq_method_ref = gen_qualified_ref_raw(ctx, &eq_method_qi);
            return FieldCompare::MethodExpr(JsExpr::App(
                Box::new(eq_method_ref),
                vec![expr],
            ));
        }

        FieldCompare::StrictEq
    }

    let is_single_ctor = ctors_with_types.len() == 1;
    ctors_with_types.iter().map(|(ctor_name, _field_count, field_types)| {
        // Only decompose single-record argument for single-constructor types (newtypes).
        // For sum types, the record is stored at value0 so we can't access x.label directly.
        if is_single_ctor && field_types.len() == 1 {
            if let Type::Record(row_fields, _) = &field_types[0] {
                let fields: Vec<(String, FieldCompare)> = row_fields.iter().map(|(label, ty)| {
                    let label_str = interner::resolve(label.symbol()).unwrap_or_default().to_string();
                    let compare = if matches!(ty, Type::Record(fs, _) if fs.is_empty()) {
                        FieldCompare::AlwaysTrue
                    } else {
                        field_compare_for_type(ctx, ty, &eq1_partial, eq1_type_var, &eq_constraints, method_name, is_eq)
                    };
                    (label_str, compare)
                }).collect();
                return CtorFields { ctor_name: ctor_name.clone(), fields };
            }
        }
        // Positional fields
        let fields: Vec<(String, FieldCompare)> = field_types.iter().enumerate().map(|(i, ty)| {
            let field_name = format!("value{i}");
            let compare = if matches!(ty, Type::Record(fs, _) if fs.is_empty()) {
                FieldCompare::AlwaysTrue
            } else {
                field_compare_for_type(ctx, ty, &eq1_partial, eq1_type_var, &eq_constraints, method_name, is_eq)
            };
            (field_name, compare)
        }).collect();
        CtorFields { ctor_name: ctor_name.clone(), fields }
    }).collect()
}

/// Check if a constraint's type args (CST TypeExpr) match a given Type.
/// This does structural matching for common patterns.
pub(crate) fn constraint_type_matches_type(
    constraint_args: &[crate::cst::TypeExpr],
    ty: &crate::typechecker::types::Type,
) -> bool {
    use crate::typechecker::types::Type;
    use crate::cst::TypeExpr;

    if constraint_args.len() != 1 {
        return false;
    }

    fn matches_inner(cst_ty: &TypeExpr, ty: &Type) -> bool {
        match (cst_ty, ty) {
            // Unwrap parentheses
            (TypeExpr::Parens { ty: inner_cst, .. }, _) => matches_inner(inner_cst, ty),
            (TypeExpr::Var { name, .. }, Type::Var(v)) => name.value == v.symbol(),
            (TypeExpr::Constructor { name, .. }, Type::Con(tqi)) => name.name == tqi.name,
            (TypeExpr::App { constructor, arg, .. }, Type::App(tf, ta)) => {
                // CST App is binary: App { constructor, arg }
                // Type::App is also binary: App(f, a)
                matches_inner(constructor, tf) && matches_inner(arg, ta)
            }
            (TypeExpr::Record { fields, .. }, Type::Record(ty_fields, _)) => {
                // Approximate: just check field count matches
                fields.len() == ty_fields.len()
            }
            _ => false,
        }
    }

    matches_inner(&constraint_args[0], ty)
}

/// Generate a failed pattern match error expression
pub(crate) fn gen_failed_pattern_match(_ctx: &CodegenCtx) -> JsExpr {
    JsExpr::New(
        Box::new(JsExpr::Var("Error".to_string())),
        vec![JsExpr::StringLit("Failed pattern match".to_string())],
    )
}

/// Generate `map` method for derive Functor.
/// ```js
/// map: function(f) { return function(x) {
///   if (x instanceof Nothing) return Nothing.value;
///   if (x instanceof Just) return Just.create(f(x.value0));
///   ...
/// }}
/// ```
pub(crate) fn gen_derive_functor_methods(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    map_param_expr: Option<JsExpr>,
) -> Vec<(String, JsExpr)> {
    let f = "f".to_string();
    let m = "m".to_string();

    // Newtype optimization: if single constructor with one field and it's a newtype,
    // the Functor map is just `function(f) { return function(m) { return f(m); }; }`
    if ctors_with_types.len() == 1 && ctors_with_types[0].1 == 1 {
        let ctor_sym = interner::intern(&ctors_with_types[0].0);
        if ctx.newtype_names.contains(&ctor_sym) {
            let map_fn = JsExpr::Function(
                None,
                vec![f.clone()],
                vec![JsStmt::Return(JsExpr::Function(
                    None,
                    vec![m.clone()],
                    vec![JsStmt::Return(JsExpr::App(
                        Box::new(JsExpr::Var(f)),
                        vec![JsExpr::Var(m)],
                    ))],
                ))],
            );
            return vec![("map".to_string(), map_fn)];
        }
    }

    let ctors: Vec<(String, usize)> = ctors_with_types.iter().map(|(n, c, _)| (n.clone(), *c)).collect();
    let mut body = Vec::new();
    let is_sum = ctors.len() > 1 || (ctors.len() == 1 && ctors[0].1 == 0);

    for (ctor_name, field_count, field_types_raw) in ctors_with_types {
        if *field_count == 0 {
            // Nullary constructor: return as-is
            let m_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(m.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
            );
            body.push(JsStmt::If(
                m_check,
                vec![JsStmt::Return(JsExpr::Indexer(
                    Box::new(JsExpr::Var(ctor_name.clone())),
                    Box::new(JsExpr::StringLit("value".to_string())),
                ))],
                None,
            ));
        } else {
            // Look up field types to determine how to map each field
            let ctor_sym = interner::intern(ctor_name);
            let ctor_qi = unqualified(ctor_sym);
            let field_kinds: Vec<FunctorFieldKind> = ctx.ctor_details.get(&ctor_qi)
                .map(|(parent, type_vars, _ftypes)| {
                    let last_tv = type_vars.last().map(|qi| qi.name);
                    let param_tv = if type_vars.len() >= 2 {
                        type_vars.get(type_vars.len() - 2).map(|qi| qi.name)
                    } else {
                        None
                    };
                    let parent_name = parent.name;
                    field_types_raw.iter().map(|ft| categorize_functor_field(ft, last_tv, param_tv, parent_name)).collect::<Vec<_>>()
                })
                .unwrap_or_else(|| vec![FunctorFieldKind::Direct; *field_count]);

            // Build args for new Ctor(arg0, arg1, ...)
            let mut args = Vec::new();
            for i in 0..*field_count {
                let field_access = JsExpr::Indexer(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::StringLit(format!("value{i}"))),
                );
                let kind = field_kinds.get(i).cloned().unwrap_or(FunctorFieldKind::Direct);
                let arg = gen_functor_map_field(ctx, &kind, &f, field_access, map_param_expr.as_ref());
                args.push(arg);
            }

            let result = JsExpr::New(
                Box::new(JsExpr::Var(ctor_name.clone())),
                args,
            );

            if is_sum {
                let m_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::Var(ctor_name.clone())),
                );
                body.push(JsStmt::If(
                    m_check,
                    vec![JsStmt::Return(result)],
                    None,
                ));
            } else {
                // Single constructor: no instanceof needed
                body.push(JsStmt::Return(result));
            }
        }
    }

    // Fallback: throw error for sum types
    if is_sum {
        body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    let map_fn = JsExpr::Function(
        None,
        vec![f],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![m],
            body,
        ))],
    );

    vec![("map".to_string(), map_fn)]
}

#[derive(Debug, Clone)]
pub(crate) enum FunctorFieldKind {
    /// The field is the type variable directly (a) → apply f
    Direct,
    /// The field does not involve the type var → pass through unchanged
    Passthrough,
    /// Map through a known functor: Array, Tuple, etc. Inner is how to map the arg.
    /// Symbol is the type constructor name (e.g. "Array")
    KnownFunctor(Symbol, Box<FunctorFieldKind>),
    /// Map through the parametric functor variable (f a). Inner is how to map the arg.
    ParamFunctor(Box<FunctorFieldKind>),
    /// Map through a function type (a -> b). Inner is how to map the return type.
    FunctionMap(Box<FunctorFieldKind>),
    /// Record with per-field mapping
    Record(Vec<(Symbol, FunctorFieldKind)>),
}

/// Categorize a constructor field for Functor deriving.
/// `ty` is the field type, `last_tv` is the last type variable (the one being mapped),
/// `param_tv` is the second-to-last type variable (the parametric functor, e.g. `f`),
/// `parent_type` is the type being derived for.
pub(crate) fn categorize_functor_field(
    ty: &crate::typechecker::types::Type,
    last_tv: Option<Symbol>,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
) -> FunctorFieldKind {
    use crate::typechecker::types::Type;

    let last_tv = match last_tv {
        Some(v) => v,
        None => return FunctorFieldKind::Passthrough,
    };

    if !type_contains_var(ty, last_tv) {
        return FunctorFieldKind::Passthrough;
    }

    match ty {
        Type::Var(v) if v.symbol() == last_tv => FunctorFieldKind::Direct,

        Type::Fun(_arg_ty, ret_ty) => {
            // a -> b: map over the return type using functorFn composition
            let inner = categorize_functor_field(ret_ty, Some(last_tv), param_tv, parent_type);
            FunctorFieldKind::FunctionMap(Box::new(inner))
        }

        Type::Forall(_, body) => {
            // forall t. constraint => body desugars to function params at runtime
            // Each forall/constraint adds a function layer
            categorize_forall_field(body, last_tv, param_tv, parent_type)
        }

        Type::Record(fields, _tail) => {
            let mut field_kinds = Vec::new();
            for (name, field_ty) in fields {
                let kind = categorize_functor_field(field_ty, Some(last_tv), param_tv, parent_type);
                field_kinds.push((name.symbol(), kind));
            }
            FunctorFieldKind::Record(field_kinds)
        }

        Type::App(head, arg) => {
            categorize_app_field(head, arg, last_tv, param_tv, parent_type)
        }

        _ => FunctorFieldKind::Direct,
    }
}

/// Handle forall types: each forall variable (and constraint dict) becomes a function parameter
pub(crate) fn categorize_forall_field(
    ty: &crate::typechecker::types::Type,
    last_tv: Symbol,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
) -> FunctorFieldKind {
    use crate::typechecker::types::Type;
    match ty {
        Type::Fun(_arg, ret) => {
            // constraint dict or forall var becomes a function param
            let inner = categorize_forall_field(ret, last_tv, param_tv, parent_type);
            FunctorFieldKind::FunctionMap(Box::new(inner))
        }
        Type::Forall(_, body) => {
            categorize_forall_field(body, last_tv, param_tv, parent_type)
        }
        _ => categorize_functor_field(ty, Some(last_tv), param_tv, parent_type),
    }
}

/// Handle App types: extract the head constructor and determine mapping strategy
pub(crate) fn categorize_app_field(
    head: &crate::typechecker::types::Type,
    arg: &crate::typechecker::types::Type,
    last_tv: Symbol,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
) -> FunctorFieldKind {
    use crate::typechecker::types::Type;

    // Get the innermost argument's kind (how to map it)
    let inner = categorize_functor_field(arg, Some(last_tv), param_tv, parent_type);

    match head {
        // Simple: Con arg (e.g. Array a, Tuple a)
        Type::Con(qi) => {
            FunctorFieldKind::KnownFunctor(qi.name, Box::new(inner))
        }
        // Parametric: Var(f) arg (e.g. f a)
        Type::Var(v) if param_tv == Some(v.symbol()) => {
            FunctorFieldKind::ParamFunctor(Box::new(inner))
        }
        // Nested App: e.g. App(App(Con(Tuple), Int), arg) — peel off to get head
        Type::App(_inner_head, _inner_arg) => {
            // Extract the outermost type constructor
            if let Some(head_con) = extract_app_head(head) {
                FunctorFieldKind::KnownFunctor(head_con, Box::new(inner))
            } else {
                // Unknown nested app — try parametric
                FunctorFieldKind::Direct
            }
        }
        _ => FunctorFieldKind::Direct,
    }
}

/// Extract the head type constructor name from a (possibly nested) App chain.
pub(crate) fn extract_app_head(ty: &crate::typechecker::types::Type) -> Option<Symbol> {
    use crate::typechecker::types::Type;
    match ty {
        Type::Con(qi) => Some(qi.name),
        Type::App(head, _) => extract_app_head(head),
        _ => None,
    }
}

pub(crate) fn type_contains_var(ty: &crate::typechecker::types::Type, var: Symbol) -> bool {
    use crate::typechecker::types::Type;
    match ty {
        Type::Var(v) => v.symbol() == var,
        Type::App(h, arg) => type_contains_var(h, var) || type_contains_var(arg, var),
        Type::Fun(a, b) => type_contains_var(a, var) || type_contains_var(b, var),
        Type::Forall(_, body) => type_contains_var(body, var),
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_contains_var(t, var))
                || tail.as_ref().map_or(false, |t| type_contains_var(t, var))
        }
        _ => false,
    }
}

/// Resolve Data.Functor.map reference
pub(crate) fn resolve_functor_map_ref(ctx: &CodegenCtx) -> JsExpr {
    let map_sym = interner::intern("map");
    let map_qi = QualifiedIdent { module: None, name: map_sym };
    gen_qualified_ref_raw(ctx, &map_qi)
}

/// Resolve the functor instance for a known type constructor (e.g. functorArray, functorFn)
pub(crate) fn resolve_functor_instance(ctx: &CodegenCtx, type_con: Symbol) -> Option<JsExpr> {
    let type_str = interner::resolve(type_con).unwrap_or_default();
    // Strip module qualifier if present (e.g. "Data.Array.Array" -> "Array")
    let short_name = type_str.rsplit('.').next().unwrap_or(&type_str);
    // Special cases for built-in types
    let instance_name = match short_name {
        "Function" | "Fn" | "->" => "functorFn".to_string(),
        other => format!("functor{other}"),
    };
    let instance_sym = interner::intern(&instance_name);
    let qi = QualifiedIdent { module: None, name: instance_sym };
    Some(gen_qualified_ref_raw(ctx, &qi))
}

/// Generate the map expression for a field based on its FunctorFieldKind.
/// `f_var` is the name of the mapping function parameter.
/// `field_expr` is the expression accessing the field (e.g. m.value0).
/// `map_param_expr` is the expression for the parametric functor dict (e.g. dictFunctor), if any.
pub(crate) fn gen_functor_map_field(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    f_var: &str,
    field_expr: JsExpr,
    map_param_expr: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct => {
            // f(field)
            JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_expr])
        }
        FunctorFieldKind::Passthrough => {
            field_expr
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            // map(functorX)(inner_fn)(field)
            // where inner_fn maps the argument
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            if let Some(instance) = resolve_functor_instance(ctx, *con) {
                // Data_Functor.map(functorX)(inner_fn)(field)
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(map_ref),
                            vec![instance],
                        )),
                        vec![inner_fn],
                    )),
                    vec![field_expr],
                )
            } else {
                // Fallback: just apply f
                JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_expr])
            }
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            // map(dictFunctor)(inner_fn)(field)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            if let Some(param) = map_param_expr {
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(map_ref),
                            vec![param.clone()],
                        )),
                        vec![inner_fn],
                    )),
                    vec![field_expr],
                )
            } else {
                // No parametric functor available — shouldn't happen, fall back
                JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_expr])
            }
        }
        FunctorFieldKind::FunctionMap(inner) => {
            // map(functorFn)(inner_fn)(field) — function composition
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            let fn_sym = interner::intern("functorFn");
            let fn_qi = QualifiedIdent { module: None, name: fn_sym };
            let fn_instance = gen_qualified_ref_raw(ctx, &fn_qi);
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(map_ref),
                        vec![fn_instance],
                    )),
                    vec![inner_fn],
                )),
                vec![field_expr],
            )
        }
        FunctorFieldKind::Record(fields) => {
            // Build a record literal with per-field mapping
            // Passthrough fields first, then mapped fields (sorted alphabetically)
            let mut obj_fields = Vec::new();
            for (name, field_kind) in fields {
                let name_str = interner::resolve(*name).unwrap_or_default().to_string();
                let field_access = JsExpr::Indexer(
                    Box::new(field_expr.clone()),
                    Box::new(JsExpr::StringLit(name_str.clone())),
                );
                let mapped = gen_functor_map_field(ctx, field_kind, f_var, field_access, map_param_expr);
                obj_fields.push((name_str, mapped));
            }
            // Sort: passthrough fields first, then mapped fields, both alphabetically
            obj_fields.sort_by(|a, b| {
                let a_is_pass = matches!(fields.iter().find(|(n, _)| interner::resolve(*n).unwrap_or_default() == a.0).map(|(_, k)| k), Some(FunctorFieldKind::Passthrough));
                let b_is_pass = matches!(fields.iter().find(|(n, _)| interner::resolve(*n).unwrap_or_default() == b.0).map(|(_, k)| k), Some(FunctorFieldKind::Passthrough));
                match (a_is_pass, b_is_pass) {
                    (true, false) => std::cmp::Ordering::Less,
                    (false, true) => std::cmp::Ordering::Greater,
                    _ => a.0.cmp(&b.0),
                }
            });
            JsExpr::ObjectLit(obj_fields.into_iter().map(|(n, e)| (n, e)).collect())
        }
    }
}

/// Generate a mapping function expression for use as an argument to map.
/// For Direct, this is just `f`. For nested kinds, this wraps in another function.
pub(crate) fn gen_functor_map_fn(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    f_var: &str,
    map_param_expr: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct => {
            // Just f
            JsExpr::Var(f_var.to_string())
        }
        FunctorFieldKind::Passthrough => {
            // Identity — shouldn't normally be called for passthrough
            JsExpr::Var(f_var.to_string())
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            // map(functorX)(inner_fn)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            if let Some(instance) = resolve_functor_instance(ctx, *con) {
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(map_ref),
                        vec![instance],
                    )),
                    vec![inner_fn],
                )
            } else {
                inner_fn
            }
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            // map(dictFunctor)(inner_fn)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            if let Some(param) = map_param_expr {
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(map_ref),
                        vec![param.clone()],
                    )),
                    vec![inner_fn],
                )
            } else {
                inner_fn
            }
        }
        FunctorFieldKind::FunctionMap(inner) => {
            // map(functorFn)(inner_fn)
            let inner_fn = gen_functor_map_fn(ctx, inner, f_var, map_param_expr);
            let map_ref = resolve_functor_map_ref(ctx);
            let fn_sym = interner::intern("functorFn");
            let fn_qi = QualifiedIdent { module: None, name: fn_sym };
            let fn_instance = gen_qualified_ref_raw(ctx, &fn_qi);
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(map_ref),
                    vec![fn_instance],
                )),
                vec![inner_fn],
            )
        }
        FunctorFieldKind::Record(fields) => {
            // function(v1) { return { field: mapped, ... }; }
            let v_param = "v1".to_string();
            let v_expr = JsExpr::Var(v_param.clone());
            let mapped = gen_functor_map_field(ctx, &FunctorFieldKind::Record(fields.clone()), f_var, v_expr, map_param_expr);
            JsExpr::Function(None, vec![v_param], vec![JsStmt::Return(mapped)])
        }
    }
}


// ===== Foldable deriving =====

/// Generate methods for derive Foldable.
/// Produces foldl, foldr, and foldMap methods.
pub(crate) fn gen_derive_foldable_methods(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    foldable_param: Option<JsExpr>,
) -> Vec<(String, JsExpr)> {
    let first_ctor = ctors_with_types.first();
    let (last_tv, param_tv, parent_type) = first_ctor
        .and_then(|(name, _, _)| {
            let ctor_sym = interner::intern(name);
            let ctor_qi = unqualified(ctor_sym);
            ctx.ctor_details.get(&ctor_qi).map(|(parent, type_vars, _)| {
                let last = type_vars.last().map(|qi| qi.name);
                let param = if type_vars.len() >= 2 {
                    Some(type_vars[type_vars.len() - 2].name)
                } else {
                    None
                };
                (last, param, parent.name)
            })
        })
        .unwrap_or((None, None, interner::intern("Unknown")));

    let is_sum = ctors_with_types.len() > 1 || (ctors_with_types.len() == 1 && ctors_with_types[0].1 == 0);

    let foldl_fn = gen_foldable_foldl(ctx, ctors_with_types, last_tv, param_tv, parent_type, is_sum, foldable_param.as_ref());
    let foldr_fn = gen_foldable_foldr(ctx, ctors_with_types, last_tv, param_tv, parent_type, is_sum, foldable_param.as_ref());
    let foldmap_fn = gen_foldable_foldmap(ctx, ctors_with_types, last_tv, param_tv, parent_type, is_sum, foldable_param.as_ref());

    vec![
        ("foldl".to_string(), foldl_fn),
        ("foldr".to_string(), foldr_fn),
        ("foldMap".to_string(), foldmap_fn),
    ]
}

/// Resolve a foldable method (foldl/foldr/foldMap) applied to a known foldable instance (e.g., foldableArray).
pub(crate) fn resolve_foldable_method_for_type(ctx: &CodegenCtx, method: &str, type_con: Symbol) -> JsExpr {
    let method_sym = interner::intern(method);
    let method_qi = QualifiedIdent { module: None, name: method_sym };
    let method_ref = gen_qualified_ref_raw(ctx, &method_qi);
    let type_str = interner::resolve(type_con).unwrap_or_default();
    let short_name = type_str.rsplit('.').next().unwrap_or(&type_str);
    let instance_name = format!("foldable{short_name}");
    let instance_sym = interner::intern(&instance_name);
    let inst_qi = QualifiedIdent { module: None, name: instance_sym };
    let instance = gen_qualified_ref_raw(ctx, &inst_qi);
    JsExpr::App(Box::new(method_ref), vec![instance])
}

/// Resolve a foldable method applied to the constraint dict param (e.g., foldl(dictFoldable)).
pub(crate) fn resolve_foldable_method_for_param(ctx: &CodegenCtx, method: &str, foldable_param: &JsExpr) -> JsExpr {
    let method_sym = interner::intern(method);
    let method_qi = QualifiedIdent { module: None, name: method_sym };
    let method_ref = gen_qualified_ref_raw(ctx, &method_qi);
    JsExpr::App(Box::new(method_ref), vec![foldable_param.clone()])
}

/// Generate the foldl method: function(f) { return function(z) { return function(m) { ... } } }
pub(crate) fn gen_foldable_foldl(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    last_tv: Option<Symbol>,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
    is_sum: bool,
    foldable_param: Option<&JsExpr>,
) -> JsExpr {
    let f = "f".to_string();
    let z = "z".to_string();
    let m = "m".to_string();

    let mut body = Vec::new();

    for (ctor_name, field_count, field_types) in ctors_with_types {
        let m_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(m.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );

        if *field_count == 0 {
            body.push(JsStmt::If(m_check, vec![JsStmt::Return(JsExpr::Var(z.clone()))], None));
        } else {
            let field_kinds: Vec<FunctorFieldKind> = field_types.iter()
                .map(|ft| categorize_functor_field(ft, last_tv, param_tv, parent_type))
                .collect();

            let mut acc = JsExpr::Var(z.clone());
            for (i, kind) in field_kinds.iter().enumerate() {
                let field_access = JsExpr::Indexer(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::StringLit(format!("value{i}"))),
                );
                acc = gen_foldl_step(ctx, kind, acc, field_access, &f, foldable_param);
            }

            body.push(JsStmt::If(m_check, vec![JsStmt::Return(acc)], None));
        }
    }

    if is_sum {
        body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    JsExpr::Function(None, vec![f], vec![JsStmt::Return(
        JsExpr::Function(None, vec![z], vec![JsStmt::Return(
            JsExpr::Function(None, vec![m], body),
        )]),
    )])
}

/// Generate a single foldl step: fold a field into the accumulator.
pub(crate) fn gen_foldl_step(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    acc: JsExpr,
    field: JsExpr,
    f_var: &str,
    foldable_param: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Passthrough | FunctorFieldKind::FunctionMap(_) => acc,
        FunctorFieldKind::Direct => {
            // f(acc)(field)
            JsExpr::App(
                Box::new(JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![acc])),
                vec![field],
            )
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            // foldl(foldableX)(combiner)(acc)(field)
            let foldl_ref = resolve_foldable_method_for_type(ctx, "foldl", *con);
            let combiner = gen_foldl_combiner(ctx, inner, f_var, foldable_param);
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::App(Box::new(foldl_ref), vec![combiner])),
                    vec![acc],
                )),
                vec![field],
            )
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            if let Some(param) = foldable_param {
                // foldl(dictFoldable)(combiner)(acc)(field)
                let foldl_ref = resolve_foldable_method_for_param(ctx, "foldl", param);
                let combiner = gen_foldl_combiner(ctx, inner, f_var, foldable_param);
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::App(Box::new(foldl_ref), vec![combiner])),
                        vec![acc],
                    )),
                    vec![field],
                )
            } else {
                acc
            }
        }
        FunctorFieldKind::Record(fields) => {
            // Thread acc through each foldable field in alphabetical order
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(*name).unwrap_or_default().to_string());
            let mut result = acc;
            for (name, sub_kind) in sorted_fields {
                let name_str = interner::resolve(*name).unwrap_or_default();
                let sub_field = JsExpr::Indexer(
                    Box::new(field.clone()),
                    Box::new(JsExpr::StringLit(name_str.to_string())),
                );
                result = gen_foldl_step(ctx, sub_kind, result, sub_field, f_var, foldable_param);
            }
            result
        }
    }
}

/// Generate a foldl combiner expression for nested types.
pub(crate) fn gen_foldl_combiner(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    f_var: &str,
    foldable_param: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct | FunctorFieldKind::Passthrough | FunctorFieldKind::FunctionMap(_) => {
            JsExpr::Var(f_var.to_string())
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            let foldl_ref = resolve_foldable_method_for_type(ctx, "foldl", *con);
            let inner_combiner = gen_foldl_combiner(ctx, inner, f_var, foldable_param);
            JsExpr::App(Box::new(foldl_ref), vec![inner_combiner])
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            if let Some(param) = foldable_param {
                let foldl_ref = resolve_foldable_method_for_param(ctx, "foldl", param);
                let inner_combiner = gen_foldl_combiner(ctx, inner, f_var, foldable_param);
                JsExpr::App(Box::new(foldl_ref), vec![inner_combiner])
            } else {
                JsExpr::Var(f_var.to_string())
            }
        }
        FunctorFieldKind::Record(fields) => {
            // function(v1) { return function(v2) { return <thread v1 through v2's fields> } }
            let v1 = "v1".to_string();
            let v2 = "v2".to_string();
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(*name).unwrap_or_default().to_string());
            let mut result = JsExpr::Var(v1.clone());
            for (name, sub_kind) in sorted_fields {
                let name_str = interner::resolve(*name).unwrap_or_default();
                let sub_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(v2.clone())),
                    Box::new(JsExpr::StringLit(name_str.to_string())),
                );
                result = gen_foldl_step(ctx, sub_kind, result, sub_field, f_var, foldable_param);
            }
            JsExpr::Function(None, vec![v1], vec![JsStmt::Return(
                JsExpr::Function(None, vec![v2], vec![JsStmt::Return(result)]),
            )])
        }
    }
}

/// Generate the foldr method: function(f) { return function(z) { return function(m) { ... } } }
pub(crate) fn gen_foldable_foldr(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    last_tv: Option<Symbol>,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
    is_sum: bool,
    foldable_param: Option<&JsExpr>,
) -> JsExpr {
    let f = "f".to_string();
    let z = "z".to_string();
    let m = "m".to_string();

    let mut body = Vec::new();

    for (ctor_name, field_count, field_types) in ctors_with_types {
        let m_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(m.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );

        if *field_count == 0 {
            body.push(JsStmt::If(m_check, vec![JsStmt::Return(JsExpr::Var(z.clone()))], None));
        } else {
            let field_kinds: Vec<FunctorFieldKind> = field_types.iter()
                .map(|ft| categorize_functor_field(ft, last_tv, param_tv, parent_type))
                .collect();

            // Collect all foldable atoms in order, then process right-to-left
            let mut atoms: Vec<(FunctorFieldKind, JsExpr)> = Vec::new();
            for (i, kind) in field_kinds.iter().enumerate() {
                let field_access = JsExpr::Indexer(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::StringLit(format!("value{i}"))),
                );
                collect_foldr_atoms(kind, field_access, &mut atoms);
            }

            // Process atoms right-to-left (reverse order)
            let mut acc = JsExpr::Var(z.clone());
            for (kind, field) in atoms.iter().rev() {
                acc = gen_foldr_step_atom(ctx, kind, acc, field.clone(), &f, foldable_param);
            }

            body.push(JsStmt::If(m_check, vec![JsStmt::Return(acc)], None));
        }
    }

    if is_sum {
        body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    JsExpr::Function(None, vec![f], vec![JsStmt::Return(
        JsExpr::Function(None, vec![z], vec![JsStmt::Return(
            JsExpr::Function(None, vec![m], body),
        )]),
    )])
}

/// Collect foldr "atoms" — individual foldable field accesses, flattening records.
/// Records are flattened in alphabetical order (foldr will reverse).
pub(crate) fn collect_foldr_atoms(
    kind: &FunctorFieldKind,
    field: JsExpr,
    out: &mut Vec<(FunctorFieldKind, JsExpr)>,
) {
    match kind {
        FunctorFieldKind::Passthrough | FunctorFieldKind::FunctionMap(_) => {}
        FunctorFieldKind::Record(fields) => {
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(*name).unwrap_or_default().to_string());
            for (name, sub_kind) in sorted_fields {
                let name_str = interner::resolve(*name).unwrap_or_default();
                let sub_field = JsExpr::Indexer(
                    Box::new(field.clone()),
                    Box::new(JsExpr::StringLit(name_str.to_string())),
                );
                collect_foldr_atoms(sub_kind, sub_field, out);
            }
        }
        other => {
            out.push((other.clone(), field));
        }
    }
}

/// Generate a single foldr step for an atom (non-record, non-passthrough).
pub(crate) fn gen_foldr_step_atom(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    acc: JsExpr,
    field: JsExpr,
    f_var: &str,
    foldable_param: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct => {
            // f(field)(acc)
            JsExpr::App(
                Box::new(JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field])),
                vec![acc],
            )
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            // foldr(foldableX)(combiner)(acc)(field)
            let foldr_ref = resolve_foldable_method_for_type(ctx, "foldr", *con);
            let combiner = gen_foldr_combiner(ctx, inner, f_var, foldable_param);
            JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::App(Box::new(foldr_ref), vec![combiner])),
                    vec![acc],
                )),
                vec![field],
            )
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            if let Some(param) = foldable_param {
                // foldr(dictFoldable)(combiner)(acc)(field)
                let foldr_ref = resolve_foldable_method_for_param(ctx, "foldr", param);
                let combiner = gen_foldr_combiner(ctx, inner, f_var, foldable_param);
                JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::App(Box::new(foldr_ref), vec![combiner])),
                        vec![acc],
                    )),
                    vec![field],
                )
            } else {
                acc
            }
        }
        _ => acc, // Passthrough, FunctionMap, Record handled elsewhere
    }
}

/// Generate a foldr combiner expression for nested types.
/// For nested foldables, we need flip(foldr(inner_combiner)) because
/// foldr(combiner) :: b -> t a -> b, but we need t a -> b -> b.
pub(crate) fn gen_foldr_combiner(
    ctx: &CodegenCtx,
    kind: &FunctorFieldKind,
    f_var: &str,
    foldable_param: Option<&JsExpr>,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct | FunctorFieldKind::Passthrough | FunctorFieldKind::FunctionMap(_) => {
            JsExpr::Var(f_var.to_string())
        }
        FunctorFieldKind::KnownFunctor(con, inner) => {
            // flip(foldr(foldableX)(inner_combiner))
            let foldr_ref = resolve_foldable_method_for_type(ctx, "foldr", *con);
            let inner_combiner = gen_foldr_combiner(ctx, inner, f_var, foldable_param);
            let foldr_applied = JsExpr::App(Box::new(foldr_ref), vec![inner_combiner]);
            gen_flip_expr(ctx, foldr_applied)
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            if let Some(param) = foldable_param {
                // flip(foldr(dictFoldable)(inner_combiner))
                let foldr_ref = resolve_foldable_method_for_param(ctx, "foldr", param);
                let inner_combiner = gen_foldr_combiner(ctx, inner, f_var, foldable_param);
                let foldr_applied = JsExpr::App(Box::new(foldr_ref), vec![inner_combiner]);
                gen_flip_expr(ctx, foldr_applied)
            } else {
                JsExpr::Var(f_var.to_string())
            }
        }
        FunctorFieldKind::Record(fields) => {
            // function(v1) { return function(v2) { return <foldr v1's fields into v2> } }
            // v1 = element, v2 = accumulator (foldr order)
            let v1 = "v1".to_string();
            let v2 = "v2".to_string();

            let mut atoms: Vec<(FunctorFieldKind, JsExpr)> = Vec::new();
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(*name).unwrap_or_default().to_string());
            for (name, sub_kind) in sorted_fields {
                let name_str = interner::resolve(*name).unwrap_or_default();
                let sub_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(v1.clone())),
                    Box::new(JsExpr::StringLit(name_str.to_string())),
                );
                collect_foldr_atoms(sub_kind, sub_field, &mut atoms);
            }

            let mut result = JsExpr::Var(v2.clone());
            for (kind, field) in atoms.iter().rev() {
                result = gen_foldr_step_atom(ctx, kind, result, field.clone(), f_var, foldable_param);
            }

            JsExpr::Function(None, vec![v1], vec![JsStmt::Return(
                JsExpr::Function(None, vec![v2], vec![JsStmt::Return(result)]),
            )])
        }
    }
}

/// Generate Data_Function.flip(expr)
pub(crate) fn gen_flip_expr(ctx: &CodegenCtx, expr: JsExpr) -> JsExpr {
    let flip_sym = interner::intern("flip");
    let flip_qi = QualifiedIdent { module: None, name: flip_sym };
    let flip_ref = gen_qualified_ref_raw(ctx, &flip_qi);
    JsExpr::App(Box::new(flip_ref), vec![expr])
}

/// Generate the foldMap method: function(dictMonoid) { ... return function(f) { return function(m) { ... } } }
pub(crate) fn gen_foldable_foldmap(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    last_tv: Option<Symbol>,
    param_tv: Option<Symbol>,
    parent_type: Symbol,
    is_sum: bool,
    foldable_param: Option<&JsExpr>,
) -> JsExpr {
    let dict_monoid = "dictMonoid".to_string();
    let f = "f".to_string();
    let m = "m".to_string();

    // Local variable names inside function(dictMonoid)
    let mempty_var = "mempty".to_string();
    let append_var = "append1".to_string();
    let foldmap_arr_var = "foldMap2".to_string(); // foldMap for Array
    let foldmap_param_var = "foldMap3".to_string(); // foldMap for constraint param

    // Build the declarations inside function(dictMonoid)
    let mut decls = Vec::new();

    // var mempty = Data_Monoid.mempty(dictMonoid)
    let mempty_sym = interner::intern("mempty");
    let mempty_qi = QualifiedIdent { module: None, name: mempty_sym };
    let mempty_ref = gen_qualified_ref_raw(ctx, &mempty_qi);
    decls.push(JsStmt::VarDecl(mempty_var.clone(), Some(
        JsExpr::App(Box::new(mempty_ref), vec![JsExpr::Var(dict_monoid.clone())]),
    )));

    // var append1 = Data_Semigroup.append(dictMonoid.Semigroup0())
    let append_sym = interner::intern("append");
    let append_qi = QualifiedIdent { module: None, name: append_sym };
    let append_ref = gen_qualified_ref_raw(ctx, &append_qi);
    let semigroup0_access = JsExpr::App(
        Box::new(JsExpr::Indexer(
            Box::new(JsExpr::Var(dict_monoid.clone())),
            Box::new(JsExpr::StringLit("Semigroup0".to_string())),
        )),
        vec![],
    );
    decls.push(JsStmt::VarDecl(append_var.clone(), Some(
        JsExpr::App(Box::new(append_ref), vec![semigroup0_access]),
    )));

    // var foldMap2 = Data_Foldable.foldMap(foldableArray)(dictMonoid)
    let array_sym = interner::intern("Array");
    let foldmap_arr_base = resolve_foldable_method_for_type(ctx, "foldMap", array_sym);
    decls.push(JsStmt::VarDecl(foldmap_arr_var.clone(), Some(
        JsExpr::App(Box::new(foldmap_arr_base), vec![JsExpr::Var(dict_monoid.clone())]),
    )));

    // var foldMap3 = Data_Foldable.foldMap(dictFoldable)(dictMonoid) (if constraint)
    if let Some(param) = foldable_param {
        let foldmap_param_base = resolve_foldable_method_for_param(ctx, "foldMap", param);
        decls.push(JsStmt::VarDecl(foldmap_param_var.clone(), Some(
            JsExpr::App(Box::new(foldmap_param_base), vec![JsExpr::Var(dict_monoid.clone())]),
        )));
    }

    // Build the inner function(f) { return function(m) { ... } }
    let mut body = Vec::new();

    for (ctor_name, field_count, field_types) in ctors_with_types {
        let m_check = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(m.clone())),
            Box::new(JsExpr::Var(ctor_name.clone())),
        );

        if *field_count == 0 {
            body.push(JsStmt::If(m_check, vec![JsStmt::Return(JsExpr::Var(mempty_var.clone()))], None));
        } else {
            let field_kinds: Vec<FunctorFieldKind> = field_types.iter()
                .map(|ft| categorize_functor_field(ft, last_tv, param_tv, parent_type))
                .collect();

            // Collect all foldMap expressions for foldable fields
            let mut exprs: Vec<JsExpr> = Vec::new();
            for (i, kind) in field_kinds.iter().enumerate() {
                let field_access = JsExpr::Indexer(
                    Box::new(JsExpr::Var(m.clone())),
                    Box::new(JsExpr::StringLit(format!("value{i}"))),
                );
                collect_foldmap_exprs(kind, field_access, &f, &foldmap_arr_var, &foldmap_param_var, &mut exprs, foldable_param.is_some());
            }

            let result = if exprs.is_empty() {
                JsExpr::Var(mempty_var.clone())
            } else {
                combine_with_append(&exprs, &append_var)
            };

            body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
        }
    }

    if is_sum {
        body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    let inner_fn = JsExpr::Function(None, vec![f], vec![JsStmt::Return(
        JsExpr::Function(None, vec![m], body),
    )]);

    decls.push(JsStmt::Return(inner_fn));

    JsExpr::Function(None, vec![dict_monoid], decls)
}

/// Collect foldMap expressions for a field, flattening records.
pub(crate) fn collect_foldmap_exprs(
    kind: &FunctorFieldKind,
    field: JsExpr,
    f_var: &str,
    foldmap_arr_var: &str,
    foldmap_param_var: &str,
    out: &mut Vec<JsExpr>,
    has_param: bool,
) {
    match kind {
        FunctorFieldKind::Passthrough | FunctorFieldKind::FunctionMap(_) => {}
        FunctorFieldKind::Direct => {
            // f(field)
            out.push(JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field]));
        }
        FunctorFieldKind::KnownFunctor(_con, inner) => {
            // foldMap2(inner_fn)(field)
            let inner_fn = gen_foldmap_fn(inner, f_var, foldmap_arr_var, foldmap_param_var, has_param);
            out.push(JsExpr::App(
                Box::new(JsExpr::App(Box::new(JsExpr::Var(foldmap_arr_var.to_string())), vec![inner_fn])),
                vec![field],
            ));
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            if has_param {
                // foldMap3(inner_fn)(field)
                let inner_fn = gen_foldmap_fn(inner, f_var, foldmap_arr_var, foldmap_param_var, has_param);
                out.push(JsExpr::App(
                    Box::new(JsExpr::App(Box::new(JsExpr::Var(foldmap_param_var.to_string())), vec![inner_fn])),
                    vec![field],
                ));
            }
        }
        FunctorFieldKind::Record(fields) => {
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(*name).unwrap_or_default().to_string());
            for (name, sub_kind) in sorted_fields {
                let name_str = interner::resolve(*name).unwrap_or_default();
                let sub_field = JsExpr::Indexer(
                    Box::new(field.clone()),
                    Box::new(JsExpr::StringLit(name_str.to_string())),
                );
                collect_foldmap_exprs(sub_kind, sub_field, f_var, foldmap_arr_var, foldmap_param_var, out, has_param);
            }
        }
    }
}

/// Generate foldMap function for nested types: the function passed to foldMap2/foldMap3.
pub(crate) fn gen_foldmap_fn(
    kind: &FunctorFieldKind,
    f_var: &str,
    foldmap_arr_var: &str,
    foldmap_param_var: &str,
    has_param: bool,
) -> JsExpr {
    match kind {
        FunctorFieldKind::Direct | FunctorFieldKind::Passthrough | FunctorFieldKind::FunctionMap(_) => {
            JsExpr::Var(f_var.to_string())
        }
        FunctorFieldKind::KnownFunctor(_con, inner) => {
            // foldMap2(inner_fn)
            let inner_fn = gen_foldmap_fn(inner, f_var, foldmap_arr_var, foldmap_param_var, has_param);
            JsExpr::App(Box::new(JsExpr::Var(foldmap_arr_var.to_string())), vec![inner_fn])
        }
        FunctorFieldKind::ParamFunctor(inner) => {
            if has_param {
                // foldMap3(inner_fn)
                let inner_fn = gen_foldmap_fn(inner, f_var, foldmap_arr_var, foldmap_param_var, has_param);
                JsExpr::App(Box::new(JsExpr::Var(foldmap_param_var.to_string())), vec![inner_fn])
            } else {
                JsExpr::Var(f_var.to_string())
            }
        }
        FunctorFieldKind::Record(fields) => {
            // function(v1) { return append(...)(...) }
            let v1 = "v1".to_string();
            let mut exprs: Vec<JsExpr> = Vec::new();
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(*name).unwrap_or_default().to_string());
            for (name, sub_kind) in sorted_fields {
                let name_str = interner::resolve(*name).unwrap_or_default();
                let sub_field = JsExpr::Indexer(
                    Box::new(JsExpr::Var(v1.clone())),
                    Box::new(JsExpr::StringLit(name_str.to_string())),
                );
                collect_foldmap_exprs(sub_kind, sub_field, f_var, foldmap_arr_var, foldmap_param_var, &mut exprs, has_param);
            }
            let result = if exprs.is_empty() {
                JsExpr::Var("mempty".to_string())
            } else {
                combine_with_append(&exprs, "append1")
            };
            JsExpr::Function(None, vec![v1], vec![JsStmt::Return(result)])
        }
    }
}

/// Combine expressions with right-folded append: append(e1)(append(e2)(append(e3)(e4)))
pub(crate) fn combine_with_append(exprs: &[JsExpr], append_var: &str) -> JsExpr {
    if exprs.len() == 1 {
        return exprs[0].clone();
    }
    // Right-fold: last expr is base, then wrap from right to left
    let mut result = exprs.last().unwrap().clone();
    for expr in exprs[..exprs.len() - 1].iter().rev() {
        result = JsExpr::App(
            Box::new(JsExpr::App(
                Box::new(JsExpr::Var(append_var.to_string())),
                vec![expr.clone()],
            )),
            vec![result],
        );
    }
    result
}


/// Field classification for Traversable deriving
#[derive(Debug, Clone)]
pub(crate) enum TraversableFieldKind {
    /// The type variable directly (a) - apply f
    Direct,
    /// Known traversable like Array - use traverse2 (Array's traverse)
    KnownTraversable,
    /// The type parameter f - use traverse3 (param's traverse)  
    ParamTraversable,
    /// Concrete type not involving type var - pass through
    Passthrough,
    /// Record type with traversable fields
    Record(Vec<(String, TraversableFieldKind)>),
    /// Nested: outer traversable wrapping inner (e.g., f (f a)) - compose traversals
    Nested(Box<TraversableFieldKind>, Box<TraversableFieldKind>),
}

/// Categorize a field for Traversable deriving.
/// `last_tv` is the last type variable (a), `param_tv` is the functor parameter (f).
pub(crate) fn categorize_traversable_field(
    ty: &crate::typechecker::types::Type,
    last_tv: Option<Symbol>,
    parent_type: Symbol,
    param_tv: Option<Symbol>,
) -> TraversableFieldKind {
    use crate::typechecker::types::Type;
    let last = match last_tv {
        Some(v) => v,
        None => return TraversableFieldKind::Passthrough,
    };
    match ty {
        Type::Var(v) if v.symbol() == last => TraversableFieldKind::Direct,
        Type::Var(_) => TraversableFieldKind::Passthrough,
        Type::App(head, arg) => {
            let head_con = extract_app_head(head);
            let inner_kind = categorize_traversable_field(arg, last_tv, parent_type, param_tv);

            match head_con {
                Some(con) => {
                    let is_param = match head.as_ref() {
                        Type::Var(v) => param_tv == Some(v.symbol()),
                        _ => false,
                    };
                    let array_sym = interner::intern("Array");
                    let is_array = con == array_sym;
                    
                    if is_param {
                        match inner_kind {
                            TraversableFieldKind::Passthrough => TraversableFieldKind::Passthrough,
                            TraversableFieldKind::Direct => TraversableFieldKind::ParamTraversable,
                            other => TraversableFieldKind::Nested(
                                Box::new(TraversableFieldKind::ParamTraversable),
                                Box::new(other),
                            ),
                        }
                    } else if is_array {
                        match inner_kind {
                            TraversableFieldKind::Passthrough => TraversableFieldKind::Passthrough,
                            TraversableFieldKind::Direct => TraversableFieldKind::KnownTraversable,
                            other => TraversableFieldKind::Nested(
                                Box::new(TraversableFieldKind::KnownTraversable),
                                Box::new(other),
                            ),
                        }
                    } else {
                        if type_contains_var(ty, last) {
                            TraversableFieldKind::Direct
                        } else {
                            TraversableFieldKind::Passthrough
                        }
                    }
                }
                None => {
                    let is_param = match head.as_ref() {
                        Type::Var(v) => param_tv == Some(v.symbol()),
                        _ => false,
                    };
                    if is_param {
                        match inner_kind {
                            TraversableFieldKind::Passthrough => TraversableFieldKind::Passthrough,
                            TraversableFieldKind::Direct => TraversableFieldKind::ParamTraversable,
                            other => TraversableFieldKind::Nested(
                                Box::new(TraversableFieldKind::ParamTraversable),
                                Box::new(other),
                            ),
                        }
                    } else if type_contains_var(ty, last) {
                        TraversableFieldKind::Direct
                    } else {
                        TraversableFieldKind::Passthrough
                    }
                }
            }
        }
        Type::Record(fields, _tail) => {
            let mut rec_fields = Vec::new();
            let mut has_effectful = false;
            let mut sorted_fields: Vec<_> = fields.iter().collect();
            sorted_fields.sort_by_key(|(name, _)| interner::resolve(name.symbol()).unwrap_or_default());
            for (name, fty) in &sorted_fields {
                let name_str = interner::resolve(name.symbol()).unwrap_or_default();
                let kind = categorize_traversable_field(fty, last_tv, parent_type, param_tv);
                if !matches!(kind, TraversableFieldKind::Passthrough) {
                    has_effectful = true;
                }
                rec_fields.push((name_str, kind));
            }
            if has_effectful {
                TraversableFieldKind::Record(rec_fields)
            } else {
                TraversableFieldKind::Passthrough
            }
        }
        _ => {
            if type_contains_var(ty, last) {
                TraversableFieldKind::Direct
            } else {
                TraversableFieldKind::Passthrough
            }
        }
    }
}

/// Count the number of effectful (non-passthrough) fields in a TraversableFieldKind
pub(crate) fn count_effectful(kind: &TraversableFieldKind) -> usize {
    match kind {
        TraversableFieldKind::Passthrough => 0,
        TraversableFieldKind::Direct | TraversableFieldKind::KnownTraversable | TraversableFieldKind::ParamTraversable => 1,
        TraversableFieldKind::Record(fields) => {
            fields.iter().map(|(_, k)| count_effectful(k)).sum()
        }
        TraversableFieldKind::Nested(_, inner) => count_effectful(inner),
    }
}

/// Generate the traverse expression for a single field
pub(crate) fn gen_traverse_field_expr(
    kind: &TraversableFieldKind,
    field_access: JsExpr,
    f_var: &str,
    var_counter: &mut usize,
    apply_var: &str,
    map1_var: &str,
    _pure1_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
) -> (JsExpr, Vec<JsExpr>) {
    match kind {
        TraversableFieldKind::Direct => {
            (JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_access]), vec![])
        }
        TraversableFieldKind::KnownTraversable => {
            (JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse2_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ), vec![])
        }
        TraversableFieldKind::ParamTraversable => {
            (JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse3_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ), vec![])
        }
        TraversableFieldKind::Passthrough => {
            (field_access, vec![])
        }
        TraversableFieldKind::Record(_fields) => {
            // Records in top-level fields are handled by the caller
            (field_access, vec![])
        }
        TraversableFieldKind::Nested(outer, inner) => {
            let inner_fn = gen_nested_traverse_fn(inner, f_var, var_counter, apply_var, map1_var, _pure1_var, traverse2_var, traverse3_var);
            let outer_traverse = match outer.as_ref() {
                TraversableFieldKind::KnownTraversable => JsExpr::Var(traverse2_var.to_string()),
                TraversableFieldKind::ParamTraversable => JsExpr::Var(traverse3_var.to_string()),
                _ => JsExpr::Var(traverse3_var.to_string()),
            };
            (JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(outer_traverse),
                    vec![inner_fn],
                )),
                vec![field_access],
            ), vec![])
        }
    }
}

/// Generate a traverse function for nested types
pub(crate) fn gen_nested_traverse_fn(
    kind: &TraversableFieldKind,
    f_var: &str,
    var_counter: &mut usize,
    apply_var: &str,
    map1_var: &str,
    pure1_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
) -> JsExpr {
    match kind {
        TraversableFieldKind::Direct => {
            JsExpr::Var(f_var.to_string())
        }
        TraversableFieldKind::KnownTraversable => {
            JsExpr::App(
                Box::new(JsExpr::Var(traverse2_var.to_string())),
                vec![JsExpr::Var(f_var.to_string())],
            )
        }
        TraversableFieldKind::ParamTraversable => {
            JsExpr::App(
                Box::new(JsExpr::Var(traverse3_var.to_string())),
                vec![JsExpr::Var(f_var.to_string())],
            )
        }
        TraversableFieldKind::Record(fields) => {
            let param_name = format!("v{}", *var_counter);
            *var_counter += 1;
            
            // Collect effectful fields with their access expressions
            let mut effects: Vec<JsExpr> = Vec::new();
            let mut param_names: Vec<String> = Vec::new();
            let param_access = JsExpr::Var(param_name.clone());
            
            collect_effects_for_record_fields(fields, &param_access, f_var, traverse2_var, traverse3_var, &mut effects);
            for _ in 0..effects.len() {
                param_names.push(format!("v{}", *var_counter));
                *var_counter += 1;
            }
            
            // Build the record result using params
            let record_obj = build_nested_record_result(fields, &param_access, &param_names, &mut 0);
            
            // Build nested lambda
            let mut lambda: JsExpr = record_obj;
            for i in (0..param_names.len()).rev() {
                lambda = JsExpr::Function(
                    None,
                    vec![param_names[i].clone()],
                    vec![JsStmt::Return(lambda)],
                );
            }
            
            // Build applicative chain
            let result = build_applicative_chain(&lambda, &effects, apply_var, map1_var);
            
            JsExpr::Function(
                None,
                vec![param_name],
                vec![JsStmt::Return(result)],
            )
        }
        TraversableFieldKind::Nested(outer, inner) => {
            let inner_fn = gen_nested_traverse_fn(inner, f_var, var_counter, apply_var, map1_var, pure1_var, traverse2_var, traverse3_var);
            let outer_traverse = match outer.as_ref() {
                TraversableFieldKind::KnownTraversable => JsExpr::Var(traverse2_var.to_string()),
                TraversableFieldKind::ParamTraversable => JsExpr::Var(traverse3_var.to_string()),
                _ => JsExpr::Var(traverse3_var.to_string()),
            };
            JsExpr::App(
                Box::new(outer_traverse),
                vec![inner_fn],
            )
        }
        TraversableFieldKind::Passthrough => {
            JsExpr::Var(f_var.to_string())
        }
    }
}

/// Collect effects from record fields (recursing into nested records)
pub(crate) fn collect_effects_for_record_fields(
    fields: &[(String, TraversableFieldKind)],
    record_access: &JsExpr,
    f_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
    out: &mut Vec<JsExpr>,
) {
    for (name, kind) in fields {
        let field_acc = JsExpr::Indexer(
            Box::new(record_access.clone()),
            Box::new(JsExpr::StringLit(name.clone())),
        );
        match kind {
            TraversableFieldKind::Passthrough => {}
            TraversableFieldKind::Direct => {
                out.push(JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_acc]));
            }
            TraversableFieldKind::KnownTraversable => {
                out.push(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::Var(traverse2_var.to_string())),
                        vec![JsExpr::Var(f_var.to_string())],
                    )),
                    vec![field_acc],
                ));
            }
            TraversableFieldKind::ParamTraversable => {
                out.push(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::Var(traverse3_var.to_string())),
                        vec![JsExpr::Var(f_var.to_string())],
                    )),
                    vec![field_acc],
                ));
            }
            TraversableFieldKind::Record(sub_fields) => {
                collect_effects_for_record_fields(sub_fields, &field_acc, f_var, traverse2_var, traverse3_var, out);
            }
            TraversableFieldKind::Nested(_, _) => {
                out.push(field_acc);
            }
        }
    }
}

/// Build nested record result using param vars
pub(crate) fn build_nested_record_result(
    fields: &[(String, TraversableFieldKind)],
    record_access: &JsExpr,
    param_names: &[String],
    param_idx: &mut usize,
) -> JsExpr {
    let mut obj_fields = Vec::new();
    for (name, kind) in fields {
        match kind {
            TraversableFieldKind::Passthrough => {
                obj_fields.push((name.clone(), JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                )));
            }
            TraversableFieldKind::Record(sub_fields) => {
                let sub_access = JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                );
                let sub_obj = build_nested_record_result(sub_fields, &sub_access, param_names, param_idx);
                obj_fields.push((name.clone(), sub_obj));
            }
            _ => {
                if *param_idx < param_names.len() {
                    obj_fields.push((name.clone(), JsExpr::Var(param_names[*param_idx].clone())));
                    *param_idx += 1;
                }
            }
        }
    }
    JsExpr::ObjectLit(obj_fields)
}

/// Build applicative chain: apply(apply(map1(lambda)(eff0))(eff1))...(effN-1)
pub(crate) fn build_applicative_chain(
    lambda: &JsExpr,
    effects: &[JsExpr],
    apply_var: &str,
    map1_var: &str,
) -> JsExpr {
    if effects.is_empty() {
        return lambda.clone();
    }
    // Start: map1(lambda)(effects[0])
    let mut result = JsExpr::App(
        Box::new(JsExpr::App(
            Box::new(JsExpr::Var(map1_var.to_string())),
            vec![lambda.clone()],
        )),
        vec![effects[0].clone()],
    );
    // Chain: apply(result)(effects[i])
    for eff in &effects[1..] {
        result = JsExpr::App(
            Box::new(JsExpr::App(
                Box::new(JsExpr::Var(apply_var.to_string())),
                vec![result],
            )),
            vec![eff.clone()],
        );
    }
    result
}

/// Collect all effectful expressions for a field (flattening records)
pub(crate) fn collect_effects_for_field(
    kind: &TraversableFieldKind,
    field_access: JsExpr,
    f_var: &str,
    traverse2_var: &str,
    traverse3_var: &str,
    out: &mut Vec<JsExpr>,
) {
    match kind {
        TraversableFieldKind::Passthrough => {}
        TraversableFieldKind::Direct => {
            out.push(JsExpr::App(Box::new(JsExpr::Var(f_var.to_string())), vec![field_access]));
        }
        TraversableFieldKind::KnownTraversable => {
            out.push(JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse2_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ));
        }
        TraversableFieldKind::ParamTraversable => {
            out.push(JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::Var(traverse3_var.to_string())),
                    vec![JsExpr::Var(f_var.to_string())],
                )),
                vec![field_access],
            ));
        }
        TraversableFieldKind::Record(fields) => {
            for (name, sub_kind) in fields {
                let sub_access = JsExpr::Indexer(
                    Box::new(field_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                );
                collect_effects_for_field(sub_kind, sub_access, f_var, traverse2_var, traverse3_var, out);
            }
        }
        TraversableFieldKind::Nested(_, _) => {
            out.push(field_access);
        }
    }
}

/// Build the constructor result expression using param variables for effectful fields
pub(crate) fn build_ctor_result_expr(
    ctor_name: &str,
    field_kinds: &[TraversableFieldKind],
    m_var: &str,
    param_names: &[String],
) -> JsExpr {
    let mut args = Vec::new();
    let mut param_idx = 0;
    
    for (i, kind) in field_kinds.iter().enumerate() {
        let field_access = JsExpr::Indexer(
            Box::new(JsExpr::Var(m_var.to_string())),
            Box::new(JsExpr::StringLit(format!("value{i}"))),
        );
        match kind {
            TraversableFieldKind::Passthrough => {
                args.push(field_access);
            }
            TraversableFieldKind::Direct | TraversableFieldKind::KnownTraversable | TraversableFieldKind::ParamTraversable => {
                if param_idx < param_names.len() {
                    args.push(JsExpr::Var(param_names[param_idx].clone()));
                    param_idx += 1;
                }
            }
            TraversableFieldKind::Record(fields) => {
                let record_obj = build_ctor_record_result(fields, &field_access, param_names, &mut param_idx);
                args.push(record_obj);
            }
            TraversableFieldKind::Nested(_, _) => {
                if param_idx < param_names.len() {
                    args.push(JsExpr::Var(param_names[param_idx].clone()));
                    param_idx += 1;
                }
            }
        }
    }
    
    JsExpr::New(Box::new(JsExpr::Var(ctor_name.to_string())), args)
}

/// Build record result for a constructor field
pub(crate) fn build_ctor_record_result(
    fields: &[(String, TraversableFieldKind)],
    record_access: &JsExpr,
    param_names: &[String],
    param_idx: &mut usize,
) -> JsExpr {
    let mut obj_fields = Vec::new();
    for (name, kind) in fields {
        match kind {
            TraversableFieldKind::Passthrough => {
                obj_fields.push((name.clone(), JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                )));
            }
            TraversableFieldKind::Direct | TraversableFieldKind::KnownTraversable | TraversableFieldKind::ParamTraversable => {
                if *param_idx < param_names.len() {
                    obj_fields.push((name.clone(), JsExpr::Var(param_names[*param_idx].clone())));
                    *param_idx += 1;
                }
            }
            TraversableFieldKind::Record(sub_fields) => {
                let sub_access = JsExpr::Indexer(
                    Box::new(record_access.clone()),
                    Box::new(JsExpr::StringLit(name.clone())),
                );
                let sub_obj = build_ctor_record_result(sub_fields, &sub_access, param_names, param_idx);
                obj_fields.push((name.clone(), sub_obj));
            }
            TraversableFieldKind::Nested(_, _) => {
                if *param_idx < param_names.len() {
                    obj_fields.push((name.clone(), JsExpr::Var(param_names[*param_idx].clone())));
                    *param_idx += 1;
                }
            }
        }
    }
    JsExpr::ObjectLit(obj_fields)
}

/// Generate methods for derive Traversable.
pub(crate) fn gen_derive_traversable_methods(
    ctx: &CodegenCtx,
    ctors_with_types: &[(String, usize, Vec<crate::typechecker::types::Type>)],
    instance_name: &str,
    dict_params: &[String],
) -> Vec<(String, JsExpr)> {
    let f_var = "f".to_string();
    let m_var = "m".to_string();
    let pure1 = "pure1".to_string();
    let apply_var = "apply".to_string();
    let map1 = "map1".to_string();
    let traverse2 = "traverse2".to_string();
    let traverse3 = "traverse3".to_string();

    let first_ctor = ctors_with_types.first();
    let (last_tv, param_tv, parent_type) = first_ctor
        .and_then(|(name, _, _)| {
            let ctor_sym = interner::intern(name);
            let ctor_qi = unqualified(ctor_sym);
            ctx.ctor_details.get(&ctor_qi).map(|(parent, type_vars, _)| {
                let last = type_vars.last().map(|qi| qi.name);
                let param = if type_vars.len() >= 2 {
                    Some(type_vars[type_vars.len() - 2].name)
                } else {
                    None
                };
                (last, param, parent.name)
            })
        })
        .unwrap_or((None, None, interner::intern("Unknown")));

    let is_sum = ctors_with_types.len() > 1 || (ctors_with_types.len() == 1 && ctors_with_types[0].1 == 0);

    let mut body = Vec::new();

    for (ctor_name, field_count, field_types) in ctors_with_types {
        if *field_count == 0 {
            let m_check = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(m_var.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
            );
            let result = JsExpr::App(
                Box::new(JsExpr::Var(pure1.clone())),
                vec![JsExpr::Indexer(
                    Box::new(JsExpr::Var(ctor_name.clone())),
                    Box::new(JsExpr::StringLit("value".to_string())),
                )],
            );
            body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
        } else {
            let field_kinds: Vec<TraversableFieldKind> = field_types.iter()
                .map(|ft| categorize_traversable_field(ft, last_tv, parent_type, param_tv))
                .collect();

            let total_effectful: usize = field_kinds.iter().map(|k| count_effectful(k)).sum();

            if total_effectful == 0 {
                let m_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(m_var.clone())),
                    Box::new(JsExpr::Var(ctor_name.clone())),
                );
                let mut args = Vec::new();
                for i in 0..*field_count {
                    args.push(JsExpr::Indexer(
                        Box::new(JsExpr::Var(m_var.clone())),
                        Box::new(JsExpr::StringLit(format!("value{i}"))),
                    ));
                }
                let result = JsExpr::App(
                    Box::new(JsExpr::Var(pure1.clone())),
                    vec![JsExpr::New(Box::new(JsExpr::Var(ctor_name.clone())), args)],
                );
                body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
            } else {
                let m_check = JsExpr::InstanceOf(
                    Box::new(JsExpr::Var(m_var.clone())),
                    Box::new(JsExpr::Var(ctor_name.clone())),
                );

                let mut var_counter = *field_count;

                // Check for single-field nested type (like M7)
                if *field_count == 1 && matches!(&field_kinds[0], TraversableFieldKind::Nested(_, _)) {
                    let field_access = JsExpr::Indexer(
                        Box::new(JsExpr::Var(m_var.clone())),
                        Box::new(JsExpr::StringLit("value0".to_string())),
                    );
                    var_counter = 1;
                    let (eff_expr, _) = gen_traverse_field_expr(
                        &field_kinds[0], field_access, &f_var, &mut var_counter,
                        &apply_var, &map1, &pure1, &traverse2, &traverse3,
                    );
                    let ctor_lambda = JsExpr::Function(
                        None,
                        vec!["v1".to_string()],
                        vec![JsStmt::Return(JsExpr::New(
                            Box::new(JsExpr::Var(ctor_name.clone())),
                            vec![JsExpr::Var("v1".to_string())],
                        ))],
                    );
                    let result = JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(JsExpr::Var(map1.clone())),
                            vec![ctor_lambda],
                        )),
                        vec![eff_expr],
                    );
                    body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
                    continue;
                }

                let mut all_effects: Vec<JsExpr> = Vec::new();
                let mut param_names: Vec<String> = Vec::new();
                
                for (i, kind) in field_kinds.iter().enumerate() {
                    let field_access = JsExpr::Indexer(
                        Box::new(JsExpr::Var(m_var.clone())),
                        Box::new(JsExpr::StringLit(format!("value{i}"))),
                    );
                    collect_effects_for_field(kind, field_access, &f_var, &traverse2, &traverse3, &mut all_effects);
                }
                
                for _ in 0..all_effects.len() {
                    param_names.push(format!("v{var_counter}"));
                    var_counter += 1;
                }

                let ctor_result = build_ctor_result_expr(
                    ctor_name, &field_kinds, &m_var, &param_names,
                );
                
                let mut lambda: JsExpr = ctor_result;
                for i in (0..param_names.len()).rev() {
                    lambda = JsExpr::Function(
                        None,
                        vec![param_names[i].clone()],
                        vec![JsStmt::Return(lambda)],
                    );
                }

                let result = build_applicative_chain(&lambda, &all_effects, &apply_var, &map1);
                
                body.push(JsStmt::If(m_check, vec![JsStmt::Return(result)], None));
            }
        }
    }

    if is_sum {
        body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    // Build traverse method body with var decls
    let mut traverse_body = Vec::new();
    let pure_ref = {
        let pure_sym = interner::intern("pure");
        let pure_qi = QualifiedIdent { module: None, name: pure_sym };
        gen_qualified_ref_raw(ctx, &pure_qi)
    };
    traverse_body.push(JsStmt::VarDecl(pure1.clone(), Some(JsExpr::App(
        Box::new(pure_ref),
        vec![JsExpr::Var("dictApplicative".to_string())],
    ))));
    traverse_body.push(JsStmt::VarDecl("Apply0".to_string(), Some(JsExpr::App(
        Box::new(JsExpr::Indexer(
            Box::new(JsExpr::Var("dictApplicative".to_string())),
            Box::new(JsExpr::StringLit("Apply0".to_string())),
        )),
        vec![],
    ))));
    let apply_ref = {
        let apply_sym = interner::intern("apply");
        let apply_qi = QualifiedIdent { module: None, name: apply_sym };
        gen_qualified_ref_raw(ctx, &apply_qi)
    };
    traverse_body.push(JsStmt::VarDecl(apply_var.clone(), Some(JsExpr::App(
        Box::new(apply_ref),
        vec![JsExpr::Var("Apply0".to_string())],
    ))));
    let map_ref = resolve_functor_map_ref(ctx);
    traverse_body.push(JsStmt::VarDecl(map1.clone(), Some(JsExpr::App(
        Box::new(map_ref),
        vec![JsExpr::App(
            Box::new(JsExpr::Indexer(
                Box::new(JsExpr::Var("Apply0".to_string())),
                Box::new(JsExpr::StringLit("Functor0".to_string())),
            )),
            vec![],
        )],
    ))));
    // traverse2 = Data_Traversable.traverse(Data_Traversable.traversableArray)(dictApplicative)
    // This is the Array traverse, fully applied with the Array traversable dict
    let dt_traverse_ref = {
        let traverse_sym = interner::intern("traverse");
        let dt_module = interner::intern("Data.Traversable");
        let traverse_qi = QualifiedIdent { module: Some(dt_module), name: traverse_sym };
        gen_qualified_ref_raw(ctx, &traverse_qi)
    };
    let traversable_array_ref = {
        let ta_sym = interner::intern("traversableArray");
        let dt_module = interner::intern("Data.Traversable");
        let ta_qi = QualifiedIdent { module: Some(dt_module), name: ta_sym };
        gen_qualified_ref_raw(ctx, &ta_qi)
    };
    traverse_body.push(JsStmt::VarDecl(traverse2.clone(), Some(JsExpr::App(
        Box::new(JsExpr::App(
            Box::new(dt_traverse_ref.clone()),
            vec![traversable_array_ref],
        )),
        vec![JsExpr::Var("dictApplicative".to_string())],
    ))));
    // traverse3 = Data_Traversable.traverse(dictTraversable)(dictApplicative)
    // The hoisting mechanism will extract Data_Traversable.traverse(dictTraversable) as traverse1
    if !dict_params.is_empty() {
        traverse_body.push(JsStmt::VarDecl(traverse3.clone(), Some(JsExpr::App(
            Box::new(JsExpr::App(
                Box::new(dt_traverse_ref),
                vec![JsExpr::Var(dict_params[0].clone())],
            )),
            vec![JsExpr::Var("dictApplicative".to_string())],
        ))));
    }

    traverse_body.push(JsStmt::Return(JsExpr::Function(
        None,
        vec![f_var],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec![m_var],
            body,
        ))],
    )));

    let traverse_fn = JsExpr::Function(
        None,
        vec!["dictApplicative".to_string()],
        traverse_body,
    );

    // sequence method
    let data_traversable_traverse = {
        let traverse_sym = interner::intern("traverse");
        let dt_module = interner::intern("Data.Traversable");
        let traverse_qi = QualifiedIdent { module: Some(dt_module), name: traverse_sym };
        gen_qualified_ref_raw(ctx, &traverse_qi)
    };
    let identity_ref = {
        // identity needs to be Control_Category.identity(Control_Category.categoryFn)
        let identity_sym = interner::intern("identity");
        let cc_module = interner::intern("Control.Category");
        let identity_qi = QualifiedIdent { module: Some(cc_module), name: identity_sym };
        let identity_base = gen_qualified_ref_raw(ctx, &identity_qi);
        let category_fn_sym = interner::intern("categoryFn");
        let category_fn_qi = QualifiedIdent { module: Some(cc_module), name: category_fn_sym };
        let category_fn_ref = gen_qualified_ref_raw(ctx, &category_fn_qi);
        JsExpr::App(Box::new(identity_base), vec![category_fn_ref])
    };
    let self_ref = if !dict_params.is_empty() {
        JsExpr::App(
            Box::new(JsExpr::Var(instance_name.to_string())),
            vec![JsExpr::Var(dict_params[0].clone())],
        )
    } else {
        JsExpr::Var(instance_name.to_string())
    };
    let sequence_fn = JsExpr::Function(
        None,
        vec!["dictApplicative".to_string()],
        vec![JsStmt::Return(JsExpr::Function(
            None,
            vec!["v".to_string()],
            vec![JsStmt::Return(JsExpr::App(
                Box::new(JsExpr::App(
                    Box::new(JsExpr::App(
                        Box::new(JsExpr::App(
                            Box::new(data_traversable_traverse),
                            vec![self_ref],
                        )),
                        vec![JsExpr::Var("dictApplicative".to_string())],
                    )),
                    vec![identity_ref],
                )),
                vec![JsExpr::Var("v".to_string())],
            ))],
        ))],
    );

    vec![
        ("traverse".to_string(), traverse_fn),
        ("sequence".to_string(), sequence_fn),
    ]
}

/// Generate methods for derive Newtype class.
/// The original compiler only emits Coercible0: function() { return undefined; }
pub(crate) fn gen_derive_newtype_class_methods() -> Vec<(String, JsExpr)> {
    vec![]
}

/// Generate `to` and `from` methods for derive Generic.
/// These convert between the type and its generic representation.
/// For now, generates identity-like stubs since the Generic rep is typically
/// handled at the type level and the runtime is just constructor tagging.
pub(crate) fn gen_derive_generic_methods(ctx: &CodegenCtx, ctors: &[(String, usize)]) -> Vec<(String, JsExpr)> {
    // Resolve Data.Generic.Rep module reference
    let rep_mod = {
        let rep_parts: Vec<Symbol> = vec![
            interner::intern("Data"),
            interner::intern("Generic"),
            interner::intern("Rep"),
        ];
        ctx.import_map.get(&rep_parts).cloned()
    };

    let rep_ref = |name: &str| -> JsExpr {
        if let Some(ref js_mod) = rep_mod {
            JsExpr::ModuleAccessor(js_mod.clone(), name.to_string())
        } else {
            JsExpr::Var(name.to_string())
        }
    };

    // `to`: convert generic rep → value
    // For a single constructor with no fields: to(x) = Ctor.value
    // For sum types: to(x) = if (x instanceof Inl) ... else if (x instanceof Inr) ...
    let x = "x".to_string();

    // Build `to` function body
    let mut to_body = Vec::new();
    for (i, (ctor_name, field_count)) in ctors.iter().enumerate() {
        let ctor_expr = if *field_count == 0 {
            JsExpr::Indexer(
                Box::new(JsExpr::Var(ctor_name.clone())),
                Box::new(JsExpr::StringLit("value".to_string())),
            )
        } else if *field_count == 1 {
            // Single-arg ctor: the value is stored directly in the sum node's value0
            let inner = gen_generic_unwrap_arg(&rep_ref, &x, i, ctors.len());
            JsExpr::New(
                Box::new(JsExpr::Var(ctor_name.clone())),
                vec![inner],
            )
        } else {
            // Multi-field: unwrap Product chain
            let mut args = Vec::new();
            let inner = gen_generic_unwrap_arg(&rep_ref, &x, i, ctors.len());
            for fi in 0..*field_count {
                let field = gen_generic_product_field(&rep_ref, &inner, fi, *field_count);
                args.push(field);
            }
            JsExpr::New(Box::new(JsExpr::Var(ctor_name.clone())), args)
        };

        if ctors.len() == 1 {
            to_body.push(JsStmt::Return(ctor_expr));
        } else {
            let cond = gen_generic_inl_inr_check(&rep_ref, &x, i, ctors.len());
            to_body.push(JsStmt::If(cond, vec![JsStmt::Return(ctor_expr)], None));
        }
    }
    if ctors.len() > 1 {
        to_body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    let to_fn = JsExpr::Function(None, vec![x.clone()], to_body);

    // Build `from` function body
    let mut from_body = Vec::new();
    for (i, (ctor_name, field_count)) in ctors.iter().enumerate() {
        let wrap_in_sum = |expr: JsExpr| -> JsExpr {
            gen_generic_inl_inr_wrap(&rep_ref, expr, i, ctors.len())
        };

        let inner = if *field_count == 0 {
            wrap_in_sum(JsExpr::Indexer(
                Box::new(rep_ref("NoArguments")),
                Box::new(JsExpr::StringLit("value".to_string())),
            ))
        } else if *field_count == 1 {
            // Single-arg ctor: Argument is a newtype (identity), so just use the value directly
            wrap_in_sum(JsExpr::Indexer(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::StringLit("value0".to_string())),
            ))
        } else {
            // Multi-field: build Product chain
            // Argument is a newtype (identity), so use field values directly
            let mut product = JsExpr::Indexer(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::StringLit(format!("value{}", field_count - 1))),
            );
            for fi in (0..field_count - 1).rev() {
                product = JsExpr::New(
                    Box::new(rep_ref("Product")),
                    vec![
                        JsExpr::Indexer(
                            Box::new(JsExpr::Var(x.clone())),
                            Box::new(JsExpr::StringLit(format!("value{fi}"))),
                        ),
                        product,
                    ],
                );
            }
            wrap_in_sum(product)
        };

        if ctors.len() == 1 {
            from_body.push(JsStmt::Return(inner));
        } else {
            let cond = JsExpr::InstanceOf(
                Box::new(JsExpr::Var(x.clone())),
                Box::new(JsExpr::Var(ctor_name.clone())),
            );
            from_body.push(JsStmt::If(cond, vec![JsStmt::Return(inner)], None));
        }
    }
    if ctors.len() > 1 {
        from_body.push(JsStmt::Throw(gen_failed_pattern_match(ctx)));
    }

    let from_fn = JsExpr::Function(None, vec![x], from_body);

    vec![
        ("to".to_string(), to_fn),
        ("from".to_string(), from_fn),
    ]
}

/// Generate the condition for checking if x is in the Nth position of an Inl/Inr sum tree.
pub(crate) fn gen_generic_inl_inr_check(rep_ref: &dyn Fn(&str) -> JsExpr, x: &str, idx: usize, total: usize) -> JsExpr {
    if total == 1 {
        return JsExpr::BoolLit(true);
    }
    if total == 2 {
        if idx == 0 {
            return JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inl")));
        } else {
            return JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inr")));
        }
    }
    // For 3+ constructors: navigate idx levels deep into the Inr chain.
    // Sum(A, Sum(B, Sum(C, D))):
    //   A (0): x instanceof Inl
    //   B (1): x instanceof Inr && x.value0 instanceof Inl
    //   C (2): x instanceof Inr && x.value0 instanceof Inr && x.value0.value0 instanceof Inl
    //   D (3): x instanceof Inr && x.value0 instanceof Inr && x.value0.value0 instanceof Inr
    if idx == 0 {
        JsExpr::InstanceOf(Box::new(JsExpr::Var(x.to_string())), Box::new(rep_ref("Inl")))
    } else {
        // Build chain: x instanceof Inr && x.value0 instanceof Inr && ... && x.value0...value0 instanceof Inl/Inr
        let mut expr = JsExpr::InstanceOf(
            Box::new(JsExpr::Var(x.to_string())),
            Box::new(rep_ref("Inr")),
        );
        // Navigate idx-1 levels of .value0 instanceof Inr
        let mut current = JsExpr::Indexer(
            Box::new(JsExpr::Var(x.to_string())),
            Box::new(JsExpr::StringLit("value0".to_string())),
        );
        for _ in 1..idx {
            let check = JsExpr::InstanceOf(
                Box::new(current.clone()),
                Box::new(rep_ref("Inr")),
            );
            expr = JsExpr::Binary(JsBinaryOp::And, Box::new(expr), Box::new(check));
            current = JsExpr::Indexer(
                Box::new(current),
                Box::new(JsExpr::StringLit("value0".to_string())),
            );
        }
        if idx < total - 1 {
            // Middle constructors: final check is Inl
            let final_check = JsExpr::InstanceOf(
                Box::new(current),
                Box::new(rep_ref("Inl")),
            );
            JsExpr::Binary(JsBinaryOp::And, Box::new(expr), Box::new(final_check))
        } else {
            // Last constructor: no extra check needed — being at this Inr depth is sufficient
            expr
        }
    }
}

/// Unwrap the generic arg from the Inl/Inr sum tree at position idx.
/// For Sum(A, Sum(B, Sum(C, D))):
///   A (0): x.value0          (unwrap Inl)
///   B (1): x.value0.value0   (unwrap Inr, then Inl)
///   C (2): x.value0.value0.value0 (unwrap Inr, Inr, then Inl)
///   D (3): x.value0.value0.value0 (unwrap Inr, Inr, then Inr — but last Inr has value0 for its content)
pub(crate) fn gen_generic_unwrap_arg(rep_ref: &dyn Fn(&str) -> JsExpr, x: &str, idx: usize, total: usize) -> JsExpr {
    let _ = rep_ref;
    if total == 1 {
        return JsExpr::Var(x.to_string());
    }
    // For Sum(A, Sum(B, Sum(C, D))):
    //   A (idx=0): x.value0              (1 level)
    //   B (idx=1): x.value0.value0       (2 levels)
    //   C (idx=2): x.value0.value0.value0 (3 levels)
    //   D (idx=3): x.value0.value0.value0 (3 levels — same as C, last shares depth)
    // Non-last: depth = idx + 1. Last: depth = idx.
    let depth = if idx < total - 1 { idx + 1 } else { idx };
    let mut expr = JsExpr::Var(x.to_string());
    for _ in 0..depth {
        expr = JsExpr::Indexer(
            Box::new(expr),
            Box::new(JsExpr::StringLit("value0".to_string())),
        );
    }
    expr
}

/// Extract a field from a Product chain at position fi.
pub(crate) fn gen_generic_product_field(_rep_ref: &dyn Fn(&str) -> JsExpr, inner: &JsExpr, fi: usize, total: usize) -> JsExpr {
    // Argument is a newtype (identity), so Product contains raw values, not Argument objects.
    // Product(a, Product(b, c)) has value0=a, value1=Product(b,c)
    if total == 1 {
        // Single field: inner is the value itself (no Product wrapping)
        inner.clone()
    } else if fi < total - 1 {
        // Navigate Product chain: inner.value0 (first), inner.value1.value0 (second), etc.
        let mut expr = inner.clone();
        for _ in 0..fi {
            expr = JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())));
        }
        JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value0".to_string())))
    } else {
        // Last field: navigate to the end of the product chain
        let mut expr = inner.clone();
        for _ in 0..(fi - 1) {
            expr = JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())));
        }
        JsExpr::Indexer(Box::new(expr), Box::new(JsExpr::StringLit("value1".to_string())))
    }
}

/// Wrap a value in Inl/Inr constructors for the generic sum position.
pub(crate) fn gen_generic_inl_inr_wrap(rep_ref: &dyn Fn(&str) -> JsExpr, inner: JsExpr, idx: usize, total: usize) -> JsExpr {
    if total == 1 {
        return inner;
    }
    // For Sum(A, Sum(B, Sum(C, D))):
    //   A (idx=0): Inl(inner)
    //   B (idx=1): Inr(Inl(inner))
    //   C (idx=2): Inr(Inr(Inl(inner)))
    //   D (idx=3): Inr(Inr(Inr(inner)))
    // Pattern: wrap in Inl for non-last, then wrap in idx Inr's from inside out
    let mut wrapped = if idx < total - 1 {
        JsExpr::New(Box::new(rep_ref("Inl")), vec![inner])
    } else {
        inner
    };
    for _ in 0..idx {
        wrapped = JsExpr::New(Box::new(rep_ref("Inr")), vec![wrapped]);
    }
    wrapped
}
