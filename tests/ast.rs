use purescript_fast_compiler::ast::{self, Binder, Decl, Expr, Literal, TypeExpr, DefinitionSite};
use purescript_fast_compiler::cst::unqualified_ident;
use purescript_fast_compiler::interner::intern;
use purescript_fast_compiler::parser;
use purescript_fast_compiler::typechecker::error::TypeError;
use purescript_fast_compiler::typechecker::registry::{ModuleExports, ModuleRegistry};
use purescript_fast_compiler::typechecker::types::{Scheme, Type};

fn convert_module(source: &str) -> (ast::Module, Vec<purescript_fast_compiler::typechecker::error::TypeError>) {
    let module = parser::parse(source).expect("parse failed");
    ast::convert(module, &ModuleRegistry::new())
}

fn convert_module_with_registry(source: &str, registry: &ModuleRegistry) -> (ast::Module, Vec<TypeError>) {
    let module = parser::parse(source).expect("parse failed");
    ast::convert(module, registry)
}

/// Build a registry containing a module "Data.Foo" that exports:
/// - values: foo, bar
/// - data type: Baz with constructors MkBaz, NoBaz
/// - class: MyClass (with method myMethod)
fn make_test_registry() -> ModuleRegistry {
    let mut exports = ModuleExports::default();

    // Values
    exports.values.insert(
        unqualified_ident("foo"),
        Scheme::mono(Type::prim_con("Int")),
    );
    exports.values.insert(
        unqualified_ident("bar"),
        Scheme::mono(Type::prim_con("String")),
    );

    // Data constructors for type Baz
    let mk_baz = unqualified_ident("MkBaz");
    let no_baz = unqualified_ident("NoBaz");
    exports.data_constructors.insert(
        unqualified_ident("Baz"),
        vec![mk_baz, no_baz],
    );
    // Constructors are also values
    exports.values.insert(mk_baz, Scheme::mono(Type::prim_con("Baz")));
    exports.values.insert(no_baz, Scheme::mono(Type::prim_con("Baz")));

    // Class
    exports.class_param_counts.insert(unqualified_ident("MyClass"), 1);
    // Class method
    exports.class_methods.insert(
        unqualified_ident("myMethod"),
        (unqualified_ident("MyClass"), vec![unqualified_ident("a")]),
    );
    exports.values.insert(
        unqualified_ident("myMethod"),
        Scheme::mono(Type::prim_con("Int")),
    );

    let mut registry = ModuleRegistry::new();
    registry.register(&[intern("Data"), intern("Foo")], exports);
    registry
}

fn get_value_decl_expr<'a>(module: &'a ast::Module, name: &str) -> &'a Expr {
    let sym = intern(name);
    for decl in &module.decls {
        if let Decl::Value {
            name: n, guarded, ..
        } = decl
        {
            if n.value == sym {
                if let ast::GuardedExpr::Unconditional(expr) = guarded {
                    return expr;
                }
            }
        }
    }
    panic!("value declaration '{}' not found", name);
}

// ===== Paren stripping =====

#[test]
fn test_paren_stripping() {
    let (module, errors) = convert_module("module T where\nf = (42)");
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "f");
    assert!(
        matches!(expr, Expr::Literal { lit: Literal::Int(42), .. }),
        "expected Literal(42), got {:?}",
        expr
    );
}

#[test]
fn test_nested_paren_stripping() {
    let (module, errors) = convert_module("module T where\nf = ((((42))))");
    assert!(errors.is_empty());
    let expr = get_value_decl_expr(&module, "f");
    assert!(matches!(expr, Expr::Literal { lit: Literal::Int(42), .. }));
}

// ===== Operator desugaring =====

#[test]
fn test_value_operator_desugaring() {
    let source = "module T where\ninfixl 6 add as +\nadd a b = a\nx = 1 + 2";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    // Should be App(App(Var(add), 1), 2)
    match expr {
        Expr::App { func, arg, .. } => {
            // arg = 2
            assert!(
                matches!(arg.as_ref(), Expr::Literal { lit: Literal::Int(2), .. }),
                "expected 2 as right arg"
            );
            // func = App(Var(add), 1)
            match func.as_ref() {
                Expr::App { func: inner_func, arg: inner_arg, .. } => {
                    assert!(
                        matches!(inner_arg.as_ref(), Expr::Literal { lit: Literal::Int(1), .. }),
                        "expected 1 as left arg"
                    );
                    // inner_func should be Var(add) — the target function, not the operator symbol
                    match inner_func.as_ref() {
                        Expr::Var { name, .. } => {
                            let name_str = purescript_fast_compiler::interner::resolve(name.name).unwrap_or_default();
                            assert_eq!(name_str, "add", "operator should desugar to target 'add'");
                        }
                        other => panic!("expected Var for operator, got {:?}", other),
                    }
                }
                other => panic!("expected inner App, got {:?}", other),
            }
        }
        other => panic!("expected App(App(...)), got {:?}", other),
    }
}

#[test]
fn test_op_parens_desugaring() {
    let source = "module T where\ninfixl 6 add as +\nadd a b = a\nf = (+)";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "f");
    // (+) should become Var { name: add } — the target function, not the operator symbol
    match expr {
        Expr::Var { name, .. } => {
            let sym = intern("add");
            assert_eq!(name.name, sym, "expected add");
        }
        other => panic!("expected Var for (+), got {:?}", other),
    }
}

// ===== Operator precedence rebalancing =====

#[test]
fn test_operator_precedence_rebalancing() {
    // `1 + 2 * 3` with + at prec 6 and * at prec 7
    // Parser gives right-assoc: Op(1, +, Op(2, *, 3))
    // After rebalancing: App(App(+, 1), App(App(*, 2), 3))
    // i.e. (1 + (2 * 3))
    let source = "module T where\ninfixl 6 add as +\ninfixl 7 mul as *\nadd a b = a\nmul a b = a\nx = 1 + 2 * 3";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    // Top-level: App(App(+, 1), App(App(*, 2), 3))
    match expr {
        Expr::App { func, arg: right, .. } => {
            // right = App(App(*, 2), 3)
            match right.as_ref() {
                Expr::App { func: mul_app, arg: three, .. } => {
                    assert!(matches!(three.as_ref(), Expr::Literal { lit: Literal::Int(3), .. }));
                    match mul_app.as_ref() {
                        Expr::App { arg: two, .. } => {
                            assert!(matches!(two.as_ref(), Expr::Literal { lit: Literal::Int(2), .. }));
                        }
                        other => panic!("expected App(*, 2), got {:?}", other),
                    }
                }
                other => panic!("expected App(App(*, 2), 3), got {:?}", other),
            }
            // func = App(+, 1)
            match func.as_ref() {
                Expr::App { arg: one, .. } => {
                    assert!(matches!(one.as_ref(), Expr::Literal { lit: Literal::Int(1), .. }));
                }
                other => panic!("expected App(+, 1), got {:?}", other),
            }
        }
        other => panic!("expected outer App, got {:?}", other),
    }
}

#[test]
fn test_operator_precedence_reverse() {
    // `1 * 2 + 3` with * at prec 7 and + at prec 6
    // Parser gives: Op(1, *, Op(2, +, 3))
    // After rebalancing with shunting-yard: App(App(+, App(App(*, 1), 2)), 3)
    // i.e. ((1 * 2) + 3)
    let source = "module T where\ninfixl 6 add as +\ninfixl 7 mul as *\nadd a b = a\nmul a b = a\nx = 1 * 2 + 3";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    // Top-level: App(App(+, App(App(*, 1), 2)), 3)
    match expr {
        Expr::App { func, arg: three, .. } => {
            assert!(
                matches!(three.as_ref(), Expr::Literal { lit: Literal::Int(3), .. }),
                "expected 3 as right arg of +"
            );
            match func.as_ref() {
                Expr::App { func: plus_var, arg: mul_expr, .. } => {
                    // plus_var should resolve to add (the target function)
                    match plus_var.as_ref() {
                        Expr::Var { name, .. } => {
                            let s = purescript_fast_compiler::interner::resolve(name.name).unwrap_or_default();
                            assert_eq!(s, "add");
                        }
                        other => panic!("expected Var(add), got {:?}", other),
                    }
                    // mul_expr = App(App(*, 1), 2)
                    match mul_expr.as_ref() {
                        Expr::App { func: mul_app, arg: two, .. } => {
                            assert!(matches!(two.as_ref(), Expr::Literal { lit: Literal::Int(2), .. }));
                            match mul_app.as_ref() {
                                Expr::App { arg: one, .. } => {
                                    assert!(matches!(one.as_ref(), Expr::Literal { lit: Literal::Int(1), .. }));
                                }
                                other => panic!("expected App(*, 1), got {:?}", other),
                            }
                        }
                        other => panic!("expected App(App(*, 1), 2), got {:?}", other),
                    }
                }
                other => panic!("expected App(+, ...), got {:?}", other),
            }
        }
        other => panic!("expected outer App, got {:?}", other),
    }
}

// ===== Type operator desugaring =====

#[test]
fn test_type_operator_desugaring() {
    let source = "module T where\ninfixr 0 type RowApply as +\ndata RowApply\nf :: forall r. Record (x :: Int + r) -> Int\nf x = 42";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    // Find the type signature
    let sym = intern("f");
    let sig = module.decls.iter().find_map(|d| {
        if let Decl::TypeSignature { name, ty, .. } = d {
            if name.value == sym { Some(ty) } else { None }
        } else {
            None
        }
    }).expect("type signature for f not found");
    // The type should contain no TypeOp — it should be desugared to App(App(Constructor(RowApply), ...))
    fn has_no_type_op(ty: &TypeExpr) -> bool {
        match ty {
            TypeExpr::App { constructor, arg, .. } => has_no_type_op(constructor) && has_no_type_op(arg),
            TypeExpr::Function { from, to, .. } => has_no_type_op(from) && has_no_type_op(to),
            TypeExpr::Forall { vars, ty, .. } => {
                vars.iter().all(|(_, _, k)| k.as_ref().map_or(true, |k| has_no_type_op(k))) && has_no_type_op(ty)
            }
            TypeExpr::Constrained { constraints, ty, .. } => {
                constraints.iter().all(|c| c.args.iter().all(has_no_type_op)) && has_no_type_op(ty)
            }
            TypeExpr::Record { fields, .. } => fields.iter().all(|f| has_no_type_op(&f.ty)),
            TypeExpr::Row { fields, tail, .. } => {
                fields.iter().all(|f| has_no_type_op(&f.ty)) && tail.as_ref().map_or(true, |t| has_no_type_op(t))
            }
            TypeExpr::Kinded { ty, kind, .. } => has_no_type_op(ty) && has_no_type_op(kind),
            _ => true,
        }
    }
    assert!(has_no_type_op(sig), "type expression should not contain TypeOp after conversion");
}

// ===== Binder operator desugaring =====

#[test]
fn test_binder_op_becomes_constructor() {
    let source = "module T where\ndata List a = Nil | Cons a (List a)\ninfixr 6 Cons as :\nf x = case x of\n  a : b -> a";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "f");
    // Should be Case with a Binder::Constructor (not Binder::Op)
    match expr {
        Expr::Case { alts, .. } => {
            assert!(!alts.is_empty());
            let binder = &alts[0].binders[0];
            match binder {
                Binder::Constructor { name, args, .. } => {
                    let name_str = purescript_fast_compiler::interner::resolve(name.name).unwrap_or_default();
                    assert_eq!(name_str, "Cons", "binder op should desugar to target 'Cons'");
                    assert_eq!(args.len(), 2);
                }
                other => panic!("expected Binder::Constructor, got {:?}", other),
            }
        }
        other => panic!("expected Case expression, got {:?}", other),
    }
}

// ===== Definition sites =====

#[test]
fn test_local_definition_site() {
    let source = "module T where\nf = 1\ng = f";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "g");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert!(
                matches!(definition_site, DefinitionSite::Local(_)),
                "expected Local definition site for f"
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_lambda_scope_definition_site() {
    let source = "module T where\nf = \\x -> x";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "f");
    match expr {
        Expr::Lambda { body, .. } => match body.as_ref() {
            Expr::Var { definition_site, .. } => {
                assert!(
                    matches!(definition_site, DefinitionSite::Local(_)),
                    "lambda-bound var should have Local definition site"
                );
            }
            other => panic!("expected Var in lambda body, got {:?}", other),
        },
        other => panic!("expected Lambda, got {:?}", other),
    }
}

#[test]
fn test_let_scope_definition_site() {
    let source = "module T where\nf = let\n      y = 1\n    in y";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "f");
    match expr {
        Expr::Let { body, .. } => match body.as_ref() {
            Expr::Var { definition_site, .. } => {
                assert!(matches!(definition_site, DefinitionSite::Local(_)));
            }
            other => panic!("expected Var in let body, got {:?}", other),
        },
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn test_constructor_definition_site() {
    let source = "module T where\ndata Maybe a = Just a | Nothing\nx = Just 1";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::App { func, .. } => match func.as_ref() {
            Expr::Constructor {
                definition_site, ..
            } => {
                assert!(matches!(definition_site, DefinitionSite::Local(_)));
            }
            other => panic!("expected Constructor, got {:?}", other),
        },
        other => panic!("expected App(Constructor, ...), got {:?}", other),
    }
}

// ===== Type expression paren stripping =====

#[test]
fn test_type_paren_stripping() {
    let source = "module T where\nf :: (Int) -> Int\nf x = x";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let sym = intern("f");
    let sig = module.decls.iter().find_map(|d| {
        if let Decl::TypeSignature { name, ty, .. } = d {
            if name.value == sym { Some(ty) } else { None }
        } else {
            None
        }
    }).expect("type signature not found");
    // The `from` of the function type should be Constructor(Int), not Parens
    match sig {
        TypeExpr::Function { from, .. } => {
            assert!(
                matches!(from.as_ref(), TypeExpr::Constructor { .. }),
                "expected Constructor after paren stripping, got {:?}",
                from
            );
        }
        other => panic!("expected Function type, got {:?}", other),
    }
}

// ===== Instance/Derive class definition site =====

#[test]
fn test_instance_class_definition_site() {
    let source = "module T where\nclass MyClass a where\n  foo :: a -> Int\ninstance MyClass Int where\n  foo x = 1";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let instance = module.decls.iter().find_map(|d| {
        if let Decl::Instance { class_definition_site, .. } = d {
            Some(class_definition_site)
        } else {
            None
        }
    }).expect("instance not found");
    assert!(
        matches!(instance, DefinitionSite::Local(_)),
        "class definition site should be Local"
    );
}

// ===== Fixity target definition site =====

#[test]
fn test_fixity_target_definition_site() {
    let source = "module T where\nadd a b = a\ninfixl 6 add as +";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let fixity_site = module.decls.iter().find_map(|d| {
        if let Decl::Fixity { target_definition_site, .. } = d {
            Some(target_definition_site)
        } else {
            None
        }
    }).expect("fixity decl not found");
    assert!(matches!(fixity_site, DefinitionSite::Local(_)));
}

// ===== No panics on various module shapes =====

#[test]
fn test_empty_module() {
    let (module, errors) = convert_module("module T where");
    assert!(errors.is_empty());
    assert!(module.decls.is_empty());
}

#[test]
fn test_do_notation() {
    let source = "module T where\npure x = x\nf = do\n  x <- pure 1\n  pure x";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "f");
    assert!(matches!(expr, Expr::Do { .. }));
}

#[test]
fn test_record_literal() {
    let source = "module T where\nx = { a: 1, b: 2 }";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    assert!(matches!(expr, Expr::Record { .. }));
}

#[test]
fn test_case_expression() {
    let source = "module T where\ndata Bool2 = T2 | F2\nf x = case x of\n  T2 -> 1\n  F2 -> 0";
    let (module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "f");
    assert!(matches!(expr, Expr::Case { .. }));
}

// ===== Error reporting for unresolved names =====

#[test]
fn test_error_undefined_variable() {
    let source = "module T where\nf = unknownVar";
    let (_module, errors) = convert_module(source);
    assert!(
        errors.iter().any(|e| matches!(e, TypeError::UndefinedVariable { .. })),
        "expected UndefinedVariable error, got: {:?}", errors
    );
}

#[test]
fn test_error_undefined_constructor() {
    let source = "module T where\nf = UnknownCtor";
    let (_module, errors) = convert_module(source);
    assert!(
        errors.iter().any(|e| matches!(e, TypeError::UndefinedVariable { .. })),
        "expected UndefinedVariable error for unknown constructor, got: {:?}", errors
    );
}

#[test]
fn test_error_unknown_type_in_signature() {
    let source = "module T where\nf :: UnknownType\nf = 1";
    let (_module, errors) = convert_module(source);
    assert!(
        errors.iter().any(|e| matches!(e, TypeError::UnknownType { .. })),
        "expected UnknownType error, got: {:?}", errors
    );
}

#[test]
fn test_error_unknown_class_in_constraint() {
    let source = "module T where\nf :: UnknownClass a => a -> a\nf x = x";
    let (_module, errors) = convert_module(source);
    assert!(
        errors.iter().any(|e| matches!(e, TypeError::UnknownClass { .. })),
        "expected UnknownClass error, got: {:?}", errors
    );
}

#[test]
fn test_error_unknown_type_operator() {
    let source = "module T where\nf :: Int ~> String\nf = 1";
    let (_module, errors) = convert_module(source);
    assert!(
        errors.iter().any(|e| matches!(e, TypeError::UndefinedVariable { .. })),
        "expected UndefinedVariable error for unknown type operator, got: {:?}", errors
    );
}

#[test]
fn test_no_error_for_known_names() {
    let source = "module T where\ndata Maybe a = Just a | Nothing\nf = Just 1";
    let (_module, errors) = convert_module(source);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
}

// ===== Qualified import definition sites =====

#[test]
fn test_qualified_import_value_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo as F\nx = F.foo";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "qualified value should have Imported definition site"
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_qualified_import_constructor_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo as F\nx = F.MkBaz";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Constructor { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "qualified constructor should have Imported definition site"
            );
        }
        other => panic!("expected Constructor, got {:?}", other),
    }
}

#[test]
fn test_qualified_import_type_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo as F\nf :: F.Baz -> Int\nf x = 42";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let sym = intern("f");
    let sig = module.decls.iter().find_map(|d| {
        if let Decl::TypeSignature { name, ty, .. } = d {
            if name.value == sym { Some(ty) } else { None }
        } else {
            None
        }
    }).expect("type signature for f not found");
    // The `from` of the Function type should be Constructor with Imported site
    match sig {
        TypeExpr::Function { from, .. } => match from.as_ref() {
            TypeExpr::Constructor { definition_site, .. } => {
                assert_eq!(
                    *definition_site,
                    DefinitionSite::Imported { module: intern("Data.Foo") },
                    "qualified type should have Imported definition site"
                );
            }
            other => panic!("expected Constructor type, got {:?}", other),
        },
        other => panic!("expected Function type, got {:?}", other),
    }
}

#[test]
fn test_qualified_import_class_in_constraint_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo as F\nf :: F.MyClass a => a -> a\nf x = x";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let sym = intern("f");
    let sig = module.decls.iter().find_map(|d| {
        if let Decl::TypeSignature { name, ty, .. } = d {
            if name.value == sym { Some(ty) } else { None }
        } else {
            None
        }
    }).expect("type signature for f not found");
    // Should be Constrained with Imported definition site on the constraint
    match sig {
        TypeExpr::Constrained { constraints, .. } => {
            assert!(!constraints.is_empty(), "expected at least one constraint");
            assert_eq!(
                constraints[0].definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "qualified class constraint should have Imported definition site"
            );
        }
        other => panic!("expected Constrained type, got {:?}", other),
    }
}

#[test]
fn test_unqualified_import_value_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo\nx = foo";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "unqualified imported value should have Imported definition site"
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_unqualified_import_constructor_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo\nx = MkBaz";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Constructor { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "unqualified imported constructor should have Imported definition site"
            );
        }
        other => panic!("expected Constructor, got {:?}", other),
    }
}

#[test]
fn test_qualified_import_undefined_value_error() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo as F\nx = F.nonexistent";
    let (_module, errors) = convert_module_with_registry(source, &registry);
    assert!(
        errors.iter().any(|e| matches!(e, TypeError::UndefinedVariable { .. })),
        "expected UndefinedVariable error for F.nonexistent, got: {:?}", errors
    );
}

#[test]
fn test_qualified_import_class_method_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo as F\nx = F.myMethod";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "qualified class method should have Imported definition site"
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_explicit_import_value_definition_site() {
    let registry = make_test_registry();
    let source = "module T where\nimport Data.Foo (foo)\nx = foo";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "explicitly imported value should have Imported definition site"
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_hiding_import_definition_site() {
    let registry = make_test_registry();
    // Import everything except bar; foo should still be available
    let source = "module T where\nimport Data.Foo hiding (bar)\nx = foo";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_local_shadows_import_definition_site() {
    let registry = make_test_registry();
    // Local definition of `foo` should shadow the import
    let source = "module T where\nimport Data.Foo\nfoo = 42\nx = foo";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert!(
                matches!(definition_site, DefinitionSite::Local(_)),
                "local definition should shadow import, got {:?}",
                definition_site
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_qualified_bypasses_local_shadow() {
    let registry = make_test_registry();
    // Local `foo` shadows unqualified import, but F.foo should still resolve to import
    let source = "module T where\nimport Data.Foo as F\nfoo = 42\nx = F.foo";
    let (module, errors) = convert_module_with_registry(source, &registry);
    assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
    let expr = get_value_decl_expr(&module, "x");
    match expr {
        Expr::Var { definition_site, .. } => {
            assert_eq!(
                *definition_site,
                DefinitionSite::Imported { module: intern("Data.Foo") },
                "qualified reference should bypass local shadow"
            );
        }
        other => panic!("expected Var, got {:?}", other),
    }
}

#[test]
fn test_module_not_found_error() {
    let registry = ModuleRegistry::new();
    let source = "module T where\nimport Data.Unknown\nx = 1";
    let (_module, errors) = convert_module_with_registry(source, &registry);
    assert!(
        errors.iter().any(|e| matches!(e, TypeError::ModuleNotFound { .. })),
        "expected ModuleNotFound error, got: {:?}", errors
    );
}
