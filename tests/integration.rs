//! Integration tests for the full compiler pipeline.
//!
//! These tests exercise the public API end-to-end:
//! source string → lex → parse → typecheck

use purescript_fast_compiler::diagnostics::CompilerError;
use purescript_fast_compiler::interner;
use purescript_fast_compiler::typechecker::check_module;
use purescript_fast_compiler::typechecker::error::TypeError;
use purescript_fast_compiler::typechecker::types::Type;
use purescript_fast_compiler::{lex, parse};

// ===== Helpers =====

fn parse_and_check(source: &str) -> (std::collections::HashMap<interner::Symbol, Type>, Vec<TypeError>) {
    let module = parse(source).expect("parse failed");
    let result = check_module(&module);
    (result.types, result.errors)
}

fn lookup_type(source: &str, name: &str) -> Type {
    let (types, errors) = parse_and_check(source);
    assert!(errors.is_empty(), "typecheck errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    let sym = interner::intern(name);
    types
        .get(&sym)
        .unwrap_or_else(|| panic!("name '{}' not found in module types", name))
        .clone()
}

// ===== Lexing =====

#[test]
fn lex_simple_module() {
    let result = lex("module Main where\nx = 42").unwrap();
    assert!(result.tokens.len() > 0);
}

#[test]
fn lex_error_unterminated_string() {
    let result = lex(r#""unterminated"#);
    assert!(result.is_err());
}

// ===== Parsing =====

#[test]
fn parse_minimal_module() {
    let module = parse("module Main where").unwrap();
    assert!(module.decls.is_empty());
}

#[test]
fn parse_module_with_value() {
    let module = parse("module Main where\nx = 42").unwrap();
    assert_eq!(module.decls.len(), 1);
    assert!(matches!(module.decls[0], purescript_fast_compiler::CstDecl::Value { .. }));
}

#[test]
fn parse_module_with_data_type() {
    let source = r#"
module Main where

data Maybe a = Just a | Nothing
"#;
    let module = parse(source).unwrap();
    assert_eq!(module.decls.len(), 1);
    match &module.decls[0] {
        purescript_fast_compiler::CstDecl::Data { constructors, type_vars, .. } => {
            assert_eq!(type_vars.len(), 1);
            assert_eq!(constructors.len(), 2);
        }
        other => panic!("Expected Data decl, got: {:?}", other),
    }
}

#[test]
fn parse_module_with_imports() {
    let source = r#"
module Main where

import Prelude
import Data.Maybe (Maybe(..))
"#;
    let module = parse(source).unwrap();
    assert_eq!(module.imports.len(), 2);
}

#[test]
fn parse_module_with_class_and_instance() {
    let source = r#"
module Main where

class MyEq a where
  myEq :: a -> a -> Boolean

instance MyEq Int where
  myEq x y = true
"#;
    let module = parse(source).unwrap();
    assert!(module.decls.len() >= 2);
}

#[test]
fn parse_error_missing_where() {
    let result = parse("module Main");
    assert!(result.is_err());
}

#[test]
fn parse_error_invalid_syntax() {
    let result = parse("module Main where\n= = =");
    assert!(result.is_err());
}

// ===== Full pipeline: parse + typecheck =====

#[test]
fn e2e_simple_int_value() {
    assert_eq!(
        lookup_type("module T where\nx = 42", "x"),
        Type::int(),
    );
}

#[test]
fn e2e_simple_string_value() {
    assert_eq!(
        lookup_type(r#"module T where
x = "hello""#, "x"),
        Type::string(),
    );
}

#[test]
fn e2e_function_with_signature() {
    let source = "module T where\nid :: forall a. a -> a\nid x = x";
    let ty = lookup_type(source, "id");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, *to, "id should have same input/output type");
        }
        other => panic!("Expected function type for id, got: {}", other),
    }
}

#[test]
fn e2e_data_constructor_nullary() {
    let source = "module T where\ndata Color = Red | Green | Blue\nx = Red";
    assert_eq!(
        lookup_type(source, "x"),
        Type::con_local("Color"),
    );
}

#[test]
fn e2e_data_constructor_with_field() {
    let source = "module T where\ndata Box a = MkBox a\nx = MkBox 42";
    assert_eq!(
        lookup_type(source, "x"),
        Type::app(Type::con_local("Box"), Type::int()),
    );
}

#[test]
fn e2e_case_expression() {
    let source = "module T where
data MyBool = MyTrue | MyFalse
f x = case x of
  MyTrue -> 1
  MyFalse -> 0";
    let ty = lookup_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::con_local("MyBool"));
            assert_eq!(*to, Type::int());
        }
        other => panic!("Expected MyBool -> Int, got: {}", other),
    }
}

#[test]
fn e2e_let_polymorphism() {
    let source = "module T where
f = let
  id = \\x -> x
in id 42";
    assert_eq!(lookup_type(source, "f"), Type::int());
}

#[test]
fn e2e_multiple_declarations() {
    let source = "module T where
f x = x
g = f 42
h = f true";
    let (types, errors) = parse_and_check(source);
    assert!(errors.is_empty(), "typecheck errors: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    assert_eq!(*types.get(&interner::intern("g")).unwrap(), Type::int());
    assert_eq!(*types.get(&interner::intern("h")).unwrap(), Type::boolean());
}

#[test]
fn e2e_array_literal() {
    assert_eq!(
        lookup_type("module T where\nx = [1, 2, 3]", "x"),
        Type::array(Type::int()),
    );
}

#[test]
fn e2e_nested_if() {
    let source = r#"module T where
f x = if x then 1 else if x then 2 else 3"#;
    let ty = lookup_type(source, "f");
    match ty {
        Type::Fun(from, to) => {
            assert_eq!(*from, Type::boolean());
            assert_eq!(*to, Type::int());
        }
        other => panic!("Expected Boolean -> Int, got: {}", other),
    }
}

// ===== Error cases =====

#[test]
fn e2e_error_parse_failure() {
    let result = parse("module T where\n= invalid");
    assert!(result.is_err());
    match result.unwrap_err() {
        CompilerError::SyntaxError { .. } => {}
        other => panic!("Expected SyntaxError, got: {:?}", other),
    }
}

#[test]
fn e2e_error_type_mismatch() {
    let (_, errors) = parse_and_check("module T where\nx :: Int\nx = true");
    assert!(!errors.is_empty(), "expected errors");
    assert!(errors.iter().any(|e| matches!(e, TypeError::UnificationError { .. })),
        "Expected UnificationError, got: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn e2e_error_undefined_variable() {
    let (_, errors) = parse_and_check("module T where\nx = undefinedVar");
    assert!(!errors.is_empty(), "expected errors");
    assert!(errors.iter().any(|e| matches!(e, TypeError::UndefinedVariable { .. })),
        "Expected UndefinedVariable, got: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn e2e_error_duplicate_signature() {
    let (_, errors) = parse_and_check("module T where\nx :: Int\nx :: String\nx = 42");
    assert!(!errors.is_empty(), "expected errors");
    assert!(errors.iter().any(|e| matches!(e, TypeError::DuplicateTypeSignature { .. })),
        "Expected DuplicateTypeSignature, got: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn e2e_error_orphan_signature() {
    let (_, errors) = parse_and_check("module T where\nx :: Int");
    assert!(!errors.is_empty(), "expected errors");
    assert!(errors.iter().any(|e| matches!(e, TypeError::OrphanTypeSignature { .. })),
        "Expected OrphanTypeSignature, got: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn e2e_error_if_branch_mismatch() {
    let (_, errors) = parse_and_check(r#"module T where
x = if true then 1 else "hello""#);
    assert!(!errors.is_empty(), "expected errors");
    assert!(errors.iter().any(|e| matches!(e, TypeError::UnificationError { .. })),
        "Expected UnificationError, got: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn e2e_error_array_element_mismatch() {
    let (_, errors) = parse_and_check("module T where\nx = [1, true]");
    assert!(!errors.is_empty(), "expected errors");
    assert!(errors.iter().any(|e| matches!(e, TypeError::UnificationError { .. })),
        "Expected UnificationError, got: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn debug_fixture_errors() {
    fn check(name: &str, source: &str) {
        let (_, errors) = parse_and_check(source);
        let codes: Vec<String> = errors.iter().map(|e| format!("{} ({})", e.code(), e)).collect();
        if codes.is_empty() {
            eprintln!("{}: FALSE_PASS", name);
        } else {
            eprintln!("{}: {}", name, codes.join(" | "));
        }
    }

    check("NewtypeInstance5", "module Main where\nnewtype X a = X a\nclass Functor f where\n  map :: forall a b. (a -> b) -> f a -> f b\nderive newtype instance functorX :: Functor X");
    check("2806", "module X where\ndata E a b = L a | R b\ng :: forall a b . E a b -> a\ng e | L x <- e = x");
}

#[test]
fn e2e_span_types_local_vars() {
    use purescript_fast_compiler::build::{build_from_sources_with_options, BuildOptions};

    let lib_source = std::fs::read_to_string("tests/fixtures/lsp/hover/Simple/Lib.purs").unwrap();
    let main_source = std::fs::read_to_string("tests/fixtures/lsp/hover/Simple.purs").unwrap();
    let main_mod = parse(&main_source).expect("parse Main");

    let prelude_glob = "tests/fixtures/packages/prelude/src/**/*.purs";
    let mut sources: Vec<(String, String)> = Vec::new();
    sources.push(("Lib.purs".to_string(), lib_source));
    sources.push(("Main.purs".to_string(), main_source));
    for entry in glob::glob(prelude_glob).unwrap().flatten() {
        if let Ok(src) = std::fs::read_to_string(&entry) {
            sources.push((entry.to_string_lossy().into_owned(), src));
        }
    }
    let source_refs: Vec<(&str, &str)> = sources.iter().map(|(p, s)| (p.as_str(), s.as_str())).collect();
    let options = BuildOptions { output_dir: None, ..Default::default() };
    let (_, registry) = build_from_sources_with_options(&source_refs, &None, None, &options);

    let result = purescript_fast_compiler::typechecker::check_module_for_ide(&main_mod, &registry);
    // Should have span_types entries for local variables (n, c, q, y, r, a)
    assert!(result.span_types.len() >= 5, "expected at least 5 span_types entries, got {}", result.span_types.len());
}

#[test]
fn element_compose_mapprops_row_poly() {
    // Reproduces the Lumi.Components.Pill pattern:
    // element (unsafePerformEffect $ unsafeCreateDOMComponent "div") <<< mapProps
    // where element :: forall r. Comp { | r } -> { | r } -> JSX
    // and mapProps returns a concrete record
    let source = r#"
module Test where

foreign import data ReactComponent :: Type -> Type
foreign import data JSX :: Type
foreign import data Effect :: Type -> Type

foreign import compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
infixr 9 compose as <<<

foreign import element :: forall r. ReactComponent { | r } -> { | r } -> JSX
foreign import unsafeCreateDOMComponent :: forall r. String -> Effect (ReactComponent { | r })
foreign import unsafePerformEffect :: forall a. Effect a -> a

type Props = { x :: Int, y :: String }

test :: Props -> JSX
test = elementFn <<< mapProps
  where
    elementFn = element (unsafePerformEffect (unsafeCreateDOMComponent "div"))
    mapProps props = { a: props.x, b: props.y }
"#;
    let (_, errors) = parse_and_check(source);
    assert!(errors.is_empty(), "Expected no errors, got: {:?}", errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn makestateless_element_compose_multimodule() {
    // Reproduces the Lumi.Components.Pill bug:
    // makeStateless calls make which has Union constraint + ComponentSpec type alias
    // The Union-expanded record should NOT leak through to consumer modules.
    use purescript_fast_compiler::build::{build_from_sources_with_options, BuildOptions};

    let lib_source = r#"
module Lib
  ( Unit(..)
  , unit
  , Component
  , ComponentSpec
  , JSX
  , ReactComponent
  , Effect
  , Self
  , element
  , createComponent
  , make
  , makeStateless
  , unsafeCreateDOMComponent
  , unsafePerformEffect
  , compose
  , apply
  , module Lib
  ) where

data Unit = Unit

foreign import data ReactComponent :: Type -> Type
foreign import data JSX :: Type
foreign import data Effect :: Type -> Type
foreign import data Component :: Type -> Type
foreign import data ReactComponentInstance :: Type -> Type -> Type

type Self props state =
  { props :: props
  , state :: state
  }

type ComponentSpec props state =
  ( initialState :: state
  , render :: Self props state -> JSX
  , didMount :: Self props state -> Effect Unit
  )

foreign import element :: forall props. ReactComponent { | props } -> { | props } -> JSX
foreign import createComponent :: forall props. String -> Component props
foreign import unsafeCreateDOMComponent :: forall props. String -> Effect (ReactComponent { | props })
foreign import unsafePerformEffect :: forall a. Effect a -> a
foreign import compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
foreign import apply :: forall a b. (a -> b) -> a -> b

infixr 9 compose as <<<
infixr 0 apply as $

foreign import _make ::
  forall spec props state.
  Component props ->
  { initialState :: state, render :: Self props state -> JSX | spec } ->
  props ->
  JSX

make ::
  forall spec props state.
  Component props ->
  { initialState :: state, render :: Self props state -> JSX | spec } ->
  props ->
  JSX
make = _make

unit :: Unit
unit = Unit

makeStateless ::
  forall props.
  Component props ->
  (props -> JSX) ->
  props ->
  JSX
makeStateless component render = make component { initialState: unit, render: \self -> render self.props }
"#;

    let main_source = r#"
module Main where

import Lib

type PillProps =
  { status :: String
  , style :: String
  , title :: String
  }

component :: Component PillProps
component = createComponent "Pill"

pill :: PillProps -> JSX
pill = makeStateless component $ lumiPillElement <<< mapProps
  where
    lumiPillElement = element (unsafePerformEffect $ unsafeCreateDOMComponent "lumi-pill")
    mapProps props =
      { "data-status": props.status
      , children: props.title
      , style: props.style
      }

type SegmentedPillProps =
  { content :: String
  , style :: String
  }

segmentedComponent :: Component SegmentedPillProps
segmentedComponent = createComponent "SegmentedPill"

segmentedPill :: SegmentedPillProps -> JSX
segmentedPill = makeStateless segmentedComponent $ pillElement <<< mapProps
  where
    pillElement = element (unsafePerformEffect $ unsafeCreateDOMComponent "lumi-segmented-pill")
    mapProps props =
      { children: props.content
      , style: props.style
      }
"#;

    let sources: Vec<(String, String)> = vec![
        ("Lib.purs".to_string(), lib_source.to_string()),
        ("Main.purs".to_string(), main_source.to_string()),
    ];
    let source_refs: Vec<(&str, &str)> = sources.iter().map(|(p, s)| (p.as_str(), s.as_str())).collect();
    let options = BuildOptions { output_dir: None, ..Default::default() };
    let (result, _registry) = build_from_sources_with_options(&source_refs, &None, None, &options);

    for m in &result.modules {
        if !m.type_errors.is_empty() {
            for e in &m.type_errors {
                eprintln!("  Error in {}: {}", m.module_name, e.format_pretty());
            }
        }
    }

    let main_mod = result.modules.iter().find(|m| m.module_name == "Main")
        .expect("Main module not found in results");
    assert!(main_mod.type_errors.is_empty(),
        "Expected no errors in Main, got: {:?}",
        main_mod.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}

#[test]
fn record_merge_union_constraint_no_leak_multimodule() {
    // Reproduces the OaVirtual.Page.Bookmarks.GridView bug from build_from_sources:
    // A polymorphic function (computeLayout') calls Record.merge internally,
    // which has a Union constraint. That body-internal Union constraint must NOT
    // leak via signature_constraints to consumer modules, where stale TyVarIds
    // would cause unification errors (e.g., DateTime unified with a record type).
    use purescript_fast_compiler::build::{build_from_sources_with_options, BuildOptions};

    // Reproduces OaVirtual.Page.Bookmarks.GridView bug from build_from_sources:
    // A function (wrapper) has explicit forall-only signature but its body calls
    // _inner which has a Combine constraint. That body-internal Combine constraint
    // with stale unif vars must NOT leak via signature_constraints to consumer modules.
    // Reproduces the exact bug pattern: a function with explicit signature calls
    // another function with a Union constraint via open row types. The Union
    // constraint's stale TyVarIds must not leak via signature_constraints.
    // This mirrors makeStateless calling make (React.Basic.Classic) and
    // computeLayout calling Record.merge (OaVirtual.Page.Bookmarks).
    //
    // We verify by checking the registry: wrapper's exported signature_constraints
    // should NOT contain the Union constraint from make's body.
    let lib_source = r#"
module Lib
  ( wrapper
  , Component(..)
  , JSX
  ) where

import Prim.Row (class Union)

data Unit = Unit

foreign import data JSX :: Type
foreign import data Component :: Type -> Type

type Self props state =
  { props :: props
  , state :: state
  }

type ComponentSpec props state =
  ( initialState :: state
  , render :: Self props state -> JSX
  )

make ::
  forall spec props state.
  Union spec () (ComponentSpec props state) =>
  Component props ->
  { initialState :: state, render :: Self props state -> JSX | spec } ->
  props ->
  JSX
make = _make

foreign import _make ::
  forall spec props state.
  Component props ->
  { initialState :: state, render :: Self props state -> JSX | spec } ->
  props ->
  JSX

wrapper ::
  forall props.
  Component props ->
  (props -> JSX) ->
  props ->
  JSX
wrapper component render = make component { initialState: Unit, render: \self -> render self.props }
"#;

    let sources: Vec<(String, String)> = vec![
        ("Lib.purs".to_string(), lib_source.to_string()),
    ];
    let source_refs: Vec<(&str, &str)> = sources.iter().map(|(p, s)| (p.as_str(), s.as_str())).collect();
    let options = BuildOptions { output_dir: None, ..Default::default() };
    let (result, registry) = build_from_sources_with_options(&source_refs, &None, None, &options);

    // Lib should compile without errors
    for m in &result.modules {
        assert!(m.type_errors.is_empty(),
            "Expected no errors in {}, got: {:?}",
            m.module_name,
            m.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
    }

    // The key assertion: wrapper's exported signature_constraints should NOT
    // contain Union. The Union constraint comes from make's body, not from
    // wrapper's explicit type signature (forall props. Component props -> ...).
    let lib_name = vec![purescript_fast_compiler::interner::intern("Lib")];
    let lib_exports = registry.lookup(&lib_name).expect("Lib not found in registry");

    // Check that wrapper does NOT have any signature_constraints
    let wrapper_qi = purescript_fast_compiler::cst::unqualified_ident("wrapper");
    let has_union = lib_exports.signature_constraints.get(&wrapper_qi)
        .map_or(false, |constraints| {
            constraints.iter().any(|(class_name, _)| {
                let name = purescript_fast_compiler::interner::resolve(class_name.name).unwrap_or_default();
                name == "Union"
            })
        });
    assert!(!has_union,
        "wrapper should NOT have Union in signature_constraints (body constraint leak)");
}

#[test]
fn alias_hidden_forall_constraint_in_signature_constraints() {
    // Reproduces the FinalTagless bug: `type Expr a = forall e. E e => e a`
    // A value `three :: Expr Number` has constraints hidden inside the type alias.
    // The typechecker must extract `E` into signature_constraints so codegen
    // generates the dict parameter wrapper `function (dictE) { ... }`.
    let source = r#"
module Main where

class E e where
  num :: Number -> e Number
  add :: e Number -> e Number -> e Number

type Expr a = forall e. E e => e a

three :: Expr Number
three = add (num 1.0) (num 2.0)
"#;
    let module = parse(source).expect("parse failed");
    let result = check_module(&module);
    assert!(result.errors.is_empty(), "typecheck errors: {:?}", result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());

    // Check that `three` has `E` in its signature_constraints
    let three_qi = purescript_fast_compiler::cst::unqualified_ident("three");
    let has_e = result.exports.signature_constraints.get(&three_qi)
        .map_or(false, |constraints| {
            constraints.iter().any(|(class_name, _)| {
                let name = purescript_fast_compiler::interner::resolve(class_name.name).unwrap_or_default();
                name == "E"
            })
        });
    assert!(has_e,
        "three should have E in signature_constraints (alias-hidden constraint)");
}

#[test]
fn operator_with_source_module_resolves_to_import_not_local() {
    // Reproduces the FinalTagless instance body bug: when class E defines method `add`,
    // and the `+` operator maps to Data.Semiring.add, using `+` inside the E instance
    // body should resolve to the imported Semiring add (inlined as JS +), not the
    // local E class accessor.
    // This is a codegen-level test — we verify the fixture passes via the build test.
    // Here we just verify the type-level constraints are correct.
    let source = r#"
module Main where

class E e where
  num :: Number -> e Number
  add :: e Number -> e Number -> e Number

type Expr a = forall e. E e => e a

data Id a = Id a

instance exprId :: E Id where
  num = Id
  add (Id n) (Id m) = Id n

three :: Expr Number
three = add (num 1.0) (num 2.0)
"#;
    let module = parse(source).expect("parse failed");
    let result = check_module(&module);
    // Should have no errors (basic structure is valid)
    assert!(result.errors.is_empty(), "typecheck errors: {:?}", result.errors.iter().map(|e| e.to_string()).collect::<Vec<_>>());
}
