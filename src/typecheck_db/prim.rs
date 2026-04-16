//! Built-in `Prim` and `Prim.*` module exports.
//!
//! These are the compiler-baked surfaces every user module
//! implicitly `import Prim`s (unqualified). Content mirrors the
//! legacy checker's
//! [`src/typechecker/check/prim.rs`](src/typechecker/check/prim.rs);
//! shape is the new-typechecker [`ModuleExports`].
//!
//! Scope covered here:
//! * Core value + kind types (Int, Number, String, Char, Boolean,
//!   Array, Function, Record; Type, Constraint, Symbol, Row) and
//!   their arities.
//! * Compiler-magic classes, complete with their functional
//!   dependencies (important: the solver's improvement rules rely
//!   on these matching reality):
//!   - `Prim` — Partial, IsSymbol
//!   - `Prim.Coerce` — Coercible
//!   - `Prim.Int` — Add, Compare, Mul, ToString
//!   - `Prim.Row` — Lacks, Cons, Nub, Union
//!   - `Prim.RowList` — RowToList
//!   - `Prim.Symbol` — Append, Compare, Cons
//!   - `Prim.TypeError` — Fail, Warn
//! * Kind-level `Boolean`, `Ordering`, `RowList` types and their
//!   type-level constructors (True/False, LT/EQ/GT, Cons/Nil, and
//!   the `TypeError` doc-tree constructors).

use std::collections::HashMap;

use crate::typecheck_db::module_registry::ModuleExports;
use crate::typecheck_db::passes::exhaustiveness::CtorInfo;
use crate::typecheck_db::passes::instance_index::{ClassInfo, FunDep};

/// Build every Prim[.*] module's exports and return them keyed by
/// canonical module name. Called once when a `ModuleRegistry` is
/// constructed; every user module imports the unqualified `Prim`
/// entry implicitly.
pub fn prim_exports() -> HashMap<String, ModuleExports> {
    let mut out: HashMap<String, ModuleExports> = HashMap::new();
    out.insert("Prim".into(), prim_main());
    out.insert("Prim.Boolean".into(), prim_boolean());
    out.insert("Prim.Coerce".into(), prim_coerce());
    out.insert("Prim.Int".into(), prim_int());
    out.insert("Prim.Ordering".into(), prim_ordering());
    out.insert("Prim.Row".into(), prim_row());
    out.insert("Prim.RowList".into(), prim_rowlist());
    out.insert("Prim.Symbol".into(), prim_symbol());
    out.insert("Prim.TypeError".into(), prim_typeerror());
    out
}

/// Convenience: is `name` one of the Prim[.*] module paths?
pub fn is_prim_module_name(name: &str) -> bool {
    name == "Prim" || name.starts_with("Prim.")
}

// ---------------------------------------------------------------------------
// Module builders
// ---------------------------------------------------------------------------

fn prim_main() -> ModuleExports {
    let mut e = ModuleExports::default();

    // Core value types.
    for (name, arity) in [
        ("Int", 0),
        ("Number", 0),
        ("String", 0),
        ("Char", 0),
        ("Boolean", 0),
        ("Array", 1),
        ("Record", 1),
        ("Function", 2),
    ] {
        e.type_arities.insert(name.into(), arity);
    }
    // Kind types — appear in type_arities so import machinery
    // sees them as known names.
    for (name, arity) in [("Type", 0), ("Constraint", 0), ("Symbol", 0), ("Row", 1)] {
        e.type_arities.insert(name.into(), arity);
    }

    // Magic classes.
    e.classes.insert(
        "Partial".into(),
        ClassInfo { type_vars: vec![], fundeps: vec![] },
    );
    e.classes.insert(
        "IsSymbol".into(),
        ClassInfo { type_vars: vec!["sym".into()], fundeps: vec![] },
    );

    e
}

fn prim_boolean() -> ModuleExports {
    let mut e = ModuleExports::default();
    // Type-level True / False. Exposed as 0-arity types so the
    // importer sees them as known names.
    for t in ["True", "False"] {
        e.type_arities.insert(t.into(), 0);
    }
    e
}

fn prim_coerce() -> ModuleExports {
    let mut e = ModuleExports::default();
    // class Coercible a b — two-parameter, no fundeps. Role-based
    // solving lives in the Coercible phase; Phase B treats this
    // as a regular class.
    e.classes.insert(
        "Coercible".into(),
        ClassInfo {
            type_vars: vec!["a".into(), "b".into()],
            fundeps: vec![],
        },
    );
    e
}

fn prim_int() -> ModuleExports {
    let mut e = ModuleExports::default();
    // Type-level Int arithmetic classes. Fundeps as in the
    // upstream Prim.Int: each arithmetic class has three params
    // with mutual determinism.
    //
    // class Add (l :: Int) (r :: Int) (sum :: Int)
    //    | l r -> sum, sum l -> r, sum r -> l
    // class Mul …, class Compare … (only l r -> ordering),
    // class ToString (i :: Int) (sym :: Symbol) | i -> sym.
    for (name, vars, fundeps) in [
        (
            "Add",
            vec!["l", "r", "sum"],
            vec![(vec![0, 1], vec![2]), (vec![2, 0], vec![1]), (vec![2, 1], vec![0])],
        ),
        (
            "Mul",
            vec!["l", "r", "product"],
            vec![(vec![0, 1], vec![2]), (vec![2, 0], vec![1]), (vec![2, 1], vec![0])],
        ),
        (
            "Compare",
            vec!["l", "r", "ordering"],
            vec![(vec![0, 1], vec![2])],
        ),
    ] {
        e.classes.insert(
            name.into(),
            ClassInfo {
                type_vars: vars.iter().map(|s| (*s).to_string()).collect(),
                fundeps: fundeps
                    .into_iter()
                    .map(|(d, dd)| FunDep { determiners: d, determined: dd })
                    .collect(),
            },
        );
    }
    e.classes.insert(
        "ToString".into(),
        ClassInfo {
            type_vars: vec!["i".into(), "sym".into()],
            fundeps: vec![FunDep { determiners: vec![0], determined: vec![1] }],
        },
    );
    e
}

fn prim_ordering() -> ModuleExports {
    let mut e = ModuleExports::default();
    // type Ordering with constructors LT, EQ, GT. Kind-level
    // type; expose as type + ctor names.
    e.type_arities.insert("Ordering".into(), 0);
    e.data_constructors.insert(
        "Ordering".into(),
        vec!["LT".into(), "EQ".into(), "GT".into()],
    );
    for ctor in ["LT", "EQ", "GT"] {
        e.ctors.insert(
            ctor.into(),
            CtorInfo {
                parent_type: "Ordering".into(),
                type_vars: vec![],
                fields: vec![],
            },
        );
    }
    e
}

fn prim_row() -> ModuleExports {
    let mut e = ModuleExports::default();
    // class Lacks (label :: Symbol) (row :: Row k) — two params,
    // no fundep in legacy Prim.
    e.classes.insert(
        "Lacks".into(),
        ClassInfo {
            type_vars: vec!["label".into(), "row".into()],
            fundeps: vec![],
        },
    );
    // class Cons label a tail row
    //   | label a tail -> row, label row -> a tail
    e.classes.insert(
        "Cons".into(),
        ClassInfo {
            type_vars: vec!["label".into(), "a".into(), "tail".into(), "row".into()],
            fundeps: vec![
                FunDep { determiners: vec![0, 1, 2], determined: vec![3] },
                FunDep { determiners: vec![0, 3], determined: vec![1, 2] },
            ],
        },
    );
    // class Nub orig nubbed | orig -> nubbed
    e.classes.insert(
        "Nub".into(),
        ClassInfo {
            type_vars: vec!["original".into(), "nubbed".into()],
            fundeps: vec![FunDep { determiners: vec![0], determined: vec![1] }],
        },
    );
    // class Union left right union
    //   | left right -> union, left union -> right, right union -> left
    e.classes.insert(
        "Union".into(),
        ClassInfo {
            type_vars: vec!["left".into(), "right".into(), "union".into()],
            fundeps: vec![
                FunDep { determiners: vec![0, 1], determined: vec![2] },
                FunDep { determiners: vec![0, 2], determined: vec![1] },
                FunDep { determiners: vec![1, 2], determined: vec![0] },
            ],
        },
    );
    e
}

fn prim_rowlist() -> ModuleExports {
    let mut e = ModuleExports::default();
    // type RowList k :: Type — represented as arity-1 type.
    e.type_arities.insert("RowList".into(), 1);
    // Type-level constructors Cons, Nil on RowList.
    e.data_constructors.insert(
        "RowList".into(),
        vec!["Cons".into(), "Nil".into()],
    );
    e.ctors.insert(
        "Nil".into(),
        CtorInfo { parent_type: "RowList".into(), type_vars: vec!["k".into()], fields: vec![] },
    );
    e.ctors.insert(
        "Cons".into(),
        CtorInfo {
            parent_type: "RowList".into(),
            type_vars: vec!["k".into()],
            fields: vec![],
        },
    );
    // class RowToList row list | row -> list
    e.classes.insert(
        "RowToList".into(),
        ClassInfo {
            type_vars: vec!["row".into(), "list".into()],
            fundeps: vec![FunDep { determiners: vec![0], determined: vec![1] }],
        },
    );
    e
}

fn prim_symbol() -> ModuleExports {
    let mut e = ModuleExports::default();
    // class Append l r result | l r -> result, r result -> l, l result -> r
    e.classes.insert(
        "Append".into(),
        ClassInfo {
            type_vars: vec!["left".into(), "right".into(), "result".into()],
            fundeps: vec![
                FunDep { determiners: vec![0, 1], determined: vec![2] },
                FunDep { determiners: vec![1, 2], determined: vec![0] },
                FunDep { determiners: vec![0, 2], determined: vec![1] },
            ],
        },
    );
    // class Compare l r ordering | l r -> ordering
    e.classes.insert(
        "Compare".into(),
        ClassInfo {
            type_vars: vec!["left".into(), "right".into(), "ordering".into()],
            fundeps: vec![FunDep { determiners: vec![0, 1], determined: vec![2] }],
        },
    );
    // class Cons head tail sym | head tail -> sym, sym -> head tail
    e.classes.insert(
        "Cons".into(),
        ClassInfo {
            type_vars: vec!["head".into(), "tail".into(), "sym".into()],
            fundeps: vec![
                FunDep { determiners: vec![0, 1], determined: vec![2] },
                FunDep { determiners: vec![2], determined: vec![0, 1] },
            ],
        },
    );
    e
}

fn prim_typeerror() -> ModuleExports {
    let mut e = ModuleExports::default();
    // class Fail (doc :: Doc) — fails compilation with a doc.
    e.classes.insert(
        "Fail".into(),
        ClassInfo { type_vars: vec!["doc".into()], fundeps: vec![] },
    );
    // class Warn (doc :: Doc) — compiles but warns.
    e.classes.insert(
        "Warn".into(),
        ClassInfo { type_vars: vec!["doc".into()], fundeps: vec![] },
    );
    // Doc type + constructors. No fields — these are used at
    // type level and never constructed at value level.
    for name in ["Doc", "Text", "Beside", "Above", "Quote", "QuoteLabel"] {
        e.type_arities.insert(name.into(), 0);
    }
    e
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_prim_submodules_present() {
        let e = prim_exports();
        for name in [
            "Prim",
            "Prim.Boolean",
            "Prim.Coerce",
            "Prim.Int",
            "Prim.Ordering",
            "Prim.Row",
            "Prim.RowList",
            "Prim.Symbol",
            "Prim.TypeError",
        ] {
            assert!(e.contains_key(name), "missing {name}");
        }
    }

    #[test]
    fn is_prim_module_name_matches_main_and_submodules() {
        assert!(is_prim_module_name("Prim"));
        assert!(is_prim_module_name("Prim.Row"));
        assert!(is_prim_module_name("Prim.Int"));
        assert!(!is_prim_module_name("Data.Maybe"));
        assert!(!is_prim_module_name("Primitive"));
    }

    #[test]
    fn prim_main_has_core_value_types() {
        let e = &prim_exports()["Prim"];
        for name in ["Int", "Number", "String", "Char", "Boolean", "Array", "Record", "Function"] {
            assert!(e.type_arities.contains_key(name), "missing {name}");
        }
    }

    #[test]
    fn prim_main_function_arity_is_two() {
        let e = &prim_exports()["Prim"];
        assert_eq!(e.type_arities["Function"], 2);
        assert_eq!(e.type_arities["Array"], 1);
        assert_eq!(e.type_arities["Int"], 0);
    }

    #[test]
    fn prim_main_exposes_partial_and_is_symbol() {
        let e = &prim_exports()["Prim"];
        assert!(e.classes.contains_key("Partial"));
        assert_eq!(e.classes["Partial"].type_vars.len(), 0);
        assert!(e.classes.contains_key("IsSymbol"));
        assert_eq!(e.classes["IsSymbol"].type_vars.len(), 1);
    }

    #[test]
    fn prim_coerce_exposes_coercible() {
        let e = &prim_exports()["Prim.Coerce"];
        assert!(e.classes.contains_key("Coercible"));
        assert_eq!(e.classes["Coercible"].type_vars.len(), 2);
    }

    #[test]
    fn prim_int_add_has_bidirectional_fundeps() {
        let e = &prim_exports()["Prim.Int"];
        let add = &e.classes["Add"];
        assert_eq!(add.type_vars, vec!["l".to_string(), "r".into(), "sum".into()]);
        // Expect three fundeps covering every two-arg determiner
        // pair.
        assert_eq!(add.fundeps.len(), 3);
    }

    #[test]
    fn prim_row_cons_has_correct_fundeps() {
        let e = &prim_exports()["Prim.Row"];
        let cons = &e.classes["Cons"];
        assert_eq!(cons.type_vars.len(), 4);
        // label a tail -> row, label row -> a tail
        assert_eq!(cons.fundeps.len(), 2);
        assert_eq!(cons.fundeps[0].determiners, vec![0, 1, 2]);
        assert_eq!(cons.fundeps[0].determined, vec![3]);
        assert_eq!(cons.fundeps[1].determiners, vec![0, 3]);
        assert_eq!(cons.fundeps[1].determined, vec![1, 2]);
    }

    #[test]
    fn prim_row_union_has_three_fundeps() {
        let e = &prim_exports()["Prim.Row"];
        let union = &e.classes["Union"];
        assert_eq!(union.fundeps.len(), 3);
    }

    #[test]
    fn prim_row_nub_and_lacks() {
        let e = &prim_exports()["Prim.Row"];
        assert_eq!(e.classes["Nub"].type_vars.len(), 2);
        assert_eq!(e.classes["Nub"].fundeps.len(), 1);
        assert_eq!(e.classes["Lacks"].type_vars.len(), 2);
        assert!(e.classes["Lacks"].fundeps.is_empty());
    }

    #[test]
    fn prim_ordering_has_lt_eq_gt() {
        let e = &prim_exports()["Prim.Ordering"];
        assert_eq!(
            e.data_constructors["Ordering"],
            vec!["LT".to_string(), "EQ".into(), "GT".into()],
        );
        assert!(e.ctors.contains_key("LT"));
        assert!(e.ctors.contains_key("EQ"));
        assert!(e.ctors.contains_key("GT"));
    }

    #[test]
    fn prim_rowlist_has_row_to_list_class() {
        let e = &prim_exports()["Prim.RowList"];
        assert!(e.classes.contains_key("RowToList"));
        assert_eq!(e.classes["RowToList"].fundeps.len(), 1);
    }

    #[test]
    fn prim_symbol_cons_has_bidirectional_fundeps() {
        let e = &prim_exports()["Prim.Symbol"];
        let cons = &e.classes["Cons"];
        assert_eq!(cons.type_vars.len(), 3);
        assert_eq!(cons.fundeps.len(), 2);
    }

    #[test]
    fn prim_typeerror_has_fail_and_warn() {
        let e = &prim_exports()["Prim.TypeError"];
        assert!(e.classes.contains_key("Fail"));
        assert!(e.classes.contains_key("Warn"));
        for t in ["Doc", "Text", "Beside", "Above", "Quote", "QuoteLabel"] {
            assert!(e.type_arities.contains_key(t), "missing {t}");
        }
    }

    #[test]
    fn prim_boolean_exposes_true_false_types() {
        let e = &prim_exports()["Prim.Boolean"];
        assert!(e.type_arities.contains_key("True"));
        assert!(e.type_arities.contains_key("False"));
    }

    #[test]
    fn prim_exports_have_no_instances() {
        // Prim classes are compiler-magic; no runtime instances.
        for (name, exp) in prim_exports() {
            assert!(
                exp.instances.is_empty(),
                "{name} unexpectedly has instances",
            );
        }
    }
}
