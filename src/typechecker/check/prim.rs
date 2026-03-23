use crate::interner::intern;
use crate::names::{self, TypeVarName};
use crate::typechecker::registry::ModuleExports;

// Build the exports for the built-in Prim module.
// Prim provides core types (Int, Number, String, Char, Boolean, Array, Function, Record)
// and is implicitly imported unqualified in every module.
static PRIM_EXPORTS: std::sync::LazyLock<ModuleExports> =
    std::sync::LazyLock::new(prim_exports_inner);

pub fn prim_exports() -> &'static ModuleExports {
    &PRIM_EXPORTS
}

fn prim_exports_inner() -> ModuleExports {
    let mut exports = ModuleExports::default();

    // Register Prim types as known types (empty constructor lists since they're opaque).
    // This makes them findable by the import system (import_item looks up data_constructors).
    // Exports use unqualified keys (like all module exports); import processing
    // adds qualification as needed.
    // Core value types
    for name in &[
        "Int", "Number", "String", "Char", "Boolean", "Array", "Function", "Record", "->",
    ] {
        exports.data_constructors.insert(names::unqualified_type(name), Vec::new());
    }

    // Kind types: Type, Constraint, Symbol, Row
    for name in &["Type", "Constraint", "Symbol", "Row"] {
        exports.data_constructors.insert(names::unqualified_type(name), Vec::new());
    }

    // Type constructor arities for Prim types
    exports.type_con_arities.insert(names::unqualified_type("Int"), 0);
    exports.type_con_arities.insert(names::unqualified_type("Number"), 0);
    exports.type_con_arities.insert(names::unqualified_type("String"), 0);
    exports.type_con_arities.insert(names::unqualified_type("Char"), 0);
    exports.type_con_arities.insert(names::unqualified_type("Boolean"), 0);
    exports.type_con_arities.insert(names::unqualified_type("Array"), 1);
    exports.type_con_arities.insert(names::unqualified_type("Record"), 1);
    exports.type_con_arities.insert(names::unqualified_type("Function"), 2);
    exports.type_con_arities.insert(names::unqualified_type("Type"), 0);
    exports.type_con_arities.insert(names::unqualified_type("Constraint"), 0);
    exports.type_con_arities.insert(names::unqualified_type("Symbol"), 0);
    exports.type_con_arities.insert(names::unqualified_type("Row"), 1);

    // class Partial
    exports.instances.insert(names::unqualified_class("Partial"), Vec::new());
    exports.class_param_counts.insert(names::unqualified_class("Partial"), 0);

    // class IsSymbol (sym :: Symbol) — compiler-solved class for type-level symbols
    exports.instances.insert(names::unqualified_class("IsSymbol"), Vec::new());
    exports.class_param_counts.insert(names::unqualified_class("IsSymbol"), 1);

    exports
}

/// Check if a CST ModuleName matches "Prim".
pub(super) fn is_prim_module(module_name: &crate::cst::ModuleName) -> bool {
    module_name.parts.len() == 1
        && crate::interner::symbol_eq(module_name.parts[0], "Prim")
}

/// Check if a CST ModuleName is a Prim submodule (e.g. Prim.Coerce, Prim.Row).
pub(super) fn is_prim_submodule(module_name: &crate::cst::ModuleName) -> bool {
    module_name.parts.len() >= 2
        && crate::interner::symbol_eq(module_name.parts[0], "Prim")
}

/// Build exports for Prim submodules (Prim.Coerce, Prim.Row, Prim.RowList, etc.).
/// These are built-in modules with compiler-magic classes and types.
pub fn prim_submodule_exports(module_name: &crate::cst::ModuleName) -> ModuleExports {
    let mut exports = ModuleExports::default();

    let sub = if module_name.parts.len() >= 2 {
        crate::interner::resolve(module_name.parts[1]).unwrap_or_default()
    } else {
        return exports;
    };

    // Exports use unqualified keys (like all module exports); import processing
    // adds qualification as needed.
    match sub.as_str() {
        "Boolean" => {
            // Type-level booleans: True, False
            exports.data_constructors.insert(names::unqualified_type("True"), Vec::new());
            exports
                .data_constructors
                .insert(names::unqualified_type("False"), Vec::new());
        }
        "Coerce" => {
            // class Coercible (no user-visible methods)
            exports.instances.insert(names::unqualified_class("Coercible"), Vec::new());
            exports.class_param_counts.insert(names::unqualified_class("Coercible"), 2);
            // Coercible :: forall k. k -> k -> Constraint
            use crate::typechecker::types::Type as CoerceType;
            let k_var = TypeVarName::new(intern("k"));
            let k = CoerceType::Var(k_var);
            let cc = CoerceType::kind_constraint();
            exports.class_type_kinds.insert(names::class_name("Coercible"),
                CoerceType::Forall(vec![(k_var, false)], Box::new(
                    CoerceType::fun(k.clone(), CoerceType::fun(k, cc))
                )));
        }
        "Int" => {
            // Compiler-solved type classes for type-level Ints
            // class Add (3), class Compare (3), class Mul (3), class ToString (2)
            for class in &["Add", "Compare", "Mul"] {
                exports.instances.insert(names::unqualified_class(class), Vec::new());
                exports.class_param_counts.insert(names::unqualified_class(class), 3);
            }
            exports.instances.insert(names::unqualified_class("ToString"), Vec::new());
            exports.class_param_counts.insert(names::unqualified_class("ToString"), 2);
        }
        "Ordering" => {
            // type Ordering with constructors LT, EQ, GT
            exports.data_constructors.insert(
                names::unqualified_type("Ordering"),
                vec![names::unqualified_ctor("LT"), names::unqualified_ctor("EQ"), names::unqualified_ctor("GT")],
            );
            exports.data_constructors.insert(names::unqualified_type("LT"), Vec::new());
            exports.data_constructors.insert(names::unqualified_type("EQ"), Vec::new());
            exports.data_constructors.insert(names::unqualified_type("GT"), Vec::new());
        }
        "Row" => {
            // classes: Lacks, Cons, Nub, Union
            for class in &["Lacks", "Cons", "Nub", "Union"] {
                exports.instances.insert(names::unqualified_class(class), Vec::new());
            }
            exports.class_param_counts.insert(names::unqualified_class("Lacks"), 2);
            exports.class_param_counts.insert(names::unqualified_class("Cons"), 4);
            exports.class_param_counts.insert(names::unqualified_class("Nub"), 2);
            exports.class_param_counts.insert(names::unqualified_class("Union"), 3);

            // Export class kinds so they can be registered in class_kinds on import,
            // preventing collisions with data types of the same name.
            use crate::typechecker::types::Type;
            let _k_type = Type::kind_type();
            let k_constraint = Type::kind_constraint();
            let k_symbol = Type::kind_symbol();
            let k_var = TypeVarName::new(intern("k"));
            let k_row_k = Type::kind_row_of(Type::Var(k_var));

            // Union :: forall k. Row k -> Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(names::class_name("Union"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), k_constraint.clone())))
                )));
            // Nub :: forall k. Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(names::class_name("Nub"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), k_constraint.clone()))
                )));
            // Lacks :: forall k. Symbol -> Row k -> Constraint
            exports.class_type_kinds.insert(names::class_name("Lacks"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_symbol, Type::fun(k_row_k.clone(), k_constraint.clone()))
                )));
            // Cons :: forall k. Symbol -> k -> Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(names::class_name("Cons"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(Type::kind_symbol(), Type::fun(Type::Var(k_var),
                        Type::fun(k_row_k.clone(), Type::fun(k_row_k, k_constraint))))
                )));
        }
        "RowList" => {
            // type RowList with constructors Cons, Nil; class RowToList
            exports
                .data_constructors
                .insert(names::unqualified_type("RowList"), vec![names::unqualified_ctor("Cons"), names::unqualified_ctor("Nil")]);
            exports.data_constructors.insert(names::unqualified_type("Cons"), Vec::new());
            exports.data_constructors.insert(names::unqualified_type("Nil"), Vec::new());
            exports.instances.insert(names::unqualified_class("RowToList"), Vec::new());
            exports.class_param_counts.insert(names::unqualified_class("RowToList"), 2);
        }
        "Symbol" => {
            // classes: Append, Compare, Cons
            for class in &["Append", "Compare", "Cons"] {
                exports.instances.insert(names::unqualified_class(class), Vec::new());
            }
            exports.class_param_counts.insert(names::unqualified_class("Append"), 3);
            exports.class_param_counts.insert(names::unqualified_class("Compare"), 3);
            exports.class_param_counts.insert(names::unqualified_class("Cons"), 3);
        }
        "TypeError" => {
            // classes: Fail, Warn; type constructors: Text, Beside, Above, Quote, QuoteLabel
            for class in &["Fail", "Warn"] {
                exports.instances.insert(names::unqualified_class(class), Vec::new());
            }
            exports.class_param_counts.insert(names::unqualified_class("Fail"), 1);
            exports.class_param_counts.insert(names::unqualified_class("Warn"), 1);
            for ty in &["Doc", "Text", "Beside", "Above", "Quote", "QuoteLabel"] {
                exports.data_constructors.insert(names::unqualified_type(ty), Vec::new());
            }
        }
        _ => {
            // Unknown Prim submodule — return empty exports
        }
    }

    exports
}
