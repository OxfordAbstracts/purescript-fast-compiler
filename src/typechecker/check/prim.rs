use crate::cst::unqualified_ident;
use crate::interner::intern;
use crate::names::TypeVarName;
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
        exports.data_constructors.insert(unqualified_ident(name), Vec::new());
    }

    // Kind types: Type, Constraint, Symbol, Row
    for name in &["Type", "Constraint", "Symbol", "Row"] {
        exports.data_constructors.insert(unqualified_ident(name), Vec::new());
    }

    // Type constructor arities for Prim types
    exports.type_con_arities.insert(unqualified_ident("Int"), 0);
    exports.type_con_arities.insert(unqualified_ident("Number"), 0);
    exports.type_con_arities.insert(unqualified_ident("String"), 0);
    exports.type_con_arities.insert(unqualified_ident("Char"), 0);
    exports.type_con_arities.insert(unqualified_ident("Boolean"), 0);
    exports.type_con_arities.insert(unqualified_ident("Array"), 1);
    exports.type_con_arities.insert(unqualified_ident("Record"), 1);
    exports.type_con_arities.insert(unqualified_ident("Function"), 2);
    exports.type_con_arities.insert(unqualified_ident("Type"), 0);
    exports.type_con_arities.insert(unqualified_ident("Constraint"), 0);
    exports.type_con_arities.insert(unqualified_ident("Symbol"), 0);
    exports.type_con_arities.insert(unqualified_ident("Row"), 1);

    // class Partial
    exports.instances.insert(unqualified_ident("Partial"), Vec::new());
    exports.class_param_counts.insert(unqualified_ident("Partial"), 0);

    // class IsSymbol (sym :: Symbol) — compiler-solved class for type-level symbols
    exports.instances.insert(unqualified_ident("IsSymbol"), Vec::new());
    exports.class_param_counts.insert(unqualified_ident("IsSymbol"), 1);

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
            exports.data_constructors.insert(unqualified_ident("True"), Vec::new());
            exports
                .data_constructors
                .insert(unqualified_ident("False"), Vec::new());
        }
        "Coerce" => {
            // class Coercible (no user-visible methods)
            exports.instances.insert(unqualified_ident("Coercible"), Vec::new());
            exports.class_param_counts.insert(unqualified_ident("Coercible"), 2);
            // Coercible :: forall k. k -> k -> Constraint
            use crate::typechecker::types::Type as CoerceType;
            let k_var = TypeVarName::new(intern("k"));
            let k = CoerceType::Var(k_var);
            let cc = CoerceType::kind_constraint();
            exports.class_type_kinds.insert(intern("Coercible"),
                CoerceType::Forall(vec![(k_var, false)], Box::new(
                    CoerceType::fun(k.clone(), CoerceType::fun(k, cc))
                )));
        }
        "Int" => {
            // Compiler-solved type classes for type-level Ints
            // class Add (3), class Compare (3), class Mul (3), class ToString (2)
            for class in &["Add", "Compare", "Mul"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
                exports.class_param_counts.insert(unqualified_ident(class), 3);
            }
            exports.instances.insert(unqualified_ident("ToString"), Vec::new());
            exports.class_param_counts.insert(unqualified_ident("ToString"), 2);
        }
        "Ordering" => {
            // type Ordering with constructors LT, EQ, GT
            exports.data_constructors.insert(
                unqualified_ident("Ordering"),
                vec![unqualified_ident("LT"), unqualified_ident("EQ"), unqualified_ident("GT")],
            );
            exports.data_constructors.insert(unqualified_ident("LT"), Vec::new());
            exports.data_constructors.insert(unqualified_ident("EQ"), Vec::new());
            exports.data_constructors.insert(unqualified_ident("GT"), Vec::new());
        }
        "Row" => {
            // classes: Lacks, Cons, Nub, Union
            for class in &["Lacks", "Cons", "Nub", "Union"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
            }
            exports.class_param_counts.insert(unqualified_ident("Lacks"), 2);
            exports.class_param_counts.insert(unqualified_ident("Cons"), 4);
            exports.class_param_counts.insert(unqualified_ident("Nub"), 2);
            exports.class_param_counts.insert(unqualified_ident("Union"), 3);

            // Export class kinds so they can be registered in class_kinds on import,
            // preventing collisions with data types of the same name.
            use crate::typechecker::types::Type;
            let _k_type = Type::kind_type();
            let k_constraint = Type::kind_constraint();
            let k_symbol = Type::kind_symbol();
            let k_var = TypeVarName::new(intern("k"));
            let k_row_k = Type::kind_row_of(Type::Var(k_var));

            // Union :: forall k. Row k -> Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Union"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), k_constraint.clone())))
                )));
            // Nub :: forall k. Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Nub"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_row_k.clone(), Type::fun(k_row_k.clone(), k_constraint.clone()))
                )));
            // Lacks :: forall k. Symbol -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Lacks"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(k_symbol, Type::fun(k_row_k.clone(), k_constraint.clone()))
                )));
            // Cons :: forall k. Symbol -> k -> Row k -> Row k -> Constraint
            exports.class_type_kinds.insert(intern("Cons"),
                Type::Forall(vec![(k_var, false)], Box::new(
                    Type::fun(Type::kind_symbol(), Type::fun(Type::Var(k_var),
                        Type::fun(k_row_k.clone(), Type::fun(k_row_k, k_constraint))))
                )));
        }
        "RowList" => {
            // type RowList with constructors Cons, Nil; class RowToList
            exports
                .data_constructors
                .insert(unqualified_ident("RowList"), vec![unqualified_ident("Cons"), unqualified_ident("Nil")]);
            exports.data_constructors.insert(unqualified_ident("Cons"), Vec::new());
            exports.data_constructors.insert(unqualified_ident("Nil"), Vec::new());
            exports.instances.insert(unqualified_ident("RowToList"), Vec::new());
            exports.class_param_counts.insert(unqualified_ident("RowToList"), 2);
        }
        "Symbol" => {
            // classes: Append, Compare, Cons
            for class in &["Append", "Compare", "Cons"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
            }
            exports.class_param_counts.insert(unqualified_ident("Append"), 3);
            exports.class_param_counts.insert(unqualified_ident("Compare"), 3);
            exports.class_param_counts.insert(unqualified_ident("Cons"), 3);
        }
        "TypeError" => {
            // classes: Fail, Warn; type constructors: Text, Beside, Above, Quote, QuoteLabel
            for class in &["Fail", "Warn"] {
                exports.instances.insert(unqualified_ident(class), Vec::new());
            }
            exports.class_param_counts.insert(unqualified_ident("Fail"), 1);
            exports.class_param_counts.insert(unqualified_ident("Warn"), 1);
            for ty in &["Doc", "Text", "Beside", "Above", "Quote", "QuoteLabel"] {
                exports.data_constructors.insert(unqualified_ident(ty), Vec::new());
            }
        }
        _ => {
            // Unknown Prim submodule — return empty exports
        }
    }

    exports
}
