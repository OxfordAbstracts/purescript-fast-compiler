use std::collections::{HashMap, HashSet};

use crate::cst::{Associativity, QualifiedIdent};
use crate::interner::Symbol;
use crate::typechecker::types::{Role, Scheme, Type};

/// Exported information from a type-checked module, available for import by other modules.
#[derive(Debug, Clone, Default)]
pub struct ModuleExports {
    /// Value/constructor/method schemes
    pub values: HashMap<QualifiedIdent, Scheme>,
    /// Class method info: method_name → (class_name, class_type_vars)
    pub class_methods: HashMap<QualifiedIdent, (QualifiedIdent, Vec<QualifiedIdent>)>,
    /// Data type → constructor names
    pub data_constructors: HashMap<QualifiedIdent, Vec<QualifiedIdent>>,
    /// Constructor details: ctor_name → (parent_type, type_vars, field_types)
    pub ctor_details: HashMap<QualifiedIdent, (QualifiedIdent, Vec<QualifiedIdent>, Vec<Type>)>,
    /// Class instances: class_name → [(types, constraints)]
    pub instances: HashMap<QualifiedIdent, Vec<(Vec<Type>, Vec<(QualifiedIdent, Vec<Type>)>)>>,
    /// Type-level operators: op → target type name
    pub type_operators: HashMap<QualifiedIdent, QualifiedIdent>,
    /// Value-level operator fixities: operator → (associativity, precedence)
    pub value_fixities: HashMap<QualifiedIdent, (Associativity, u8)>,
    /// Type-level operator fixities: operator → (associativity, precedence)
    pub type_fixities: HashMap<QualifiedIdent, (Associativity, u8)>,
    /// Value-level operators that alias functions (not constructors)
    pub function_op_aliases: HashSet<QualifiedIdent>,
    /// Value-level operator targets: operator → target name (e.g. + → add, : → Cons)
    pub value_operator_targets: HashMap<QualifiedIdent, QualifiedIdent>,
    /// Class methods whose declared type has extra constraints (e.g. `Applicative m =>`).
    /// Used for CycleInDeclaration detection across module boundaries.
    pub constrained_class_methods: HashSet<QualifiedIdent>,
    /// Type aliases: alias_name → (params, body_type)
    pub type_aliases: HashMap<QualifiedIdent, (Vec<QualifiedIdent>, Type)>,
    /// Class definitions: class_name → param_count (for arity checking and orphan detection)
    pub class_param_counts: HashMap<QualifiedIdent, usize>,
    /// Origin tracking: name → original defining module symbol.
    /// Used to distinguish re-exports of the same definition from
    /// independently defined names that happen to have the same type.
    pub value_origins: HashMap<Symbol, Symbol>,
    pub type_origins: HashMap<Symbol, Symbol>,
    pub class_origins: HashMap<Symbol, Symbol>,
    /// Operator → class method target (e.g. `<>` → `append`).
    /// Used for tracking deferred constraints on operator usage.
    pub operator_class_targets: HashMap<Symbol, Symbol>,
    /// Class functional dependencies: class_name → (type_vars, fundeps as index pairs).
    /// Used for fundep-aware orphan instance checking.
    pub class_fundeps: HashMap<Symbol, (Vec<Symbol>, Vec<(Vec<usize>, Vec<usize>)>)>,
    /// Type constructor arities: type_name → number of type parameters.
    /// Used to detect over-applied types after type alias expansion.
    pub type_con_arities: HashMap<QualifiedIdent, usize>,
    /// Roles for each type constructor: type_name → [Role per type parameter].
    pub type_roles: HashMap<Symbol, Vec<Role>>,
    /// Set of type names declared as newtypes (for Coercible solving).
    pub newtype_names: HashSet<Symbol>,
    /// Signature constraints for exported functions: name → [(class_name, type_args)].
    pub signature_constraints: HashMap<QualifiedIdent, Vec<(QualifiedIdent, Vec<Type>)>>,
    /// Type constructor kinds: type_name → kind Type.
    /// Used for cross-module kind checking (e.g., detecting kind mismatches
    /// between types with the same unqualified name from different modules).
    pub type_kinds: HashMap<Symbol, Type>,
    /// Class kinds: class_name → kind (e.g., Type -> Constraint).
    /// Separate from type_kinds so class kinds don't interfere with type checking
    /// when a class and data type share the same name.
    pub class_type_kinds: HashMap<Symbol, Type>,
    /// Functions whose type has Partial in a function parameter position,
    /// e.g. `unsafePartial :: (Partial => a) -> a`. These discharge Partial
    /// when applied to a partial expression.
    pub partial_dischargers: HashSet<Symbol>,
    /// Pre-computed self-referential type aliases from this module.
    /// Imported at import time to avoid recomputing from scratch.
    pub self_referential_aliases: HashSet<Symbol>,
}

/// Registry of compiled modules, used to resolve imports.
///
/// Supports layering: a child registry can be created with `with_base()`,
/// which shares an immutable base via `Arc` (zero-copy) and stores new
/// modules in a local overlay. Lookups check the overlay first, then the base.
#[derive(Debug, Clone, Default)]
pub struct ModuleRegistry {
    modules: HashMap<Vec<Symbol>, ModuleExports>,
    base: Option<std::sync::Arc<ModuleRegistry>>,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a child registry layered on top of a shared base.
    /// New modules are stored locally; lookups fall through to the base.
    pub fn with_base(base: std::sync::Arc<ModuleRegistry>) -> Self {
        Self {
            modules: HashMap::new(),
            base: Some(base),
        }
    }

    pub fn register(&mut self, name: &[Symbol], exports: ModuleExports) {
        self.modules.insert(name.to_vec(), exports);
    }

    pub fn lookup(&self, name: &[Symbol]) -> Option<&ModuleExports> {
        self.modules
            .get(name)
            .or_else(|| self.base.as_ref().and_then(|b| b.lookup(name)))
    }

    pub fn contains(&self, name: &[Symbol]) -> bool {
        self.modules.contains_key(name) || self.base.as_ref().map_or(false, |b| b.contains(name))
    }
}
