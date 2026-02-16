use std::fmt;

use crate::interner::{self, Symbol};

/// Unique identifier for a unification variable.
/// The actual binding is stored in the UnifyState table, not here.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyVarId(pub u32);

/// Internal type representation for the typechecker.
/// Separate from cst::TypeExpr — this is what unification operates on.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// Unification variable (mutable — gets resolved during inference)
    Unif(TyVarId),

    /// Rigid/skolem type variable (from forall quantification, immutable)
    Var(Symbol),

    /// Type constructor: Int, String, Boolean, Array, Maybe, etc.
    Con(Symbol),

    /// Type application: Array Int, Maybe a
    App(Box<Type>, Box<Type>),

    /// Function type: a -> b
    Fun(Box<Type>, Box<Type>),

    /// Universal quantification: forall a. <type>
    /// Each var is (name, visible) where visible=true means `@a` for VTA
    Forall(Vec<(Symbol, bool)>, Box<Type>),

    /// Record type: { label1 :: Type1, label2 :: Type2, ... | tail }
    /// Fields are (label, type) pairs. Optional tail for row polymorphism.
    Record(Vec<(Symbol, Type)>, Option<Box<Type>>),

    /// Type-level string literal: "hello"
    TypeString(Symbol),

    /// Type-level integer literal: 42
    TypeInt(i64),
}

impl Type {
    pub fn int() -> Type {
        Type::Con(interner::intern("Int"))
    }

    pub fn float() -> Type {
        Type::Con(interner::intern("Number"))
    }

    pub fn string() -> Type {
        Type::Con(interner::intern("String"))
    }

    pub fn char() -> Type {
        Type::Con(interner::intern("Char"))
    }

    pub fn boolean() -> Type {
        Type::Con(interner::intern("Boolean"))
    }

    pub fn fun(from: Type, to: Type) -> Type {
        Type::Fun(Box::new(from), Box::new(to))
    }

    pub fn app(f: Type, arg: Type) -> Type {
        Type::App(Box::new(f), Box::new(arg))
    }

    pub fn array(elem: Type) -> Type {
        Type::app(Type::Con(interner::intern("Array")), elem)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unif(id) => write!(f, "?{}", id.0),
            Type::Var(sym) => write!(f, "{}", interner::resolve(*sym).unwrap_or_default()),
            Type::Con(sym) => write!(f, "{}", interner::resolve(*sym).unwrap_or_default()),
            Type::App(func, arg) => write!(f, "({} {})", func, arg),
            Type::Fun(from, to) => write!(f, "({} -> {})", from, to),
            Type::Forall(vars, ty) => {
                write!(f, "(forall")?;
                for (v, visible) in vars {
                    if *visible {
                        write!(f, " @{}", interner::resolve(*v).unwrap_or_default())?;
                    } else {
                        write!(f, " {}", interner::resolve(*v).unwrap_or_default())?;
                    }
                }
                write!(f, ". {})", ty)
            }
            Type::TypeString(sym) => write!(f, "\"{}\"", interner::resolve(*sym).unwrap_or_default()),
            Type::TypeInt(n) => write!(f, "{}", n),
            Type::Record(fields, tail) => {
                write!(f, "{{ ")?;
                for (i, (label, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} :: {}", interner::resolve(*label).unwrap_or_default(), ty)?;
                }
                if let Some(tail) = tail {
                    if !fields.is_empty() {
                        write!(f, " | ")?;
                    }
                    write!(f, "{}", tail)?;
                }
                write!(f, " }}")
            }
        }
    }
}

/// A type scheme (polytype): quantified type variables + monotype.
/// When instantiated, each quantified var is replaced with a fresh unification variable.
/// Quantified variables are `Type::Var(Symbol)` in the body, making schemes
/// self-contained (no references to a specific `UnifyState`).
#[derive(Debug, Clone, PartialEq)]
pub struct Scheme {
    pub forall_vars: Vec<Symbol>,
    pub ty: Type,
}

impl Scheme {
    /// Create a monomorphic scheme (no quantified variables).
    pub fn mono(ty: Type) -> Self {
        Scheme {
            forall_vars: vec![],
            ty,
        }
    }
}
