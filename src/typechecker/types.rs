use std::fmt;

use crate::{interner::{self, Symbol}, names::{self, Qualified, TypeName, TypeVarName, LabelName}};

/// Type parameter role for Coercible solving.
/// Ordered: Phantom < Representational < Nominal (most restrictive).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Role {
    Phantom = 0,
    Representational = 1,
    Nominal = 2,
}

impl Role {
    /// Compose roles through nested type constructors.
    /// If outer position is Phantom or inner is Phantom, result is Phantom.
    /// Otherwise take the more restrictive of the two.
    pub fn compose(self, other: Role) -> Role {
        if self == Role::Phantom || other == Role::Phantom {
            Role::Phantom
        } else {
            self.max(other)
        }
    }
}

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
    Var(TypeVarName),

    /// Type constructor: Int, String, Boolean, Array, Maybe, etc.
    Con(Qualified<TypeName>),

    /// Type application: Array Int, Maybe a
    App(Box<Type>, Box<Type>),

    /// Function type: a -> b
    Fun(Box<Type>, Box<Type>),

    /// Universal quantification: forall a. <type>
    /// Each var is (name, visible) where visible=true means `@a` for VTA
    Forall(Vec<(TypeVarName, bool)>, Box<Type>),

    /// Record type: { label1 :: Type1, label2 :: Type2, ... | tail }
    /// Fields are (label, type) pairs. Optional tail for row polymorphism.
    Record(Vec<(LabelName, Type)>, Option<Box<Type>>),

    /// Type-level string literal: "hello"
    TypeString(Symbol),

    /// Type-level integer literal: 42
    TypeInt(i64),
}

impl Type {
    pub fn prim_con(name: &str) -> Type {
        Type::Con(names::unqualified_type(name))
    }

    pub fn con(_module: &str, name: &str) -> Type {
        // Module qualifier ignored for now — will be used when convert_type_expr
        // gains proper module resolution.
        Type::Con(names::unqualified_type(name))
    }

    pub fn con_local(name: &str) -> Type {
        Type::Con(names::unqualified_type(name))
    }

    pub fn int() -> Type {
        Type::prim_con("Int")
    }

    pub fn float() -> Type {
        Type::prim_con("Number")
    }

    pub fn string() -> Type {
        Type::prim_con("String")
    }

    pub fn char() -> Type {
        Type::prim_con("Char")
    }

    pub fn boolean() -> Type {
        Type::prim_con("Boolean")
    }

    pub fn fun(from: Type, to: Type) -> Type {
        Type::Fun(Box::new(from), Box::new(to))
    }

    pub fn app(f: Type, arg: Type) -> Type {
        Type::App(Box::new(f), Box::new(arg))
    }

    pub fn array(elem: Type) -> Type {
        Type::app(Type::prim_con("Array"), elem)
    }

    // Kind constructors — kinds are represented as Types

    /// The kind of ordinary types: `Type`
    pub fn kind_type() -> Type {
        Type::prim_con("Type")
    }

    /// The kind of type class constraints: `Constraint`
    pub fn kind_constraint() -> Type {
        Type::prim_con("Constraint")
    }

    /// The kind of type-level strings: `Symbol`
    pub fn kind_symbol() -> Type {
        Type::prim_con("Symbol")
    }

    /// The kind of type-level integers (PureScript uses "Int" at kind level too, but
    /// we use a distinct interned name to avoid collision with the value-level Int type)
    pub fn kind_int() -> Type {
        Type::prim_con("Int")
    }

    /// The `Row` kind constructor (takes a kind argument: `Row Type`)
    pub fn kind_row() -> Type {
        Type::prim_con("Row")
    }

    /// `Row k` — the kind of row types parameterized by element kind `k`
    pub fn kind_row_of(k: Type) -> Type {
        Type::app(Type::kind_row(), k)
    }
}

impl Type {
    /// Format with parentheses when in a nested context that requires them.
    fn fmt_nested(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::App(..) | Type::Fun(..) | Type::Forall(..) => {
                write!(f, "(")?;
                self.fmt_inner(f)?;
                write!(f, ")")
            }
            _ => self.fmt_inner(f),
        }
    }

    /// Format the type without outer parentheses.
    fn fmt_inner(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unif(id) => write!(f, "?{}", id.0),
            Type::Var(name) => write!(f, "{}", name),
            Type::Con(sym) => write!(f, "{}", sym),
            Type::App(func, arg) => {
                // Function position doesn't need parens for App chains, but does for Fun/Forall
                match func.as_ref() {
                    Type::App(..) | Type::Con(..) | Type::Var(..) | Type::Unif(..) => func.fmt_inner(f)?,
                    _ => func.fmt_nested(f)?,
                };
                write!(f, " ")?;
                arg.fmt_nested(f)
            }
            Type::Fun(from, to) => {
                from.fmt_nested(f)?;
                write!(f, " -> ")?;
                // Right side of -> doesn't need parens for -> (right-associative)
                to.fmt_inner(f)
            }
            Type::Forall(vars, ty) => {
                write!(f, "forall")?;
                for (v, visible) in vars {
                    if *visible {
                        write!(f, " @{}", v)?;
                    } else {
                        write!(f, " {}", v)?;
                    }
                }
                write!(f, ". ")?;
                ty.fmt_inner(f)
            }
            Type::TypeString(sym) => write!(f, "\"{}\"", interner::resolve(*sym).unwrap_or_default()),
            Type::TypeInt(n) => write!(f, "{}", n),
            Type::Record(fields, tail) => {
                write!(f, "{{ ")?;
                for (i, (label, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} :: {}", label, ty)?;
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_inner(f)
    }
}

/// A type scheme (polytype): quantified type variables + monotype.
/// When instantiated, each quantified var is replaced with a fresh unification variable.
/// Quantified variables are `Type::Var(TypeVarName)` in the body, making schemes
/// self-contained (no references to a specific `UnifyState`).
#[derive(Debug, Clone, PartialEq)]
pub struct Scheme {
    pub forall_vars: Vec<TypeVarName>,
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
