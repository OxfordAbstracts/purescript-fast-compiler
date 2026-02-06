use string_interner::{StringInterner, DefaultSymbol, DefaultBackend};

/// Type alias for our symbol type
pub type Symbol = DefaultSymbol;

/// Type alias for our string interner
type Interner = StringInterner<DefaultBackend>;

thread_local! {
    static INTERNER: std::cell::RefCell<Interner> =
        std::cell::RefCell::new(StringInterner::new());
}

/// Intern a string and return its symbol
pub fn intern(s: &str) -> Symbol {
    INTERNER.with(|interner| interner.borrow_mut().get_or_intern(s))
}

/// Resolve a symbol back to its string
pub fn resolve(sym: Symbol) -> Option<String> {
    INTERNER.with(|interner| {
        interner.borrow().resolve(sym).map(|s| s.to_string())
    })
}

/// Clear the interner (useful for testing)
#[cfg(test)]
pub fn clear() {
    INTERNER.with(|interner| {
        *interner.borrow_mut() = StringInterner::new();
    });
}
