use string_interner::{StringInterner, DefaultSymbol, DefaultBackend};
use std::sync::Mutex;

/// Type alias for our symbol type
pub type Symbol = DefaultSymbol;

/// Type alias for our string interner
type Interner = StringInterner<DefaultBackend>;

static INTERNER: Mutex<Option<Interner>> = Mutex::new(None);

fn with_interner<R>(f: impl FnOnce(&mut Interner) -> R) -> R {
    let mut guard = INTERNER.lock().unwrap_or_else(|e| e.into_inner());
    let interner = guard.get_or_insert_with(StringInterner::new);
    f(interner)
}

/// Intern a string and return its symbol
pub fn intern(s: &str) -> Symbol {
    with_interner(|interner| interner.get_or_intern(s))
}

/// Resolve a symbol back to its string
pub fn resolve(sym: Symbol) -> Option<String> {
    with_interner(|interner| interner.resolve(sym).map(|s| s.to_string()))
}

/// Clear the interner (useful for testing)
#[cfg(test)]
pub fn clear() {
    let mut guard = INTERNER.lock().unwrap_or_else(|e| e.into_inner());
    *guard = Some(StringInterner::new());
}
