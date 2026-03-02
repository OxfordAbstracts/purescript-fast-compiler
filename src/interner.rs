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

/// Resolve a symbol and pass the &str to a closure, avoiding String allocation.
pub fn with_resolved<R>(sym: Symbol, f: impl FnOnce(&str) -> R) -> Option<R> {
    with_interner(|interner| interner.resolve(sym).map(f))
}

/// Intern a qualified name "module.name" in a single lock acquisition.
pub fn intern_qualified(module: Symbol, name: Symbol) -> Symbol {
    with_interner(|interner| {
        let m = interner.resolve(module).unwrap_or("");
        let n = interner.resolve(name).unwrap_or("");
        let mut buf = String::with_capacity(m.len() + 1 + n.len());
        buf.push_str(m);
        buf.push('.');
        buf.push_str(n);
        interner.get_or_intern(&buf)
    })
}

/// Intern a dot-joined module name from symbol parts in a single lock acquisition.
pub fn intern_module_name(parts: &[Symbol]) -> Symbol {
    with_interner(|interner| {
        let mut buf = String::new();
        for (i, &part) in parts.iter().enumerate() {
            if i > 0 {
                buf.push('.');
            }
            if let Some(s) = interner.resolve(part) {
                buf.push_str(s);
            }
        }
        interner.get_or_intern(&buf)
    })
}

/// Resolve a module name (dot-joined parts) to a String.
pub fn resolve_module_name(parts: &[Symbol]) -> String {
    with_interner(|interner| {
        let mut buf = String::new();
        for (i, &part) in parts.iter().enumerate() {
            if i > 0 {
                buf.push('.');
            }
            if let Some(s) = interner.resolve(part) {
                buf.push_str(s);
            }
        }
        buf
    })
}

/// Check if a symbol equals a string, without allocating.
pub fn symbol_eq(sym: Symbol, s: &str) -> bool {
    with_interner(|interner| interner.resolve(sym).map_or(false, |r| r == s))
}

/// Clear the interner (useful for testing)
#[cfg(test)]
pub fn clear() {
    let mut guard = INTERNER.lock().unwrap_or_else(|e| e.into_inner());
    *guard = Some(StringInterner::new());
}
