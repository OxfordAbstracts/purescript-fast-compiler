/// Name mangling utilities for JavaScript code generation.
/// Matches the original PureScript compiler's Language.PureScript.CodeGen.JS.Common module.

use crate::interner::{self, Symbol};

/// Convert a PureScript identifier (Ident / Symbol) to a valid JS identifier.
pub fn ident_to_js(sym: Symbol) -> String {
    let name = interner::resolve(sym).unwrap_or_default();
    any_name_to_js(&name)
}

/// Convert a module name (list of segments) to a JS identifier.
/// `Data.Array` → `Data_Array`, with `$$` prefix if the result is a JS built-in.
pub fn module_name_to_js(parts: &[Symbol]) -> String {
    let segments: Vec<String> = parts
        .iter()
        .map(|s| interner::resolve(*s).unwrap_or_default())
        .collect();
    let joined = segments.join("_");
    if is_js_builtin(&joined) {
        format!("$${joined}")
    } else {
        joined
    }
}

/// Convert a module name (dot-separated string) to a JS identifier.
pub fn module_name_str_to_js(name: &str) -> String {
    let joined = name.replace('.', "_");
    if is_js_builtin(&joined) {
        format!("$${joined}")
    } else {
        joined
    }
}

/// Core name-to-JS conversion: escape symbol characters and prefix reserved words.
pub fn any_name_to_js(name: &str) -> String {
    if name.is_empty() {
        return String::new();
    }

    // Check if the name starts with a digit → prefix with $$
    if name.chars().next().map_or(false, |c| c.is_ascii_digit()) {
        return format!("$${name}");
    }

    let mut needs_escaping = false;
    for ch in name.chars() {
        if !ch.is_alphanumeric() && ch != '_' {
            needs_escaping = true;
            break;
        }
    }

    let result = if needs_escaping {
        let mut buf = String::new();
        for ch in name.chars() {
            match escape_char(ch) {
                Some(escaped) => buf.push_str(escaped),
                None => buf.push(ch),
            }
        }
        buf
    } else {
        name.to_string()
    };

    if is_js_reserved(&result) || is_js_builtin(&result) {
        format!("$${result}")
    } else {
        result
    }
}

/// Escape a single character to its JS-safe representation.
fn escape_char(ch: char) -> Option<&'static str> {
    match ch {
        '_' => None,
        '.' => Some("$dot"),
        '$' => Some("$dollar"),
        '~' => Some("$tilde"),
        '=' => Some("$eq"),
        '<' => Some("$less"),
        '>' => Some("$greater"),
        '!' => Some("$bang"),
        '#' => Some("$hash"),
        '%' => Some("$percent"),
        '^' => Some("$up"),
        '&' => Some("$amp"),
        '|' => Some("$bar"),
        '*' => Some("$times"),
        '/' => Some("$div"),
        '+' => Some("$plus"),
        '-' => Some("$minus"),
        ':' => Some("$colon"),
        '\\' => Some("$bslash"),
        '?' => Some("$qmark"),
        '@' => Some("$at"),
        '\'' => Some("$prime"),
        c if c.is_alphanumeric() => None,
        _ => None, // fallback: kept as-is (non-ASCII identifiers)
    }
}

/// Check if a name is a JavaScript reserved word.
pub fn is_js_reserved(name: &str) -> bool {
    matches!(
        name,
        // ES2015+ keywords
        "break"
        | "case"
        | "catch"
        | "class"
        | "const"
        | "continue"
        | "debugger"
        | "default"
        | "delete"
        | "do"
        | "else"
        | "export"
        | "extends"
        | "finally"
        | "for"
        | "function"
        | "if"
        | "import"
        | "in"
        | "instanceof"
        | "new"
        | "return"
        | "super"
        | "switch"
        | "this"
        | "throw"
        | "try"
        | "typeof"
        | "var"
        | "void"
        | "while"
        | "with"
        // Sometimes reserved
        | "await"
        | "let"
        | "static"
        | "yield"
        // Future reserved
        | "enum"
        // Future reserved (strict mode)
        | "implements"
        | "interface"
        | "package"
        | "private"
        | "protected"
        | "public"
        // Old reserved
        | "abstract"
        | "boolean"
        | "byte"
        | "char"
        | "double"
        | "final"
        | "float"
        | "goto"
        | "int"
        | "long"
        | "native"
        | "short"
        | "synchronized"
        | "throws"
        | "transient"
        | "volatile"
        // Literals
        | "null"
        | "true"
        | "false"
    )
}

/// Check if a name matches a JavaScript built-in global.
pub fn is_js_builtin(name: &str) -> bool {
    matches!(
        name,
        "Array"
        | "ArrayBuffer"
        | "Boolean"
        | "DataView"
        | "Date"
        | "Error"
        | "EvalError"
        | "Float32Array"
        | "Float64Array"
        | "Function"
        | "Generator"
        | "GeneratorFunction"
        | "Int16Array"
        | "Int32Array"
        | "Int8Array"
        | "InternalError"
        | "JSON"
        | "Map"
        | "Math"
        | "Number"
        | "Object"
        | "Promise"
        | "Proxy"
        | "RangeError"
        | "ReferenceError"
        | "Reflect"
        | "RegExp"
        | "Set"
        | "SharedArrayBuffer"
        | "String"
        | "Symbol"
        | "SyntaxError"
        | "TypeError"
        | "TypedArray"
        | "URIError"
        | "Uint16Array"
        | "Uint32Array"
        | "Uint8Array"
        | "Uint8ClampedArray"
        | "WeakMap"
        | "WeakSet"
        | "Atomics"
        | "Intl"
        | "WebAssembly"
        | "arguments"
        | "console"
        | "decodeURI"
        | "decodeURIComponent"
        | "encodeURI"
        | "encodeURIComponent"
        | "eval"
        | "globalThis"
        | "isFinite"
        | "isNaN"
        | "parseFloat"
        | "parseInt"
        | "undefined"
        | "Infinity"
        | "NaN"
    )
}

/// Check if a string is a valid JS identifier (for property access with dot notation).
pub fn is_valid_js_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    let first = chars.next().unwrap();
    if !first.is_ascii_alphabetic() && first != '_' && first != '$' {
        return false;
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_name_to_js() {
        assert_eq!(module_name_str_to_js("Data.Array"), "Data_Array");
        assert_eq!(module_name_str_to_js("Main"), "Main");
        assert_eq!(module_name_str_to_js("Data.Map.Internal"), "Data_Map_Internal");
    }

    #[test]
    fn test_module_name_builtin_prefix() {
        assert_eq!(module_name_str_to_js("Math"), "$$Math");
    }

    #[test]
    fn test_any_name_reserved() {
        assert_eq!(any_name_to_js("class"), "$$class");
        assert_eq!(any_name_to_js("import"), "$$import");
        assert_eq!(any_name_to_js("let"), "$$let");
    }

    #[test]
    fn test_any_name_builtin() {
        assert_eq!(any_name_to_js("Array"), "$$Array");
        assert_eq!(any_name_to_js("undefined"), "$$undefined");
    }

    #[test]
    fn test_any_name_symbols() {
        assert_eq!(any_name_to_js("<>"), "$less$greater");
        assert_eq!(any_name_to_js("+"), "$plus");
        assert_eq!(any_name_to_js("&&"), "$amp$amp");
        assert_eq!(any_name_to_js("<$>"), "$less$dollar$greater");
    }

    #[test]
    fn test_any_name_plain() {
        assert_eq!(any_name_to_js("foo"), "foo");
        assert_eq!(any_name_to_js("myFunction"), "myFunction");
        assert_eq!(any_name_to_js("x1"), "x1");
    }

    #[test]
    fn test_any_name_prime() {
        assert_eq!(any_name_to_js("x'"), "x$prime");
        assert_eq!(any_name_to_js("go'"), "go$prime");
    }

    #[test]
    fn test_digit_prefix() {
        assert_eq!(any_name_to_js("1foo"), "$$1foo");
    }

    #[test]
    fn test_valid_js_identifier() {
        assert!(is_valid_js_identifier("foo"));
        assert!(is_valid_js_identifier("_bar"));
        assert!(is_valid_js_identifier("$baz"));
        assert!(!is_valid_js_identifier(""));
        assert!(!is_valid_js_identifier("1abc"));
        assert!(!is_valid_js_identifier("a-b"));
    }
}
