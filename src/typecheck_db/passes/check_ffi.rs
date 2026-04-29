//! FFI sidecar (.js) checker. Standalone pass that scans a JS
//! foreign module for CommonJS / ES interop violations the
//! reference compiler reports.
//!
//! Detection rules (lightweight regex-style scanning, no full JS
//! parser):
//!
//!   * `require(...)` anywhere → `UnsupportedFFICommonJSImports`.
//!   * `exports.X = ...` (or `module.exports`) with ANY ES syntax
//!     (`import ...` / `export ...`) → `UnsupportedFFICommonJSExports`.
//!   * `exports.X = ...` (or `module.exports`) with NO ES syntax
//!     → `DeprecatedFFICommonJSModule`.
//!
//! The scanner is comment- and string-aware enough to skip
//! obvious false positives (line comments and the simple cases of
//! `"require"` inside a string literal). For the failing-fixture
//! corpus this is sufficient; complex JS edge cases would need a
//! real lexer.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FfiError {
    UnsupportedFFICommonJSImports,
    UnsupportedFFICommonJSExports,
    DeprecatedFFICommonJSModule,
}

impl FfiError {
    pub fn code(&self) -> &'static str {
        match self {
            FfiError::UnsupportedFFICommonJSImports => "UnsupportedFFICommonJSImports",
            FfiError::UnsupportedFFICommonJSExports => "UnsupportedFFICommonJSExports",
            FfiError::DeprecatedFFICommonJSModule => "DeprecatedFFICommonJSModule",
        }
    }
}

/// Strip line comments (`// …`), block comments (`/* … */`), and
/// single-quoted / double-quoted / backtick string contents. Keeps
/// the structural shape (newlines preserved) so positional
/// tokenisation works the same.
fn strip_comments_and_strings(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        // Line comment.
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        // Block comment.
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/')
            {
                if bytes[i] == b'\n' {
                    out.push('\n');
                }
                i += 1;
            }
            i = (i + 2).min(bytes.len());
            continue;
        }
        // String literals — keep the quotes (so `"foo"` becomes
        // `""`) but drop the contents to avoid matching keywords
        // inside them.
        if b == b'"' || b == b'\'' || b == b'`' {
            let quote = b;
            out.push(quote as char);
            i += 1;
            while i < bytes.len() && bytes[i] != quote {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    i += 2;
                    continue;
                }
                if bytes[i] == b'\n' {
                    out.push('\n');
                }
                i += 1;
            }
            if i < bytes.len() {
                out.push(quote as char);
                i += 1;
            }
            continue;
        }
        out.push(b as char);
        i += 1;
    }
    out
}

/// True iff `src` contains `require(` outside strings/comments,
/// possibly with whitespace between `require` and `(`.
fn contains_require(src: &str) -> bool {
    contains_call_pattern(src, "require")
}

/// True iff `src` contains the call pattern `<keyword>(` with
/// `keyword` being a complete identifier (preceded by a non-ident
/// char or start-of-input).
fn contains_call_pattern(src: &str, keyword: &str) -> bool {
    let bytes = src.as_bytes();
    let kbytes = keyword.as_bytes();
    let mut i = 0;
    while i + kbytes.len() <= bytes.len() {
        if &bytes[i..i + kbytes.len()] == kbytes {
            let prev_ok = i == 0 || !is_ident_char(bytes[i - 1]);
            // Skip whitespace after the keyword.
            let mut j = i + kbytes.len();
            while j < bytes.len() && (bytes[j] == b' ' || bytes[j] == b'\t') {
                j += 1;
            }
            if prev_ok && j < bytes.len() && bytes[j] == b'(' {
                return true;
            }
        }
        i += 1;
    }
    false
}

/// True iff `src` contains an `exports.X = ...` or `module.exports`
/// assignment (CJS export syntax).
fn contains_cjs_export(src: &str) -> bool {
    contains_member_access(src, "exports", true)
        || contains_member_access(src, "module", false)
            && {
                // Look for the pattern `module.exports`.
                let needle = "module.exports";
                let bytes = src.as_bytes();
                let nbytes = needle.as_bytes();
                let mut i = 0;
                while i + nbytes.len() <= bytes.len() {
                    if &bytes[i..i + nbytes.len()] == nbytes {
                        let prev_ok = i == 0 || !is_ident_char(bytes[i - 1]);
                        let next_idx = i + nbytes.len();
                        let next_ok = next_idx >= bytes.len()
                            || !is_ident_char(bytes[next_idx]);
                        if prev_ok && next_ok {
                            return true;
                        }
                    }
                    i += 1;
                }
                false
            }
}

/// True iff `src` contains the pattern `<name>.<ident>` (when
/// `expect_dot=true`) or just `<name>` (otherwise) at an
/// identifier boundary.
fn contains_member_access(src: &str, name: &str, expect_dot: bool) -> bool {
    let bytes = src.as_bytes();
    let nbytes = name.as_bytes();
    let mut i = 0;
    while i + nbytes.len() <= bytes.len() {
        if &bytes[i..i + nbytes.len()] == nbytes {
            let prev_ok = i == 0 || !is_ident_char(bytes[i - 1]);
            let next_idx = i + nbytes.len();
            if prev_ok {
                if expect_dot {
                    if next_idx < bytes.len() && bytes[next_idx] == b'.' {
                        // Require an ident after the dot.
                        let after = next_idx + 1;
                        if after < bytes.len() && is_ident_char(bytes[after]) {
                            return true;
                        }
                    }
                } else if next_idx >= bytes.len()
                    || !is_ident_char(bytes[next_idx])
                {
                    return true;
                }
            }
        }
        i += 1;
    }
    false
}

/// True iff `src` contains an ES `import` or `export` statement at
/// statement-start (preceded only by whitespace on the line).
fn contains_es_module_syntax(src: &str) -> bool {
    for line in src.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("import ")
            || trimmed.starts_with("export ")
            || trimmed.starts_with("export{")
            || trimmed.starts_with("export*")
            || trimmed.starts_with("export {")
            || trimmed.starts_with("export*")
            || trimmed.starts_with("export(")
        {
            return true;
        }
    }
    false
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
}

/// Run all FFI checks on a single JS source. Returns every violation
/// (so a JS file with both `require(...)` and `exports.X = ...`
/// alongside ES syntax produces multiple errors).
pub fn check_ffi_module(js_source: &str) -> Vec<FfiError> {
    let cleaned = strip_comments_and_strings(js_source);
    let mut out = Vec::new();
    let has_require = contains_require(&cleaned);
    let has_cjs_export = contains_cjs_export(&cleaned);
    let has_es = contains_es_module_syntax(&cleaned);
    if has_require {
        out.push(FfiError::UnsupportedFFICommonJSImports);
    }
    if has_cjs_export {
        if has_es {
            out.push(FfiError::UnsupportedFFICommonJSExports);
        } else {
            out.push(FfiError::DeprecatedFFICommonJSModule);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_require_call() {
        let src = r#"var cjs = require("some module");
export var yes = cjs.yes;"#;
        let errs = check_ffi_module(src);
        assert!(errs.contains(&FfiError::UnsupportedFFICommonJSImports));
    }

    #[test]
    fn mixed_es_export_and_cjs_export_is_unsupported() {
        let src = r#"export var yes = true;
exports.no = false;"#;
        let errs = check_ffi_module(src);
        assert!(errs.contains(&FfiError::UnsupportedFFICommonJSExports));
        assert!(!errs.contains(&FfiError::DeprecatedFFICommonJSModule));
    }

    #[test]
    fn pure_cjs_export_is_deprecated() {
        let src = r#""use strict";
exports.yes = true;
exports.no = true;"#;
        let errs = check_ffi_module(src);
        assert!(errs.contains(&FfiError::DeprecatedFFICommonJSModule));
        assert!(!errs.contains(&FfiError::UnsupportedFFICommonJSExports));
    }

    #[test]
    fn cjs_export_with_es_import_is_unsupported() {
        let src = r#"import { yes, no } from "some ES module";
exports.yes = yes;
exports.no = no;"#;
        let errs = check_ffi_module(src);
        assert!(errs.contains(&FfiError::UnsupportedFFICommonJSExports));
    }

    #[test]
    fn pure_es_module_has_no_errors() {
        let src = r#"export var yes = true;
export var no = false;"#;
        let errs = check_ffi_module(src);
        assert!(errs.is_empty());
    }

    #[test]
    fn require_inside_string_does_not_fire() {
        let src = r#"export var x = "this is a require(\"foo\") test";"#;
        let errs = check_ffi_module(src);
        assert!(errs.is_empty());
    }

    #[test]
    fn require_in_line_comment_does_not_fire() {
        let src = r#"// this is a require("foo") example
export var yes = true;"#;
        let errs = check_ffi_module(src);
        assert!(errs.is_empty());
    }

    #[test]
    fn default_cjs_export_is_deprecated() {
        let src = r#"exports.default = "Done";"#;
        let errs = check_ffi_module(src);
        assert!(errs.contains(&FfiError::DeprecatedFFICommonJSModule));
    }
}
