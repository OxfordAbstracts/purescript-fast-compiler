//! IDE/compiler warnings (non-fatal). Unlike the error channels these do
//! NOT mark a module as errored (see `ModuleCheckResult::has_errors`), so a
//! module with only warnings is still memoized/clean.

use crate::span::Span;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Warning {
    pub span: Span,
    pub kind: WarningKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WarningKind {
    /// An imported name is never referenced in the module body.
    UnusedImport { name: String },
    /// A let-binding or lambda parameter is never referenced.
    UnusedName { name: String },
}

/// Emit `UnusedImport` for every imported name absent from `referenced`.
/// Names beginning with `_` are exempt (intentional-unused convention).
/// `imported` is a list of `(name, span)` where `span` points at the import
/// item to remove; duplicates (same name+span) are collapsed.
pub fn compute_unused_imports(
    imported: &[(String, Span)],
    referenced: &HashSet<String>,
) -> Vec<Warning> {
    let mut seen: HashSet<(&str, usize)> = HashSet::new();
    let mut out = Vec::new();
    for (name, span) in imported {
        if name.starts_with('_') || name.is_empty() {
            continue;
        }
        if referenced.contains(name) {
            continue;
        }
        if !seen.insert((name.as_str(), span.start)) {
            continue;
        }
        out.push(Warning {
            span: *span,
            kind: WarningKind::UnusedImport { name: name.clone() },
        });
    }
    out
}
