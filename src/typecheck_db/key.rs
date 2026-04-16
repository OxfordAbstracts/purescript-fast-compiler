//! Cache key construction and hashing.
//!
//! Every pass output is keyed by `(module, decl, pass)` and validated by an
//! `input_hash` that folds in the pass version, the decl's source hash, and
//! the `output_hash` of every dependency this pass consumed. A cache hit is
//! only valid when the stored `input_hash` matches a fresh recompute.

use std::fmt;

pub type InputHash = [u8; 32];
pub type OutputHash = [u8; 32];

/// The primary-key portion of a cache row.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PassKey {
    pub module: String,
    pub decl: String,
    pub pass: &'static str,
}

impl PassKey {
    pub fn new(module: impl Into<String>, decl: impl Into<String>, pass: &'static str) -> Self {
        Self { module: module.into(), decl: decl.into(), pass }
    }
}

impl fmt::Display for PassKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{}@{}", self.module, self.decl, self.pass)
    }
}

pub fn hash_bytes(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

/// Builder for a pass's `input_hash`.
///
/// Dependencies are accumulated, then sorted before hashing so the hash is
/// independent of the order in which deps were reported.
pub struct InputHasher {
    pass_name: &'static str,
    pass_version: u32,
    source_hash: [u8; 32],
    module_context: [u8; 32],
    deps: Vec<DepEntry>,
}

#[derive(Clone)]
struct DepEntry {
    dep_module: String,
    dep_decl: String,
    dep_pass: &'static str,
    output_hash: [u8; 32],
}

impl InputHasher {
    pub fn new(pass_name: &'static str, pass_version: u32) -> Self {
        Self {
            pass_name,
            pass_version,
            source_hash: [0u8; 32],
            module_context: [0u8; 32],
            deps: Vec::new(),
        }
    }

    pub fn with_source_hash(mut self, hash: [u8; 32]) -> Self {
        self.source_hash = hash;
        self
    }

    /// Fold in a module-scoped context hash (e.g. fixity declarations
    /// visible to this decl, the module's import list). Folding this in
    /// here — instead of mixing it with the source_hash at the call site —
    /// keeps the semantic axes separate and makes the cache diagnostics
    /// easier to reason about.
    pub fn with_module_context(mut self, hash: [u8; 32]) -> Self {
        self.module_context = hash;
        self
    }

    pub fn add_dep(
        &mut self,
        dep_module: impl Into<String>,
        dep_decl: impl Into<String>,
        dep_pass: &'static str,
        output_hash: [u8; 32],
    ) {
        self.deps.push(DepEntry {
            dep_module: dep_module.into(),
            dep_decl: dep_decl.into(),
            dep_pass,
            output_hash,
        });
    }

    pub fn finish(mut self) -> InputHash {
        self.deps.sort_by(|a, b| {
            (a.dep_module.as_str(), a.dep_decl.as_str(), a.dep_pass)
                .cmp(&(b.dep_module.as_str(), b.dep_decl.as_str(), b.dep_pass))
        });
        let mut h = blake3::Hasher::new();
        h.update(self.pass_name.as_bytes());
        h.update(&[0u8]);
        h.update(&self.pass_version.to_le_bytes());
        h.update(&self.source_hash);
        h.update(&self.module_context);
        h.update(&(self.deps.len() as u32).to_le_bytes());
        for d in &self.deps {
            h.update(d.dep_module.as_bytes());
            h.update(&[0u8]);
            h.update(d.dep_decl.as_bytes());
            h.update(&[0u8]);
            h.update(d.dep_pass.as_bytes());
            h.update(&[0u8]);
            h.update(&d.output_hash);
        }
        *h.finalize().as_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_inputs_same_hash() {
        let a = InputHasher::new("p", 1).with_source_hash([1u8; 32]).finish();
        let b = InputHasher::new("p", 1).with_source_hash([1u8; 32]).finish();
        assert_eq!(a, b);
    }

    #[test]
    fn different_source_different_hash() {
        let a = InputHasher::new("p", 1).with_source_hash([1u8; 32]).finish();
        let b = InputHasher::new("p", 1).with_source_hash([2u8; 32]).finish();
        assert_ne!(a, b);
    }

    #[test]
    fn different_version_different_hash() {
        let a = InputHasher::new("p", 1).with_source_hash([1u8; 32]).finish();
        let b = InputHasher::new("p", 2).with_source_hash([1u8; 32]).finish();
        assert_ne!(a, b);
    }

    #[test]
    fn dep_order_irrelevant() {
        let mut a = InputHasher::new("p", 1).with_source_hash([0u8; 32]);
        a.add_dep("M", "x", "q", [9u8; 32]);
        a.add_dep("M", "y", "q", [8u8; 32]);

        let mut b = InputHasher::new("p", 1).with_source_hash([0u8; 32]);
        b.add_dep("M", "y", "q", [8u8; 32]);
        b.add_dep("M", "x", "q", [9u8; 32]);

        assert_eq!(a.finish(), b.finish());
    }

    #[test]
    fn module_context_change_changes_hash() {
        let a = InputHasher::new("p", 1)
            .with_source_hash([1u8; 32])
            .with_module_context([7u8; 32])
            .finish();
        let b = InputHasher::new("p", 1)
            .with_source_hash([1u8; 32])
            .with_module_context([8u8; 32])
            .finish();
        assert_ne!(a, b);
    }

    #[test]
    fn dep_change_changes_hash() {
        let mut a = InputHasher::new("p", 1).with_source_hash([0u8; 32]);
        a.add_dep("M", "x", "q", [9u8; 32]);
        let mut b = InputHasher::new("p", 1).with_source_hash([0u8; 32]);
        b.add_dep("M", "x", "q", [10u8; 32]);
        assert_ne!(a.finish(), b.finish());
    }
}
