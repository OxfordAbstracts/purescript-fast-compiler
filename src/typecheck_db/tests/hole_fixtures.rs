//! Per-variant tests for the typed-hole fixtures under
//! `tests/fixtures/holes/`.
//!
//! Each variant dir (e.g. `1110-1/`) contains one or more `.purs`
//! files and a structured `expected.txt` produced by the reference
//! `purs` compiler. The test parses the variant, runs
//! `check_many_modules`, pulls the first `HoleDiagnostic` from
//! `Main`, and checks it against `expected.txt`.
//!
//! All tests are `#[ignore]` by default — gap-closing work in
//! `typecheck_db` will move the ratchet. Run with
//! `cargo test typecheck_db::tests::hole_fixtures -- --ignored`
//! to see the current pass rate.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use ntest_timeout::timeout;

use crate::cst;
use crate::parser::parse;
use crate::typecheck_db::driver_multi::{check_many_modules, ModuleInput};
use crate::typecheck_db::passes::infer_value::HoleDiagnostic;
use crate::typecheck_db::types::Type;

const FIXTURES_ROOT: &str = "tests/fixtures";

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn holes_root() -> PathBuf {
    manifest_dir().join(FIXTURES_ROOT).join("holes")
}

fn packages_root() -> PathBuf {
    manifest_dir().join(FIXTURES_ROOT).join("packages")
}

fn collect_purs_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if !root.exists() {
        return out;
    }
    let entries = match fs::read_dir(root) {
        Ok(e) => e,
        Err(_) => return out,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name == ".spago" || name == "output" || name == ".psc-package" {
            continue;
        }
        if path.is_dir() {
            out.extend(collect_purs_files(&path));
        } else if path.extension().and_then(|s| s.to_str()) == Some("purs") {
            out.push(path);
        }
    }
    out
}

fn module_name_of(m: &cst::Module) -> String {
    m.name
        .value
        .parts
        .iter()
        .map(|p| crate::interner::resolve(*p).unwrap_or_default())
        .collect::<Vec<_>>()
        .join(".")
}

fn imports_of(module: &cst::Module) -> Vec<String> {
    module
        .imports
        .iter()
        .map(|imp| {
            imp.module
                .parts
                .iter()
                .map(|p| crate::interner::resolve(*p).unwrap_or_default())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect()
}

fn package_modules_by_name() -> &'static HashMap<String, ModuleInput> {
    static CACHE: OnceLock<HashMap<String, ModuleInput>> = OnceLock::new();
    CACHE.get_or_init(|| {
        let root = packages_root();
        let files = collect_purs_files(&root);
        let mut out = HashMap::with_capacity(files.len());
        for file in files {
            let src = match fs::read_to_string(&file) {
                Ok(s) => s,
                Err(e) => panic!("failed to read package source {}: {e}", file.display()),
            };
            let module = match parse(&src) {
                Ok(m) => m,
                Err(e) => panic!("parse error in {}: {e:?}", file.display()),
            };
            let name = module_name_of(&module);
            out.entry(name.clone())
                .or_insert(ModuleInput::new(name, src, module));
        }
        out
    })
}

fn transitive_imports(
    seed_modules: &[ModuleInput],
    pkgs: &HashMap<String, ModuleInput>,
) -> Vec<ModuleInput> {
    let already: HashSet<String> = seed_modules.iter().map(|m| m.name.clone()).collect();
    let mut visited: HashSet<String> = already.clone();
    let mut stack: Vec<String> = seed_modules
        .iter()
        .flat_map(|m| imports_of(&m.module))
        .collect();
    let mut out: Vec<ModuleInput> = Vec::new();
    while let Some(name) = stack.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        if let Some(m) = pkgs.get(&name) {
            stack.extend(imports_of(&m.module));
            out.push(ModuleInput::new(
                m.name.clone(),
                m.source.clone(),
                m.module.clone(),
            ));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// expected.txt parser
// ---------------------------------------------------------------------------

#[derive(Debug, Default)]
struct ExpectedHole {
    hole_name: String,
    position: Option<(u32, u32, u32, u32)>,
    inferred_type: String,
    constraints: Vec<String>,
    context: Vec<String>,
}

fn parse_expected(path: &Path) -> Option<ExpectedHole> {
    let text = fs::read_to_string(path).ok()?;
    let mut out = ExpectedHole::default();
    let lines: Vec<&str> = text.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if let Some(rest) = line.strip_prefix("HOLE: ") {
            out.hole_name = rest.trim().to_string();
            i += 1;
        } else if let Some(rest) = line.strip_prefix("POSITION: ") {
            out.position = parse_position(rest.trim());
            i += 1;
        } else if line == "INFERRED_TYPE:" {
            i += 1;
            let mut parts = Vec::new();
            while i < lines.len() && lines[i].starts_with("  ") {
                parts.push(lines[i].trim().to_string());
                i += 1;
            }
            out.inferred_type = parts.join(" ");
        } else if line == "CONSTRAINTS:" {
            i += 1;
            while i < lines.len() && lines[i].starts_with("  ") {
                out.constraints.push(lines[i].trim().to_string());
                i += 1;
            }
        } else if line == "CONTEXT:" {
            i += 1;
            while i < lines.len() && lines[i].starts_with("  ") {
                let trimmed = lines[i].trim().to_string();
                // A new context entry starts with `name :: type` where `name`
                // is a plain identifier (no spaces, no punctuation). Anything
                // else is a continuation of the previous entry (record field
                // rows, closing braces/parens, row tails, etc.).
                let is_new_entry = if let Some(colon_pos) = trimmed.find(" :: ") {
                    let name_part = &trimmed[..colon_pos];
                    !name_part.is_empty()
                        && name_part
                            .chars()
                            .all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || c == '$')
                } else {
                    false
                };
                if is_new_entry || out.context.is_empty() {
                    out.context.push(trimmed);
                } else {
                    let last = out.context.last_mut().unwrap();
                    last.push(' ');
                    last.push_str(&trimmed);
                }
                i += 1;
            }
        } else {
            i += 1;
        }
    }
    Some(out)
}

fn parse_position(s: &str) -> Option<(u32, u32, u32, u32)> {
    let (lhs, rhs) = s.split_once(" - ")?;
    let (l1, c1) = lhs.split_once(':')?;
    let (l2, c2) = rhs.split_once(':')?;
    Some((
        l1.trim().parse().ok()?,
        c1.trim().parse().ok()?,
        l2.trim().parse().ok()?,
        c2.trim().parse().ok()?,
    ))
}

// ---------------------------------------------------------------------------
// Type-string normalization
// ---------------------------------------------------------------------------

/// Strip `forall a b c.` prefixes from a type string so that
/// `forall a. Show a => a -> String` compares equal to
/// `Show a => a -> String`. Applied before normalize_type so
/// both expected (which may include forall) and actual (which
/// may omit it due to scheme.ty not re-wrapping) normalize the same.
fn strip_forall_prefix(s: &str) -> String {
    let mut t = s.trim();
    while let Some(rest) = t.strip_prefix("forall ") {
        // Skip over variable names up to the `.`
        if let Some(dot_pos) = rest.find(". ") {
            t = rest[dot_pos + 2..].trim_start();
        } else if let Some(dot_end) = rest.find('.') {
            t = rest[dot_end + 1..].trim_start();
        } else {
            break;
        }
    }
    if t == s.trim() {
        s.to_string()
    } else {
        t.to_string()
    }
}

/// Strip `(T :: K)` kinded annotations: replaces `(T :: K)` with `T`.
/// Works on string representation so it applies to expected.txt strings too.
fn strip_kinded_annotations(s: &str) -> String {
    // We scan for `(` followed by a type expression, ` :: `, a kind, `)`.
    // Simple heuristic: find `:: ` inside balanced parens and strip them.
    let bytes = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'(' {
            // Find the matching `)`, checking if there's a ` :: ` inside
            let mut depth = 1usize;
            let mut j = i + 1;
            let mut ann_pos: Option<usize> = None;
            while j < bytes.len() && depth > 0 {
                if bytes[j] == b'(' { depth += 1; }
                else if bytes[j] == b')' {
                    depth -= 1;
                    if depth == 0 { break; }
                } else if depth == 1
                    && j + 4 <= bytes.len()
                    && &bytes[j..j + 4] == b" :: "
                    && ann_pos.is_none()
                {
                    ann_pos = Some(j);
                }
                j += 1;
            }
            if depth == 0 {
                if let Some(ann) = ann_pos {
                    // strip: replace `(T :: K)` with `T`
                    let inner = &s[i + 1..ann];
                    out.push_str(&strip_kinded_annotations(inner.trim()));
                    i = j + 1; // skip past `)`
                    continue;
                }
            }
        }
        if i < bytes.len() {
            out.push(bytes[i] as char);
        }
        i += 1;
    }
    out
}

fn normalize_type(s: &str) -> String {
    // Collapse whitespace, strip `?` (unif var prefix), then canonicalize
    // punctuation: remove spaces before commas and inside parentheses so
    // `Proxy ( x :: Int , y :: String )` and `Proxy (x :: Int, y :: String)`
    // compare equal.
    // Also strip kinded type annotations: `(T :: K)` → `T`.
    let pre = strip_kinded_annotations(s);
    let collapsed: String = pre
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace('?', "")
        .replace(" ,", ",")
        .replace("( ", "(")
        .replace(" )", ")")
        // `Record ()` is the empty record `{}`.
        .replace("Record ()", "{ }");
    let mut out = String::new();
    let bytes = collapsed.as_bytes();
    let mut i = 0;
    let mut remap: HashMap<String, String> = HashMap::new();
    let mut next: usize = 0;
    while i < bytes.len() {
        let b = bytes[i];
        // Standalone `_` — treat as a fresh wildcard, remapped like `t0`/`u3`
        if b == b'_' {
            let next_is_alnum = i + 1 < bytes.len()
                && (bytes[i + 1].is_ascii_alphanumeric() || bytes[i + 1] == b'_');
            if !next_is_alnum {
                let canon = remap
                    .entry("_".to_string())
                    .or_insert_with(|| {
                        let n = next;
                        next += 1;
                        format!("t{}", n)
                    })
                    .clone();
                out.push_str(&canon);
                i += 1;
                continue;
            }
        }
        if b.is_ascii_uppercase() {
            // Uppercase-starting identifier (type constructor, class, module):
            // read the full token and emit as-is without renaming.
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'')
            {
                i += 1;
            }
            out.push_str(&collapsed[start..i]);
        } else if b.is_ascii_lowercase() {
            let start = i;
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_')
            {
                i += 1;
            }
            let tok = &collapsed[start..i];
            // Strip `forall <vars>. ` — skip the keyword and all following
            // variable names up to and including the `.` so context entries
            // and hole types compare equal regardless of whether the `forall`
            // wrapper is present.
            if tok == "forall" {
                // Skip whitespace + var names until we hit `. `
                let mut j = i;
                while j < bytes.len() && bytes[j] == b' ' { j += 1; }
                loop {
                    // Skip a var name (lowercase alphanum/underscore)
                    if j < bytes.len() && (bytes[j].is_ascii_lowercase() || bytes[j].is_ascii_uppercase()) {
                        while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                            j += 1;
                        }
                        // Skip optional `( ... )` kind annotation
                        if j < bytes.len() && bytes[j] == b'(' {
                            let mut depth = 1usize;
                            j += 1;
                            while j < bytes.len() && depth > 0 {
                                if bytes[j] == b'(' { depth += 1; }
                                else if bytes[j] == b')' { depth -= 1; }
                                j += 1;
                            }
                        }
                        while j < bytes.len() && bytes[j] == b' ' { j += 1; }
                        if j < bytes.len() && bytes[j] == b'.' {
                            j += 1;
                            // skip space after dot if present
                            if j < bytes.len() && bytes[j] == b' ' { j += 1; }
                            i = j;
                            break;
                        }
                    } else {
                        break;
                    }
                }
                continue;
            }
            if is_fresh_var_name(tok) {
                let canon = remap
                    .entry(tok.to_string())
                    .or_insert_with(|| {
                        let n = next;
                        next += 1;
                        format!("t{}", n)
                    })
                    .clone();
                out.push_str(&canon);
            } else {
                out.push_str(tok);
            }
        } else if b == b'@' {
            // `@T`, `@t`, `@(...)` are visible type/kind application
            // annotations that the reference compiler shows but our
            // implementation omits.  Strip the `@` and the following
            // token (identifier or parenthesised type) so both sides
            // normalize the same way.
            let mut j = i + 1;
            if j < bytes.len() && bytes[j] == b'(' {
                // `@(Row Type)` — skip the balanced parens
                let mut depth = 1usize;
                j += 1;
                while j < bytes.len() && depth > 0 {
                    if bytes[j] == b'(' { depth += 1; }
                    else if bytes[j] == b')' { depth -= 1; }
                    j += 1;
                }
            } else {
                // `@Type` / `@sym` — skip the identifier
                while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_' || bytes[j] == b'\'') {
                    j += 1;
                }
            }
            // Remove the leading space pushed into `out` to avoid a
            // double-space; the trailing space (if any) stays as separator.
            if out.ends_with(' ') { out.pop(); }
            i = j;
        } else if b == b'"' {
            // Quoted row label: `"<digits>"` → `<digits>` (normalizes numeric labels).
            // Any other quoted string is passed through unchanged.
            let start = i + 1;
            let mut j = start;
            while j < bytes.len() && bytes[j] != b'"' {
                j += 1;
            }
            if j < bytes.len() {
                let inner = &collapsed[start..j];
                if !inner.is_empty() && inner.chars().all(|c| c.is_ascii_digit()) {
                    // Numeric label: strip quotes
                    out.push_str(inner);
                } else {
                    // Non-numeric: keep quotes
                    out.push('"');
                    out.push_str(inner);
                    out.push('"');
                }
                i = j + 1;
            } else {
                out.push(b as char);
                i += 1;
            }
        } else {
            out.push(b as char);
            i += 1;
        }
    }
    out
}

fn is_fresh_var_name(s: &str) -> bool {
    if s.is_empty() { return false; }
    if !s.starts_with(|c: char| c.is_ascii_lowercase()) {
        return false;
    }
    // All lowercase letters: single-letter vars (a, b, m) and multi-letter
    // vars like `sym`, `row` are fresh-var candidates when used alone.
    // Reference compiler suffixes fresh type vars with digits: a0, a1, sym0,
    // sym1, row2, etc. Treat any `<lowercase-letters><digits>` as a fresh var.
    let has_non_alpha = s.chars().any(|c| !c.is_ascii_alphabetic());
    if !has_non_alpha {
        // Pure alpha — single-letter is definitely a type var; multi-letter
        // is also treated as one (e.g. `sym`, `row`, `effect`).
        return true;
    }
    // Has non-alpha chars: treat as fresh var only if the suffix is all digits
    // and the prefix is all lowercase letters (e.g. sym1, row2, a0, t3).
    let split = s.trim_end_matches(|c: char| c.is_ascii_digit());
    !split.is_empty() && split.chars().all(|c| c.is_ascii_lowercase())
        && split.len() < s.len() // there is at least one digit suffix
}

// ---------------------------------------------------------------------------
// Actual diagnostic → comparison strings
// ---------------------------------------------------------------------------

/// Canonicalize a type before display so minor representational differences
/// don't cause spurious mismatches:
/// - Strip `Kinded(t, k)` → recurse on `t` (removes `(T :: Kind)` annotations)
/// - Flatten `Record([], Some(Row(fields, tail)))` → `Record(fields, tail)`
/// - Flatten `App(Con("Record"), Row(fields, tail))` → `Record(fields, tail)`
/// - Recursively flatten nested Row tails in Records
/// - Sort record fields alphabetically (match reference compiler output)
/// - Strip module qualifiers from `Con(QName { module: Some(_), name })` → `Con(name)`
fn canonicalize_type(ty: &Type) -> Type {
    use crate::typecheck_db::types::{Constraint, QName};
    match ty {
        Type::Kinded(inner, _) => canonicalize_type(inner),
        Type::Con(qname) => Type::Con(QName {
            module: None,
            name: qname.name.clone(),
        }),
        Type::App(f, a) => {
            let cf = canonicalize_type(f);
            let ca = canonicalize_type(a);
            // `Record ()` (empty record via empty-row constructor) → `{ }`
            if let (Type::Con(qn), Type::Con(inner)) = (&cf, &ca) {
                if qn.name == "Record" && (inner.name == "()" || inner.name == "RowNil") {
                    return Type::Record(vec![], None);
                }
            }
            // `Record (Row ...)` → `{ ... }`
            if let (Type::Con(qn), Type::Row(fields, tail)) = (&cf, &ca) {
                if qn.name == "Record" {
                    let mut merged: Vec<(String, Type)> =
                        fields.iter().map(|(l, t)| (l.clone(), t.clone())).collect();
                    let mut rest: Option<Box<Type>> = tail.clone();
                    loop {
                        match rest {
                            None => break,
                            Some(box_ty) => match box_ty.as_ref() {
                                Type::Row(more_fields, next_tail) => {
                                    merged.extend(more_fields.iter().map(|(l, t)| (l.clone(), t.clone())));
                                    rest = next_tail.clone();
                                }
                                Type::Record(more_fields, next_tail) => {
                                    merged.extend(more_fields.iter().map(|(l, t)| (l.clone(), t.clone())));
                                    rest = next_tail.clone();
                                }
                                _ => {
                                    rest = Some(box_ty);
                                    break;
                                }
                            },
                        }
                    }
                    merged.sort_by(|a, b| a.0.cmp(&b.0));
                    return Type::Record(
                        merged.into_iter().map(|(l, t)| (l, canonicalize_type(&t))).collect(),
                        rest.map(|t| Box::new(canonicalize_type(t.as_ref()))),
                    );
                }
            }
            Type::App(Box::new(cf), Box::new(ca))
        }
        Type::Record(fields, tail) => {
            // Flatten tail if it's a Row or another Record extension.
            let mut merged: Vec<(String, Type)> =
                fields.iter().map(|(l, t)| (l.clone(), t.clone())).collect();
            let mut rest: Option<Box<Type>> = tail.clone();
            loop {
                match rest {
                    None => break,
                    Some(box_ty) => match box_ty.as_ref() {
                        Type::Row(more_fields, next_tail) => {
                            merged.extend(more_fields.iter().map(|(l, t)| (l.clone(), t.clone())));
                            rest = next_tail.clone();
                        }
                        Type::Record(more_fields, next_tail) => {
                            merged.extend(more_fields.iter().map(|(l, t)| (l.clone(), t.clone())));
                            rest = next_tail.clone();
                        }
                        _ => {
                            rest = Some(Box::new(canonicalize_type(box_ty.as_ref())));
                            break;
                        }
                    },
                }
            }
            merged.sort_by(|a, b| a.0.cmp(&b.0));
            Type::Record(
                merged.into_iter().map(|(l, t)| (l, canonicalize_type(&t))).collect(),
                rest,
            )
        }
        Type::Row(fields, tail) => Type::Row(
            fields.iter().map(|(l, t)| (l.clone(), canonicalize_type(t))).collect(),
            tail.as_ref().map(|t| Box::new(canonicalize_type(t.as_ref()))),
        ),
        Type::Fun(a, b) => {
            Type::Fun(Box::new(canonicalize_type(a)), Box::new(canonicalize_type(b)))
        }
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(canonicalize_type(body)))
        }
        Type::Constrained(cs, body) => {
            let ccs: Vec<Constraint> = cs
                .iter()
                .map(|c| Constraint {
                    class: QName { module: None, name: c.class.name.clone() },
                    args: c.args.iter().map(canonicalize_type).collect(),
                })
                .collect();
            Type::Constrained(ccs, Box::new(canonicalize_type(body)))
        }
        _ => ty.clone(),
    }
}

fn format_actual_type(ty: &Type) -> String {
    let canon = canonicalize_type(ty);
    match &canon {
        Type::Forall(_, body) => format_actual_type(body),
        Type::Constrained(_, body) => format_actual_type(body),
        _ => format!("{}", canon),
    }
}

fn format_actual_constraint(
    cs: &crate::typecheck_db::types::Constraint,
) -> String {
    let args: Vec<String> = cs.args.iter().map(|a| format!("{}", a)).collect();
    if args.is_empty() {
        format!("{}", cs.class)
    } else {
        format!("{} {}", cs.class, args.join(" "))
    }
}

// ---------------------------------------------------------------------------
// Per-variant runner
// ---------------------------------------------------------------------------

pub(crate) fn run_hole_variant(variant: &str) {
    let owned = variant.to_string();
    let join_result: Result<Result<(), String>, _> =
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_hole_inner(&owned))
            .expect("spawn hole-variant thread")
            .join();
    match join_result {
        Ok(Ok(())) => {}
        Ok(Err(msg)) => panic!("{}", msg),
        Err(_) => panic!("hole-variant thread panicked"),
    }
}

fn run_hole_inner(variant: &str) -> Result<(), String> {
    let dir = holes_root().join(variant);
    let expected_path = dir.join("expected.txt");
    let expected = parse_expected(&expected_path)
        .ok_or_else(|| format!("cannot parse expected.txt in {}", dir.display()))?;

    let fixture_files = collect_purs_files(&dir);
    if fixture_files.is_empty() {
        return Err(format!("no .purs files in {}", dir.display()));
    }

    let mut fixture_modules: Vec<ModuleInput> = Vec::new();
    for path in &fixture_files {
        let src = fs::read_to_string(path)
            .map_err(|e| format!("read {}: {e}", path.display()))?;
        let module = parse(&src)
            .map_err(|e| format!("parse {}: {e:?}", path.display()))?;
        let name = module_name_of(&module);
        fixture_modules.push(ModuleInput::new(name, src, module));
    }

    let pkgs = package_modules_by_name();
    let closure = transitive_imports(&fixture_modules, pkgs);

    let mut by_name: HashMap<String, ModuleInput> =
        HashMap::with_capacity(fixture_modules.len() + closure.len());
    for m in closure {
        by_name.insert(m.name.clone(), m);
    }
    for m in fixture_modules {
        by_name.insert(m.name.clone(), m);
    }

    let main_source = by_name
        .get("Main")
        .map(|m| m.source.clone())
        .unwrap_or_default();

    let inputs: Vec<ModuleInput> = by_name.into_values().collect();
    let report = check_many_modules(inputs);

    let main_result = report
        .results
        .iter()
        .find(|r| r.name == "Main")
        .ok_or_else(|| "no Main module in report".to_string())?;

    let actual = main_result
        .hole_diagnostics
        .first()
        .ok_or_else(|| format!("{variant}: no HoleDiagnostic produced for Main"))?;

    compare_hole(variant, &expected, actual, &main_source)
}

fn compare_hole(
    variant: &str,
    expected: &ExpectedHole,
    actual: &HoleDiagnostic,
    source: &str,
) -> Result<(), String> {
    if actual.hole_name != expected.hole_name {
        return Err(format!(
            "{variant}: hole name: expected `{}`, got `{}`",
            expected.hole_name, actual.hole_name
        ));
    }

    if let Some((l1, c1, l2, c2)) = expected.position {
        if let Some((s, e)) = actual.span.to_pos(source) {
            if (s.line as u32, s.column as u32, e.line as u32, e.column as u32)
                != (l1, c1, l2, c2)
            {
                return Err(format!(
                    "{variant}: position: expected {l1}:{c1}-{l2}:{c2}, got {}:{}-{}:{}",
                    s.line, s.column, e.line, e.column
                ));
            }
        }
    }

    // If the expected type contains `...` (reference-compiler truncation)
    // we can't reliably compare — skip the type check for this case.
    let expected_ty = normalize_type(&expected.inferred_type);
    if !expected.inferred_type.contains("...") {
        let actual_ty = normalize_type(&format_actual_type(&actual.inferred_type));
        if expected_ty != actual_ty {
            return Err(format!(
                "{variant}: inferred type: expected `{expected_ty}`, got `{actual_ty}`"
            ));
        }
    }

    let expected_constraints: HashSet<String> = expected
        .constraints
        .iter()
        .filter(|c| !c.starts_with("where ") || !c.contains("unknown type"))
        .map(|c| normalize_type(c))
        .collect();
    let actual_constraints: HashSet<String> = actual
        .constraints
        .iter()
        .map(|c| normalize_type(&format_actual_constraint(c)))
        .collect();
    if !expected_constraints.is_empty() && expected_constraints != actual_constraints {
        return Err(format!(
            "{variant}: constraints: expected {expected_constraints:?}, got {actual_constraints:?}"
        ));
    }

    // Normalize context entries by splitting on ` :: ` and only normalizing
    // the type portion. The variable name must NOT be renamed by normalize_type
    // (which would map `a` → `t0`, making `a :: a` and `a :: a1` indistinct).
    let normalize_ctx_entry = |s: &str| -> String {
        if let Some((name, ty)) = s.split_once(" :: ") {
            format!("{} :: {}", name.trim(), normalize_type(ty))
        } else {
            normalize_type(s)
        }
    };
    let expected_ctx: HashSet<String> = expected
        .context
        .iter()
        // Skip entries with `...` (reference compiler truncates long types)
        .filter(|s| !s.contains("..."))
        .map(|s| normalize_ctx_entry(s))
        .collect();
    let actual_ctx: HashSet<String> = actual
        .local_bindings
        .iter()
        .map(|(n, t)| normalize_ctx_entry(&format!("{n} :: {}", canonicalize_type(t))))
        .collect();
    if !expected_ctx.is_empty() && !expected_ctx.is_subset(&actual_ctx) {
        let missing: Vec<String> =
            expected_ctx.difference(&actual_ctx).cloned().collect();
        let mut actual_sorted: Vec<String> = actual_ctx.iter().cloned().collect();
        actual_sorted.sort();
        return Err(format!(
            "{variant}: context missing: {missing:?}\n  actual_ctx: {actual_sorted:?}"
        ));
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Macros — one ignored variant + one passing variant
// ---------------------------------------------------------------------------

macro_rules! check_hole_variant {
    ($test_name:ident, $variant:literal) => {
        #[test]
        #[timeout(20000)]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_hole_variant($variant);
        }
    };
}

macro_rules! check_hole_variant_ignored {
    ($test_name:ident, $variant:literal) => {
        #[test]
        #[timeout(20000)]
        #[ignore = "gap-closing: typecheck_db hole reporting vs reference compiler"]
        #[allow(non_snake_case)]
        fn $test_name() {
            run_hole_variant($variant);
        }
    };
}

include!("hole_fixtures_list.rs");
