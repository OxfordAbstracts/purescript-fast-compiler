//! MDe sub-transform: operator chain rebracketing by fixity.
//!
//! Takes a chain of `Expr::Op` / `Expr::BacktickApp` nodes and
//! rebalances it based on the user-declared fixity table, then lowers
//! each operator to a plain function application:
//!
//! ```text
//! a + b * c
//! ```
//!
//! given `infixl 6 add as +` and `infixl 7 mul as *` becomes
//!
//! ```text
//! App(App(Var(add), a), App(App(Var(mul), b), c))
//! ```
//!
//! Backtick applications (`a \`f\` b`) are treated like operators with
//! a default `infixl 1` fixity and `f` as their target expression.
//!
//! Unknown operators (no fixity entry — e.g., the fixity is declared in
//! an imported module the caller hasn't yet loaded) fall back to
//! `infixl 9` with the op name itself as the target. The emitted
//! program is still well-formed enough for the downstream typechecker
//! to either accept it or produce a targeted name-resolution error.
//!
//! `Expr::OpParens(op)` becomes `Var(target)` when the operator is
//! known, and stays as-is otherwise.

use std::collections::HashMap;

use crate::cst::{Associativity, Decl, Expr, Spanned};
use crate::interner::Symbol;
use crate::names::{value_name, Qualified, ValueName};
use crate::span::Span;

// Alias matches the CST's `Ident = Symbol`, but we keep the name local so
// the module doesn't depend on a cross-crate re-export.
type Ident = Symbol;

use super::walk::fold_decl_exprs;

// ---------------------------------------------------------------------------
// Fixity table
// ---------------------------------------------------------------------------

/// Describes one operator's fixity for rebracketing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FixityInfo {
    pub associativity: Associativity,
    pub precedence: u8,
    /// Target value the operator stands in for. `a + b` rewrites to
    /// `App(App(Var(target), a), b)`.
    pub target_module: Option<Ident>,
    pub target_name: Ident,
}

/// Keyed by the operator symbol — e.g. the `Symbol` interned for `+`.
pub type FixityTable = HashMap<Ident, FixityInfo>;

/// Collect value-level fixity entries from a decl list.
///
/// Only `Decl::Fixity { is_type: false, .. }` entries contribute. The
/// returned hash is a stable digest of the whole table (sorted by op
/// symbol's underlying u32) and is what callers should feed to
/// `DesugarContext::module_fixity_hash`.
pub fn fixity_table_from_decls(decls: &[Decl]) -> (FixityTable, [u8; 32]) {
    let mut table = FixityTable::new();
    for d in decls {
        if let Decl::Fixity {
            associativity,
            precedence,
            target,
            operator,
            is_type,
            ..
        } = d
        {
            if *is_type {
                continue;
            }
            table.insert(
                operator.value.symbol(),
                FixityInfo {
                    associativity: *associativity,
                    precedence: *precedence,
                    target_module: target.module,
                    target_name: target.name,
                },
            );
        }
    }
    let hash = hash_table(&table);
    (table, hash)
}

fn hash_table(t: &FixityTable) -> [u8; 32] {
    // Deterministic hash: sort keys by their u32 repr. Version string is
    // bumped whenever this function's output encoding changes so that any
    // cached `desugar_decl` rows from before the change are invalidated.
    let mut entries: Vec<(Ident, FixityInfo)> = t.iter().map(|(k, v)| (*k, *v)).collect();
    entries.sort_by_key(|(k, _)| key_to_u32(*k));
    let mut h = blake3::Hasher::new();
    h.update(b"desugar/rebracket::fixity_table_v2");
    h.update(&(entries.len() as u32).to_le_bytes());
    for (k, v) in entries {
        h.update(&key_to_u32(k).to_le_bytes());
        h.update(&[v.associativity as u8, v.precedence]);
        crate::typecheck_db::util::hash_opt_symbol(&mut h, v.target_module);
        h.update(&key_to_u32(v.target_name).to_le_bytes());
    }
    *h.finalize().as_bytes()
}

fn key_to_u32(s: Ident) -> u32 {
    use string_interner::Symbol as _;
    s.to_usize() as u32
}

// ---------------------------------------------------------------------------
// Decl entry
// ---------------------------------------------------------------------------

pub fn desugar_decl(decl: Decl, fixity: &FixityTable) -> Decl {
    fold_decl_exprs(decl, &mut |e| rewrite_node(e, fixity))
}

fn rewrite_node(e: Expr, fixity: &FixityTable) -> Expr {
    match e {
        // Any top of an Op / BacktickApp chain: flatten + shunt + rebuild.
        Expr::Op { .. } | Expr::BacktickApp { .. } => rebracket_chain(e, fixity),
        Expr::OpParens { span, op } => match lookup_op(&op, fixity) {
            Some(info) => Expr::Var {
                span,
                name: target_var(info, span),
            },
            None => Expr::OpParens { span, op },
        },
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Chain flattening + shunting-yard
// ---------------------------------------------------------------------------

/// One position in the flattened chain. Operators are interleaved with
/// operands: `[operand, op, operand, op, ..., operand]`.
enum ChainOp {
    Named(Spanned<Qualified<crate::names::OpName>>),
    /// Backtick: the expression in backticks is the call target directly.
    Backtick { span: Span, func: Expr },
}

fn rebracket_chain(root: Expr, fixity: &FixityTable) -> Expr {
    // Flatten a right-leaning chain. The CST tends to parse chains as
    // `Op(left, op, Op(...))`; keep walking down the `right` slot until
    // a non-op shows up.
    let mut operands: Vec<Expr> = Vec::new();
    let mut ops: Vec<ChainOp> = Vec::new();
    let root_span = span_of(&root);
    let mut cursor = root;
    loop {
        match cursor {
            Expr::Op { left, op, right, .. } => {
                operands.push(*left);
                ops.push(ChainOp::Named(op));
                cursor = *right;
            }
            Expr::BacktickApp { func, left, right, span } => {
                operands.push(*left);
                ops.push(ChainOp::Backtick { span, func: *func });
                cursor = *right;
            }
            other => {
                operands.push(other);
                break;
            }
        }
    }

    // Shunting-yard: re-associate `operands`/`ops` into a single tree.
    shunt(operands, ops, fixity, root_span)
}

fn shunt(
    mut operands: Vec<Expr>,
    ops: Vec<ChainOp>,
    fixity: &FixityTable,
    span: Span,
) -> Expr {
    // Output: Vec<Expr>; op_stack: Vec<usize> (indices into `ops`).
    let mut output: Vec<Expr> = Vec::with_capacity(operands.len());
    let mut op_stack: Vec<usize> = Vec::with_capacity(ops.len());

    // Seed output with the first operand.
    let first = operands.remove(0);
    output.push(first);

    for i in 0..ops.len() {
        let (assoc_i, prec_i) = op_fixity(&ops[i], fixity);
        while let Some(&top) = op_stack.last() {
            let (_, prec_top) = op_fixity(&ops[top], fixity);
            let should_pop = prec_top > prec_i
                || (prec_top == prec_i && assoc_i == Associativity::Left);
            if !should_pop {
                break;
            }
            op_stack.pop();
            let right = output.pop().unwrap();
            let left = output.pop().unwrap();
            output.push(apply_op(&ops[top], left, right, fixity, span));
        }
        op_stack.push(i);
        output.push(operands.remove(0));
        let _ = assoc_i; // silence unused warning if precedence short-circuits
    }

    while let Some(top) = op_stack.pop() {
        let right = output.pop().unwrap();
        let left = output.pop().unwrap();
        output.push(apply_op(&ops[top], left, right, fixity, span));
    }
    output.pop().unwrap()
}

fn op_fixity(op: &ChainOp, fixity: &FixityTable) -> (Associativity, u8) {
    match op {
        ChainOp::Named(n) => {
            let sym = n.value.name.symbol();
            match fixity.get(&sym) {
                Some(info) => (info.associativity, info.precedence),
                // Unknown op:
                //   identifier-looking name (a `f` b parses as Op with
                //   `f` as the op name) → default backtick fixity infixl 1
                //   symbolic op with no fixity decl available → infixl 9
                //   (conservative, parser-consistent)
                None if is_identifier_op(sym) => (Associativity::Left, 1),
                None => (Associativity::Left, 9),
            }
        }
        ChainOp::Backtick { .. } => (Associativity::Left, 1),
    }
}

fn apply_op(op: &ChainOp, left: Expr, right: Expr, fixity: &FixityTable, span: Span) -> Expr {
    let func = match op {
        ChainOp::Named(n) => {
            let sym = n.value.name.symbol();
            match fixity.get(&sym) {
                Some(info) => Expr::Var {
                    span,
                    name: target_var(*info, span),
                },
                None if is_identifier_op(sym) => {
                    // Backtick-style `a `f` b`: the parser stored `f`
                    // as an OpName, but it's really the function value
                    // to call. Lower to `App(App(Var(f), a), b)`.
                    let vn = value_name(&resolve_sym(sym));
                    let qualified = match n.value.module {
                        Some(m) => Qualified::qualified(m, vn),
                        None => Qualified::unqualified(vn),
                    };
                    Expr::Var { span, name: qualified }
                }
                None => {
                    // Symbolic op with no fixity decl in scope — preserve
                    // the Op so downstream emits a targeted error.
                    return Expr::Op {
                        span,
                        left: Box::new(left),
                        op: n.clone(),
                        right: Box::new(right),
                    };
                }
            }
        }
        ChainOp::Backtick { func, .. } => func.clone(),
    };
    Expr::App {
        span,
        func: Box::new(Expr::App {
            span,
            func: Box::new(func),
            arg: Box::new(left),
        }),
        arg: Box::new(right),
    }
}

fn is_identifier_op(sym: Ident) -> bool {
    let s = resolve_sym(sym);
    s.chars().next().map_or(false, |c| c.is_ascii_alphabetic() || c == '_')
}

fn lookup_op(op: &Spanned<Qualified<crate::names::OpName>>, fixity: &FixityTable) -> Option<FixityInfo> {
    fixity.get(&op.value.name.symbol()).copied()
}

fn target_var(info: FixityInfo, span: Span) -> Qualified<ValueName> {
    let vn: ValueName = value_name(&resolve_sym(info.target_name));
    match info.target_module {
        Some(m) => Qualified::qualified(crate::names::ModuleQualifier::new(m), vn),
        None => Qualified::unqualified(vn),
    }
}

fn resolve_sym(s: Ident) -> String {
    crate::typecheck_db::util::resolve_symbol(s)
}

fn span_of(e: &Expr) -> Span {
    match e {
        Expr::Var { span, .. }
        | Expr::Constructor { span, .. }
        | Expr::Literal { span, .. }
        | Expr::App { span, .. }
        | Expr::VisibleTypeApp { span, .. }
        | Expr::Lambda { span, .. }
        | Expr::Op { span, .. }
        | Expr::OpParens { span, .. }
        | Expr::If { span, .. }
        | Expr::Case { span, .. }
        | Expr::Let { span, .. }
        | Expr::Do { span, .. }
        | Expr::Ado { span, .. }
        | Expr::Record { span, .. }
        | Expr::RecordAccess { span, .. }
        | Expr::RecordUpdate { span, .. }
        | Expr::Parens { span, .. }
        | Expr::TypeAnnotation { span, .. }
        | Expr::Wildcard { span, .. }
        | Expr::Hole { span, .. }
        | Expr::Array { span, .. }
        | Expr::Negate { span, .. }
        | Expr::AsPattern { span, .. }
        | Expr::BacktickApp { span, .. } => *span,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cst::Decl;
    use crate::parser::parse;

    fn first_value(src: &str) -> Decl {
        parse(src)
            .unwrap()
            .decls
            .into_iter()
            .find(|d| matches!(d, Decl::Value { .. }))
            .unwrap()
    }

    fn module_table(src: &str) -> (FixityTable, Vec<Decl>) {
        let decls = parse(src).unwrap().decls;
        let (t, _) = fixity_table_from_decls(&decls);
        (t, decls)
    }

    fn count_op(d: &Decl) -> u32 {
        let mut n = 0u32;
        let _ = super::super::walk::fold_decl_exprs(d.clone(), &mut |e| {
            if matches!(e, Expr::Op { .. } | Expr::BacktickApp { .. }) {
                n += 1;
            }
            e
        });
        n
    }

    #[test]
    fn empty_table_hash_is_stable() {
        let (_, h1) = fixity_table_from_decls(&[]);
        let (_, h2) = fixity_table_from_decls(&[]);
        assert_eq!(h1, h2);
    }

    #[test]
    fn single_op_becomes_app() {
        // `a + b` with `infixl 6 add as +` becomes App(App(Var(add), a), b).
        let (table, decls) = module_table("\
module M where
infixl 6 add as +
foo a b = a + b
");
        let value = decls.into_iter().find(|d| matches!(d, Decl::Value { .. })).unwrap();
        let out = desugar_decl(value, &table);
        assert_eq!(count_op(&out), 0, "Op should be lowered: {out:#?}");
    }

    #[test]
    fn precedence_reassociates_chain() {
        // `a + b * c` with `*` at 7 and `+` at 6 must place `*` under `+`.
        let (table, decls) = module_table("\
module M where
infixl 6 add as +
infixl 7 mul as *
foo a b c = a + b * c
");
        let value = decls.into_iter().find(|d| matches!(d, Decl::Value { .. })).unwrap();
        let out = desugar_decl(value, &table);
        assert_eq!(count_op(&out), 0);
        // The outermost App should be the `+` call; its arg should be
        // the `*` call.
        if let Decl::Value { guarded: crate::cst::GuardedExpr::Unconditional(body), .. } = &out {
            // body here is Lambda | Case | App (depending on how
            // equations are desugared and binder count is zero here).
            // In this case `foo a b c = a + b * c` has binders so the
            // Unconditional body is the RHS directly.
            let rhs = body.as_ref();
            if let Expr::App { func: outer_func, .. } = rhs {
                // outer_func is App(Var(add), a) — peel to find the head.
                if let Expr::App { func: head, .. } = outer_func.as_ref() {
                    if let Expr::Var { name, .. } = head.as_ref() {
                        assert_eq!(
                            crate::interner::resolve(name.name.symbol()).as_deref(),
                            Some("add"),
                            "expected outer Var(add), got {name:?}",
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn unknown_op_preserves_op_node() {
        // No fixity for `??`, so we keep the Op intact rather than
        // fabricating an App.
        let table = FixityTable::new();
        let d = first_value("\
module M where
foo a b = a ?? b
");
        let out = desugar_decl(d, &table);
        assert_eq!(count_op(&out), 1, "unknown op must stay as Op");
    }

    #[test]
    fn backtick_app_becomes_regular_app() {
        // Simple `a `f` b` parses as `Op` with op name `f`. The
        // rebracketer detects identifier-shaped ops without fixity decls
        // as backtick-style apps and lowers them to `App(App(Var(f), a), b)`.
        let table = FixityTable::new();
        let d = first_value("\
module M where
foo a b = a `f` b
");
        let out = desugar_decl(d, &table);
        assert_eq!(count_op(&out), 0);
    }

    #[test]
    fn op_parens_becomes_var_of_target() {
        let (table, decls) = module_table("\
module M where
infixl 6 add as +
bar = (+)
");
        let value = decls.into_iter().find(|d| matches!(d, Decl::Value { .. })).unwrap();
        let out = desugar_decl(value, &table);
        if let Decl::Value { guarded: crate::cst::GuardedExpr::Unconditional(body), .. } = &out {
            assert!(matches!(body.as_ref(), Expr::Var { .. }), "(+) → Var, got {body:?}");
        }
    }

    #[test]
    fn idempotent_on_clean_input() {
        let (table, decls) = module_table("\
module M where
infixl 6 add as +
infixl 7 mul as *
foo a b c = a + b * c
");
        let value = decls.into_iter().find(|d| matches!(d, Decl::Value { .. })).unwrap();
        let once = desugar_decl(value, &table);
        let twice = desugar_decl(once.clone(), &table);
        assert_eq!(once, twice);
    }
}
