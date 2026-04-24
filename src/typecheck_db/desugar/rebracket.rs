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
    use crate::cst::{GuardedExpr, Guard, GuardPattern, LetBinding};
    match decl {
        Decl::Value { name, binders, guarded, where_clause, span, doc_comments } => {
            let binders = binders.into_iter().map(|b| rewrite_binder(b, fixity)).collect();
            let guarded = match guarded {
                GuardedExpr::Unconditional(e) => {
                    GuardedExpr::Unconditional(Box::new(rewrite_expr(*e, fixity)))
                }
                GuardedExpr::Guarded(gs) => GuardedExpr::Guarded(
                    gs.into_iter()
                        .map(|g| Guard {
                            span: g.span,
                            patterns: g
                                .patterns
                                .into_iter()
                                .map(|p| match p {
                                    GuardPattern::Boolean(e) => {
                                        GuardPattern::Boolean(Box::new(rewrite_expr(*e, fixity)))
                                    }
                                    GuardPattern::Pattern(b, e) => GuardPattern::Pattern(
                                        rewrite_binder(b, fixity),
                                        Box::new(rewrite_expr(*e, fixity)),
                                    ),
                                })
                                .collect(),
                            expr: Box::new(rewrite_expr(*g.expr, fixity)),
                        })
                        .collect(),
                ),
            };
            let where_clause: Vec<LetBinding> =
                super::multi_eq::merge_let_bindings(where_clause)
                    .into_iter()
                    .map(|b| match b {
                        LetBinding::Value { span, binder, expr } => LetBinding::Value {
                            span,
                            binder: rewrite_binder(binder, fixity),
                            expr: rewrite_expr(expr, fixity),
                        },
                        LetBinding::Signature { span, name, ty } => {
                            LetBinding::Signature { span, name, ty }
                        }
                    })
                    .collect();
            Decl::Value { name, binders, guarded, where_clause, span, doc_comments }
        }
        // Instance and Derive declarations hold `Decl::Value`
        // members. Without recursing, `append f g x = f x <> g x`
        // inside `instance semigroupFn` keeps its `Op` node and
        // trips the IR lowering's residual-operator guard.
        Decl::Instance {
            span,
            name,
            constraints,
            class_name,
            types,
            members,
            chain,
            doc_comments,
        } => Decl::Instance {
            span,
            name,
            constraints,
            class_name,
            types,
            members: members.into_iter().map(|m| desugar_decl(m, fixity)).collect(),
            chain,
            doc_comments,
        },
        other => other,
    }
}

/// Lower every `Binder::Op` (e.g. `x : xs`) into a
/// `Binder::Constructor` whose head is the operator's target.
/// Treats symbolic operator binders as constructor patterns
/// (PureScript's convention — only constructors can be used in
/// pattern position) and recurses into every nested binder slot
/// so the output contains no `Binder::Op` anywhere. The IR
/// lowering assumes this invariant and returns
/// `LoweringError::ResidualBinderOperator` if it sees one.
///
/// The fixity table resolves operator aliases like `infixr 6
/// Cons as :` so `x : xs` lowers to
/// `Binder::Constructor { name: Cons, .. }` rather than a
/// constructor literally named `:` (which would be unbound at
/// inference time).
fn rewrite_binder(b: crate::cst::Binder, fixity: &FixityTable) -> crate::cst::Binder {
    use crate::cst::Binder;
    use crate::names::{ConstructorName, Qualified};
    match b {
        Binder::Op { span, left, op, right } => {
            let left = rewrite_binder(*left, fixity);
            let right = rewrite_binder(*right, fixity);
            let op_sym = op.value.name.symbol();
            let (ctor_str, ctor_module) = match fixity.get(&op_sym) {
                Some(info) => (resolve_sym(info.target_name), info.target_module),
                None => (resolve_sym(op_sym), op.value.module.map(|m| m.symbol())),
            };
            let cn = ConstructorName::new(crate::interner::intern(&ctor_str));
            let name = match ctor_module {
                Some(m) => Qualified::qualified(crate::names::ModuleQualifier::new(m), cn),
                None => Qualified::unqualified(cn),
            };
            Binder::Constructor { span, name, args: vec![left, right] }
        }
        Binder::Constructor { span, name, args } => Binder::Constructor {
            span,
            name,
            args: args.into_iter().map(|b| rewrite_binder(b, fixity)).collect(),
        },
        Binder::Record { span, fields } => Binder::Record {
            span,
            fields: fields
                .into_iter()
                .map(|f| crate::cst::RecordBinderField {
                    span: f.span,
                    label: f.label,
                    binder: f.binder.map(|b| rewrite_binder(b, fixity)),
                })
                .collect(),
        },
        Binder::As { span, name, binder } => Binder::As {
            span,
            name,
            binder: Box::new(rewrite_binder(*binder, fixity)),
        },
        Binder::Parens { span, binder } => Binder::Parens {
            span,
            binder: Box::new(rewrite_binder(*binder, fixity)),
        },
        Binder::Array { span, elements } => Binder::Array {
            span,
            elements: elements.into_iter().map(|b| rewrite_binder(b, fixity)).collect(),
        },
        Binder::Typed { span, binder, ty } => Binder::Typed {
            span,
            binder: Box::new(rewrite_binder(*binder, fixity)),
            ty,
        },
        leaf @ (Binder::Wildcard { .. }
        | Binder::Var { .. }
        | Binder::Literal { .. }) => leaf,
    }
}

/// Pre-order rewrite for Op chains. The CST parses
/// `a == b || c == d` as a right-leaning chain
/// `Op(a, ==, Op(b, ||, Op(c, ==, d)))`. A plain post-order
/// walker would lower the inner `Op(c, ==, d)` to `App` first,
/// hiding the outer chain's `==` entirely and leaving `||` to
/// capture `b` as its left operand. Flattening the whole chain
/// at the outermost Op preserves precedence; we then recurse
/// into each individual operand to handle nested expressions.
fn rewrite_expr(e: Expr, fixity: &FixityTable) -> Expr {
    rewrite_expr_ctx(e, fixity, false)
}

/// `in_parens` is true when the expression being rewritten is
/// the immediate body of an `Expr::Parens`. Only inside parens
/// can a chain wildcard be lifted as an operator section — in
/// bare position (e.g. `test = 1 + 2 * _`) the user must wrap
/// the section explicitly, and leaving the wildcard unlifted
/// surfaces as `IncorrectAnonymousArgument` downstream.
fn rewrite_expr_ctx(e: Expr, fixity: &FixityTable, in_parens: bool) -> Expr {
    match e {
        Expr::Op { .. } | Expr::BacktickApp { .. } => {
            let (mut operands_raw, ops_raw, root_span) = flatten_chain(e);
            // `::` has the lowest precedence in PureScript — lower
            // than any user-declared operator. The parser attaches
            // a trailing annotation to the rightmost chain operand,
            // so `a <<< b :: T` arrives as
            // `Op(a, <<<, TypeAnnotation(b, T))`. Extract the
            // annotation here so it wraps the whole shunted chain
            // rather than just `b`. Without this, the type
            // annotation binds tighter than every operator.
            let mut trailing_annotation: Option<(Span, crate::cst::TypeExpr)> = None;
            if let Some(last) = operands_raw.last() {
                if matches!(last, Expr::TypeAnnotation { .. }) {
                    if let Some(Expr::TypeAnnotation { span, expr, ty }) =
                        operands_raw.pop()
                    {
                        trailing_annotation = Some((span, ty));
                        operands_raw.push(*expr);
                    }
                }
            }
            let mut operands: Vec<Expr> = operands_raw
                .into_iter()
                .map(|x| rewrite_expr(x, fixity))
                .collect();
            // Chain-level section lifting: any leaf wildcard in
            // the flattened chain becomes a fresh lambda param,
            // bound around the whole shunted result. This is the
            // only place sections can be lifted from an *operator
            // chain* correctly — doing it per-Op post-order (as
            // `sections::desugar_decl` used to) wraps the inner
            // chain-fragment in a lambda, breaking the parent
            // operator's left-right structure. `(3 * 2 + _)`
            // needs `\x -> 3 * 2 + x`, not `3 * (\x -> 2 + x)`.
            //
            // Only lift when the chain is directly inside parens —
            // a bare `1 + _` must stay unlifted so the downstream
            // `Wildcard` in expression position surfaces as
            // `IncorrectAnonymousArgument` rather than silently
            // becoming a valid lambda.
            let mut section_params: Vec<crate::cst::Binder> = Vec::new();
            let mut section_counter: u32 = 0;
            if in_parens {
                for slot in operands.iter_mut() {
                    if matches!(slot, Expr::Wildcard { .. }) {
                        let wspan = match slot {
                            Expr::Wildcard { span } => *span,
                            _ => unreachable!(),
                        };
                        let name = crate::names::value_name(&format!(
                            "$secchain_{}",
                            section_counter
                        ));
                        section_counter += 1;
                        section_params.push(crate::cst::Binder::Var {
                            span: wspan,
                            name: crate::cst::Spanned {
                                span: wspan,
                                value: name.clone(),
                            },
                        });
                        *slot = Expr::Var {
                            span: wspan,
                            name: crate::names::Qualified::unqualified(name),
                        };
                    }
                }
            }
            let ops: Vec<ChainOp> = ops_raw
                .into_iter()
                .map(|c| match c {
                    ChainOp::Named(n) => ChainOp::Named(n),
                    ChainOp::Backtick { span, func } => ChainOp::Backtick {
                        span,
                        func: rewrite_expr(func, fixity),
                    },
                })
                .collect();
            let shunted = shunt(operands, ops, fixity, root_span);
            let result = if section_params.is_empty() {
                shunted
            } else {
                Expr::Lambda {
                    span: root_span,
                    binders: section_params,
                    body: Box::new(shunted),
                }
            };
            match trailing_annotation {
                Some((span, ty)) => Expr::TypeAnnotation {
                    span,
                    expr: Box::new(result),
                    ty,
                },
                None => result,
            }
        }
        Expr::OpParens { span, op } => match lookup_op(&op, fixity) {
            Some(info) if target_is_constructor(info) => Expr::Constructor {
                span,
                name: target_ctor(info, span),
            },
            Some(info) => Expr::Var {
                span,
                name: target_var(info, span),
            },
            // Unknown fixity: fall back to the raw operator name as
            // an unqualified (or qualified) value reference. Keeps
            // the output operator-free so the IR lowering can assume
            // `Op`/`OpParens`/`BacktickApp` are structurally
            // impossible downstream; bad operator names surface as
            // `UnboundVar` at inference time.
            None => {
                let sym = op.value.name.symbol();
                let vn = value_name(&resolve_sym(sym));
                let qualified = match op.value.module {
                    Some(m) => Qualified::qualified(m, vn),
                    None => Qualified::unqualified(vn),
                };
                Expr::Var { span, name: qualified }
            }
        },
        Expr::Parens { span, expr } => Expr::Parens {
            span,
            expr: Box::new(rewrite_expr_ctx(*expr, fixity, true)),
        },
        other => recurse_children(other, fixity),
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

/// Walk a right-leaning chain of `Op` / `BacktickApp` nodes and
/// return the `operands`, `ops`, and the chain's span. Operands
/// are returned untouched — callers (today: only `rewrite_expr`)
/// are responsible for recursively rewriting them before shunting.
fn flatten_chain(root: Expr) -> (Vec<Expr>, Vec<ChainOp>, Span) {
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
    (operands, ops, root_span)
}

/// Recurse into `e`'s children with `rewrite_expr`. Mirrors
/// `super::walk::recurse_children` but invokes our pre-order
/// rewriter on each child so nested chains are caught at their
/// outermost Op.
fn recurse_children(e: Expr, fixity: &FixityTable) -> Expr {
    use crate::cst::{
        CaseAlternative, DoStatement, Guard, GuardPattern, GuardedExpr, LetBinding, Literal,
        RecordField, RecordUpdate,
    };

    fn rec(e: Expr, fixity: &FixityTable) -> Expr {
        rewrite_expr(e, fixity)
    }
    fn rec_box(e: Box<Expr>, fixity: &FixityTable) -> Box<Expr> {
        Box::new(rec(*e, fixity))
    }
    fn rec_field(r: RecordField, fixity: &FixityTable) -> RecordField {
        RecordField {
            span: r.span,
            label: r.label,
            value: r.value.map(|e| rec(e, fixity)),
            type_ann: r.type_ann,
            is_update: r.is_update,
            is_nested: r.is_nested,
        }
    }
    fn rec_update(u: RecordUpdate, fixity: &FixityTable) -> RecordUpdate {
        RecordUpdate { span: u.span, label: u.label, value: rec(u.value, fixity) }
    }
    fn rec_guarded(g: GuardedExpr, fixity: &FixityTable) -> GuardedExpr {
        match g {
            GuardedExpr::Unconditional(e) => GuardedExpr::Unconditional(rec_box(e, fixity)),
            GuardedExpr::Guarded(gs) => GuardedExpr::Guarded(
                gs.into_iter()
                    .map(|guard| Guard {
                        span: guard.span,
                        patterns: guard
                            .patterns
                            .into_iter()
                            .map(|p| match p {
                                GuardPattern::Boolean(e) => GuardPattern::Boolean(rec_box(e, fixity)),
                                GuardPattern::Pattern(b, e) => GuardPattern::Pattern(
                                    rewrite_binder(b, fixity),
                                    rec_box(e, fixity),
                                ),
                            })
                            .collect(),
                        expr: rec_box(guard.expr, fixity),
                    })
                    .collect(),
            ),
        }
    }
    fn rec_let(b: LetBinding, fixity: &FixityTable) -> LetBinding {
        match b {
            LetBinding::Value { span, binder, expr } => LetBinding::Value {
                span,
                binder: rewrite_binder(binder, fixity),
                expr: rec(expr, fixity),
            },
            LetBinding::Signature { span, name, ty } => LetBinding::Signature { span, name, ty },
        }
    }
    fn rec_alt(a: CaseAlternative, fixity: &FixityTable) -> CaseAlternative {
        CaseAlternative {
            span: a.span,
            binders: a.binders.into_iter().map(|b| rewrite_binder(b, fixity)).collect(),
            result: rec_guarded(a.result, fixity),
        }
    }
    fn rec_do(s: DoStatement, fixity: &FixityTable) -> DoStatement {
        match s {
            DoStatement::Bind { span, binder, expr } => DoStatement::Bind {
                span,
                binder: rewrite_binder(binder, fixity),
                expr: rec(expr, fixity),
            },
            DoStatement::Let { span, bindings } => DoStatement::Let {
                span,
                bindings: bindings.into_iter().map(|b| rec_let(b, fixity)).collect(),
            },
            DoStatement::Discard { span, expr } => DoStatement::Discard { span, expr: rec(expr, fixity) },
        }
    }

    match e {
        Expr::Var { .. }
        | Expr::Constructor { .. }
        | Expr::Wildcard { .. }
        | Expr::Hole { .. }
        | Expr::OpParens { .. } => e,
        Expr::Literal { span, lit } => match lit {
            Literal::Array(xs) => Expr::Literal {
                span,
                lit: Literal::Array(xs.into_iter().map(|x| rec(x, fixity)).collect()),
            },
            other => Expr::Literal { span, lit: other },
        },
        Expr::App { span, func, arg } => Expr::App {
            span,
            func: rec_box(func, fixity),
            arg: rec_box(arg, fixity),
        },
        Expr::VisibleTypeApp { span, func, ty } => Expr::VisibleTypeApp {
            span,
            func: rec_box(func, fixity),
            ty,
        },
        Expr::Lambda { span, binders, body } => Expr::Lambda {
            span,
            binders: binders.into_iter().map(|b| rewrite_binder(b, fixity)).collect(),
            body: rec_box(body, fixity),
        },
        Expr::Op { .. } | Expr::BacktickApp { .. } => rewrite_expr(e, fixity),
        Expr::If { span, cond, then_expr, else_expr } => Expr::If {
            span,
            cond: rec_box(cond, fixity),
            then_expr: rec_box(then_expr, fixity),
            else_expr: rec_box(else_expr, fixity),
        },
        Expr::Case { span, exprs, alts } => Expr::Case {
            span,
            exprs: exprs.into_iter().map(|e| rec(e, fixity)).collect(),
            alts: alts.into_iter().map(|a| rec_alt(a, fixity)).collect(),
        },
        Expr::Let { span, bindings, body } => Expr::Let {
            span,
            bindings: super::multi_eq::merge_let_bindings(bindings)
                .into_iter()
                .map(|b| rec_let(b, fixity))
                .collect(),
            body: rec_box(body, fixity),
        },
        Expr::Do { span, module, statements } => Expr::Do {
            span,
            module,
            statements: statements.into_iter().map(|s| rec_do(s, fixity)).collect(),
        },
        Expr::Ado { span, module, statements, result } => Expr::Ado {
            span,
            module,
            statements: statements.into_iter().map(|s| rec_do(s, fixity)).collect(),
            result: rec_box(result, fixity),
        },
        Expr::Record { span, fields } => Expr::Record {
            span,
            fields: fields.into_iter().map(|r| rec_field(r, fixity)).collect(),
        },
        Expr::RecordAccess { span, expr, field } => Expr::RecordAccess {
            span,
            expr: rec_box(expr, fixity),
            field,
        },
        Expr::RecordUpdate { span, expr, updates } => Expr::RecordUpdate {
            span,
            expr: rec_box(expr, fixity),
            updates: updates.into_iter().map(|u| rec_update(u, fixity)).collect(),
        },
        Expr::Parens { span, expr } => Expr::Parens { span, expr: rec_box(expr, fixity) },
        Expr::TypeAnnotation { span, expr, ty } => Expr::TypeAnnotation {
            span,
            expr: rec_box(expr, fixity),
            ty,
        },
        Expr::Array { span, elements } => Expr::Array {
            span,
            elements: elements.into_iter().map(|e| rec(e, fixity)).collect(),
        },
        Expr::Negate { span, expr } => Expr::Negate { span, expr: rec_box(expr, fixity) },
        Expr::AsPattern { span, name, pattern } => Expr::AsPattern {
            span,
            name: rec_box(name, fixity),
            pattern: rec_box(pattern, fixity),
        },
    }
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
                // Unknown op: default to `infixl 9` per the
                // PureScript reference. Both identifier-shaped
                // backtick syntax (`a `f` b` parsed as Op) and
                // bare symbolic ops fall here when their fixity
                // decl isn't visible — matching the language
                // default keeps us aligned with how programs like
                // `Data.EuclideanRing.power` rely on `p `mod` 2`
                // binding tighter than `==`.
                None => (Associativity::Left, 9),
            }
        }
        ChainOp::Backtick { .. } => (Associativity::Left, 9),
    }
}

fn apply_op(op: &ChainOp, left: Expr, right: Expr, fixity: &FixityTable, span: Span) -> Expr {
    let func = match op {
        ChainOp::Named(n) => {
            let sym = n.value.name.symbol();
            match fixity.get(&sym) {
                Some(info) if target_is_constructor(*info) => {
                    // Constructor operator (e.g. `infixr 6 Cons as :`).
                    // Emit an `Expr::Constructor` node so downstream
                    // binder/inference passes treat the operands as
                    // constructor arguments rather than looking the
                    // name up in the value namespace.
                    Expr::Constructor {
                        span,
                        name: target_ctor(*info, span),
                    }
                }
                Some(info) => Expr::Var {
                    span,
                    name: target_var(*info, span),
                },
                None => {
                    // No fixity decl in scope. Two flavors:
                    //   * Identifier-shaped name (`a `f` b` parsed as
                    //     an Op with `f`'s identifier as the op):
                    //     lower to `App(App(Var(f), a), b)`.
                    //   * Symbolic operator (e.g. `??` with no fixity
                    //     in scope): lower to `App(App(Var("??"), a),
                    //     b)` using the raw operator name. Downstream
                    //     name resolution / typecheck surfaces the
                    //     "unbound var" error if the operator was a
                    //     typo; passing a real import that hasn't
                    //     loaded yet produces the expected resolved
                    //     `Var`. In both cases the output is fully
                    //     operator-free, which is the invariant the
                    //     IR lowering depends on.
                    let vn = value_name(&resolve_sym(sym));
                    let qualified = match n.value.module {
                        Some(m) => Qualified::qualified(m, vn),
                        None => Qualified::unqualified(vn),
                    };
                    Expr::Var { span, name: qualified }
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

fn target_is_constructor(info: FixityInfo) -> bool {
    let s = resolve_sym(info.target_name);
    s.chars().next().map_or(false, |c| c.is_ascii_uppercase())
}

fn target_ctor(info: FixityInfo, _span: Span) -> Qualified<crate::names::ConstructorName> {
    use crate::names::ConstructorName;
    let cn = ConstructorName::new(crate::interner::intern(&resolve_sym(info.target_name)));
    match info.target_module {
        Some(m) => Qualified::qualified(crate::names::ModuleQualifier::new(m), cn),
        None => Qualified::unqualified(cn),
    }
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
    fn unknown_op_lowers_to_app_of_raw_name() {
        // Even without a fixity decl in scope, an operator must
        // lower to `App(App(Var(op_name), lhs), rhs)`. The IR
        // pass relies on every `Op` / `OpParens` / `BacktickApp`
        // being gone after desugar — leaving an unknown op as
        // `Expr::Op` would force a fallback lowering elsewhere
        // and break that invariant. Typos / missing imports
        // surface as `UnboundVar` during inference, which is
        // precise enough.
        let table = FixityTable::new();
        let d = first_value("\
module M where
foo a b = a ?? b
");
        let out = desugar_decl(d, &table);
        assert_eq!(count_op(&out), 0, "unknown op must still be lowered");
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
    fn higher_precedence_subchains_inside_lower_precedence_chain() {
        // `a == zero || b == zero` with `==` at infixl 4 and `||` at
        // infixr 2 must reassociate as `(a == zero) || (b == zero)`,
        // i.e. `disj (eq a zero) (eq b zero)`. A naive post-order
        // walker rewrites the inner `Op(b, ==, zero)` first, which
        // hides the outer chain's structure and lets `||` capture
        // `zero` and `b`. This regression test pins the correct
        // reassociation.
        let (table, decls) = module_table("\
module M where
infixl 4 eq as ==
infixr 2 disj as ||
foo a b zero = a == zero || b == zero
");
        let value = decls.into_iter().find(|d| matches!(d, Decl::Value { .. })).unwrap();
        let out = desugar_decl(value, &table);
        assert_eq!(count_op(&out), 0, "all Op nodes should be lowered: {out:#?}");
        // Outermost call should be to `disj`, not `eq`. Walk down
        // the function-of-function pattern: App(App(Var(disj), _), _).
        if let Decl::Value { guarded: crate::cst::GuardedExpr::Unconditional(body), .. } = &out {
            let head = match body.as_ref() {
                Expr::App { func, .. } => match func.as_ref() {
                    Expr::App { func, .. } => func.as_ref(),
                    other => panic!("expected App-App, got {other:?}"),
                },
                other => panic!("expected outer App, got {other:?}"),
            };
            if let Expr::Var { name, .. } = head {
                assert_eq!(
                    crate::interner::resolve(name.name.symbol()).as_deref(),
                    Some("disj"),
                    "outermost call must be disj (the lower-precedence op), got {name:?}",
                );
            } else {
                panic!("expected Var head, got {head:?}");
            }
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
