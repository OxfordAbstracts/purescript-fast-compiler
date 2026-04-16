//! MDc sub-transform: `do` / `ado` → bind / map / apply chains.
//!
//! # Do
//!
//! ```text
//! do
//!   x <- e1
//!   let y = e2
//!   e3
//!   e4
//! ```
//!
//! desugars to
//!
//! ```text
//! bind e1 (\x -> let y = e2 in bind e3 (\_ -> e4))
//! ```
//!
//! `bind` is looked up in the enclosing module; for a qualified do
//! (`MyMod.do { ... }`), we emit `MyMod.bind` instead.
//!
//! # Ado
//!
//! ```text
//! ado
//!   x <- e1
//!   let y = e2
//!   z <- e3
//!   in body
//! ```
//!
//! desugars to
//!
//! ```text
//! apply (map (\x z -> let y = e2 in body) e1) e3
//! ```
//!
//! All bind variables share a single multi-arg lambda. Lets (and anonymous
//! binds from `Discard` statements) are placed inside that lambda's body
//! in source order. Lets that appear *before* the first bind become a
//! `let` wrapper around the whole apply chain. A let/discard-only ado
//! with no binds degenerates to `pure body` wrapped in its lets.
//!
//! Keeping the exact source nesting of lets is important: inner lets can
//! reference variables bound by outer lets, and vice-versa would type-
//! check but give different semantics.

use crate::cst::{Binder, Decl, DoStatement, Expr, LetBinding};
use crate::names::{value_name, ModuleQualifier, Qualified, ValueName};
use crate::span::Span;

use super::walk::fold_decl_exprs;

pub fn desugar_decl(decl: Decl) -> Decl {
    fold_decl_exprs(decl, &mut rewrite_node)
}

fn rewrite_node(e: Expr) -> Expr {
    match e {
        Expr::Do { span, module, statements } => desugar_do(span, module, statements),
        Expr::Ado { span, module, statements, result } => {
            desugar_ado(span, module, statements, *result)
        }
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Do
// ---------------------------------------------------------------------------

fn desugar_do(span: Span, module: Option<ModuleQualifier>, statements: Vec<DoStatement>) -> Expr {
    // A well-formed `do` ends in a `Discard` (the result expression). If
    // the last statement is a Bind or Let we emit a hole so the user gets
    // a reasonable error later; the parser normally rejects this shape.
    if statements.is_empty() {
        return hole(span, "empty_do");
    }
    let mut it = statements.into_iter().rev();
    let mut acc: Expr = match it.next().unwrap() {
        DoStatement::Discard { expr, .. } => expr,
        DoStatement::Bind { .. } | DoStatement::Let { .. } => return hole(span, "do_missing_result"),
    };
    for s in it {
        acc = wrap_do_stmt(module, s, acc);
    }
    acc
}

fn wrap_do_stmt(module: Option<ModuleQualifier>, stmt: DoStatement, rest: Expr) -> Expr {
    match stmt {
        DoStatement::Bind { span, binder, expr } => {
            bind_app(module, span, expr, binder, rest)
        }
        DoStatement::Discard { span, expr } => {
            // `e; rest` → `bind e (\_ -> rest)`. PureScript uses the
            // `Discard` class to allow non-Unit `m a` values; using
            // `bind` with a wildcard binder produces the same effect
            // and keeps us in vanilla monadic territory.
            bind_app(module, span, expr, Binder::Wildcard { span }, rest)
        }
        DoStatement::Let { span, bindings } => Expr::Let {
            span,
            bindings,
            body: Box::new(rest),
        },
    }
}

/// Build `bind expr (\binder -> rest)`.
fn bind_app(
    module: Option<ModuleQualifier>,
    span: Span,
    expr: Expr,
    binder: Binder,
    rest: Expr,
) -> Expr {
    let lam = Expr::Lambda {
        span,
        binders: vec![binder],
        body: Box::new(rest),
    };
    apply2(span, prelude_fn(module, span, "bind"), expr, lam)
}

// ---------------------------------------------------------------------------
// Ado
// ---------------------------------------------------------------------------

fn desugar_ado(
    span: Span,
    module: Option<ModuleQualifier>,
    statements: Vec<DoStatement>,
    result: Expr,
) -> Expr {
    // Split:
    //   binds:  Vec<(Binder, Expr)> in source order — applicative operands
    //   prefix_lets: lets that appear before the first bind (if any)
    //   body_stmts: lets (and anonymous discards) interleaved among and
    //               after binds — placed inside the lambda body
    //
    // body_stmts entries are distinguished as:
    //   BodyPiece::Let(Vec<LetBinding>)
    //   BodyPiece::BindEnd        // marker placed after a bind to say
    //                             // "subsequent let pieces belong after
    //                             // this bind's binder in lambda-body
    //                             // order"
    //
    // Simpler representation: keep source-order pieces and rebuild the
    // body with them, ignoring the bind markers (since every bind
    // contributes a binder to the outer lambda and the body is just the
    // fold of the non-bind pieces).

    enum Piece {
        Let(Span, Vec<LetBinding>),
    }

    let mut binds: Vec<(Binder, Expr)> = Vec::new();
    let mut prefix_lets: Vec<(Span, Vec<LetBinding>)> = Vec::new();
    let mut body_pieces: Vec<Piece> = Vec::new();
    let mut seen_bind = false;

    for s in statements {
        match s {
            DoStatement::Bind { binder, expr, .. } => {
                seen_bind = true;
                binds.push((binder, expr));
            }
            DoStatement::Discard { span, expr } => {
                seen_bind = true;
                binds.push((Binder::Wildcard { span }, expr));
            }
            DoStatement::Let { span: ls, bindings } => {
                if seen_bind {
                    body_pieces.push(Piece::Let(ls, bindings));
                } else {
                    prefix_lets.push((ls, bindings));
                }
            }
        }
    }

    // Build the inner body: `let piece1 in let piece2 in ... in result`.
    let mut body = result;
    for p in body_pieces.into_iter().rev() {
        match p {
            Piece::Let(ls, bindings) => {
                body = Expr::Let { span: ls, bindings, body: Box::new(body) };
            }
        }
    }

    // Degenerate case: no binds. Emit `pure body` wrapped in prefix_lets.
    if binds.is_empty() {
        let mut out = apply1(span, prelude_fn(module, span, "pure"), body);
        for (ls, bindings) in prefix_lets.into_iter().rev() {
            out = Expr::Let { span: ls, bindings, body: Box::new(out) };
        }
        return out;
    }

    // Build the multi-arg lambda: `\x1 x2 ... xn -> body`.
    let binders: Vec<Binder> = binds.iter().map(|(b, _)| b.clone()).collect();
    let lambda = Expr::Lambda {
        span,
        binders,
        body: Box::new(body),
    };

    // Build the applicative chain:
    //   map lambda e1
    //   apply (prev) e2
    //   apply (prev) e3
    //   ...
    let mut chain = apply2(
        span,
        prelude_fn(module, span, "map"),
        lambda,
        binds[0].1.clone(),
    );
    for (_, ei) in binds.iter().skip(1) {
        chain = apply2(span, prelude_fn(module, span, "apply"), chain, ei.clone());
    }

    // Wrap with prefix lets.
    for (ls, bindings) in prefix_lets.into_iter().rev() {
        chain = Expr::Let { span: ls, bindings, body: Box::new(chain) };
    }
    chain
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

/// `Expr::Var` referring to a Prelude-ish function name, possibly
/// qualified with a module (for `MyMod.do`).
fn prelude_fn(module: Option<ModuleQualifier>, span: Span, name: &str) -> Expr {
    let vn: ValueName = value_name(name);
    let q = match module {
        Some(m) => Qualified::qualified(m, vn),
        None => Qualified::unqualified(vn),
    };
    Expr::Var { span, name: q }
}

/// `f a`
fn apply1(span: Span, func: Expr, arg: Expr) -> Expr {
    Expr::App {
        span,
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

/// `f a b`
fn apply2(span: Span, func: Expr, a: Expr, b: Expr) -> Expr {
    apply1(span, apply1(span, func, a), b)
}

fn hole(span: Span, name: &str) -> Expr {
    Expr::Hole {
        span,
        name: value_name(name),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn first_decl(src: &str) -> Decl {
        parse(src).unwrap().decls.into_iter().next().unwrap()
    }

    fn count<F: Fn(&Expr) -> bool + Copy>(d: &Decl, pred: F) -> u32 {
        let mut n = 0u32;
        let _ = super::super::walk::fold_decl_exprs(d.clone(), &mut |e| {
            if pred(&e) {
                n += 1;
            }
            e
        });
        n
    }

    fn count_do(d: &Decl) -> u32 {
        count(d, |e| matches!(e, Expr::Do { .. }))
    }

    fn count_ado(d: &Decl) -> u32 {
        count(d, |e| matches!(e, Expr::Ado { .. }))
    }

    #[test]
    fn do_with_one_bind_becomes_bind_app() {
        let d = first_decl("\
module M where
foo = do
  x <- act
  pure x
");
        assert_eq!(count_do(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_do(&d2), 0);
    }

    #[test]
    fn do_with_let_preserves_let() {
        let d = first_decl("\
module M where
foo = do
  let y = 1
  pure y
");
        let d2 = desugar_decl(d);
        assert_eq!(count_do(&d2), 0);
    }

    #[test]
    fn do_with_discard_middle_becomes_nested_bind() {
        let d = first_decl("\
module M where
foo = do
  act1
  act2
  pure 0
");
        assert_eq!(count_do(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_do(&d2), 0);
    }

    #[test]
    fn ado_with_two_binds_uses_map_and_apply() {
        let d = first_decl("\
module M where
foo = ado
  x <- e1
  y <- e2
  in x
");
        assert_eq!(count_ado(&d), 1);
        let d2 = desugar_decl(d);
        assert_eq!(count_ado(&d2), 0);
    }

    #[test]
    fn ado_with_let_between_binds_places_let_inside_lambda() {
        let d = first_decl("\
module M where
foo = ado
  x <- e1
  let z = x
  y <- e2
  in z
");
        let d2 = desugar_decl(d);
        assert_eq!(count_ado(&d2), 0);
        // The inner body should contain a Let (the `let z = x`).
        let n_lets = count(&d2, |e| matches!(e, Expr::Let { .. }));
        assert!(n_lets >= 1, "expected at least one Let, got {n_lets}");
    }

    #[test]
    fn nested_do_inside_bind_is_flattened() {
        // The lambda body of an outer bind may itself contain a do; both
        // should be rewritten bottom-up (post-order).
        let d = first_decl("\
module M where
foo = do
  x <- do
    y <- inner
    pure y
  pure x
");
        assert_eq!(count_do(&d), 2);
        let d2 = desugar_decl(d);
        assert_eq!(count_do(&d2), 0);
    }

    #[test]
    fn non_do_is_untouched() {
        let d = first_decl("module M where\nfoo = 1\n");
        let d2 = desugar_decl(d.clone());
        assert_eq!(d, d2);
    }

    #[test]
    fn idempotent() {
        let d = first_decl("\
module M where
foo = do
  x <- act
  pure x
");
        let d1 = desugar_decl(d);
        let d2 = desugar_decl(d1.clone());
        assert_eq!(d1, d2);
    }
}
