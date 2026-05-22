//! End-to-end acceptance tests for `typecheck_db`.
//!
//! Each test loads one or more real PureScript sources (kept as
//! `.purs` files under `fixtures/`) and drives them through
//! [`check_many_modules`]. The point is to exercise the
//! full per-decl pipeline — parse → desugar → infer → check
//! exhaustiveness → solve constraints → distill exports — against
//! programs a user would actually write, and to do it for both
//! success paths (zero errors expected) and failure paths
//! (specific, expected errors).
//!
//! Layout:
//!
//! * `harness` — thin helpers that wrap the test-assertion shape
//!   every case uses. Adding a new feature to the suite should
//!   normally be "drop in a `.purs` + one test function".
//! * `single_module` — one-file programs.
//! * `multi_module` — two or more modules, where later modules
//!   import earlier ones.
//! * `failures` — programs whose errors are the *point*. Each
//!   test asserts the expected error kind + enough detail
//!   (constructor name, class name, etc.) to prove the check
//!   is catching the right thing for the right reason.
//!
//! Fixtures live in `fixtures/<category>/<name>.purs` and are
//! included at compile time via `include_str!`, so the tests
//! don't depend on any runtime path lookups.

mod harness;
mod single_module;
mod multi_module;
mod failures;
mod incremental;
mod failing_fixtures;
mod hole_fixtures;
mod passing_fixtures;
mod prelude;
mod all_packages;
mod package_subsets;
