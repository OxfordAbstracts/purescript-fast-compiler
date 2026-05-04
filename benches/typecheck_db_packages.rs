//! Criterion benchmark for the `typecheck_db` pipeline.
//!
//! Two scenarios:
//! * `prelude_closure` — typecheck `Prelude` and its transitive
//!   imports. ~50–150 modules; quick to run, useful for tracking
//!   regressions in the most common path.
//! * `mid_module` — typecheck `Data.Map` and its closure. Larger
//!   (~300–500 modules) so it exercises more of the hot paths
//!   (records, classes, instances) than Prelude alone.
//!
//! Source files are discovered + parsed once at startup (outside
//! the timed region). The timed closure pays only the
//! `check_many_modules` cost, which is what we care about for
//! optimization work.
//!
//! Run with:
//! ```
//! cargo bench --bench typecheck_db_packages
//! ```

use std::collections::HashMap;
use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

use purescript_fast_compiler::typecheck_db::driver_multi::{
    check_many_modules, ModuleInput,
};
use purescript_fast_compiler::typecheck_db::test_support::{
    package_modules_by_name, transitive_closure_of,
};

/// Build the closure for one target module. Panics if the target
/// is missing — there is no useful bench result without it.
fn closure_for(target: &str, pkgs: &HashMap<String, ModuleInput>) -> Vec<ModuleInput> {
    if !pkgs.contains_key(target) {
        panic!("bench target {target:?} not found in tests/fixtures/packages/");
    }
    transitive_closure_of(target, pkgs)
}

/// Clone a closure so each Criterion iteration starts from the same
/// pristine `Vec<ModuleInput>`. `check_many_modules` consumes the
/// vec, so we need to hand it a fresh copy each iteration.
fn clone_closure(closure: &[ModuleInput]) -> Vec<ModuleInput> {
    closure
        .iter()
        .map(|m| ModuleInput::new(m.name.clone(), m.source.clone(), m.module.clone()))
        .collect()
}

fn bench_typecheck(c: &mut Criterion) {
    // Parse every package source once. ~4800 files; ~1.5s on a
    // warm filesystem. Outside the timed region.
    let pkgs = package_modules_by_name();

    let prelude_closure = closure_for("Prelude", &pkgs);
    let mid_closure = closure_for("Data.Map", &pkgs);

    eprintln!(
        "bench targets: prelude_closure={} modules, mid_module={} modules",
        prelude_closure.len(),
        mid_closure.len(),
    );

    let mut group = c.benchmark_group("typecheck_db");
    // Each iteration runs the full multi-module check, which is
    // O(seconds) for these closures — keep the sample budget small
    // so `cargo bench` finishes in a few minutes rather than an
    // hour. Criterion still produces stable mean/stddev with
    // sample_size 10 because per-iter variance on a quiet machine
    // is dominated by the work itself.
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));

    group.bench_function("prelude_closure", |b| {
        b.iter_batched(
            || clone_closure(&prelude_closure),
            |modules| {
                let report = check_many_modules(black_box(modules));
                black_box(report);
            },
            criterion::BatchSize::LargeInput,
        );
    });

    group.bench_function("mid_module", |b| {
        b.iter_batched(
            || clone_closure(&mid_closure),
            |modules| {
                let report = check_many_modules(black_box(modules));
                black_box(report);
            },
            criterion::BatchSize::LargeInput,
        );
    });

    group.finish();
}

criterion_group!(benches, bench_typecheck);
criterion_main!(benches);
