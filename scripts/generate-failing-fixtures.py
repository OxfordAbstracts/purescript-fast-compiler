#!/usr/bin/env python3
"""Generate failing_fixtures_list.rs from tests/fixtures/original-compiler/failing/.

Each top-level .purs file becomes one check_failing_build_unit! entry.
Sub-directory .purs files (support modules like 1733/Thingy.purs) are excluded
because they're loaded automatically by build_unit_sources when the parent
fixture (1733.purs) is processed.

Usage:
    python3 scripts/generate-failing-fixtures.py
"""
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
FAILING_ROOT = REPO / "tests" / "fixtures" / "original-compiler" / "failing"
OUT = REPO / "src" / "typecheck_db" / "tests" / "failing_fixtures_list.rs"


def fixture_ident(stem: str) -> str:
    """Convert a fixture stem like '2109-bind' to a valid Rust identifier."""
    return "f_" + stem.replace("-", "_")


def main() -> None:
    purs_files = sorted(f for f in FAILING_ROOT.iterdir() if f.suffix == ".purs")
    entries = []
    for purs in purs_files:
        stem = purs.stem
        ident = fixture_ident(stem)
        entries.append(f'check_failing_build_unit!({ident}, "{stem}");')

    OUT.write_text("\n".join(entries) + "\n")
    print(f"Wrote {len(entries)} entries to {OUT.relative_to(REPO)}")


if __name__ == "__main__":
    main()
