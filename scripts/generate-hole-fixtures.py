#!/usr/bin/env python3
"""
Generate typed-hole test fixtures from existing passing fixtures.

For each fixture in tests/fixtures/original-compiler/passing/, picks three
distinct insertion points and replaces the code at each with `?test`, then
runs `purs compile` to capture the typed-hole diagnostic as expected output.

Output: tests/fixtures/holes/<name>-<N>/<Module>.purs  +  expected.txt

Usage:
    scripts/generate-hole-fixtures.py                 # all fixtures
    scripts/generate-hole-fixtures.py Ado 1110 Let2   # named fixtures only
    FIXTURE_THREADS=4 scripts/generate-hole-fixtures.py

Requirements:
- `purs` in PATH
- Support packages under tests/fixtures/packages/
"""
from __future__ import annotations

import multiprocessing as mp
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

REPO = Path(__file__).resolve().parent.parent
PASSING = REPO / "tests" / "fixtures" / "original-compiler" / "passing"
HOLES = REPO / "tests" / "fixtures" / "holes"
PACKAGES = REPO / "tests" / "fixtures" / "packages"

SUPPORT_PACKAGES = [
    "prelude", "arrays", "assert", "bifunctors", "catenable-lists",
    "console", "const", "contravariant", "control", "datetime",
    "distributive", "effect", "either", "enums", "exceptions",
    "exists", "filterable", "foldable-traversable", "foreign",
    "foreign-object", "free", "functions", "functors", "gen",
    "graphs", "identity", "integers", "invariant", "json", "lazy",
    "lcg", "lists", "maybe", "newtype", "nonempty", "numbers",
    "ordered-collections", "orders", "partial", "profunctor",
    "quickcheck", "random", "record", "refs", "safe-coerce",
    "semirings", "st", "strings", "tailrec", "transformers",
    "tuples", "type-equality", "typelevel-prelude", "unfoldable",
    "unsafe-coerce", "validation",
]


@dataclass
class Site:
    """A candidate hole-insertion site in a source file."""
    start: int          # byte offset into source
    end: int            # byte offset into source (exclusive)
    kind: str           # "top-rhs" | "sub-expr" | "type"
    line: int           # 1-indexed line (for reporting)


# ---------------------------------------------------------------------------
# Source scanning
# ---------------------------------------------------------------------------

# PureScript identifier / atomic-expression tokens we're willing to replace
# with a hole. We deliberately keep this conservative.
IDENT_RE = re.compile(r"\b[a-z_][A-Za-z0-9_']*\b")
CTOR_RE = re.compile(r"\b[A-Z][A-Za-z0-9_']*\b")
NUMBER_RE = re.compile(r"\b\d+(?:\.\d+)?\b")
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')

RESERVED = {
    "module", "where", "import", "as", "hiding", "data", "newtype",
    "type", "class", "instance", "derive", "foreign", "infix",
    "infixl", "infixr", "let", "in", "do", "ado", "case", "of",
    "if", "then", "else", "true", "false", "forall", "∀", "_",
    "Int", "String", "Number", "Boolean", "Char", "Array", "Unit",
    "Effect", "Prelude", "Main",
}


def strip_comments_and_strings(src: str) -> str:
    """Replace block/line comments and string literals with spaces, preserving offsets.

    Used for scanning — we don't want to pick a hole site inside a comment
    or string literal.
    """
    out = list(src)
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        # Line comment
        if c == "-" and i + 1 < n and src[i + 1] == "-":
            j = i
            while j < n and src[j] != "\n":
                out[j] = " " if src[j] != "\n" else src[j]
                j += 1
            i = j
            continue
        # Block comment
        if c == "{" and i + 1 < n and src[i + 1] == "-":
            depth = 1
            out[i] = " "
            out[i + 1] = " "
            j = i + 2
            while j < n and depth > 0:
                if src[j] == "{" and j + 1 < n and src[j + 1] == "-":
                    depth += 1
                    out[j] = " "
                    out[j + 1] = " "
                    j += 2
                elif src[j] == "-" and j + 1 < n and src[j + 1] == "}":
                    depth -= 1
                    out[j] = " "
                    out[j + 1] = " "
                    j += 2
                else:
                    if src[j] != "\n":
                        out[j] = " "
                    j += 1
            i = j
            continue
        # String literal
        if c == '"':
            out[i] = " "
            j = i + 1
            # triple-quoted?
            if j + 1 < n and src[j] == '"' and src[j + 1] == '"':
                out[j] = " "
                out[j + 1] = " "
                j += 2
                while j + 2 < n and not (src[j] == '"' and src[j + 1] == '"' and src[j + 2] == '"'):
                    if src[j] != "\n":
                        out[j] = " "
                    j += 1
                if j + 2 < n:
                    out[j] = " "
                    out[j + 1] = " "
                    out[j + 2] = " "
                    j += 3
            else:
                while j < n and src[j] != '"':
                    if src[j] == "\\" and j + 1 < n:
                        if src[j] != "\n":
                            out[j] = " "
                        if src[j + 1] != "\n":
                            out[j + 1] = " "
                        j += 2
                    else:
                        if src[j] != "\n":
                            out[j] = " "
                        j += 1
                if j < n:
                    out[j] = " "
                    j += 1
            i = j
            continue
        # Char literal
        if c == "'":
            out[i] = " "
            j = i + 1
            while j < n and src[j] != "'":
                if src[j] == "\\" and j + 1 < n:
                    if src[j] != "\n":
                        out[j] = " "
                    if src[j + 1] != "\n":
                        out[j + 1] = " "
                    j += 2
                else:
                    if src[j] != "\n":
                        out[j] = " "
                    j += 1
            if j < n:
                out[j] = " "
                j += 1
            i = j
            continue
        i += 1
    return "".join(out)


def line_of(src: str, offset: int) -> int:
    return src.count("\n", 0, offset) + 1


def find_module_body_start(src: str) -> int:
    """Find the offset immediately after `module X where`."""
    m = re.search(r"\bmodule\b[^\n]*\bwhere\b", src)
    if not m:
        return 0
    return m.end()


def find_top_rhs_sites(src: str, scan: str) -> list[Site]:
    """Find RHS of top-level value decls: `foo = <rhs>` at column 1."""
    sites: list[Site] = []
    body_start = find_module_body_start(src)
    # Very naive: look for lines where `<ident> (<args>)? =` appears at column 1
    # and capture the RHS up to the next line that also starts at column 1 with
    # a declaration-looking token.
    lines: list[tuple[int, int]] = []  # (start_offset, end_offset)
    pos = 0
    for ln in src.split("\n"):
        lines.append((pos, pos + len(ln)))
        pos += len(ln) + 1

    decl_re = re.compile(r"^\s*([a-z_][A-Za-z0-9_']*)\s*([^=]*?)=(?!=)")
    for i, (ls, le) in enumerate(lines):
        if ls < body_start:
            continue
        line = src[ls:le]
        if not line.strip() or line.lstrip().startswith("--"):
            continue
        stripped = line.lstrip()
        indent = len(line) - len(stripped)
        first_word = stripped.split()[0] if stripped.split() else ""
        # skip keywords that start a construct
        if first_word in {"module", "import", "data", "newtype", "type",
                          "class", "instance", "derive", "foreign", "infix",
                          "infixl", "infixr", "else", "where", "let", "in",
                          "do", "ado", "case", "of", "if", "then"}:
            continue
        # Skip `main =` — main's type is usually Effect Unit (or similar
        # effectful Unit), which accepts almost any expression.
        if first_word == "main" and indent == 0:
            continue
        # Skip type signatures (`foo :: ...`)
        if "::" in line:
            # If the `::` appears before any `=`, it's a type signature
            eq_pos = line.find("=")
            dc_pos = line.find("::")
            if eq_pos == -1 or dc_pos < eq_pos:
                continue
        m = decl_re.match(line)
        if not m:
            continue
        # For indented decls (instance methods, where bindings), the RHS
        # continuation belongs to lines that are MORE indented than this one.
        # We track that below using `indent`.
        # Skip if we can't find an `=`
        eq_line_off = line.find("=", m.start(2) if m.start(2) != m.end(2) else m.start())
        # Using the match object directly:
        # find the first `=` that isn't `==`, `=>`, `<=`, `>=`
        eq_off_in_line = None
        k = 0
        while k < len(line):
            if line[k] == "=":
                prev = line[k - 1] if k > 0 else ""
                nxt = line[k + 1] if k + 1 < len(line) else ""
                if prev in "<>/=!" or nxt == "=" or nxt == ">":
                    k += 1
                    continue
                eq_off_in_line = k
                break
            k += 1
        if eq_off_in_line is None:
            continue
        rhs_start = ls + eq_off_in_line + 1
        # Find end of this RHS: continuation lines are strictly more indented
        # than the decl's own indentation.
        rhs_end = len(src)
        for j in range(i + 1, len(lines)):
            ls2, le2 = lines[j]
            l2 = src[ls2:le2]
            if not l2.strip():
                continue
            cont_indent = len(l2) - len(l2.lstrip())
            if cont_indent <= indent:
                rhs_end = ls2 - 1
                break
        # Skim leading whitespace and newlines
        while rhs_start < rhs_end and src[rhs_start] in " \t\n":
            rhs_start += 1
        rhs_text = src[rhs_start:rhs_end].rstrip()
        if not rhs_text:
            continue
        # Skip open-form expressions: replacing a `do { ... }` block with
        # `?test` generally works, but the RHS may contain a `where` clause
        # we can't simply drop. Keep it simple: skip if there's a `where`
        # continuation in this decl.
        if re.search(r"^\s*where\b", rhs_text, flags=re.MULTILINE):
            continue
        # Must not itself be a hole
        if "?test" in rhs_text:
            continue
        sites.append(Site(rhs_start, rhs_start + len(rhs_text), "top-rhs",
                          line_of(src, rhs_start)))
    return sites


def compute_sig_ranges(src: str) -> list[tuple[int, int]]:
    """Offset ranges of type signatures' type bodies (after `::`).

    Accepts top-level and indented (class/instance body) signatures.
    """
    pos = 0
    sig_ranges: list[tuple[int, int]] = []
    in_sig = False
    sig_start = 0
    sig_indent = 0
    for ln in src.split("\n"):
        ls = pos
        le = pos + len(ln)
        if in_sig:
            stripped = ln.lstrip()
            ln_indent = len(ln) - len(stripped) if stripped else sig_indent + 1
            if stripped and ln_indent > sig_indent:
                pass
            else:
                sig_ranges.append((sig_start, ls - 1))
                in_sig = False
        if not in_sig:
            stripped = ln.lstrip()
            indent = len(ln) - len(stripped)
            m = re.match(r"[a-z_][A-Za-z0-9_']*\s*::", stripped)
            if m:
                dc = ln.index("::", indent)
                in_sig = True
                sig_start = ls + dc + 2
                sig_indent = indent
        pos = le + 1
    if in_sig:
        sig_ranges.append((sig_start, pos))
    return sig_ranges


def compute_sig_full_lines(src: str) -> list[tuple[int, int]]:
    """Offset ranges spanning the entire line of a signature (incl. the lhs).

    Used to exclude signature-lines from sub-expression scanning — the lhs
    name (e.g. `pure` in `pure :: forall a. a -> f a`) is a binder, not a
    usage.
    """
    pos = 0
    ranges: list[tuple[int, int]] = []
    in_sig = False
    sig_start = 0
    sig_indent = 0
    for ln in src.split("\n"):
        ls = pos
        le = pos + len(ln)
        if in_sig:
            stripped = ln.lstrip()
            ln_indent = len(ln) - len(stripped) if stripped else sig_indent + 1
            if stripped and ln_indent > sig_indent:
                pass
            else:
                ranges.append((sig_start, ls - 1))
                in_sig = False
        if not in_sig:
            stripped = ln.lstrip()
            indent = len(ln) - len(stripped)
            m = re.match(r"[a-z_][A-Za-z0-9_']*\s*::", stripped)
            if m:
                in_sig = True
                sig_start = ls
                sig_indent = indent
        pos = le + 1
    if in_sig:
        ranges.append((sig_start, pos))
    return ranges


def find_sub_expr_sites(src: str, scan: str) -> list[Site]:
    """Find small sub-expression tokens suitable for replacement.

    Strategy: scan for lowercase identifiers that appear in expression
    position (not in a type signature, not at column 1 of a decl line)
    and that aren't reserved words.
    """
    sites: list[Site] = []
    body_start = find_module_body_start(src)

    signature_line_ranges = compute_sig_full_lines(src)

    def in_sig(offset: int) -> bool:
        for s, e in signature_line_ranges:
            if s <= offset <= e:
                return True
        return False

    # Lines that start decl headers (data/type/class/etc.): skip entirely.
    skip_line_ranges: list[tuple[int, int]] = []
    pos = 0
    for ln in src.split("\n"):
        ls = pos
        le = pos + len(ln)
        first = (ln.split()[0] if ln.split() else "") if not (ln.startswith(" ") or ln.startswith("\t")) else ""
        if first in {"module", "import", "data", "newtype", "type",
                     "class", "instance", "derive", "foreign", "infix",
                     "infixl", "infixr"}:
            # Extend to continuation lines
            end_line = le
            j = pos + len(ln) + 1
            lines_rest = src[j:].split("\n")
            # Simpler: mark only this line, continuations are harder to detect
            skip_line_ranges.append((ls, le))
        pos = le + 1

    def in_skip(offset: int) -> bool:
        for s, e in skip_line_ranges:
            if s <= offset <= e:
                return True
        return False

    for m in IDENT_RE.finditer(scan):
        if m.start() < body_start:
            continue
        word = m.group()
        if word in RESERVED:
            continue
        if in_sig(m.start()):
            continue
        if in_skip(m.start()):
            continue
        # Skip very short single-letter idents that are likely binder names
        # (hard to give a useful hole there).
        if len(word) < 2:
            continue
        # Skip idents that are record labels: preceded by `,` or `{` and followed by `:`
        end = m.end()
        # preceding non-space char
        p = m.start() - 1
        while p >= 0 and scan[p] in " \t":
            p -= 1
        pre = scan[p] if p >= 0 else ""
        # following non-space char
        q = end
        while q < len(scan) and scan[q] in " \t":
            q += 1
        post = scan[q] if q < len(scan) else ""
        if pre in "{," and post == ":":
            continue
        # Skip idents immediately followed by `=` (they're on the LHS of a binding)
        if post == "=" and q + 1 < len(scan) and scan[q + 1] != "=":
            continue
        # Skip `let NAME =` / `where NAME =` definitions — look back on the line
        line_start = scan.rfind("\n", 0, m.start()) + 1
        line_prefix = scan[line_start:m.start()].strip()
        if not line_prefix or line_prefix.endswith("let") or line_prefix.endswith("where"):
            if post == "=" or re.match(r"\s*[^=]*=", scan[end:end + 40]):
                continue
        sites.append(Site(m.start(), m.end(), "sub-expr", line_of(src, m.start())))
    return sites


def find_type_sites(src: str, scan: str) -> list[Site]:
    """Find atomic type tokens inside type signatures."""
    sites: list[Site] = []
    sig_ranges = compute_sig_ranges(src)

    TYPE_CTOR = re.compile(r"\b[A-Z][A-Za-z0-9_']*\b")
    TYPE_VAR = re.compile(r"\b[a-z_][A-Za-z0-9_']*\b")

    TYPE_RESERVED = {"forall", "where", "hiding", "as", "do", "ado",
                     "let", "in", "of", "case", "if", "then", "else"}

    for s, e in sig_ranges:
        slab = scan[s:e]

        # First, find all forall-quantifier regions in this sig so we can skip
        # the variable names inside `forall a b.` (they're binders, not usages).
        forall_binder_spans: list[tuple[int, int]] = []
        for fm in re.finditer(r"\bforall\b", slab):
            # The binders run until the next `.` at the same nesting level.
            # Keep it simple: take the chars from `forall` end to the next `.`
            # that isn't inside parens.
            start = fm.end()
            depth = 0
            k = start
            while k < len(slab):
                c = slab[k]
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                elif c == "." and depth == 0:
                    break
                k += 1
            forall_binder_spans.append((start, k))

        def in_forall(pos: int) -> bool:
            for a, b in forall_binder_spans:
                if a <= pos < b:
                    return True
            return False

        for m in TYPE_CTOR.finditer(slab):
            abs_start = s + m.start()
            abs_end = s + m.end()
            if abs_end < len(scan) and scan[abs_end] == ".":
                continue
            if abs_start > 0 and scan[abs_start - 1] == ".":
                continue
            sites.append(Site(abs_start, abs_end, "type", line_of(src, abs_start)))

        for m in TYPE_VAR.finditer(slab):
            tok = m.group()
            if tok in TYPE_RESERVED:
                continue
            # Skip binders inside `forall a b.`
            if in_forall(m.start()):
                continue
            abs_start = s + m.start()
            abs_end = s + m.end()
            # Skip if preceded by `=>` context tail (`Class a => ...`) — the
            # `a` in `Class a` is a usage, so keep it. But skip if immediately
            # followed by `::` (kind annotation for a binder).
            if abs_end + 1 < len(scan) and scan[abs_end:abs_end + 2] == "::":
                continue
            sites.append(Site(abs_start, abs_end, "type", line_of(src, abs_start)))
    return sites


def candidate_sites(src: str) -> tuple[list[Site], list[Site], list[Site]]:
    """Return (top-rhs, sub-expr, type) candidate pools, shuffled for variety."""
    scan = strip_comments_and_strings(src)
    top = find_top_rhs_sites(src, scan)
    sub = find_sub_expr_sites(src, scan)
    typ = find_type_sites(src, scan)
    rng = random.Random(42 + len(src))
    for pool in (top, sub, typ):
        rng.shuffle(pool)
    return top, sub, typ


def same_line(a: Site, b: Site) -> bool:
    return a.line == b.line


def overlaps(a: Site, b: Site) -> bool:
    return not (a.end <= b.start or b.end <= a.start)


# ---------------------------------------------------------------------------
# Running purs and parsing its output
# ---------------------------------------------------------------------------

HOLE_HEADER_RE = re.compile(r"Hole '([^']+)' has the inferred type")


def parse_hole_output(stderr: str) -> Optional[dict]:
    """Parse `purs` stderr block for a typed-hole diagnostic."""
    m = HOLE_HEADER_RE.search(stderr)
    if not m:
        return None
    hole_name = m.group(1)

    # Position: look for the most recent "at <path>:L:C - L:C" before the Hole header
    pos_match = None
    for pm in re.finditer(r"at\s+[^\s]+:(\d+):(\d+)\s+-\s+(\d+):(\d+)", stderr[: m.start()]):
        pos_match = pm
    position = None
    if pos_match:
        position = (
            int(pos_match.group(1)),
            int(pos_match.group(2)),
            int(pos_match.group(3)),
            int(pos_match.group(4)),
        )

    # Find inferred type block (indented lines after the header)
    after = stderr[m.end():]
    # Skip initial blank line(s)
    lines = after.split("\n")
    idx = 0
    while idx < len(lines) and lines[idx].strip() == "":
        idx += 1
    # Collect indented lines as the type block
    type_lines: list[str] = []
    while idx < len(lines) and (lines[idx].startswith(" ") or lines[idx].startswith("\t")):
        type_lines.append(lines[idx].strip())
        idx += 1
    inferred_type = " ".join(l for l in type_lines if l).strip()

    # Optional blocks
    constraints: list[str] = []
    suggestions: list[str] = []
    context: list[str] = []

    rest_lines = lines[idx:]

    # Walk sections — each section is a header line followed by indented
    # content, terminated by a blank line or another header.
    def collect_indented(start: int) -> tuple[list[str], int]:
        items: list[str] = []
        j = start
        # Skip leading blank lines
        while j < len(rest_lines) and rest_lines[j].strip() == "":
            j += 1
        # Collect indented lines
        while j < len(rest_lines) and (rest_lines[j].startswith(" ") or rest_lines[j].startswith("\t")):
            s = rest_lines[j].strip()
            if s:
                items.append(s)
            j += 1
        return items, j

    j = 0
    while j < len(rest_lines):
        line = rest_lines[j]
        stripped = line.strip()
        if stripped.startswith("You could substitute the hole"):
            items, j = collect_indented(j + 1)
            suggestions.extend(items)
            continue
        if stripped.startswith("in the following context"):
            items, j = collect_indented(j + 1)
            context.extend(items)
            continue
        if stripped.startswith("where ") and "is an unknown type" in stripped:
            constraints.append(stripped)
        j += 1

    return {
        "name": hole_name,
        "position": position,
        "inferred_type": inferred_type,
        "constraints": constraints,
        "suggestions": suggestions,
        "context": context,
    }


def format_expected(parsed: dict) -> str:
    """Format the structured parsed output as expected.txt content."""
    out: list[str] = []
    out.append(f"HOLE: {parsed['name']}")
    if parsed["position"]:
        l1, c1, l2, c2 = parsed["position"]
        out.append(f"POSITION: {l1}:{c1} - {l2}:{c2}")
    out.append("INFERRED_TYPE:")
    out.append(f"  {parsed['inferred_type']}")
    if parsed["constraints"]:
        out.append("CONSTRAINTS:")
        for c in parsed["constraints"]:
            out.append(f"  {c}")
    if parsed["suggestions"]:
        out.append("SUGGESTIONS:")
        for s in parsed["suggestions"]:
            out.append(f"  {s}")
    if parsed["context"]:
        out.append("CONTEXT:")
        for c in parsed["context"]:
            out.append(f"  {c}")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# Per-fixture processing
# ---------------------------------------------------------------------------

def collect_fixtures() -> list[tuple[str, list[Path]]]:
    """Return list of (fixture_name, [purs_files]).

    Matches build.rs conventions: `Name.purs` + optional `Name/` sibling dir,
    or a `Name/` dir with no matching file.
    """
    entries = sorted(PASSING.iterdir())
    file_stems = {p.stem for p in entries if p.is_file() and p.suffix == ".purs"}
    dir_names = {p.name for p in entries if p.is_dir()}

    fixtures: list[tuple[str, list[Path]]] = []
    processed_dirs: set[str] = set()

    for p in entries:
        if p.is_file() and p.suffix == ".purs":
            name = p.stem
            files = [p]
            if name in dir_names:
                files.extend(sorted(q for q in (PASSING / name).rglob("*.purs")))
                processed_dirs.add(name)
            fixtures.append((name, files))
        elif p.is_dir():
            if p.name in processed_dirs or p.name in file_stems:
                continue
            files = sorted(p.rglob("*.purs"))
            if files:
                fixtures.append((p.name, files))
    return fixtures


@dataclass
class SupportBuild:
    output_dir: Path
    support_files: list[Path]


_SUPPORT_CACHE: Optional[SupportBuild] = None


def build_support() -> SupportBuild:
    """Build support packages once and return the reusable output dir."""
    global _SUPPORT_CACHE
    if _SUPPORT_CACHE is not None:
        return _SUPPORT_CACHE

    support_files: list[Path] = []
    for pkg in SUPPORT_PACKAGES:
        src_dir = PACKAGES / pkg / "src"
        support_files.extend(sorted(src_dir.rglob("*.purs")))

    build_dir = Path(tempfile.mkdtemp(prefix="holes-support-"))
    output_dir = build_dir / "output"
    output_dir.mkdir()
    # Dummy module to give purs something to compile
    empty = build_dir / "Empty.purs"
    empty.write_text("module Empty where\n")

    cmd = ["purs", "compile", "--no-prefix", "-o", str(output_dir), str(empty)]
    cmd.extend(str(p) for p in support_files)
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print("Support build failed:", result.stderr, file=sys.stderr)
        sys.exit(1)

    _SUPPORT_CACHE = SupportBuild(output_dir=output_dir, support_files=support_files)
    return _SUPPORT_CACHE


def compile_variant(main_purs: Path, companion_files: list[Path],
                     support: SupportBuild) -> str:
    """Copy the pre-built support output, compile the variant, return stderr."""
    work_dir = Path(tempfile.mkdtemp(prefix="holes-variant-"))
    try:
        out_dir = work_dir / "output"
        # Fast copy preserving mtimes so purs doesn't recompile deps
        subprocess.run(
            ["cp", "-pR", str(support.output_dir), str(out_dir)],
            check=True,
        )
        cmd = ["purs", "compile", "--no-prefix", "-o", str(out_dir),
               str(main_purs)]
        cmd.extend(str(p) for p in companion_files)
        cmd.extend(str(p) for p in support.support_files)
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=90)
        return result.stdout + "\n" + result.stderr
    except subprocess.TimeoutExpired:
        return ""
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)


def process_fixture(name: str, files: list[Path], support: SupportBuild,
                     dry_run: bool = False) -> tuple[str, int]:
    """Generate up to 3 hole variants for one fixture. Returns (name, produced)."""
    # The "main" file is the one named exactly `<name>.purs` or `Main.purs`.
    main_candidates = [f for f in files if f.stem == name or f.name == "Main.purs"]
    if not main_candidates:
        main = files[0]
    else:
        main = main_candidates[0]

    src = main.read_text()
    top, sub, typ = candidate_sites(src)

    # We'll try sites in round-robin across categories. For each variant slot
    # (1..3), pick the next site from a category we haven't drawn from yet
    # in this slot, preferring category diversity. If the site doesn't yield
    # a hole diagnostic, retry with another site (up to max_tries).
    category_order = ["top-rhs", "sub-expr", "type"]
    pools = {"top-rhs": top, "sub-expr": sub, "type": typ}
    used_sites: list[Site] = []

    produced = 0
    # For each of 3 slots, try several sites; skip slot if none work.
    max_tries_per_slot = 12

    for i in range(1, 4):
        # Compute preferred category: rotate through so variant 1 = top-rhs,
        # variant 2 = sub-expr, variant 3 = type. Fall through to other pools.
        preferred = [category_order[(i - 1 + k) % 3] for k in range(3)]
        picked = False
        tried = 0
        for cat in preferred:
            if picked:
                break
            for site in list(pools[cat]):
                if tried >= max_tries_per_slot:
                    break
                tried += 1
                if any(overlaps(site, t) for t in used_sites):
                    pools[cat].remove(site)
                    continue
                # Try this site
                variant_dir = HOLES / f"{name}-{i}"
                if variant_dir.exists():
                    shutil.rmtree(variant_dir)
                variant_dir.mkdir(parents=True)

                variant_src = src[:site.start] + "?test" + src[site.end:]
                variant_main = variant_dir / main.name
                variant_main.write_text(variant_src)

                companion_paths: list[Path] = []
                for f in files:
                    if f == main:
                        continue
                    try:
                        rel = f.relative_to(PASSING / name)
                    except ValueError:
                        rel = Path(f.name)
                    dst = variant_dir / rel
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy(f, dst)
                    companion_paths.append(dst)

                # Copy .js FFI companions if they exist (match by stem)
                for f in files:
                    js = f.with_suffix(".js")
                    if js.exists():
                        try:
                            rel = js.relative_to(PASSING / name)
                        except ValueError:
                            rel = Path(js.name)
                        dst = variant_dir / rel
                        if not dst.exists():
                            dst.parent.mkdir(parents=True, exist_ok=True)
                            shutil.copy(js, dst)

                stderr = compile_variant(variant_main, companion_paths, support)
                parsed = parse_hole_output(stderr)
                pools[cat].remove(site)
                if parsed is None:
                    shutil.rmtree(variant_dir)
                    continue

                (variant_dir / "expected.txt").write_text(format_expected(parsed))
                used_sites.append(site)
                produced += 1
                picked = True
                break
            if picked:
                break
        if not picked:
            # Could not fill this slot
            pass

    return (name, produced)


# ---------------------------------------------------------------------------
# Entrypoint
# ---------------------------------------------------------------------------

def worker(args):
    name, files, support = args
    try:
        return process_fixture(name, files, support)
    except Exception as e:
        return (name, -1)  # signal error


def main():
    filter_names = set(sys.argv[1:]) if len(sys.argv) > 1 else None

    HOLES.mkdir(parents=True, exist_ok=True)

    print("Pre-building support packages...", flush=True)
    support = build_support()
    print(f"  Support output: {support.output_dir}", flush=True)

    SKIP_FIXTURES = {"BigFunction"}

    fixtures = collect_fixtures()
    fixtures = [(n, f) for (n, f) in fixtures if n not in SKIP_FIXTURES]
    if filter_names:
        fixtures = [(n, f) for (n, f) in fixtures if n in filter_names]
    print(f"Processing {len(fixtures)} fixtures...", flush=True)

    threads = int(os.environ.get("FIXTURE_THREADS", "8"))

    total_variants = 0
    zero_fixtures: list[str] = []
    errors: list[str] = []

    if threads > 1:
        with mp.Pool(threads) as pool:
            tasks = [(n, f, support) for (n, f) in fixtures]
            for i, (name, produced) in enumerate(pool.imap_unordered(worker, tasks), start=1):
                if produced == -1:
                    errors.append(name)
                else:
                    total_variants += produced
                    if produced == 0:
                        zero_fixtures.append(name)
                if i % 25 == 0 or i == len(fixtures):
                    print(f"  {i}/{len(fixtures)}  variants so far: {total_variants}",
                          flush=True)
    else:
        for i, (name, files) in enumerate(fixtures, start=1):
            name_, produced = process_fixture(name, files, support)
            if produced == -1:
                errors.append(name)
            else:
                total_variants += produced
                if produced == 0:
                    zero_fixtures.append(name)
            if i % 10 == 0 or i == len(fixtures):
                print(f"  {i}/{len(fixtures)}  variants so far: {total_variants}",
                      flush=True)

    print()
    print(f"Done. Total variants: {total_variants}")
    print(f"Fixtures with 0 variants: {len(zero_fixtures)}")
    if zero_fixtures[:10]:
        print("  (first 10):", zero_fixtures[:10])
    if errors:
        print(f"Errors: {len(errors)}")
        print("  (first 10):", errors[:10])


if __name__ == "__main__":
    main()
