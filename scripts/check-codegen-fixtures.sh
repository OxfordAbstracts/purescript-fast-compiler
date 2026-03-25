#!/usr/bin/env bash
#
# Verify that all codegen fixture .purs files compile successfully with the
# reference PureScript compiler ("purs").
#
# Usage: ./scripts/check-codegen-fixtures.sh
#
set -euo pipefail

FIXTURE_DIR="tests/fixtures/codegen"
PACKAGES_DIR="tests/fixtures/packages"
OUTPUT_DIR=$(mktemp -d)

trap 'rm -rf "$OUTPUT_DIR"' EXIT

# Collect support-package globs (prelude, newtype, safe-coerce, unsafe-coerce)
SUPPORT_GLOBS=()
for pkg in prelude newtype safe-coerce unsafe-coerce; do
    SUPPORT_GLOBS+=("$PACKAGES_DIR/$pkg/src/**/*.purs")
done

PASS=0
FAIL=0
FAILURES=()

echo "=== Checking codegen fixtures against reference compiler (purs) ==="
echo ""

# --- Single-module fixtures ---
for purs_file in "$FIXTURE_DIR"/*.purs; do
    name=$(basename "$purs_file" .purs)
    out="$OUTPUT_DIR/$name"

    if purs compile --no-prefix -o "$out" "$purs_file" "${SUPPORT_GLOBS[@]}" 2>/dev/null; then
        # Check that the module's index.js was actually produced
        module_name="$name"
        if [[ -f "$out/$module_name/index.js" ]]; then
            echo "  PASS  $name"
            PASS=$((PASS + 1))
        else
            echo "  FAIL  $name  (compiled but no output/index.js)"
            FAIL=$((FAIL + 1))
            FAILURES+=("$name (no output)")
        fi
    else
        echo "  FAIL  $name"
        FAIL=$((FAIL + 1))
        FAILURES+=("$name")
        # Print the error for debugging
        echo "        Error output:"
        purs compile --no-prefix -o "$out" "$purs_file" "${SUPPORT_GLOBS[@]}" 2>&1 | sed 's/^/        /' || true
        echo ""
    fi
done

# --- Multi-module fixtures ---
for dir in "$FIXTURE_DIR"/*/; do
    dir_name=$(basename "$dir")

    # Skip the original-compiler-output reference dir
    [[ "$dir_name" == "original-compiler-output" ]] && continue

    out="$OUTPUT_DIR/$dir_name"
    purs_files=("$dir"*.purs)

    if purs compile --no-prefix -o "$out" "${purs_files[@]}" "${SUPPORT_GLOBS[@]}" 2>/dev/null; then
        echo "  PASS  $dir_name/ (multi-module)"
        PASS=$((PASS + 1))
    else
        echo "  FAIL  $dir_name/ (multi-module)"
        FAIL=$((FAIL + 1))
        FAILURES+=("$dir_name/")
        echo "        Error output:"
        purs compile --no-prefix -o "$out" "${purs_files[@]}" "${SUPPORT_GLOBS[@]}" 2>&1 | sed 's/^/        /' || true
        echo ""
    fi
done

echo ""
echo "=== Results ==="
echo "  Passed: $PASS"
echo "  Failed: $FAIL"

if [[ ${#FAILURES[@]} -gt 0 ]]; then
    echo ""
    echo "  Failed fixtures:"
    for f in "${FAILURES[@]}"; do
        echo "    - $f"
    done
    exit 1
fi
