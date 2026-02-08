#!/usr/bin/env bash
# Download all PureScript package set source files for parser testing
# Uses parallel downloads for speed
set -euo pipefail

FIXTURES_DIR="$(cd "$(dirname "$0")" && pwd)"
PACKAGES_LIST="$FIXTURES_DIR/packages.list"
DEST_DIR="$FIXTURES_DIR/packages"
MAX_PARALLEL=20

mkdir -p "$DEST_DIR"

total=$(wc -l < "$PACKAGES_LIST" | tr -d ' ')
echo "Downloading $total packages into $DEST_DIR (${MAX_PARALLEL} parallel)..."

download_package() {
    local name="$1" repo="$2" version="$3"
    local tmp_dir
    tmp_dir="$(mktemp -d)"

    if git clone --quiet --depth 1 --branch "$version" "$repo" "$tmp_dir/$name" 2>/dev/null; then
        local copied=0
        for dir in src test; do
            if [ -d "$tmp_dir/$name/$dir" ]; then
                find "$tmp_dir/$name/$dir" \( -name '*.purs' -o -name '*.js' \) -print0 | while IFS= read -r -d '' f; do
                    rel="${f#$tmp_dir/$name/}"
                    mkdir -p "$DEST_DIR/$name/$(dirname "$rel")"
                    cp "$f" "$DEST_DIR/$name/$rel"
                done
            fi
        done
        local c
        c=$(find "$DEST_DIR/$name" \( -name '*.purs' -o -name '*.js' \) 2>/dev/null | wc -l | tr -d ' ')
        if [ "$c" -gt 0 ]; then
            echo "ok $name@$version ($c files)"
        else
            echo "ok $name@$version (no .purs/.js files)"
        fi
    else
        echo "FAILED $name@$version"
    fi

    rm -rf "$tmp_dir"
}

export -f download_package
export DEST_DIR

# Run downloads in parallel using xargs
cat "$PACKAGES_LIST" | xargs -P "$MAX_PARALLEL" -L 1 bash -c 'download_package "$@"' _

echo ""
echo "Done!"
echo "Total .purs files: $(find "$DEST_DIR" -name '*.purs' | wc -l | tr -d ' ')"
echo "Total .js files: $(find "$DEST_DIR" -name '*.js' | wc -l | tr -d ' ')"
