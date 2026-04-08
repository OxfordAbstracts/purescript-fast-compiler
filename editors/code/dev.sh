#!/usr/bin/env bash
set -euo pipefail

# Dev script: build, launch VS Code with extension, and watch for changes.
# Usage: ./editors/code/dev.sh [path/to/file.purs]

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
EXT_DIR="$ROOT/editors/code"

FILE="${1:-}"

# --- Initial builds ---
echo "==> Building pfc (cargo build)..."
(cd "$ROOT" && cargo build)

echo "==> Building extension (tsc)..."
(cd "$EXT_DIR" && npm run build)

# --- Put debug binary on PATH so the extension finds "pfc" ---
export PATH="$ROOT/target/debug:$PATH"

# --- Launch VS Code ---
VSCODE_ARGS=(--extensionDevelopmentPath "$EXT_DIR")
if [ -n "$FILE" ]; then
    VSCODE_ARGS+=("$FILE")
fi

echo "==> Launching VS Code..."
code "${VSCODE_ARGS[@]}" &
VSCODE_PID=$!

# --- Background watchers ---
PIDS=()

cleanup() {
    echo ""
    echo "==> Shutting down watchers..."
    for pid in "${PIDS[@]}"; do
        kill "$pid" 2>/dev/null || true
    done
    wait 2>/dev/null
}
trap cleanup EXIT INT TERM

# Watch TypeScript extension source
echo "==> Starting esbuild --watch..."
(cd "$EXT_DIR" && npm run watch) &
PIDS+=($!)

# Watch Rust source and rebuild
echo "==> Starting cargo watch..."
(cd "$ROOT" && cargo watch -w src -s 'cargo build 2>&1 && echo "==> pfc rebuilt. Reload VS Code window (Cmd+Shift+P → Reload Window) to restart LSP."') &
PIDS+=($!)

echo ""
echo "Watchers running. Press Ctrl+C to stop."
echo "After Rust rebuilds, reload the VS Code window to restart the LSP server."
echo ""

# Wait for any child to exit
wait
