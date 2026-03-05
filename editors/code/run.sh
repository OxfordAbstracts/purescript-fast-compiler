#!/usr/bin/env bash
set -euo pipefail

# Run script: build and launch VS Code with extension (no watchers).
# Usage: ./editors/code/run.sh [path/to/file.purs]

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
EXT_DIR="$ROOT/editors/code"

FILE="${1:-}"

# --- Build ---
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
code "${VSCODE_ARGS[@]}"
