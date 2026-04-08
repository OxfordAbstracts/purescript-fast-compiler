#!/usr/bin/env bash
set -euo pipefail

# Build the VS Code extension and produce a .vsix bundle.
# Usage: ./editors/code/build.sh
#
# Output: editors/code/pfc-lsp-<version>.vsix

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
EXT_DIR="$ROOT/editors/code"

cd "$EXT_DIR"

# Install dependencies
echo "==> Installing dependencies..."
npm install --silent

# Compile TypeScript
echo "==> Compiling TypeScript..."
npm run build

# Package as .vsix
echo "==> Packaging extension..."
vsce package --no-dependencies

VSIX=$(ls -t *.vsix 2>/dev/null | head -1)
if [ -n "$VSIX" ]; then
    echo "==> Built: $EXT_DIR/$VSIX"
    echo ""
    echo "Install with: code --install-extension $EXT_DIR/$VSIX"
else
    echo "ERROR: .vsix file not found after packaging"
    exit 1
fi
