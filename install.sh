#!/usr/bin/env bash
# Install Chief Wiggum to ~/.claude/chief-wiggum

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGET="${HOME}/.claude/chief-wiggum"

echo "Installing Chief Wiggum to $TARGET"

# Create target directory
mkdir -p "$TARGET"

# Copy files
echo "Copying files..."
cp -r "$SCRIPT_DIR/bin" "$TARGET/"
cp -r "$SCRIPT_DIR/lib" "$TARGET/"
cp -r "$SCRIPT_DIR/hooks" "$TARGET/"
cp -r "$SCRIPT_DIR/skills" "$TARGET/"
cp -r "$SCRIPT_DIR/config" "$TARGET/"

# Make scripts executable
chmod +x "$TARGET/bin/"*
chmod +x "$TARGET/hooks/callbacks/"*

echo ""
echo "✓ Installed to $TARGET"
echo ""
echo "Next steps:"
echo "  1. Add $TARGET/bin to your PATH:"
echo "     echo 'export PATH=\"\$HOME/.claude/chief-wiggum/bin:\$PATH\"' >> ~/.bashrc"
echo "     source ~/.bashrc"
echo ""
echo "  2. Navigate to a project and initialize:"
echo "     cd /path/to/your/project"
echo "     chief init"
echo ""
echo "  3. Edit .ralph/kanban.md to add your tasks"
echo ""
echo "  4. Run chief to start workers:"
echo "     chief run"
echo ""
