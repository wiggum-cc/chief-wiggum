#!/usr/bin/env bash
# Install Chief Wiggum to ~/.claude/chief-wiggum using symlinks
# Useful for development - changes to source files take effect immediately

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGET="${HOME}/.claude/chief-wiggum"
SKILLS_TARGET="${HOME}/.claude/skills"

echo "Installing Chief Wiggum to $TARGET (symlink mode)"

# Remove existing installation if present
if [[ -e "$TARGET" ]]; then
    echo "Removing existing installation at $TARGET"
    rm -rf "$TARGET"
fi

# Create parent directory if needed
mkdir -p "$(dirname "$TARGET")"

# Create symlink to source directory
ln -s "$SCRIPT_DIR" "$TARGET"

echo "Symlinked $SCRIPT_DIR -> $TARGET"

# Install skills to ~/.claude/skills
echo ""
echo "Installing skills to $SKILLS_TARGET"

mkdir -p "$SKILLS_TARGET"

# Link each skill directory
for skill_dir in "$SCRIPT_DIR/skills"/*/; do
    if [[ -d "$skill_dir" ]]; then
        skill_name=$(basename "$skill_dir")
        # Skip the old chief-wiggum nested structure if it exists
        if [[ "$skill_name" == "chief-wiggum" ]]; then
            continue
        fi
        skill_link="$SKILLS_TARGET/$skill_name"
        if [[ -e "$skill_link" ]]; then
            echo "  Removing existing $skill_link"
            rm -rf "$skill_link"
        fi
        ln -s "$skill_dir" "$skill_link"
        echo "  Linked $skill_name -> $skill_link"
    fi
done

echo ""
echo "Installation complete!"
echo ""
echo "Next steps:"
echo "  1. Add $TARGET/bin to your PATH:"
echo "     echo 'export PATH=\"\$HOME/.claude/chief-wiggum/bin:\$PATH\"' >> ~/.bashrc"
echo "     source ~/.bashrc"
echo ""
echo "  2. Navigate to a project and initialize:"
echo "     cd /path/to/your/project"
echo "     wiggum init"
echo ""
echo "  3. Edit .ralph/kanban.md to add your tasks"
echo ""
echo "  4. Run wiggum to start workers:"
echo "     wiggum run"
echo ""
