#!/usr/bin/env bash
# Install Chief Wiggum to ~/.claude/chief-wiggum using symlinks
# Useful for development - changes to source files take effect immediately

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGET="${HOME}/.claude/chief-wiggum"
SKILLS_TARGET="${HOME}/.claude/skills"

# Check for required binaries
check_dependencies() {
    local missing=()

    # Core tools (likely need manual installation)
    local core_bins=(jq git gh curl claude)

    # Standard POSIX utilities
    local posix_bins=(grep cat date sed rm head find awk basename sort mkdir kill cut ls tail sleep mv xargs tr wc tee ps dirname tac stat)

    # UUID generation
    local uuid_bins=(uuidgen)

    local all_bins=("${core_bins[@]}" "${posix_bins[@]}" "${uuid_bins[@]}")

    for bin in "${all_bins[@]}"; do
        if ! command -v "$bin" &>/dev/null; then
            missing+=("$bin")
        fi
    done

    if [[ ${#missing[@]} -gt 0 ]]; then
        echo "Error: Missing required dependencies: ${missing[*]}"
        echo ""
        echo "Please install them using your package manager."
        echo ""
        echo "Core tools (jq, git, gh, curl, claude):"
        echo "  apt:    sudo apt install jq git gh curl"
        echo "  brew:   brew install jq git gh curl"
        echo "  pacman: sudo pacman -S jq git github-cli curl"
        echo "  claude: https://docs.anthropic.com/en/docs/claude-code"
        echo ""
        echo "UUID generation (uuidgen):"
        echo "  apt:    sudo apt install uuid-runtime"
        echo "  brew:   (included with macOS)"
        echo "  pacman: sudo pacman -S util-linux"
        echo ""
        echo "POSIX utilities should be available on most systems."
        echo "If missing, install coreutils/util-linux from your package manager."
        exit 1
    fi

    echo "All required binaries found (${#all_bins[@]} total)"
}

# Check for uv and install if missing
ensure_uv() {
    if command -v uv &>/dev/null; then
        echo "uv is already installed"
        return 0
    fi

    echo "Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh

    # Source the uv env for current session
    # shellcheck disable=SC1091
    if [[ -f "$HOME/.local/bin/env" ]]; then
        source "$HOME/.local/bin/env"
    elif [[ -f "$HOME/.cargo/env" ]]; then
        source "$HOME/.cargo/env"
    fi

    if ! command -v uv &>/dev/null; then
        echo "Error: uv installation failed or not in PATH"
        echo "Please install uv manually: https://docs.astral.sh/uv/getting-started/installation/"
        exit 1
    fi

    echo "uv installed successfully"
}

# Run uv sync in tui directory
setup_tui() {
    local tui_dir="$1/tui"
    if [[ -d "$tui_dir" ]] && [[ -f "$tui_dir/pyproject.toml" ]]; then
        echo "Setting up TUI Python environment..."
        (cd "$tui_dir" && uv sync)
        echo "TUI environment ready"
    fi
}

echo "Installing Chief Wiggum to $TARGET (symlink mode)"

# Check dependencies first
check_dependencies
ensure_uv

# Remove existing installation if present
if [[ -e "$TARGET" ]]; then
    echo "Removing existing installation at $TARGET"
    [[ -n "$TARGET" && "$TARGET" != "/" ]] && rm -rf "$TARGET"
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
            [[ -n "$skill_link" && "$skill_link" != "/" ]] && rm -rf "$skill_link"
        fi
        ln -s "$skill_dir" "$skill_link"
        echo "  Linked $skill_name -> $skill_link"
    fi
done

# Setup TUI Python environment
setup_tui "$SCRIPT_DIR"

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
