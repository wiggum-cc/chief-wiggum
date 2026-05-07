"""Entry point for wiggum-tui."""

import sys
from pathlib import Path


def main():
    """Main entry point."""
    from wiggum_tui.app import WiggumApp

    # Find .ralph directory - check current dir and parents
    ralph_dir = None
    check_dir = Path.cwd()

    for _ in range(10):  # Check up to 10 levels
        candidate = check_dir / ".ralph"
        if candidate.is_dir():
            ralph_dir = candidate
            break
        if check_dir.parent == check_dir:
            break
        check_dir = check_dir.parent

    if ralph_dir is None:
        print("Error: No .ralph directory found. Run 'wiggum init' first.")
        sys.exit(1)

    app = WiggumApp(ralph_dir=ralph_dir)
    app.run()


if __name__ == "__main__":
    main()
