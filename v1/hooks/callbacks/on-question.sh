#!/usr/bin/env bash
# Callback: Auto-answer permission requests

REQUEST_TYPE="$1"

# Auto-allow safe operations
case "$REQUEST_TYPE" in
  "file_read"|"file_edit"|"bash_read_only")
    echo "ALLOW"
    ;;
  "bash_write"|"git_commit")
    echo "ALLOW"  # Workers operate in isolated worktrees
    ;;
  *)
    echo "DENY"
    ;;
esac
