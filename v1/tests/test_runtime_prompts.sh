#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/runtime/runtime-prompts.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Reset guard to allow re-sourcing in tests
unset _RUNTIME_PROMPTS_LOADED
source "$WIGGUM_HOME/lib/runtime/runtime-prompts.sh"

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    # Reset module state for clean test isolation
    _PROMPT_PRE_SYSTEM=""
    _PROMPT_POST_SYSTEM=""
    _PROMPT_PRE_USER=""
    _PROMPT_POST_USER=""
    _PROMPTS_INITIALIZED=0
    # Clear env vars
    unset WIGGUM_PROMPT_PRE_SYSTEM 2>/dev/null || true
    unset WIGGUM_PROMPT_POST_SYSTEM 2>/dev/null || true
    unset WIGGUM_PROMPT_PRE_USER 2>/dev/null || true
    unset WIGGUM_PROMPT_POST_USER 2>/dev/null || true
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# _runtime_resolve_prompt_value Tests
# =============================================================================

test_resolve_empty_value() {
    local result
    result=$(_runtime_resolve_prompt_value "")
    assert_equals "" "$result" "Empty value should resolve to empty string"
}

test_resolve_literal_value() {
    local result
    result=$(_runtime_resolve_prompt_value "Hello world")
    assert_equals "Hello world" "$result" "Literal value should be returned as-is"
}

test_resolve_file_reference_exists() {
    echo "File content here" > "$TEST_DIR/prompt.md"
    local result
    result=$(_runtime_resolve_prompt_value "@$TEST_DIR/prompt.md")
    assert_equals "File content here" "$result" "File reference should return file contents"
}

test_resolve_file_reference_missing() {
    local result
    result=$(_runtime_resolve_prompt_value "@$TEST_DIR/nonexistent.md" 2>/dev/null)
    assert_equals "" "$result" "Missing file reference should resolve to empty string"
}

test_resolve_file_reference_relative() {
    mkdir -p "$WIGGUM_HOME/config/prompts"
    echo "Relative file content" > "$WIGGUM_HOME/config/prompts/_test_prompt.md"
    local result
    result=$(_runtime_resolve_prompt_value "@config/prompts/_test_prompt.md")
    assert_equals "Relative file content" "$result" "Relative @file should resolve relative to WIGGUM_HOME"
    rm -f "$WIGGUM_HOME/config/prompts/_test_prompt.md"
}

test_resolve_file_reference_multiline() {
    printf "Line 1\nLine 2\nLine 3" > "$TEST_DIR/multi.md"
    local result
    result=$(_runtime_resolve_prompt_value "@$TEST_DIR/multi.md")
    local expected
    expected=$(printf "Line 1\nLine 2\nLine 3")
    assert_equals "$expected" "$result" "File reference should preserve multiline content"
}

# =============================================================================
# runtime_prompts_init Tests
# =============================================================================

test_init_defaults_to_empty() {
    # No config, no env vars - should all be empty
    export WIGGUM_HOME="$TEST_DIR/fake_home"
    mkdir -p "$WIGGUM_HOME"
    runtime_prompts_init "claude"
    assert_equals "" "$_PROMPT_PRE_SYSTEM" "Pre-system should default to empty"
    assert_equals "" "$_PROMPT_POST_SYSTEM" "Post-system should default to empty"
    assert_equals "" "$_PROMPT_PRE_USER" "Pre-user should default to empty"
    assert_equals "" "$_PROMPT_POST_USER" "Post-user should default to empty"
    WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"
}

test_init_env_vars_override() {
    export WIGGUM_PROMPT_PRE_SYSTEM="env-pre-sys"
    export WIGGUM_PROMPT_POST_SYSTEM="env-post-sys"
    export WIGGUM_PROMPT_PRE_USER="env-pre-usr"
    export WIGGUM_PROMPT_POST_USER="env-post-usr"
    runtime_prompts_init "claude"
    assert_equals "env-pre-sys" "$_PROMPT_PRE_SYSTEM" "Env var should set pre-system"
    assert_equals "env-post-sys" "$_PROMPT_POST_SYSTEM" "Env var should set post-system"
    assert_equals "env-pre-usr" "$_PROMPT_PRE_USER" "Env var should set pre-user"
    assert_equals "env-post-usr" "$_PROMPT_POST_USER" "Env var should set post-user"
}

test_init_config_file() {
    local fake_home="$TEST_DIR/fake_home"
    mkdir -p "$fake_home/config"
    cat > "$fake_home/config/config.json" << 'EOF'
{
  "runtime": {
    "backends": {
      "claude": {
        "prompts": {
          "pre_system": "config-pre-sys",
          "post_system": "config-post-sys",
          "pre_user": "config-pre-usr",
          "post_user": "config-post-usr"
        }
      }
    }
  }
}
EOF
    export WIGGUM_HOME="$fake_home"
    runtime_prompts_init "claude"
    assert_equals "config-pre-sys" "$_PROMPT_PRE_SYSTEM" "Config should set pre-system"
    assert_equals "config-post-sys" "$_PROMPT_POST_SYSTEM" "Config should set post-system"
    assert_equals "config-pre-usr" "$_PROMPT_PRE_USER" "Config should set pre-user"
    assert_equals "config-post-usr" "$_PROMPT_POST_USER" "Config should set post-user"
    WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"
}

test_init_env_overrides_config() {
    local fake_home="$TEST_DIR/fake_home"
    mkdir -p "$fake_home/config"
    cat > "$fake_home/config/config.json" << 'EOF'
{
  "runtime": {
    "backends": {
      "claude": {
        "prompts": {
          "pre_system": "from-config",
          "post_user": "from-config-post"
        }
      }
    }
  }
}
EOF
    export WIGGUM_HOME="$fake_home"
    export WIGGUM_PROMPT_PRE_SYSTEM="from-env"
    runtime_prompts_init "claude"
    assert_equals "from-env" "$_PROMPT_PRE_SYSTEM" "Env var should override config"
    assert_equals "from-config-post" "$_PROMPT_POST_USER" "Config should be used when no env var"
    WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"
}

test_init_file_reference_in_config() {
    local fake_home="$TEST_DIR/fake_home"
    mkdir -p "$fake_home/config/prompts"
    echo "System prefix from file" > "$fake_home/config/prompts/pre-system.md"
    cat > "$fake_home/config/config.json" << 'EOF'
{
  "runtime": {
    "backends": {
      "claude": {
        "prompts": {
          "pre_system": "@config/prompts/pre-system.md"
        }
      }
    }
  }
}
EOF
    export WIGGUM_HOME="$fake_home"
    runtime_prompts_init "claude"
    assert_equals "System prefix from file" "$_PROMPT_PRE_SYSTEM" "@file in config should be resolved"
    WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"
}

test_init_project_config_overrides_global() {
    local fake_home="$TEST_DIR/fake_home"
    mkdir -p "$fake_home/config"
    cat > "$fake_home/config/config.json" << 'EOF'
{
  "runtime": {
    "backends": {
      "claude": {
        "prompts": {
          "pre_system": "global-value"
        }
      }
    }
  }
}
EOF
    local fake_ralph="$TEST_DIR/fake_project"
    mkdir -p "$fake_ralph/.ralph"
    cat > "$fake_ralph/.ralph/config.json" << 'EOF'
{
  "runtime": {
    "backends": {
      "claude": {
        "prompts": {
          "pre_system": "project-value"
        }
      }
    }
  }
}
EOF
    export WIGGUM_HOME="$fake_home"
    export RALPH_DIR="$fake_ralph"
    runtime_prompts_init "claude"
    assert_equals "project-value" "$_PROMPT_PRE_SYSTEM" "Project config should override global config"
    unset RALPH_DIR
    WIGGUM_HOME="$(cd "$TESTS_DIR/.." && pwd)"
}

test_init_idempotent() {
    export WIGGUM_PROMPT_PRE_SYSTEM="first-call"
    runtime_prompts_init "claude"
    assert_equals "first-call" "$_PROMPT_PRE_SYSTEM" "First init should set value"

    # Change env var and call again - should NOT change (idempotent)
    export WIGGUM_PROMPT_PRE_SYSTEM="second-call"
    runtime_prompts_init "claude"
    assert_equals "first-call" "$_PROMPT_PRE_SYSTEM" "Second init should be no-op (idempotent)"
}

# =============================================================================
# runtime_wrap_system Tests
# =============================================================================

test_wrap_system_no_wrappers() {
    local result
    result=$(runtime_wrap_system "Original system prompt")
    assert_equals "Original system prompt" "$result" "No wrappers should return original"
}

test_wrap_system_pre_only() {
    _PROMPT_PRE_SYSTEM="[PREFIX]"
    local result
    result=$(runtime_wrap_system "Original")
    local expected
    expected=$(printf "[PREFIX]\nOriginal")
    assert_equals "$expected" "$result" "Pre-only should prepend with newline"
}

test_wrap_system_post_only() {
    _PROMPT_POST_SYSTEM="[SUFFIX]"
    local result
    result=$(runtime_wrap_system "Original")
    local expected
    expected=$(printf "Original\n[SUFFIX]")
    assert_equals "$expected" "$result" "Post-only should append with newline"
}

test_wrap_system_both() {
    _PROMPT_PRE_SYSTEM="[PREFIX]"
    _PROMPT_POST_SYSTEM="[SUFFIX]"
    local result
    result=$(runtime_wrap_system "Original")
    local expected
    expected=$(printf "[PREFIX]\nOriginal\n[SUFFIX]")
    assert_equals "$expected" "$result" "Both should wrap with newlines"
}

test_wrap_system_empty_prompt() {
    _PROMPT_PRE_SYSTEM="[PREFIX]"
    _PROMPT_POST_SYSTEM="[SUFFIX]"
    local result
    result=$(runtime_wrap_system "")
    local expected
    expected=$(printf "[PREFIX]\n\n[SUFFIX]")
    assert_equals "$expected" "$result" "Empty prompt should still get wrapped"
}

# =============================================================================
# runtime_wrap_user Tests
# =============================================================================

test_wrap_user_no_wrappers() {
    local result
    result=$(runtime_wrap_user "Original user prompt")
    assert_equals "Original user prompt" "$result" "No wrappers should return original"
}

test_wrap_user_pre_only() {
    _PROMPT_PRE_USER="[USER-PREFIX]"
    local result
    result=$(runtime_wrap_user "Original")
    local expected
    expected=$(printf "[USER-PREFIX]\nOriginal")
    assert_equals "$expected" "$result" "Pre-only should prepend with newline"
}

test_wrap_user_post_only() {
    _PROMPT_POST_USER="[USER-SUFFIX]"
    local result
    result=$(runtime_wrap_user "Original")
    local expected
    expected=$(printf "Original\n[USER-SUFFIX]")
    assert_equals "$expected" "$result" "Post-only should append with newline"
}

test_wrap_user_both() {
    _PROMPT_PRE_USER="[USER-PREFIX]"
    _PROMPT_POST_USER="[USER-SUFFIX]"
    local result
    result=$(runtime_wrap_user "Original")
    local expected
    expected=$(printf "[USER-PREFIX]\nOriginal\n[USER-SUFFIX]")
    assert_equals "$expected" "$result" "Both should wrap with newlines"
}

# =============================================================================
# Run All Tests
# =============================================================================

# _runtime_resolve_prompt_value tests
run_test test_resolve_empty_value
run_test test_resolve_literal_value
run_test test_resolve_file_reference_exists
run_test test_resolve_file_reference_missing
run_test test_resolve_file_reference_relative
run_test test_resolve_file_reference_multiline

# runtime_prompts_init tests
run_test test_init_defaults_to_empty
run_test test_init_env_vars_override
run_test test_init_config_file
run_test test_init_env_overrides_config
run_test test_init_file_reference_in_config
run_test test_init_project_config_overrides_global
run_test test_init_idempotent

# runtime_wrap_system tests
run_test test_wrap_system_no_wrappers
run_test test_wrap_system_pre_only
run_test test_wrap_system_post_only
run_test test_wrap_system_both
run_test test_wrap_system_empty_prompt

# runtime_wrap_user tests
run_test test_wrap_user_no_wrappers
run_test test_wrap_user_pre_only
run_test test_wrap_user_post_only
run_test test_wrap_user_both

print_test_summary
exit_with_test_result
