#!/usr/bin/env bash
# wdoc-add.sh - Download documentation and clone source for packages
#
# Handles `wdoc add` by downloading web docs via wget --mirror and
# cloning git repos. HTML is converted to markdown via a stdlib Python
# converter that extracts main content and strips site chrome.
#
# Storage layout under .ralph/docs/<package>/:
#   web-raw/  - Original mirrored HTML
#   web/      - Converted markdown files
#   git/      - Shallow git clone
set -euo pipefail

[ -n "${_WDOC_ADD_LOADED:-}" ] && return 0
_WDOC_ADD_LOADED=1

source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

# Add a package: download docs and/or clone source
#
# Args:
#   name    - Package name (e.g., "textual")
#   doc_url - Documentation URL (optional, empty string to skip)
#   src_url - Git repository URL (optional, empty string to skip)
#
# Returns: 0 on success, 1 on error
wdoc_add() {
    local name="$1"
    local doc_url="${2:-}"
    local src_url="${3:-}"

    if [[ -z "$name" ]]; then
        log_error "wdoc_add: package name required"
        return 1
    fi

    if [[ -z "$doc_url" && -z "$src_url" ]]; then
        log_error "wdoc_add: at least one of -doc or -src must be provided"
        return 1
    fi

    local docs_dir="$RALPH_DIR/docs/$name"
    safe_path "$docs_dir" "docs_dir" || return 1
    mkdir -p "$docs_dir"

    # Register the package first
    wdoc_registry_add "$name" "$doc_url" "$src_url"
    log_info "Registered package: $name"

    # Download documentation
    if [[ -n "$doc_url" ]]; then
        if _wdoc_download_docs "$name" "$doc_url" "$docs_dir"; then
            wdoc_registry_set_timestamp "$name" "doc_fetched_at"
            log_info "Documentation downloaded for $name"
        else
            log_warn "Documentation download failed for $name (continuing)"
        fi
    fi

    # Clone source repository
    if [[ -n "$src_url" ]]; then
        if _wdoc_clone_source "$name" "$src_url" "$docs_dir"; then
            wdoc_registry_set_timestamp "$name" "src_cloned_at"
            log_info "Source cloned for $name"
        else
            log_warn "Source clone failed for $name (continuing)"
        fi
    fi

    log_info "Package $name added successfully"
    return 0
}

# Download and mirror documentation website
#
# Args:
#   name    - Package name
#   doc_url - Documentation URL
#   docs_dir - Base docs directory for this package
#
# Returns: 0 on success, 1 on error
_wdoc_download_docs() {
    local name="$1"
    local doc_url="$2"
    local docs_dir="$3"

    local raw_dir="$docs_dir/web-raw"
    local md_dir="$docs_dir/web"
    safe_path "$raw_dir" "raw_dir" || return 1
    safe_path "$md_dir" "md_dir" || return 1

    # Clean previous download
    if [[ -d "$raw_dir" ]]; then
        rm -rf "$raw_dir"
    fi

    mkdir -p "$raw_dir"

    # Extract domain for --domains restriction
    local domain
    domain=$(echo "$doc_url" | sed -E 's|^https?://([^/]+).*|\1|')

    log_info "Mirroring documentation from $doc_url"

    local exit_code=0
    wget --mirror \
         --convert-links \
         --adjust-extension \
         --page-requisites \
         --no-parent \
         --domains="$domain" \
         --reject="*.png,*.jpg,*.jpeg,*.gif,*.svg,*.ico,*.woff,*.woff2,*.ttf,*.eot,*.mp4,*.webm,*.zip,*.tar.gz" \
         --timeout=30 \
         --tries=3 \
         --quiet \
         -P "$raw_dir" \
         "$doc_url" 2>&1 || exit_code=$?

    # wget returns 8 for some server responses that are actually fine
    if [[ "$exit_code" -ne 0 && "$exit_code" -ne 8 ]]; then
        log_warn "wget exited with code $exit_code (may be partial download)"
    fi

    # Check if we got any HTML files
    local html_count
    html_count=$(find "$raw_dir" -name "*.html" -o -name "*.htm" 2>/dev/null | head -20 | wc -l)
    html_count="${html_count:-0}"

    if [[ "$html_count" -eq 0 ]]; then
        log_error "No HTML files downloaded from $doc_url"
        return 1
    fi

    log_info "Downloaded $html_count HTML files, converting to markdown"

    # Convert HTML to markdown
    _wdoc_convert_html_to_md "$raw_dir" "$md_dir"
}

# Convert HTML files to markdown
#
# Args:
#   raw_dir - Directory containing HTML files
#   md_dir  - Output directory for markdown files
#
# Returns: 0 on success, 1 on error
_wdoc_convert_html_to_md() {
    local raw_dir="$1"
    local md_dir="$2"

    safe_path "$md_dir" "md_dir" || return 1

    # Clean previous conversion
    if [[ -d "$md_dir" ]]; then
        rm -rf "$md_dir"
    fi

    mkdir -p "$md_dir"

    # Use the Python converter — it extracts the main content area and
    # strips nav/sidebar/footer chrome before converting to markdown.
    log_debug "Converting HTML to markdown using html2md.py"
    local exit_code=0
    python3 "$WIGGUM_HOME/lib/wdoc/html2md.py" "$raw_dir" "$md_dir" 2>&1 || exit_code=$?

    if [[ "$exit_code" -ne 0 ]]; then
        log_error "html2md.py conversion failed (exit: $exit_code)"
        return 1
    fi

    return 0
}

# Clone source repository
#
# Args:
#   name    - Package name
#   src_url - Git repository URL
#   docs_dir - Base docs directory for this package
#
# Returns: 0 on success, 1 on error
_wdoc_clone_source() {
    local name="$1"
    local src_url="$2"
    local docs_dir="$3"

    local git_dir="$docs_dir/git"
    safe_path "$git_dir" "git_dir" || return 1

    # Clean previous clone
    if [[ -d "$git_dir" ]]; then
        rm -rf "$git_dir"
    fi

    log_info "Cloning source from $src_url"

    local exit_code=0
    git clone --depth=1 --single-branch "$src_url" "$git_dir" 2>&1 || exit_code=$?

    if [[ "$exit_code" -ne 0 ]]; then
        log_error "git clone failed for $src_url (exit: $exit_code)"
        return 1
    fi

    return 0
}
