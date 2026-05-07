#!/usr/bin/env python3
"""html2md.py - Convert HTML files to Markdown using only stdlib.

Batch mode: python3 html2md.py <input_dir> <output_dir>
Single file: python3 html2md.py <input.html> <output.md>

Handles: h1-h6, p, a, code, pre, ul/ol/li, strong/em, blockquote, table.
Strips: nav, footer, header, sidebar, script, style, svg elements.
Extracts main content area when possible (id=content-area, main, article).
"""

import os
import re
import sys
from html.parser import HTMLParser
from pathlib import Path

# Tags whose content is discarded entirely
SKIP_TAGS = {"nav", "footer", "aside", "script", "style", "svg", "noscript"}

# IDs/roles that indicate the main content area
CONTENT_IDS = {"content-area", "content", "main-content", "article-content"}
CONTENT_TAGS = {"article", "main"}

# Classes/roles that indicate sidebar/chrome to skip
SKIP_CLASSES = {"sidebar", "side-bar", "toc", "navigation", "nav-", "navbar",
                "breadcrumb", "pagination", "footer", "header-nav"}


def extract_content_area(html):
    """Extract the main content area from HTML, stripping chrome.

    Looks for common content container IDs (content-area, content, main-content)
    and content tags (article, main). Falls back to full body if none found.
    """
    # Try known content IDs
    for cid in CONTENT_IDS:
        pattern = rf'id="{cid}"[^>]*>'
        match = re.search(pattern, html)
        if match:
            start = match.end()
            # Find the matching closing tag by counting depth
            extracted = _extract_from_position(html, match.start(), start)
            if extracted and len(extracted) > 200:
                return extracted

    # Try content tags (article, main)
    for tag in CONTENT_TAGS:
        pattern = rf'<{tag}[^>]*>'
        match = re.search(pattern, html)
        if match:
            start = match.end()
            extracted = _extract_from_position(html, match.start(), start)
            if extracted and len(extracted) > 200:
                return extracted

    # Try body
    body_match = re.search(r'<body[^>]*>', html)
    if body_match:
        end_match = re.search(r'</body>', html)
        if end_match:
            return html[body_match.end():end_match.start()]

    return html


def _extract_from_position(html, tag_start, content_start):
    """Extract content from a position, finding the matching close tag."""
    # Determine the tag name from the opening
    tag_match = re.match(r'<(\w+)', html[tag_start:])
    if not tag_match:
        return None
    tag_name = tag_match.group(1)

    depth = 1
    pos = content_start
    open_pattern = re.compile(rf'<{tag_name}[\s>]')
    close_pattern = re.compile(rf'</{tag_name}>')

    while depth > 0 and pos < len(html):
        next_open = open_pattern.search(html, pos)
        next_close = close_pattern.search(html, pos)

        if next_close is None:
            break

        if next_open and next_open.start() < next_close.start():
            depth += 1
            pos = next_open.end()
        else:
            depth -= 1
            if depth == 0:
                return html[content_start:next_close.start()]
            pos = next_close.end()

    # Fallback: take a generous chunk
    return html[content_start:content_start + 500000]


class HTML2Markdown(HTMLParser):
    def __init__(self):
        super().__init__()
        self._result = []
        self._skip_depth = 0
        self._pre_depth = 0
        self._list_stack = []  # stack of ("ul"|"ol", counter)
        self._in_table = False
        self._table_rows = []
        self._current_row = []
        self._current_cell = []
        self._last_href = None

    def _push(self, text):
        if self._skip_depth == 0:
            self._result.append(text)

    def handle_starttag(self, tag, attrs):
        tag = tag.lower()
        attrs_dict = dict(attrs)

        # Capture href for links before any skip logic
        if tag == "a":
            self._last_href = attrs_dict.get("href")

        # Skip blocks
        if tag in SKIP_TAGS:
            self._skip_depth += 1
            return
        if tag in ("div", "section", "span"):
            cls = (attrs_dict.get("class", "") + " " + attrs_dict.get("role", "")).lower()
            if any(k in cls for k in SKIP_CLASSES):
                self._skip_depth += 1
                return
            # Skip sr-only (screen reader only) elements
            if "sr-only" in cls:
                self._skip_depth += 1
                return
        # Skip elements with hidden attribute
        if "hidden" in attrs_dict:
            self._skip_depth += 1
            return

        if self._skip_depth > 0:
            return

        # Headings
        if tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            level = int(tag[1])
            self._push("\n\n" + "#" * level + " ")
        elif tag == "p":
            self._push("\n\n")
        elif tag == "br":
            self._push("\n")
        elif tag == "hr":
            self._push("\n\n---\n\n")
        elif tag == "blockquote":
            self._push("\n\n> ")
        elif tag in ("strong", "b"):
            self._push("**")
        elif tag in ("em", "i"):
            self._push("*")
        elif tag == "code" and self._pre_depth == 0:
            self._push("`")
        elif tag == "a":
            self._push("[")
        elif tag == "pre":
            self._pre_depth += 1
            self._push("\n\n```\n")
        elif tag == "ul":
            self._list_stack.append(("ul", 0))
            self._push("\n")
        elif tag == "ol":
            self._list_stack.append(("ol", 0))
            self._push("\n")
        elif tag == "li":
            indent = "  " * max(0, len(self._list_stack) - 1)
            if self._list_stack:
                kind, count = self._list_stack[-1]
                if kind == "ol":
                    count += 1
                    self._list_stack[-1] = (kind, count)
                    self._push(f"{indent}{count}. ")
                else:
                    self._push(f"{indent}- ")
            else:
                self._push("- ")
        elif tag == "table":
            self._in_table = True
            self._table_rows = []
        elif tag == "tr":
            self._current_row = []
        elif tag in ("td", "th"):
            self._current_cell = []
        # Skip img tags with data: URIs (base64 inline images)
        elif tag == "img":
            src = attrs_dict.get("src", "")
            alt = attrs_dict.get("alt", "")
            if alt and not src.startswith("data:"):
                self._push(f"![{alt}]")

    def handle_endtag(self, tag):
        tag = tag.lower()

        # Skip blocks - handle all tags that could have incremented skip_depth
        if tag in SKIP_TAGS:
            self._skip_depth = max(0, self._skip_depth - 1)
            return
        if tag in ("div", "section", "span") and self._skip_depth > 0:
            self._skip_depth = max(0, self._skip_depth - 1)
            return

        if self._skip_depth > 0:
            return

        if tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            self._push("\n\n")
        elif tag == "p":
            self._push("\n\n")
        elif tag == "blockquote":
            self._push("\n\n")
        elif tag in ("strong", "b"):
            self._push("**")
        elif tag in ("em", "i"):
            self._push("*")
        elif tag == "code" and self._pre_depth == 0:
            self._push("`")
        elif tag == "a":
            if self._last_href and not self._last_href.startswith(("#", "javascript:")):
                href = self._last_href
                # Rewrite .html/.htm cross-links to .md
                if not href.startswith(("http://", "https://", "mailto:")):
                    href = re.sub(r'\.html?(?=#|$)', '.md', href)
                self._push(f"]({href})")
            else:
                self._push("]")
            self._last_href = None
        elif tag == "pre":
            self._pre_depth = max(0, self._pre_depth - 1)
            self._push("\n```\n\n")
        elif tag in ("ul", "ol"):
            if self._list_stack:
                self._list_stack.pop()
            self._push("\n")
        elif tag == "li":
            self._push("\n")
        elif tag in ("td", "th"):
            cell_text = "".join(self._current_cell).strip().replace("|", "\\|")
            self._current_row.append(cell_text)
            self._current_cell = []
        elif tag == "tr":
            self._table_rows.append(self._current_row)
            self._current_row = []
        elif tag == "table":
            self._flush_table()
            self._in_table = False

    def handle_data(self, data):
        if self._skip_depth > 0:
            return

        if self._in_table and self._current_cell is not None:
            self._current_cell.append(data)
            return

        if self._pre_depth > 0:
            self._push(data)
        else:
            self._push(data.replace("\n", " "))

    def handle_entityref(self, name):
        entities = {"amp": "&", "lt": "<", "gt": ">", "quot": '"', "nbsp": " "}
        self.handle_data(entities.get(name, f"&{name};"))

    def handle_charref(self, name):
        try:
            if name.startswith("x"):
                char = chr(int(name[1:], 16))
            else:
                char = chr(int(name))
            self.handle_data(char)
        except (ValueError, OverflowError):
            self.handle_data(f"&#{name};")

    def _flush_table(self):
        if not self._table_rows:
            return
        self._push("\n\n")
        for i, row in enumerate(self._table_rows):
            self._push("| " + " | ".join(row) + " |\n")
            if i == 0:
                self._push("| " + " | ".join("---" for _ in row) + " |\n")
        self._push("\n")
        self._table_rows = []

    def get_markdown(self):
        text = "".join(self._result)
        # Clean up excessive blank lines
        while "\n\n\n" in text:
            text = text.replace("\n\n\n", "\n\n")
        # Remove lines that are only whitespace
        lines = text.split("\n")
        lines = [line.rstrip() for line in lines]
        text = "\n".join(lines)
        # Collapse runs of empty lines
        text = re.sub(r'\n{3,}', '\n\n', text)
        return text.strip() + "\n"


def convert_file(input_path, output_path):
    """Convert a single HTML file to markdown."""
    try:
        with open(input_path, "r", encoding="utf-8", errors="replace") as f:
            html = f.read()
    except (OSError, IOError) as e:
        print(f"Warning: cannot read {input_path}: {e}", file=sys.stderr)
        return False

    # Extract main content area to avoid nav/sidebar noise
    content = extract_content_area(html)

    parser = HTML2Markdown()
    parser.feed(content)
    md = parser.get_markdown()

    if not md.strip():
        return False

    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(md)
    return True


def convert_directory(input_dir, output_dir):
    """Convert all HTML files in input_dir to markdown in output_dir."""
    input_path = Path(input_dir)
    output_path = Path(output_dir)
    converted = 0
    skipped = 0

    for html_file in input_path.rglob("*.htm*"):
        rel = html_file.relative_to(input_path)
        md_file = output_path / rel.with_suffix(".md")

        if convert_file(str(html_file), str(md_file)):
            converted += 1
        else:
            skipped += 1

    print(f"Converted {converted} files, skipped {skipped}", file=sys.stderr)
    return converted


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <input_dir|input.html> <output_dir|output.md>", file=sys.stderr)
        sys.exit(1)

    src, dst = sys.argv[1], sys.argv[2]

    if os.path.isdir(src):
        count = convert_directory(src, dst)
        if count == 0:
            print("Warning: no HTML files found to convert", file=sys.stderr)
    elif os.path.isfile(src):
        if not convert_file(src, dst):
            print(f"Failed to convert {src}", file=sys.stderr)
            sys.exit(1)
    else:
        print(f"Error: {src} does not exist", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
