"""Trim the theme's share of every built page.

Readers with JavaScript browse with the explorer, which hides the theme's
header, navigation and footer, so the theme's markup serves readers without
JavaScript and the explorer's fallback. Two changes keep it small:

- A page that only says where an old explorer URL moved (a heading and the
  renderer's `bp-moved` block: a link, a redirect that keeps the URL's
  fragment, and a meta refresh) is published as that content in a bare
  document. In the theme, each of these thousands of pages weighed about 18 KB
  for less than 1 KB of content.
- Every page loses the indentation the theme writes, about a sixth of the
  site. In text, a run of whitespace that holds a line break displays exactly
  as one line break, so each such run becomes one. Tags, comments and the
  elements that show their text as written keep every character: pre, code,
  kbd, raw text such as script, style and textarea, TeX, Mermaid diagrams, and
  the renderer's pre-wrap blocks.
"""

from __future__ import annotations

import html
import re
import string
from collections.abc import Iterator

from mkdocs.plugins import event_priority

# Elements whose text is shown or run as written (the theme displays code, kbd and pre as pre-wrap).
VERBATIM_TAGS = frozenset({"pre", "code", "kbd", "listing"})
# Raw text: everything up to the element's closing tag is its text, never markup.
RAW_TEXT_TAGS = frozenset({"script", "style", "textarea", "title", "xmp", "iframe", "noembed", "noframes", "noscript"})
# TeX, Mermaid diagram source (a mindmap is nested by its indentation) and the renderer's pre-wrap blocks.
VERBATIM_CLASSES = frozenset({"arithmatex", "mermaid", "bp-readback-body", "bp-as-typed"})
VOID_TAGS = frozenset({
    "area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr",
})

# HTML's whitespace characters, not Python's: a no-break space is text, and it does not end a tag name.
_SPACE = "\t\n\f\r "
# An attribute as HTML reads it: a name, then optionally `=` and a value. A quote opens a value only where
# a value starts. The atomic groups keep every match linear.
_NAME = rf"(?>[^{_SPACE}/>][^{_SPACE}/>=]*)"
_VALUE = rf"\"[^\"]*\"|'[^']*'|(?>[^{_SPACE}>\"'][^{_SPACE}>]*)"
_ATTRIBUTES = re.compile(rf"({_NAME})(?:[{_SPACE}]*=[{_SPACE}]*({_VALUE}))?")
_MARKUP = re.compile(
    r"<!--(?:>|->|.*?(?:--!?>|\Z))"  # a comment; an unterminated one runs to the end
    r"|<![^>]*>|<\?[^>]*>|</(?![A-Za-z])[^>]*>"  # a doctype or declaration, and the bogus comments
    rf"|<(/?)([A-Za-z][^{_SPACE}/>]*)((?:[{_SPACE}/]+|{_NAME}(?:[{_SPACE}]*=[{_SPACE}]*(?:{_VALUE}))?)*)>",
    re.DOTALL,
)
# HTML matches tag names ignoring the case of ASCII letters only: `</scr\u0131pt>` does not close a script.
_SCRIPT_MARK = re.compile(rf"<!--|-->|<(/?)script(?=[{_SPACE}/>])", re.IGNORECASE | re.ASCII)
_ASCII_LOWER = str.maketrans(string.ascii_uppercase, string.ascii_lowercase)
_BREAK_RUN = re.compile(r"[ \t\f\r]*\n[ \t\n\f\r]*")


def _classes(attributes: str) -> set[str]:
    """The element's classes: its first `class` attribute, character references decoded."""

    for attribute in _ATTRIBUTES.finditer(attributes):
        if attribute.group(1).translate(_ASCII_LOWER) == "class":
            value = attribute.group(2) or ""
            if value[:1] in {'"', "'"}:
                value = value[1:-1]
            return set(re.split(f"[{_SPACE}]+", html.unescape(value))) - {""}
    return set()


def _raw_text_end(page: str, tag: str, start: int) -> int:
    """Return where the closing tag of the raw-text element whose text starts at `start` begins."""

    if tag != "script":
        closing = re.compile(rf"</{tag}(?=[{_SPACE}/>])", re.IGNORECASE | re.ASCII).search(page, start)
        return closing.start() if closing else len(page)
    # Script text has HTML's escaped and double-escaped states: inside `<!--`, a `<script` makes the
    # next `</script` part of the text.
    state = "data"
    for mark in _SCRIPT_MARK.finditer(page, start):
        token = mark.group()
        if token == "<!--":
            state = "escaped" if state == "data" else state
        elif token == "-->":
            # From the escaped and the double-escaped states alike, `-->` returns to plain script text.
            state = "data"
        elif mark.group(1):
            if state != "double":
                return mark.start()
            state = "escaped"
        elif state == "escaped":
            state = "double"
    return len(page)


def scan(page: str) -> Iterator[tuple[str, int, int, str, str]]:
    """Yield the page's markup as (kind, start, end, tag, attributes); the text between is text.

    Kinds are `start` and `end` tags, `raw` text (kept whole), and `other` (comments, declarations).
    """

    at = 0
    while (markup := _MARKUP.search(page, at)) is not None:
        at = markup.end()
        if markup.group(2) is None:
            yield "other", markup.start(), at, "", ""
            continue
        tag = markup.group(2).translate(_ASCII_LOWER)
        closing = bool(markup.group(1))
        yield ("end" if closing else "start"), markup.start(), at, tag, markup.group(3)
        if not closing and tag in RAW_TEXT_TAGS:
            stop = _raw_text_end(page, tag, at)
            yield "raw", at, stop, tag, ""
            at = stop


def compact(page: str) -> str:
    """Collapse each whitespace run that holds a line break in text outside verbatim elements."""

    parts: list[str] = []
    at = 0
    open_elements: list[tuple[str, bool]] = []
    verbatim = 0
    for kind, start, end, tag, attributes in scan(page):
        text = page[at:start]
        parts.append(text if verbatim else _BREAK_RUN.sub("\n", text))
        parts.append(page[start:end])
        at = end
        if kind == "start" and tag not in VOID_TAGS:
            keeps = tag in VERBATIM_TAGS or tag in RAW_TEXT_TAGS or bool(_classes(attributes) & VERBATIM_CLASSES)
            open_elements.append((tag, keeps))
            verbatim += keeps
        elif kind == "end":
            # As browsers do, a closing tag also closes the elements still open inside its element.
            for depth in range(len(open_elements) - 1, -1, -1):
                if open_elements[depth][0] == tag:
                    verbatim -= sum(keeps for _, keeps in open_elements[depth:])
                    del open_elements[depth:]
                    break
    text = page[at:]
    parts.append(text if verbatim else _BREAK_RUN.sub("\n", text))
    return "".join(parts)


def is_notice(content: str) -> bool:
    """Whether a page's content is a heading and the renderer's `bp-moved` block, and nothing else."""

    tokens = scan(content)
    heading = next(tokens, None)
    if heading is None or heading[:1] + heading[3:4] != ("start", "h1") or content[: heading[1]].strip():
        return False
    heading_end = next(tokens, None)
    if heading_end is None or heading_end[:1] + heading_end[3:4] != ("end", "h1"):
        return False
    block = next(tokens, None)
    if (
        block is None
        or block[:1] + block[3:4] != ("start", "div")
        or _classes(block[4]) != {"bp-moved"}
        or content[heading_end[2] : block[1]].strip()
    ):
        return False
    depth = 1
    for kind, _, end, tag, _ in tokens:
        if tag == "div" and kind in {"start", "end"}:
            depth += 1 if kind == "start" else -1
            if depth == 0:
                return not content[end:].strip()
    return False


def bare_document(content: str, title: str, language: str) -> str:
    return (
        f'<!doctype html>\n<html lang="{html.escape(language)}">\n<head>\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width,initial-scale=1">\n'
        f"<title>{html.escape(title, quote=False)}</title>\n</head>\n<body>\n{content.strip()}\n</body>\n</html>\n"
    )


@event_priority(-100)
def on_post_page(output: str, *, page, config) -> str:
    content = page.content or ""
    if is_notice(content):
        title = f"{page.title} - {config.site_name}" if page.title else config.site_name
        output = bare_document(content, title, config.theme.get("language") or "en")
    return compact(output)
