#!/usr/bin/env python3
"""Fail when the rendered blueprint loses article cards, publishes dead links, or shows a math delimiter that
did not pair."""

from __future__ import annotations

import json
import re
import sys
from functools import lru_cache
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit


# Text in these elements is shown as written, so a `$` in it is meant.
VERBATIM = frozenset({"code", "pre", "script", "style", "textarea"})
# A `$` shaped like a math delimiter: doubled, or attached to a word with TeX syntax in it (`$2^{n}`, `x_i$`). A
# currency amount (`$5`) or an escaped `\$` is not.
DELIMITER = re.compile(r"\$\$|\$[^\s$]*[\\^_{}]|[\\^_{}][^\s$]*\$")
VOID = frozenset({"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"})


class PageParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.hrefs: list[str] = []
        self.ids: set[str] = set()
        self.cards: list[str] = []
        # The page's text outside verbatim elements, with None where a math element sits.
        self.flow: list[str | None] = []
        # The open elements, each with whether its text is exempt (verbatim or math, or inside such an element).
        self._open: list[tuple[str, bool]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        classes = (values.get("class") or "").split()
        if tag not in VOID:
            inside = bool(self._open and self._open[-1][1])
            if "arithmatex" in classes and not inside:
                self.flow.append(None)
            self._open.append((tag, inside or tag in VERBATIM or "arithmatex" in classes))
        if values.get("id"):
            self.ids.add(values["id"] or "")
        if values.get("href") is not None:
            self.hrefs.append(values["href"] or "")
        if "bp-thmwrapper" in classes and values.get("data-autoform-node-id"):
            self.cards.append(values["data-autoform-node-id"] or "")

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self.handle_starttag(tag, attrs)
        self.handle_endtag(tag)

    def handle_endtag(self, tag: str) -> None:
        # An element left open inside this one (HTML lets `<p>` and `<li>` close implicitly) closes with it.
        for depth in range(len(self._open) - 1, -1, -1):
            if self._open[depth][0] == tag:
                del self._open[depth:]
                return

    def handle_data(self, data: str) -> None:
        if not (self._open and self._open[-1][1]):
            self.flow.append(data)

    def unpaired_delimiters(self) -> list[str]:
        """Text around a math delimiter that did not pair. Arithmatex leaves the `$` in the text: a `$$` display
        that touches its paragraph renders as `$`, inline math, `$`, and an unclosed span keeps its `$`."""
        found = []
        for at, text in enumerate(self.flow):
            if text is None or "$" not in text:
                continue
            before_math = at + 1 < len(self.flow) and self.flow[at + 1] is None and text.endswith("$")
            after_math = at > 0 and self.flow[at - 1] is None and text.startswith("$")
            if before_math or after_math or DELIMITER.search(text):
                found.append(" ".join(text.split())[:120])
        return found


def parse(path: Path) -> PageParser:
    parser = PageParser()
    parser.feed(path.read_text(encoding="utf-8", errors="replace"))
    parser.close()
    return parser


def published_path(source: Path, docs: Path, site: Path) -> Path:
    relative = source.relative_to(docs)
    if relative.name.casefold() == "readme.md":
        return site / relative.parent / "index.html"
    return (site / relative).with_suffix(".html")


def resolve_link(page: Path, href: str, site: Path) -> tuple[Path, str, bool] | None:
    split = urlsplit(href)
    if split.scheme or split.netloc or href.startswith(("mailto:", "tel:", "javascript:", "data:")):
        return None
    raw = unquote(split.path)
    if not raw:
        target = page
    elif raw.startswith("/"):
        target = site / raw.lstrip("/")
    else:
        target = page.parent / raw
    target = target.resolve()
    try:
        target.relative_to(site)
    except ValueError:
        return target, unquote(split.fragment), False
    if raw.endswith("/") or target.is_dir():
        target /= "index.html"
    elif not target.suffix:
        html = target.with_suffix(".html")
        if html.is_file():
            target = html
    return target, unquote(split.fragment), True


def json_urls(value: object):
    """Yield URL fields from one generated dependency payload."""

    if isinstance(value, dict):
        for key, item in value.items():
            if key in {"url", "data_url", "article_url", "book"} and isinstance(item, str):
                yield item
            else:
                yield from json_urls(item)
    elif isinstance(value, list):
        for item in value:
            yield from json_urls(item)


def main() -> int:
    docs = Path(sys.argv[1] if len(sys.argv) > 1 else "site-src").resolve()
    site = Path(sys.argv[2] if len(sys.argv) > 2 else "site").resolve()
    issues: list[str] = []
    cards = 0

    for source in sorted((docs / "roadmap").rglob("*.md")):
        expected = parse(source).cards
        if not expected:
            continue
        output = published_path(source, docs, site)
        if not output.is_file():
            issues.append(f"{source.relative_to(docs)}: published page is missing: {output.relative_to(site)}")
            continue
        actual = parse(output).cards
        cards += len(expected)
        if actual != expected:
            missing = [node_id for node_id in expected if node_id not in actual]
            extra = [node_id for node_id in actual if node_id not in expected]
            issues.append(
                f"{output.relative_to(site)}: article-card mismatch "
                f"({len(expected)} generated, {len(actual)} published; "
                f"missing {missing[:5]}, extra {extra[:5]})"
            )

    @lru_cache(maxsize=1024)
    def ids(path: Path) -> frozenset[str]:
        return frozenset(parse(path).ids)

    pages = sorted(site.rglob("*.html"))
    # A missing or empty tree passes every check here, so a broken build would look clean.
    if not pages or not cards:
        issues.append(f"{len(pages)} HTML pages under {site} and {cards} article cards from {docs}; a built site has both")
    links = 0
    for page in pages:
        parsed = parse(page)
        unpaired = parsed.unpaired_delimiters()
        if unpaired:
            issues.append(f"{page.relative_to(site)}: a math delimiter did not pair, leaving `$` in the text: {unpaired[0]!r}")
        for href in parsed.hrefs:
            resolved = resolve_link(page, href, site)
            if resolved is None:
                continue
            links += 1
            target, fragment, within_site = resolved
            try:
                shown = target.relative_to(site).as_posix()
            except ValueError:
                shown = str(target)
            if not within_site:
                issues.append(f"{page.relative_to(site)}: {href!r} escapes the published site to {shown}")
            elif not target.is_file():
                issues.append(f"{page.relative_to(site)}: {href!r} targets missing {shown}")
            # The explorer reads its state from the fragment, as in node=... or
            # view=list&status=..., so only a fragment without "=" names an element.
            elif (
                fragment
                and "=" not in fragment
                and target.suffix.casefold() == ".html"
                and fragment not in ids(target)
            ):
                issues.append(f"{page.relative_to(site)}: {href!r} targets missing fragment in {shown}")

    payloads = sorted((site / "dependencies").rglob("*.json"))
    if (docs / "dependencies.json").is_file():
        payloads.insert(0, site / "dependencies.json")
    for payload in payloads:
        try:
            value = json.loads(payload.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            issues.append(f"{payload.relative_to(site)}: invalid dependency payload: {error}")
            continue
        for href in json_urls(value):
            resolved = resolve_link(payload, href, site)
            if resolved is None:
                continue
            links += 1
            target, fragment, within_site = resolved
            shown = target.relative_to(site).as_posix() if within_site else str(target)
            if not within_site:
                issues.append(f"{payload.relative_to(site)}: {href!r} escapes the published site to {shown}")
            elif not target.is_file():
                issues.append(f"{payload.relative_to(site)}: {href!r} targets missing {shown}")
            elif (
                fragment
                and "=" not in fragment
                and target.suffix.casefold() == ".html"
                and fragment not in ids(target)
            ):
                issues.append(f"{payload.relative_to(site)}: {href!r} targets missing fragment in {shown}")

    if issues:
        for issue in issues[:100]:
            print(f"error: {issue}", file=sys.stderr)
        if len(issues) > 100:
            print(f"error: {len(issues) - 100} more site-integrity failures", file=sys.stderr)
        return 1
    print(f"OK: {len(pages)} HTML pages, {links} internal links, {cards} article cards")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
