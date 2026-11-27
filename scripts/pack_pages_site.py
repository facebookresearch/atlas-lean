#!/usr/bin/env python3
"""The GitHub Pages copy of the site, with its pages stored gzipped.

    python scripts/pack_pages_site.py pack SITE OUT
    python scripts/pack_pages_site.py check SITE OUT

GitHub Pages publishes sites of up to 1 GB. It compresses the files it sends but counts the files it stores, and
it serves a stored `.gz` file as `application/gzip`, without `Content-Encoding`, so a browser does not inflate it
by itself. `pack` copies a built site, the wiki job's or the full site of scripts/build_mathlib_pages.py, to OUT and
stores each page under `mathlib/` and `roadmap/` as `PAGE.gz`, next to a small page at its address. The small page loads
scripts/pages_packing.js, which OUT serves as `javascripts/pages-packing.js`: the script fetches the stored page,
inflates it with `DecompressionStream` and opens it in place of the small page. The explorer and the project map
fetch the pages they show; the script answers their fetch of a stored page with the inflated page, so the other
pages that run either load it too, at the start of their head. Every other file is copied unchanged.

`check` verifies OUT against SITE: every file of SITE comes back from OUT byte for byte, as its copy, by inflating
its stored page or by removing the script tag `pack` added, each small page is the one `pack` writes, and OUT has no
other file. docs/BLUEPRINT.md describes the GitHub Pages copy. Nothing this script writes is committed.
"""

from __future__ import annotations

import argparse
import gzip
import html
import os
import posixpath
import re
import shutil
import sys
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parent.parent
LOADER = ROOT / "scripts" / "pages_packing.js"
LOADER_PATH = "javascripts/pages-packing.js"
# The pages stored gzipped; scripts/pages_packing.js applies the same rule to the explorer's fetches.
PACKED = ("mathlib/", "roadmap/")
HEAD = b"<head>"
# The scripts of the explorer and of the project map, which fetch the pages they show.
EXPLORER = re.compile(rb'<script\b[^>]*\ssrc="[^"]*\bjavascripts/(?:blueprint-dag|project-map)\.js"')
TITLE = re.compile(rb"<title>(.*?)</title>", re.S)


def is_packed(path: str) -> bool:
    return path.startswith(PACKED) and path.endswith(".html")


def to_root(path: str) -> str:
    """The relative address of the site's root from the file at `path`."""
    return "../" * path.count("/")


def deflate(data: bytes) -> bytes:
    # No name and no time stamp in the header: the same page always gives the same bytes.
    return gzip.compress(data, compresslevel=9, mtime=0)


def stub(path: str, page: bytes) -> bytes:
    """The small page that `pack` writes at the address of a page it stores gzipped.

    Its note shows only if the page has not opened after two seconds, or at once without JavaScript; the loader
    replaces it with what went wrong if opening fails. The loader comes after the note, so that a slow download of
    the loader cannot hold back the note.
    """
    found = TITLE.search(page)
    title = found.group(1).decode("utf-8").strip() if found else ""
    stored = html.escape(quote(posixpath.basename(path) + ".gz"))
    return (
        "<!doctype html>\n"
        '<html lang="en">\n'
        "<head>\n"
        '<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width,initial-scale=1">\n'
        '<meta name="color-scheme" content="light dark">\n'
        f"<title>{title}</title>\n"
        "<style>p{visibility:hidden;animation:shown 0s 2s forwards}@keyframes shown{to{visibility:visible}}</style>\n"
        "<noscript><style>p{animation:none;visibility:visible}</style></noscript>\n"
        "</head>\n"
        "<body>\n"
        "<p>This page is stored compressed, to keep the site within GitHub Pages' size limit. It opens with "
        "JavaScript, in a browser that has DecompressionStream.</p>\n"
        f'<script src="{to_root(path)}{LOADER_PATH}" data-packed-page="{stored}"></script>\n'
        "</body>\n"
        "</html>\n"
    ).encode()


def loader_tag(path: str) -> bytes:
    return f'<script src="{to_root(path)}{LOADER_PATH}"></script>'.encode()


def with_loader(path: str, page: bytes) -> bytes:
    """A page that runs the explorer or the map, with the loader's tag at the start of its head, before every other
    script."""
    if page.count(HEAD) != 1:
        raise ValueError(f"{path}: runs the explorer or the map but has {page.count(HEAD)} <head> tags, not one")
    if LOADER_PATH.encode() in page:
        raise ValueError(f"{path}: already names {LOADER_PATH}")
    return page.replace(HEAD, HEAD + loader_tag(path), 1)


def runs_explorer(path: str, page: bytes) -> bool:
    return path.endswith(".html") and not is_packed(path) and EXPLORER.search(page) is not None


def site_files(site: Path) -> list[str]:
    """The files of a site directory, as sorted relative paths. A symbolic link is refused, and so is a directory
    that cannot be read."""
    if site.is_symlink() or not site.is_dir():
        raise ValueError(f"{site}: not a directory")

    def unreadable(error: OSError):
        raise ValueError(f"{error.filename}: {error.strerror}")

    paths = []
    for directory, subdirectories, files in os.walk(site, onerror=unreadable):
        for name in subdirectories + files:
            if (Path(directory) / name).is_symlink():
                raise ValueError(f"{(Path(directory) / name).relative_to(site).as_posix()}: a symbolic link")
        paths += [(Path(directory) / name).relative_to(site).as_posix() for name in files]
    return sorted(paths)


def pack(site: Path, out: Path) -> list[str]:
    files = site_files(site)
    present = set(files)
    for path in files:
        if is_packed(path) and path + ".gz" in present:
            raise ValueError(f"{path}: the site already has {path}.gz")
    if LOADER_PATH in present:
        raise ValueError(f"the site already has {LOADER_PATH}")
    if out.exists() or out.is_symlink():
        raise ValueError(f"{out} already exists")
    packed = [0, 0, 0]
    explorer = [0, 0, 0]
    for path in files:
        source, target = site / path, out / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if is_packed(path):
            page = source.read_bytes()
            small, stored = stub(path, page), deflate(page)
            target.write_bytes(small)
            target.with_name(target.name + ".gz").write_bytes(stored)
            packed = [packed[0] + 1, packed[1] + len(page), packed[2] + len(small) + len(stored)]
        elif path.endswith(".html") and runs_explorer(path, page := source.read_bytes()):
            loaded = with_loader(path, page)
            target.write_bytes(loaded)
            explorer = [explorer[0] + 1, explorer[1] + len(page), explorer[2] + len(loaded)]
        else:
            shutil.copyfile(source, target)
    loader = out / LOADER_PATH
    loader.parent.mkdir(parents=True, exist_ok=True)
    loader.write_bytes(LOADER.read_bytes())
    total_in = sum((site / path).stat().st_size for path in files)
    total_out = sum((out / path).stat().st_size for path in site_files(out))
    return [
        f"pages under {' and '.join(PACKED)}: {packed[0]:,} pages, {packed[1]:,} bytes, stored with their small "
        f"pages in {packed[2]:,} bytes",
        f"other pages that run the explorer or the map, loading {LOADER_PATH} first: {explorer[0]:,} pages, "
        f"{explorer[1]:,} -> {explorer[2]:,} bytes",
        f"other files, copied unchanged: {len(files) - packed[0] - explorer[0]:,} files, "
        f"{total_in - packed[1] - explorer[1]:,} bytes",
        f"site: {len(files):,} files, {total_in:,} bytes -> {len(files) + packed[0] + 1:,} files, {total_out:,} bytes, "
        f"with {LOADER_PATH}",
    ]


def check(site: Path, out: Path) -> list[str]:
    errors = []
    try:
        files = site_files(site)
    except ValueError as error:
        return [str(error)]
    expected = {LOADER_PATH}
    for path in files:
        source, target = site / path, out / path
        content = source.read_bytes()
        expected.add(path)
        if is_packed(path):
            stored = target.with_name(target.name + ".gz")
            expected.add(path + ".gz")
            if not stored.is_file():
                errors.append(f"{path}.gz: missing")
            else:
                try:
                    if gzip.decompress(stored.read_bytes()) != content:
                        errors.append(f"{path}.gz: does not inflate to {path}")
                except (OSError, EOFError) as error:
                    errors.append(f"{path}.gz: not gzip: {error}")
            if not target.is_file() or target.read_bytes() != stub(path, content):
                errors.append(f"{path}: not the small page that opens {path}.gz")
        elif not target.is_file():
            errors.append(f"{path}: missing")
        elif runs_explorer(path, content):
            packed, tag = target.read_bytes(), loader_tag(path)
            at = content.find(HEAD) + len(HEAD)
            if packed[:at + len(tag)] != content[:at] + tag or packed[at + len(tag):] != content[at:]:
                errors.append(f"{path}: is not the site's page with {LOADER_PATH} loaded first in its head")
        elif target.read_bytes() != content:
            errors.append(f"{path}: differs from the site's file")
    loader = out / LOADER_PATH
    if not loader.is_file() or loader.read_bytes() != LOADER.read_bytes():
        errors.append(f"{LOADER_PATH}: not scripts/pages_packing.js")
    try:
        packed_files = site_files(out)
    except ValueError as error:
        return errors + [str(error)]
    errors += [f"{path}: not a file of the packed site" for path in sorted(set(packed_files) - expected)]
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("pack", "check"):
        command = commands.add_parser(name)
        command.add_argument("site", type=Path)
        command.add_argument("out", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "pack":
            report, errors = pack(args.site, args.out), []
        else:
            report, errors = [], check(args.site, args.out)
    except (ValueError, OSError) as error:
        report, errors = [], [str(error)]
    for error in errors[:100]:
        print(f"error: {error}", file=sys.stderr)
    if len(errors) > 100:
        print(f"error: and {len(errors) - 100} more", file=sys.stderr)
    if errors:
        return 1
    if args.command == "check":
        report = [f"{args.out}: every file of {args.site} comes back byte for byte"]
    print("\n".join(report))
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as stream:
            stream.write("".join(f"- {line}\n" for line in report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
