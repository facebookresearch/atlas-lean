#!/usr/bin/env python3
"""Tests for scripts/pack_pages_site.py and scripts/pages_packing.js on a small site."""

from __future__ import annotations

import gzip
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pack_pages_site as packing  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "pack_pages_site.py"


def page(title: str, body: str = "") -> str:
    return (f'<!doctype html>\n<html lang="en" class="no-js">\n<head>\n<meta charset="utf-8">\n<title>{title}</title>\n'
            f'<script>__md_scope=new URL("..",location)</script>\n</head>\n<body>\n{body}\n</body>\n</html>\n')


def explorer(title: str, to_root: str, body: str = "") -> str:
    return page(title, f'<div class="bp-dag-viewer" hidden></div>\n{body}\n'
                       f'<script defer="defer" src="{to_root}javascripts/blueprint-dag.js"></script>')


SITE = {
    "index.html": explorer("ATLAS", ""),
    "coverage/index.html": explorer("What the sources cover - ATLAS", "../"),
    "404.html": page("ATLAS", '<script src="/assets/javascripts/bundle.js"></script>'),
    "roadmap/index.html": explorer("ATLAS roadmap - ATLAS", "../"),
    # A page whose fallback link downloads the explorer's data: the data must stay where the link leads.
    "roadmap/Logic/first-order-syntax/index.html": explorer(
        "First-order syntax - ATLAS", "../../../",
        '<a href="../../../dependencies/index.json" download>Download the complete graph data</a>\n'
        '<a href="../../../mathlib/Topology.Basic.html#IsOpen.union">IsOpen.union</a>'),
    "dependencies/map/index.html": ('<!doctype html>\n<html lang="en">\n<head>\n<title>ATLAS roadmap · map</title>\n'
                                    '<script defer src="../../javascripts/project-map.js"></script>\n</head>\n'
                                    '<body class="pm-page"></body>\n</html>\n'),
    "dependencies/index.json": json.dumps({"nodes": [{"id": "roadmap", "title": "ATLAS roadmap"}] * 50}),
    "dependencies/map/data/parts/0f.json": json.dumps({"part": "0f", "nodes": list(range(500))}),
    "dependencies/scopes/Logic/first-order-syntax.html": page("This page moved - ATLAS"),
    "publication.json": json.dumps({"files": {"index.html": "0" * 64}}),
    "search/search_index.json": json.dumps({"docs": [{"location": "mathlib/Topology.Basic.html", "title": "T"}]}),
    "mathlib/index.html": page("Mathlib - ATLAS", '<a href="Topology.Basic.html#IsOpen.union">IsOpen.union</a>'),
    "mathlib/Topology.Basic.html": page("Mathlib.Topology.Basic - ATLAS",
                                        '<div class="ml-decl" id="IsOpen.union">' + "theorem IsOpen.union " * 200 + "</div>"),
    "mathlib/Topology/topological-spaces/index.html": page("Topological spaces &amp; maps - ATLAS"),
    "javascripts/blueprint-dag.js": "// the explorer\n",
    "javascripts/project-map.js": "// the map\n",
    "assets/stylesheets/main.css": "body { margin: 0 }\n",
    "stylesheets/mathlib.css": ".ml-decl { margin: 0 }\n",
}
PACKED = ["mathlib/Topology.Basic.html", "mathlib/Topology/topological-spaces/index.html", "mathlib/index.html",
          "roadmap/index.html", "roadmap/Logic/first-order-syntax/index.html"]
EXPLORER = ["index.html", "coverage/index.html", "dependencies/map/index.html"]


def write_site(root: Path, files: dict[str, str]) -> None:
    for path, content in files.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(content, encoding="utf-8")


def tree(root: Path) -> dict[str, bytes]:
    return {path.relative_to(root).as_posix(): path.read_bytes() for path in root.rglob("*") if path.is_file()}


class PackTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.site, self.out = self.root / "site", self.root / "out"
        write_site(self.site, SITE)
        self.report = packing.pack(self.site, self.out)

    def test_pages_under_mathlib_and_roadmap_become_small_pages_that_open_their_stored_copy(self):
        for path in PACKED:
            original = (self.site / path).read_bytes()
            self.assertEqual(gzip.decompress((self.out / f"{path}.gz").read_bytes()), original)
            small = (self.out / path).read_text(encoding="utf-8")
            title = re.search(r"<title>(.*)</title>", original.decode()).group(1)
            self.assertIn(f"<title>{title}</title>", small)
            src, stored = re.search(r'<script src="([^"]+)" data-packed-page="([^"]+)"></script>', small).groups()
            self.assertEqual(posixpath.normpath(posixpath.join(posixpath.dirname(path), src)), packing.LOADER_PATH)
            self.assertEqual(stored, posixpath.basename(path) + ".gz")
            self.assertEqual(small.count("<script"), 1)
            # A note that says why the page needs JavaScript: shown at once without it, after two seconds with it.
            self.assertIn("<p>This page is stored compressed", small)
            self.assertIn("animation:shown 0s 2s forwards", small)
            self.assertIn("<noscript><style>p{animation:none;visibility:visible}</style></noscript>", small)
            self.assertLess(small.index("<p>"), small.index("<script"))
            self.assertLess(len(small), 1000)
        self.assertIn('src="../../../javascripts/pages-packing.js" data-packed-page="index.html.gz"',
                      (self.out / "mathlib/Topology/topological-spaces/index.html").read_text())

    def test_other_pages_that_run_the_explorer_or_the_map_load_the_loader_before_any_other_script(self):
        for path in EXPLORER:
            original, packed = (self.site / path).read_bytes(), (self.out / path).read_bytes()
            src = re.match(rb'(?s).*?<head><script src="([^"]+)"></script>', packed).group(1).decode()
            self.assertEqual(posixpath.normpath(posixpath.join(posixpath.dirname(path), src)), packing.LOADER_PATH)
            self.assertEqual(packed.replace(f'<script src="{src}"></script>'.encode(), b"", 1), original)
            self.assertLess(packed.index(b"pages-packing.js"), packed.index(b"<script", packed.index(b"</script>")))

    def test_every_other_file_is_copied_unchanged_and_the_loader_is_added(self):
        packed = tree(self.out)
        for path, content in SITE.items():
            if path not in PACKED + EXPLORER:
                self.assertEqual(packed[path], content.encode(), path)
        self.assertEqual(packed[packing.LOADER_PATH], (ROOT / "scripts" / "pages_packing.js").read_bytes())
        self.assertEqual(set(packed), set(SITE) | {f"{p}.gz" for p in PACKED} | {packing.LOADER_PATH})
        # Every address a page links to still has its file: the data download and the Mathlib page's small page.
        for href in ("../../../dependencies/index.json", "../../../mathlib/Topology.Basic.html"):
            self.assertIn(posixpath.normpath(posixpath.join("roadmap/Logic/first-order-syntax", href)), packed)

    def test_check_passes_and_packing_is_deterministic(self):
        self.assertEqual(packing.check(self.site, self.out), [])
        again = self.root / "again"
        self.assertEqual(packing.pack(self.site, again), self.report)
        self.assertEqual(tree(again), tree(self.out))
        sizes = {path: len(content.encode()) for path, content in SITE.items()}
        stored = sum((self.out / p).stat().st_size + (self.out / f"{p}.gz").stat().st_size for p in PACKED)
        loaded = sum((self.out / p).stat().st_size for p in EXPLORER)
        pages, others = sum(sizes[p] for p in PACKED), sum(sizes[p] for p in EXPLORER)
        total = sum(len(content) for content in tree(self.out).values())
        self.assertEqual(self.report, [
            f"pages under mathlib/ and roadmap/: 5 pages, {pages:,} bytes, stored with their small pages in "
            f"{stored:,} bytes",
            f"other pages that run the explorer or the map, loading {packing.LOADER_PATH} first: 3 pages, "
            f"{others:,} -> {loaded:,} bytes",
            f"other files, copied unchanged: {len(SITE) - 8} files, {sum(sizes.values()) - pages - others:,} bytes",
            f"site: {len(SITE)} files, {sum(sizes.values()):,} bytes -> {len(SITE) + 6} files, {total:,} bytes, "
            f"with {packing.LOADER_PATH}",
        ])

    def test_check_reports_every_departure_from_the_site(self):
        mathlib_page, explorer_page = PACKED[0], EXPLORER[1]
        tag = packing.loader_tag(explorer_page)

        def bad_gzip(out):
            (out / f"{mathlib_page}.gz").write_bytes(b"not gzip")

        def other_content(out):
            (out / f"{mathlib_page}.gz").write_bytes(packing.deflate(b"<p>another page</p>"))

        def missing_stored(out):
            (out / f"{mathlib_page}.gz").unlink()

        def missing_file(out):
            (out / "dependencies/index.json").unlink()

        def other_title(out):
            path = out / mathlib_page
            path.write_bytes(path.read_bytes().replace(b"Mathlib.Topology.Basic", b"Elsewhere"))

        def plain_page(out):
            shutil.copyfile(self.site / mathlib_page, out / mathlib_page)

        def no_loader(out):
            shutil.copyfile(self.site / explorer_page, out / explorer_page)

        def loader_twice(out):
            path = out / explorer_page
            path.write_bytes(path.read_bytes().replace(b"</head>", tag + b"</head>"))

        def loader_late(out):
            path = out / explorer_page
            path.write_bytes(path.read_bytes().replace(tag, b"").replace(b"</head>", tag + b"</head>"))

        def changed_file(out):
            (out / "publication.json").write_text("{}")

        def changed_loader(out):
            (out / packing.LOADER_PATH).write_text("// another script\n")

        def extra(out):
            (out / "mathlib/extra.html").write_text("<p>extra</p>")

        def link(out):
            (out / "assets/link.css").symlink_to(out / "assets/stylesheets/main.css")

        loads = f"{explorer_page}: is not the site's page with {packing.LOADER_PATH} loaded first"
        cases = {
            bad_gzip: f"{mathlib_page}.gz: not gzip", other_content: f"{mathlib_page}.gz: does not inflate to",
            missing_stored: f"{mathlib_page}.gz: missing", missing_file: "dependencies/index.json: missing",
            other_title: f"{mathlib_page}: not the small page", plain_page: f"{mathlib_page}: not the small page",
            no_loader: loads, loader_twice: loads, loader_late: loads,
            changed_file: "publication.json: differs from the site's file",
            changed_loader: f"{packing.LOADER_PATH}: not scripts/pages_packing.js",
            extra: "mathlib/extra.html: not a file of the packed site", link: "assets/link.css: a symbolic link",
        }
        for spoil, expected in cases.items():
            with self.subTest(spoil.__name__):
                out = self.root / spoil.__name__
                shutil.copytree(self.out, out)
                spoil(out)
                errors = packing.check(self.site, out)
                self.assertTrue(any(expected in error for error in errors), errors)

    def test_pack_refuses_what_it_cannot_store_faithfully(self):
        cases = {
            "collision": {"roadmap/index.html.gz": "stored already"},
            "loader": {packing.LOADER_PATH: "// a script of the same name\n"},
            "heads": {"index.html": SITE["index.html"].replace("</body>", "<pre><head></pre></body>")},
            "named": {"index.html": SITE["index.html"].replace("</body>", f"<!-- {packing.LOADER_PATH} --></body>")},
        }
        for name, change in cases.items():
            with self.subTest(name):
                site = self.root / f"site-{name}"
                write_site(site, {**SITE, **change})
                with self.assertRaises(ValueError):
                    packing.pack(site, self.root / f"out-{name}")
        with self.assertRaises(ValueError):
            packing.pack(self.site, self.out)
        site = self.root / "site-link"
        write_site(site, SITE)
        (site / "assets/link.css").symlink_to(site / "assets/stylesheets/main.css")
        with self.assertRaises(ValueError):
            packing.pack(site, self.root / "out-link")

    def test_a_missing_or_unreadable_site_is_refused_not_packed_empty(self):
        missing = self.root / "missing"
        with self.assertRaises(ValueError):
            packing.pack(missing, self.root / "out-missing")
        self.assertFalse((self.root / "out-missing").exists())
        self.assertTrue(packing.check(missing, self.out))
        self.assertTrue(packing.check(self.site, self.root / "missing-out"))
        linked = self.root / "linked"
        linked.symlink_to(self.site, target_is_directory=True)
        with self.assertRaises(ValueError):
            packing.pack(linked, self.root / "out-linked")
        if os.geteuid() != 0:  # root reads any directory
            closed = self.site / "mathlib/Topology"
            closed.chmod(0)
            self.addCleanup(closed.chmod, 0o755)
            with self.assertRaises(ValueError):
                packing.pack(self.site, self.root / "out-closed")

    def test_command_line(self):
        out, summary = self.root / "cli", self.root / "summary.md"
        env = {**os.environ, "GITHUB_STEP_SUMMARY": str(summary)}
        run = subprocess.run([sys.executable, str(SCRIPT), "pack", str(self.site), str(out)],
                             capture_output=True, text=True, env=env)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(run.stdout.splitlines(), self.report)
        self.assertEqual(summary.read_text().splitlines(), [f"- {line}" for line in self.report])
        run = subprocess.run([sys.executable, str(SCRIPT), "check", str(self.site), str(out)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        (out / "publication.json").write_text("{}")
        run = subprocess.run([sys.executable, str(SCRIPT), "check", str(self.site), str(out)], capture_output=True, text=True)
        self.assertEqual(run.returncode, 1)
        self.assertIn("error: publication.json: differs from the site's file", run.stderr)
        for args in ([str(self.site), str(out)], [str(self.root / "missing"), str(self.root / "cli-missing")]):
            run = subprocess.run([sys.executable, str(SCRIPT), "pack", *args], capture_output=True, text=True)
            self.assertEqual(run.returncode, 1)
            self.assertIn("error: ", run.stderr)


def node_fetches() -> bool:
    """Whether Node.js is there with the browser's fetch and DecompressionStream (Node.js 18 or later)."""
    if not shutil.which("node"):
        return False
    probe = "process.exit(typeof Request === 'function' && typeof DecompressionStream === 'function' ? 0 : 1)"
    return subprocess.run(["node", "-e", probe], capture_output=True).returncode == 0


@unittest.skipUnless(node_fetches(), "needs Node.js 18 or later")
class LoaderTests(unittest.TestCase):
    """The loader's answer to the fetches of the explorer and the map, run by Node.js at the site's address with a
    fake server."""

    SITE_URL = "https://example.test/atlas-lean/"
    # The paths below the site's root that a fetch may name; whether each is stored gzipped must follow is_packed.
    PATHS = ["mathlib/Topology.Basic.html", "mathlib/index.html", "roadmap/index.html", "roadmap/Logic/a%20b.html",
             "roadmap/Logic/", "index.html", "coverage/index.html", "404.html", "dependencies/index.json",
             "dependencies/scopes/Logic/x.html", "roadmap.html", "mathlib.html", "xroadmap/a.html", "roadmap/a.json",
             "roadmap/a.html.gz", "search/search_index.json"]
    HARNESS = r"""
const fs = require("fs"), vm = require("vm"), zlib = require("zlib");
const [loaderPath, site, pathsJSON] = process.argv.slice(1);
const stored = {[site + "roadmap/Logic/index.html.gz"]: zlib.gzipSync("<p>Logic</p>")};
const calls = [];
async function server(input, init) {
  const request = new Request(input, init);
  const body = request.body ? await request.text() : null;
  calls.push([request.method, request.url, request.credentials, request.signal.aborted, request.redirect, body]);
  const file = request.url.split("?")[0];
  // The browser refuses a redirect it was told to refuse, as a network error.
  if (file.endsWith("/redirected.html.gz")) {
    if (request.redirect === "error") throw new TypeError("Failed to fetch");
    return new Response("elsewhere");
  }
  if (file in stored) return new Response(stored[file], {headers: {"Content-Type": "application/gzip"}});
  if (file.endsWith(".gz")) return new Response("missing", {status: 404});
  return new Response("plain");
}
const window = {fetch: server};
const context = {window, URL, Request, Response, DecompressionStream, TypeError, String,
  location: {href: site + "roadmap/index.html", hash: ""},
  document: {baseURI: site + "roadmap/index.html",
             currentScript: {src: site + "javascripts/pages-packing.js", getAttribute: () => null}}};
vm.createContext(context);
const loader = fs.readFileSync(loaderPath, "utf8");
vm.runInContext(loader, context);
vm.runInContext(loader, context);  // loaded twice: the fetch is wrapped once
(async () => {
  const out = {};
  let response = await window.fetch(site + "roadmap/Logic/index.html?v=2", {credentials: "same-origin"});
  out.page = [response.status, response.headers.get("Content-Type"), response.url, response.redirected,
              await response.text()];
  out.slash = await (await window.fetch(site + "roadmap/Logic/")).text();
  out.missing = (await window.fetch(site + "roadmap/missing.html")).status;
  try { await window.fetch(site + "roadmap/redirected.html"); out.redirected = "answered"; }
  catch (error) { out.redirected = error.name; }
  out.data = await (await window.fetch(site + "dependencies/index.json")).text();
  out.post = await (await window.fetch(site + "roadmap/Logic/index.html", {method: "POST", body: "{}"})).text();
  // A request object with a body reaches the browser's fetch unread.
  out.postRequest = await (await window.fetch(new Request(site + "dependencies/x.json", {method: "POST", body: "[1]"}))).text();
  out.getRequest = await (await window.fetch(new Request(site + "roadmap/Logic/index.html"))).text();
  out.relative = await (await window.fetch("Logic/index.html")).text();
  out.other = await (await window.fetch("https://other.test/atlas-lean/roadmap/Logic/index.html")).text();
  out.outside = await (await window.fetch("https://example.test/elsewhere/roadmap/Logic/index.html")).text();
  const controller = new AbortController();
  controller.abort();
  await window.fetch(site + "roadmap/Logic/index.html", {signal: controller.signal});
  out.calls = calls.splice(0);
  for (const path of JSON.parse(pathsJSON)) await window.fetch(site + path);
  out.rule = calls.map(call => call[1].slice(site.length));
  console.log(JSON.stringify(out));
})();
"""

    def test_the_explorer_s_fetch_of_a_stored_page_is_answered_with_the_inflated_page(self):
        run = subprocess.run(["node", "-e", self.HARNESS, str(ROOT / "scripts" / "pages_packing.js"), self.SITE_URL,
                              json.dumps(self.PATHS)], capture_output=True, text=True, timeout=60)
        self.assertEqual(run.returncode, 0, run.stderr)
        out = json.loads(run.stdout)
        site = self.SITE_URL
        # The answer has no URL of its own, so the explorer reads the page as the one it asked for.
        self.assertEqual(out["page"], [200, "text/html; charset=utf-8", "", False, "<p>Logic</p>"])
        self.assertEqual(out["slash"], "<p>Logic</p>")
        self.assertEqual(out["missing"], 404)
        self.assertEqual(out["redirected"], "TypeError")
        for key in ("data", "post", "postRequest", "other", "outside"):
            self.assertEqual(out[key], "plain", key)
        self.assertEqual(out["getRequest"], "<p>Logic</p>")
        self.assertEqual(out["relative"], "<p>Logic</p>")
        stored = ["same-origin", False, "error", None]
        self.assertEqual(out["calls"], [
            ["GET", f"{site}roadmap/Logic/index.html.gz?v=2", *stored],
            ["GET", f"{site}roadmap/Logic/index.html.gz", *stored],
            ["GET", f"{site}roadmap/missing.html.gz", *stored],
            ["GET", f"{site}roadmap/redirected.html.gz", *stored],
            ["GET", f"{site}dependencies/index.json", "same-origin", False, "follow", None],
            ["POST", f"{site}roadmap/Logic/index.html", "same-origin", False, "follow", "{}"],
            ["POST", f"{site}dependencies/x.json", "same-origin", False, "follow", "[1]"],
            ["GET", f"{site}roadmap/Logic/index.html.gz", *stored],
            ["GET", f"{site}roadmap/Logic/index.html.gz", *stored],
            ["GET", "https://other.test/atlas-lean/roadmap/Logic/index.html", "same-origin", False, "follow", None],
            ["GET", "https://example.test/elsewhere/roadmap/Logic/index.html", "same-origin", False, "follow", None],
            ["GET", f"{site}roadmap/Logic/index.html.gz", "same-origin", True, "error", None],
        ])
        # The script stores the pages that pack_pages_site.py stores, and only those.
        expected = []
        for path in self.PATHS:
            file = path + "index.html" if path.endswith("/") else path
            expected.append(file + ".gz" if packing.is_packed(file.replace("%20", " ")) else path)
        self.assertEqual(out["rule"], expected)


if __name__ == "__main__":
    unittest.main()
