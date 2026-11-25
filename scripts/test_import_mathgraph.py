#!/usr/bin/env python3
"""The mathgraph importer writes the planned pages a reviewed manifest authorises; a failed check writes nothing, and a
failed write is rolled back."""

from __future__ import annotations

import hashlib
import io
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

import jsonschema

from scripts import cards
from scripts import generate_wiki as wiki
from scripts import import_mathgraph as importer
from scripts import sync_wiki as sync

REVISION = "0123456789abcdef0123456789abcdef01234567"
SOURCE = "A. Author, *A Book on Groups*, Example Press, 2000."
NO_EDGES = hashlib.sha256(b"[]").hexdigest()  # edges_sha256 of a result with no outgoing edge
TAXONOMY = {
    "schema": "atlas-wiki-taxonomy/v1",
    "regions": {"Algebra & Number Theory": ["Algebra"]},
    "subjects": {"Algebra": {"title": "Algebra", "description": "Algebra studies operations.", "fields": [
        {"slug": "groups", "title": "Groups", "description": "Groups and their actions.", "subfields": []},
        {"slug": "rings", "title": "Rings", "description": "Rings, their ideals and modules.", "subfields": [
            {"slug": "local-rings", "title": "Local rings", "description": "Rings with one maximal ideal."},
        ]},
    ]}},
    "placements": {
        "Mathlib/GroupTheory/Coset/Basic": {"to": "Algebra/groups", "title": "Cosets"},
        "Mathlib/GroupTheory/Sylow": {"to": "Algebra/groups", "title": "Sylow theorems"},
        "Mathlib/GroupTheory/FreeGroup/Basic": {"to": "Algebra/groups", "title": "Free groups"},
        "Mathlib/RingTheory/Ideal/Basic": {"to": "Algebra/rings", "title": "Ideals"},
    },
    "mathlib_exclusions": [],
}
GROUPS = ("# Groups\n\nGroups and their actions.\n\n- [Cosets](cosets.md)\n- [Lagrange's theorem](lagrange.md)\n"
          "- [Group actions](actions/README.md)\n")
COSETS = "The left cosets of a subgroup partition the group."
LAGRANGE = "The order of a subgroup of a finite group divides the order of the group."
# Each page of the wiki, below blueprint/roadmap, with what its annotation holds besides its subject and its id,
# `af_` and its position in 24 hex digits.
PAGES = {
    "README.md": ("# ATLAS roadmap\n\n## Algebra & Number Theory\n\n- [Algebra](Algebra/README.md)\n", {}),
    "Algebra/README.md": ("# Algebra\n\nAlgebra studies operations.\n\n- [Groups](groups/README.md)\n", {}),
    "Algebra/groups/README.md": (GROUPS, {}),
    "Algebra/groups/cosets.md": (f"# Cosets\n\n{COSETS}\n",
                                 {"object": [{"location": {"declaration": "QuotientGroup.leftRel"}}]}),
    "Algebra/groups/lagrange.md": (f"# Lagrange's theorem\n\n{LAGRANGE}\n\n## Depends on\n\n- [Cosets](cosets.md)\n",
                                   {}),
    "Algebra/groups/actions/README.md": ("# Group actions\n\n- [Orbit–stabilizer theorem](orbit-stabilizer.md)\n",
                                         {"extensions": {"org.autoform": {"navigation": "module"}}}),
    "Algebra/groups/actions/orbit-stabilizer.md": (
        "# Orbit–stabilizer theorem\n\nThe orbit of a point has as many elements as the index of its stabilizer.\n",
        {"object": [{"location": {"declaration": "MulAction.orbitEquivQuotientStabilizer"}}]}),
}


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def seed(key: str) -> dict:
    return {"source": "mathgraph", "node": importer.mathgraph_id(key), "revision": REVISION}


def missing(key: str, kind: str = "statement", reason: str = "under-review") -> dict:
    return {"key": key, "kind": kind, "reason": reason}


def on(target: str, kind: str = "statement") -> dict:
    """A dependency on another row of the manifest."""
    return {"target": target, "kind": kind}


def annotation_digest(relative: str) -> str:
    """The SHA-256 of a page's annotation row, as its links file holds it, as canonical JSON: sorted keys, the
    separators `,` and `:`, non-ASCII characters as they are."""
    rows = [json.loads(line) for line in sync.links_file(wiki.ROADMAP / relative).read_text().splitlines()]
    row = next(row for row in rows if row["subject"][0]["uri"] == f"../roadmap/{relative}")
    return digest(json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False))


def on_page(relative: str, statement: str, kind: str = "statement") -> dict:
    """A dependency on a page of the fixture, bound to its reviewed identity: the SHA-256 of *statement*, its statement
    as reviewed, and that of its annotation row as it stands."""
    return {"target": f"blueprint/roadmap/{relative}", "kind": kind, "target_statement_sha256": digest(statement),
            "target_annotation_sha256": annotation_digest(relative)}


def planned(key: str, **fields) -> dict:
    row = {"key": key, "kind": "planned", "mg_kind": "theorem", "title": f"Title of {key}",
           "statement": f"The statement of {key}.", "sketch": None, "sources": [SOURCE],
           "page_dir": "blueprint/roadmap/Algebra/groups", "stem": key, "seed": seed(key), "depends": [],
           "pending": [], "not_ready": False, "prose_missing": None,
           "reference_sha256": digest(f"Book, chapter on {key}"), "edges_sha256": NO_EDGES}
    row.update(fields)
    row.setdefault("statement_sha256", digest(row["statement"]))
    row.setdefault("sketch_sha256", digest(row["sketch"] or ""))
    # mathgraph's own text, which the public text is adapted from: here, the same.
    row.setdefault("mg_statement_sha256", row["statement_sha256"])
    row.setdefault("mg_sketch_sha256", row["sketch_sha256"])
    return row


def map_row(key: str, page: str | None = None, **fields) -> dict:
    """A line of the map for the result *key*, as the importer writes one: its page *page*, by default the page of
    that name in the groups field."""
    row = {"key": key, "node": importer.mathgraph_id(key), "revision": REVISION,
           "page": page or f"blueprint/roadmap/Algebra/groups/{key}.md",
           **{name: digest(f"{name} of {key}") for name in importer.MAP_FIELDS if name.endswith("_sha256")},
           "pending": [missing("p-group")]}
    row.update(fields)
    return row


class Fixture(unittest.TestCase):
    """A small wiki the module's paths point into: a subject with a field folder, which holds a linked page at the
    folder path of the Cosets topic, a planned page and a topic folder; a second field with no folder yet."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.tmp)
        vault = self.tmp / "blueprint"
        for one in (patch.object(wiki, "ROOT", self.tmp), patch.object(wiki, "VAULT", vault),
                    patch.object(wiki, "ROADMAP", vault / "roadmap"),
                    patch.object(wiki, "TAXONOMY", self.tmp / "scripts" / "taxonomy.json"),
                    patch.object(sync, "LINKS", vault / "links"),
                    patch.object(importer, "MAP", self.tmp / "scripts" / "mathgraph-map.jsonl")):
            one.start()
            self.addCleanup(one.stop)
        self.write("scripts/taxonomy.json", json.dumps(TAXONOMY))
        self.write("blueprint/links/_defaults.json", json.dumps(sync.DEFAULTS) + "\n")
        for number, (path, (text, fields)) in enumerate(PAGES.items()):
            self.write(f"blueprint/roadmap/{path}", text)
            self.annotate(path, id=f"af_{number:024x}", **fields)

    def write(self, relative: str, text: str) -> Path:
        path = self.tmp / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def annotate(self, path: str, **fields) -> None:
        links = sync.links_file(wiki.ROADMAP / path)
        links.parent.mkdir(parents=True, exist_ok=True)
        row = {"subject": [{"type": "generic", "uri": f"../roadmap/{path}"}], **fields}
        with links.open("a") as handle:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")

    def manifest(self, rows: list) -> tuple[Path, str]:
        text = "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows)
        return self.write("manifest.jsonl", text), digest(text)

    def run_importer(self, rows: list, mode: str = "--apply", sha: str | None = None) -> tuple[int, str, str]:
        path, found = self.manifest(rows)
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = importer.main([mode, "--manifest", str(path), "--manifest-sha256", sha or found])
        return code, out.getvalue(), err.getvalue()

    def snapshot(self) -> dict[str, bytes | tuple[str, str] | None]:
        """Every file of the fixture with its bytes, every symbolic link with its target, and every folder (None), the
        manifest aside."""
        return {path.relative_to(self.tmp).as_posix(): ("symlink", os.readlink(path)) if path.is_symlink()
                else path.read_bytes() if path.is_file() else None
                for path in sorted(self.tmp.rglob("*")) if path.name != "manifest.jsonl"}

    def applied(self, rows: list) -> str:
        code, out, err = self.run_importer(rows)
        self.assertEqual(code, 0, err)
        return out

    def refused(self, rows: list, *messages: str, sha: str | None = None, mode: str = "--apply") -> str:
        before = self.snapshot()
        code, out, err = self.run_importer(rows, mode=mode, sha=sha)
        self.assertEqual(code, 1, out)
        for message in messages:
            self.assertIn(message, err)
        self.assertIn("nothing written", err)
        self.assertEqual(self.snapshot(), before)
        return err

    def failing(self, call: int):
        """The *call*-th file write failing as a full disk would: os.link, which puts a new file in place, and
        os.replace, which puts an edited one, counted together."""
        calls = []

        def hindered(real):
            def write(source, target, *args, **kwargs):
                calls.append(target)
                if len(calls) == call:
                    raise OSError(28, "No space left on device")
                return real(source, target, *args, **kwargs)
            return write

        return patch.multiple(os, link=hindered(os.link), replace=hindered(os.replace))

    def run_identity(self, *argv: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = importer.main(["--identity", *argv])
        return code, out.getvalue(), err.getvalue()

    def page(self, relative: str) -> str:
        return (wiki.ROADMAP / relative).read_text()

    def rows(self, subject: str = "Algebra") -> list[dict]:
        return [json.loads(line) for line in (sync.LINKS / f"{subject}.jsonl").read_text().splitlines()]

    def mapped(self) -> list[dict]:
        return [json.loads(line) for line in importer.MAP.read_text().splitlines()]


class Pages(Fixture):
    def test_a_planned_page_states_its_result_and_lists_its_own_prerequisites(self) -> None:
        before = (sync.LINKS / "Algebra.jsonl").read_text()
        rows = [
            planned("sylow-existence", page_dir="blueprint/roadmap/Algebra/groups/sylow-theorems",
                    sketch="Induct on the order of the group.",
                    depends=[on_page("Algebra/groups/lagrange.md", LAGRANGE)],
                    pending=[missing("p-group", reason="not-imported"),
                             missing("class-equation", "proof", "source-unverified")],
                    not_ready=True, prose_missing="A good expansion gives p-groups and the class equation pages.",
                    edges_sha256=digest('[["proof","class-equation"],["statement","p-group"]]')),
            # Its statement is adapted from mathgraph's, whose own digest the map keeps.
            planned("sylow-conjugacy", page_dir="blueprint/roadmap/Algebra/groups/sylow-theorems",
                    depends=[on("sylow-existence", "proof")], mg_statement_sha256=digest("Sylow subgroups conjugate.")),
        ]
        self.applied(rows)
        self.assertEqual(self.page("Algebra/groups/sylow-theorems/README.md"),
                         "# Sylow theorems\n\n- [Title of sylow-existence](sylow-existence.md)\n"
                         "- [Title of sylow-conjugacy](sylow-conjugacy.md)\n")
        self.assertEqual(self.page("Algebra/groups/sylow-theorems/sylow-existence.md"),
                         "# Title of sylow-existence\n\nThe statement of sylow-existence.\n\n"
                         "## Proof sketch\n\nInduct on the order of the group.\n\n"
                         "## Expansion\n\nA good expansion gives p-groups and the class equation pages.\n\n"
                         "## Depends on\n\n- [Lagrange's theorem](../lagrange.md)\n\n"
                         f"## Sources\n\n- {SOURCE}\n")
        self.assertEqual(self.page("Algebra/groups/sylow-theorems/sylow-conjugacy.md"),
                         "# Title of sylow-conjugacy\n\nThe statement of sylow-conjugacy.\n\n"
                         "## Proof depends on\n\n- [Title of sylow-existence](sylow-existence.md)\n\n"
                         f"## Sources\n\n- {SOURCE}\n")
        # The folder joins its field's list after the folders it lists; nothing else of the page changes.
        self.assertEqual(self.page("Algebra/groups/README.md"), GROUPS + "- [Sylow theorems](sylow-theorems/README.md)\n")
        links = (sync.LINKS / "Algebra.jsonl").read_text()
        self.assertTrue(links.startswith(before))
        folder, existence, conjugacy = (json.loads(line) for line in links[len(before):].splitlines())
        sha = digest("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))
        self.assertEqual(folder, {
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/sylow-theorems/README.md"}],
            "id": importer.folder_id(wiki.ROADMAP / "Algebra/groups/sylow-theorems", sha)})
        self.assertEqual(existence, {
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/sylow-theorems/sylow-existence.md"}],
            "id": importer.article_id(seed("sylow-existence")),
            "extensions": {"org.atlas-wiki": {"seed": seed("sylow-existence"), "pending": rows[0]["pending"]},
                           "org.autoform": {"not_ready": True}}})
        self.assertEqual(conjugacy, {
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/sylow-theorems/sylow-conjugacy.md"}],
            "id": importer.article_id(seed("sylow-conjugacy")),
            "extensions": {"org.atlas-wiki": {"seed": seed("sylow-conjugacy")}}})
        for row in (folder, existence, conjugacy):
            self.assertRegex(row["id"], r"\Aaf_[0-9a-f]{24}\Z")
        self.assertEqual(self.mapped(), [
            {"key": "sylow-existence", "node": importer.mathgraph_id("sylow-existence"), "revision": REVISION,
             "page": "blueprint/roadmap/Algebra/groups/sylow-theorems/sylow-existence.md",
             "statement_sha256": rows[0]["statement_sha256"], "sketch_sha256": rows[0]["sketch_sha256"],
             "mg_statement_sha256": rows[0]["statement_sha256"], "mg_sketch_sha256": rows[0]["sketch_sha256"],
             "reference_sha256": digest("Book, chapter on sylow-existence"),
             "edges_sha256": digest('[["proof","class-equation"],["statement","p-group"]]'),
             "pending": rows[0]["pending"]},
            {"key": "sylow-conjugacy", "node": importer.mathgraph_id("sylow-conjugacy"), "revision": REVISION,
             "page": "blueprint/roadmap/Algebra/groups/sylow-theorems/sylow-conjugacy.md",
             "statement_sha256": digest("The statement of sylow-conjugacy."), "sketch_sha256": digest(""),
             "mg_statement_sha256": digest("Sylow subgroups conjugate."), "mg_sketch_sha256": digest(""),
             "reference_sha256": digest("Book, chapter on sylow-conjugacy"), "edges_sha256": NO_EDGES,
             "pending": []},
        ])

    def test_no_dependency_section_is_written_without_a_link_to_list(self) -> None:
        self.applied([planned("alone"),
                      planned("proof-only", depends=[on_page("Algebra/groups/cosets.md", COSETS, "proof")]),
                      planned("pending-proof", pending=[missing("p-group", "proof")], not_ready=True,
                              prose_missing="A good expansion gives p-groups a page.")])
        self.assertEqual(self.page("Algebra/groups/alone.md"),
                         f"# Title of alone\n\nThe statement of alone.\n\n## Sources\n\n- {SOURCE}\n")
        # A theorem with only a proof prerequisite says nothing about its statement's prerequisites.
        self.assertEqual(self.page("Algebra/groups/proof-only.md"), "# Title of proof-only\n\n"
                         "The statement of proof-only.\n\n## Proof depends on\n\n- [Cosets](cosets.md)\n\n"
                         f"## Sources\n\n- {SOURCE}\n")
        self.assertEqual(self.page("Algebra/groups/pending-proof.md"), "# Title of pending-proof\n\n"
                         "The statement of pending-proof.\n\n## Expansion\n\nA good expansion gives p-groups a page.\n\n"
                         f"## Sources\n\n- {SOURCE}\n")
        for page in ("alone", "proof-only", "pending-proof"):
            self.assertNotIn("no prerequisites", self.page(f"Algebra/groups/{page}.md"))

    def test_a_definition_has_no_proof_sections(self) -> None:
        self.applied([planned("p-subgroup", mg_kind="definition", pending=[missing("p-group")], not_ready=True,
                              prose_missing="A good expansion gives p-groups a page.")])
        self.assertEqual(self.page("Algebra/groups/p-subgroup.md"),
                         "# Title of p-subgroup\n\nThe statement of p-subgroup.\n\n"
                         f"## Expansion\n\nA good expansion gives p-groups a page.\n\n## Sources\n\n- {SOURCE}\n")


class Placement(Fixture):
    def test_an_existing_page_at_the_topic_path_puts_new_pages_beside_it(self) -> None:
        out = self.applied([planned(key, page_dir="blueprint/roadmap/Algebra/groups/cosets")
                            for key in ("double-cosets", "coset-count")])
        self.assertTrue((wiki.ROADMAP / "Algebra/groups/double-cosets.md").is_file())
        self.assertTrue((wiki.ROADMAP / "Algebra/groups/coset-count.md").is_file())
        self.assertFalse((wiki.ROADMAP / "Algebra/groups/cosets").exists())
        self.assertEqual(self.page("Algebra/groups/cosets.md"), PAGES["Algebra/groups/cosets.md"][0])
        self.assertIn("beside blueprint/roadmap/Algebra/groups/cosets.md", out)

    def test_a_new_topic_with_one_page_puts_it_in_its_field_folder(self) -> None:
        self.applied([planned("free-group", page_dir="blueprint/roadmap/Algebra/groups/free-groups")])
        self.assertTrue((wiki.ROADMAP / "Algebra/groups/free-group.md").is_file())
        self.assertFalse((wiki.ROADMAP / "Algebra/groups/free-groups").exists())
        self.assertEqual(self.page("Algebra/groups/README.md"), GROUPS + "- [Title of free-group](free-group.md)\n")

    def test_a_field_and_a_subfield_without_folders_get_folder_pages_as_the_generator_writes_them(self) -> None:
        self.applied([planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
                      planned("maximal-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
                      planned("residue-field", page_dir="blueprint/roadmap/Algebra/rings/local-rings")])
        # As generate_wiki orders them: the field's subfields first, in the taxonomy's order, then its topics.
        self.assertEqual(self.page("Algebra/rings/README.md"),
                         "# Rings\n\nRings, their ideals and modules.\n\n- [Local rings](local-rings/README.md)\n"
                         "- [Ideals](ideals/README.md)\n")
        self.assertEqual(self.page("Algebra/rings/local-rings/README.md"),
                         "# Local rings\n\nRings with one maximal ideal.\n\n- [Title of residue-field](residue-field.md)\n")
        self.assertEqual(self.page("Algebra/rings/ideals/README.md"),
                         "# Ideals\n\n- [Title of maximal-ideal](maximal-ideal.md)\n"
                         "- [Title of prime-ideal](prime-ideal.md)\n")
        self.assertTrue(self.page("Algebra/README.md").endswith("- [Groups](groups/README.md)\n- [Rings](rings/README.md)\n"))
        folders = [row["subject"][0]["uri"] for row in self.rows() if row["subject"][0]["uri"].endswith("/README.md")]
        self.assertEqual(folders[-3:], ["../roadmap/Algebra/rings/README.md",
                                        "../roadmap/Algebra/rings/local-rings/README.md",
                                        "../roadmap/Algebra/rings/ideals/README.md"])


def listing(page: str) -> list[str]:
    """The titles a folder page lists, in order."""
    return re.findall(r"^- \[(.+?)\]\(", page, re.M)


class Order(Fixture):
    """A folder the importer makes lists its children as generate_wiki would, whatever the manifest's order: each is
    compared with generate_wiki.subject_tree's own tree for the same pages (see native)."""

    ROWS = [planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
            planned("maximal-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals",
                    depends=[on("prime-ideal")]),
            planned("ring-page", page_dir="blueprint/roadmap/Algebra/rings"),
            planned("regular-ring", page_dir="blueprint/roadmap/Algebra/rings/local-rings"),
            planned("artinian-ring", page_dir="blueprint/roadmap/Algebra/rings")]
    IDEALS = {"Algebra/rings/ideals": "Ideals"}

    def test_titles_equal_up_to_case_are_ordered_by_file_name(self) -> None:
        # Never by the manifest's order: a new folder's page is the same whichever of the two rows comes first.
        rows = [planned("aaa-lemma", title="Lemma", page_dir="blueprint/roadmap/Algebra/rings"),
                planned("zzz-lemma", title="lemma", page_dir="blueprint/roadmap/Algebra/rings")]
        before, pages = self.snapshot(), []
        for order in (rows, rows[::-1]):
            self.applied(order)
            pages.append(self.page("Algebra/rings/README.md"))
            for path in sorted(self.tmp.rglob("*"), reverse=True):
                relative = path.relative_to(self.tmp).as_posix()
                if relative not in before and path.name != "manifest.jsonl":
                    path.rmdir() if path.is_dir() else path.unlink()
                elif isinstance(before.get(relative), bytes):
                    path.write_bytes(before[relative])
            self.assertEqual(self.snapshot(), before)
        self.assertEqual(pages[0], pages[1])
        self.assertLess(pages[0].index("(aaa-lemma.md)"), pages[0].index("(zzz-lemma.md)"))

    def place(self, to: str, title: str) -> None:
        """A topic *title* in the folder *to*, as a placement of the fixture's taxonomy defines it."""
        taxonomy = json.loads((self.tmp / "scripts" / "taxonomy.json").read_text())
        taxonomy["placements"][f"Mathlib/Placed/{wiki.slugify(title)}"] = {"to": to, "title": title}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))

    def folder_pages(self, rows: list) -> dict[str, str]:
        path, sha = self.manifest(rows)
        return {importer.repo_path(page): text for page, text in importer.make_plan(path, sha).creates.items()
                if page.name == "README.md"}

    def native(self, rows: list, topics: dict[str, str]) -> wiki.Container:
        """generate_wiki.subject_tree's own tree of Algebra for the pages *rows* plan: each page a Target titled as its
        row, with the row's dependencies on other rows, in a module of its own, the modules named in the order of the
        titles; a page in one of the topic folders *topics* titles is in a directory placed as that topic, and any
        other page is a topic of its own in its field or subfield."""
        titles = sorted((row["title"].casefold(), row["key"]) for row in rows)
        rank = {key: number for number, (_, key) in enumerate(titles)}
        placements, targets = {}, {}
        for row in rows:
            folder = row["page_dir"].removeprefix("blueprint/roadmap/")
            if folder in topics:
                directory = f"MathlibExt/Topic{sorted(topics).index(folder)}"
                placements[directory] = {"to": folder.rpartition("/")[0], "title": topics[folder]}
                module = f"{directory}/M{rank[row['key']]:03d}"
            else:
                module = f"MathlibExt/Page/M{rank[row['key']]:03d}"
                placements[module] = {"to": folder, "title": row["title"]}
            targets[row["key"]] = wiki.Target(
                book="", idx=0, title=row["title"], slug=row["key"], location="", description="", declaration="",
                lean=None, statement=False, proof=False, names=[], module=tuple(module.split("/")))
        for row in rows:
            for entry in row["depends"]:
                if entry["target"] in targets:
                    target = targets[row["key"]]
                    (target.depends if entry["kind"] == "statement" else target.proof_depends).append(
                        targets[entry["target"]])
        return wiki.subject_tree("Algebra", list(targets.values()), {**TAXONOMY, "placements": placements})

    def as_native(self, rows: list, topics: dict[str, str]) -> dict[str, str]:
        """The new folder pages the importer plans for *rows*: the same in either manifest order, the folders that
        generate_wiki's tree for the same pages has (see native), and each listing its children as that tree's
        folder does."""
        pages = self.folder_pages(rows)
        self.assertEqual(self.folder_pages(rows[::-1]), pages)
        tree = self.native(rows, topics)

        def folders(node: wiki.Container, at: str):
            yield f"{at}/README.md", node
            for child in node.children:
                if isinstance(child, wiki.Container):
                    yield from folders(child, f"{at}/{child.slug}")

        expected = {path: node for field in tree.children if f"blueprint/roadmap/Algebra/{field.slug}/README.md" in pages
                    for path, node in folders(field, f"blueprint/roadmap/Algebra/{field.slug}")}
        self.assertEqual(sorted(pages), sorted(expected))
        for path, node in expected.items():
            with self.subTest(folder=path):
                self.assertEqual(listing(pages[path]), [child.title for child in wiki.listed(node.children)])
        return pages

    def test_the_manifest_order_does_not_change_a_new_folder_page(self) -> None:
        forward, backward = self.folder_pages(self.ROWS), self.folder_pages(self.ROWS[::-1])
        self.assertEqual(forward, backward)
        # The field's subfield, then its topic folder, then its pages by title; a page after the one it uses.
        self.assertEqual(forward["blueprint/roadmap/Algebra/rings/README.md"],
                         "# Rings\n\nRings, their ideals and modules.\n\n- [Local rings](local-rings/README.md)\n"
                         "- [Ideals](ideals/README.md)\n- [Title of artinian-ring](artinian-ring.md)\n"
                         "- [Title of ring-page](ring-page.md)\n")
        self.assertEqual(forward["blueprint/roadmap/Algebra/rings/ideals/README.md"],
                         "# Ideals\n\n- [Title of prime-ideal](prime-ideal.md)\n"
                         "- [Title of maximal-ideal](maximal-ideal.md)\n")

    def test_a_new_folder_page_lists_its_children_as_generate_wiki_does(self) -> None:
        self.as_native(self.ROWS, self.IDEALS)

    def test_a_page_that_a_topic_page_uses_leads_the_topic(self) -> None:
        # A page of the topic Ideals uses the field's own page Ring axiom, which generate_wiki puts first.
        rows = [planned("ring-axiom", title="Ring axiom", page_dir="blueprint/roadmap/Algebra/rings"),
                planned("prime-ideal", title="Prime ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
                planned("maximal-ideal", title="Maximal ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals",
                        depends=[on("ring-axiom")])]
        pages = self.as_native(rows, self.IDEALS)
        self.assertEqual(listing(pages["blueprint/roadmap/Algebra/rings/README.md"]), ["Ring axiom", "Ideals"])

    def test_a_page_that_uses_a_page_inside_a_sibling_topic_follows_the_topics(self) -> None:
        # The other direction. Pages follow the topic folders anyway, so a page's use of a page inside a sibling topic
        # shows where generate_wiki would otherwise put the page first: Ring units, which a page of Ideals uses, as it
        # uses Ring axiom, would lead with Ring axiom, but it uses a page of Ideals itself, so it follows.
        rows = [planned("ring-axiom", title="Ring axiom", page_dir="blueprint/roadmap/Algebra/rings"),
                planned("ring-units", title="Ring units", page_dir="blueprint/roadmap/Algebra/rings",
                        depends=[on("prime-ideal")]),
                planned("prime-ideal", title="Prime ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
                planned("maximal-ideal", title="Maximal ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals",
                        depends=[on("ring-axiom"), on("ring-units", "proof")])]
        pages = self.as_native(rows, self.IDEALS)
        self.assertEqual(listing(pages["blueprint/roadmap/Algebra/rings/README.md"]),
                         ["Ring axiom", "Ideals", "Ring units"])

    def test_a_subfield_and_its_topic_are_built_before_the_field(self) -> None:
        # Field, subfield and topic: the subfield's own page, which a topic page uses, leads the subfield; the topic
        # page's use of the field's page changes nothing in the field, where subfields come first.
        self.place("Algebra/rings/local-rings", "Regular local rings")
        topic = "blueprint/roadmap/Algebra/rings/local-rings/regular-local-rings"
        rows = [planned("ring-axiom", title="Ring axiom", page_dir="blueprint/roadmap/Algebra/rings"),
                planned("local-ring", title="Local ring", page_dir="blueprint/roadmap/Algebra/rings/local-rings"),
                planned("regular-local-ring", title="Regular local ring", page_dir=topic),
                planned("regular-is-domain", title="Regular rings are domains", page_dir=topic,
                        depends=[on("ring-axiom"), on("local-ring"), on("regular-local-ring", "proof")])]
        pages = self.as_native(rows, {topic.removeprefix("blueprint/roadmap/"): "Regular local rings"})
        self.assertEqual(listing(pages["blueprint/roadmap/Algebra/rings/README.md"]), ["Local rings", "Ring axiom"])
        self.assertEqual(listing(pages["blueprint/roadmap/Algebra/rings/local-rings/README.md"]),
                         ["Local ring", "Regular local rings"])
        self.assertEqual(listing(pages[f"{topic}/README.md"]), ["Regular local ring", "Regular rings are domains"])

    def test_a_topic_titled_like_its_new_field_is_flattened_into_it(self) -> None:
        # generate_wiki.namesake_first: the topic Rings is the field Rings' own material, so its pages lead the field
        # and it has no folder; each of them still gets its path, its annotation and its map row.
        self.place("Algebra/rings", "Rings")
        namesake = "blueprint/roadmap/Algebra/rings/rings"
        rows = [planned("commutative-ring", title="Commutative ring", page_dir=namesake),
                planned("ring-homomorphism", title="Ring homomorphism", page_dir=namesake,
                        depends=[on("commutative-ring")]),
                planned("prime-ideal", title="Prime ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
                planned("maximal-ideal", title="Maximal ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals",
                        depends=[on("ring-homomorphism")])]
        pages = self.as_native(rows, {namesake.removeprefix("blueprint/roadmap/"): "Rings", **self.IDEALS})
        self.assertNotIn(f"{namesake}/README.md", pages)
        self.assertEqual(listing(pages["blueprint/roadmap/Algebra/rings/README.md"]),
                         ["Commutative ring", "Ring homomorphism", "Ideals"])
        out = self.applied(rows)
        self.assertIn("blueprint/roadmap/Algebra/rings/commutative-ring.md\n      the planned page of commutative-ring, "
                      "in blueprint/roadmap/Algebra/rings, which holds the pages of topic 'Rings' itself, as "
                      "generate_wiki.namesake_first lays out a topic titled like its folder", out)
        self.assertFalse(os.path.lexists(self.tmp / namesake))
        written = {row["subject"][0]["uri"] for row in self.rows()}
        for key, folder in (("commutative-ring", "rings"), ("ring-homomorphism", "rings"),
                            ("prime-ideal", "rings/ideals"), ("maximal-ideal", "rings/ideals")):
            self.assertTrue((wiki.ROADMAP / f"Algebra/{folder}/{key}.md").is_file())
            self.assertIn(f"../roadmap/Algebra/{folder}/{key}.md", written)
        self.assertEqual([row["page"] for row in self.mapped()],
                         ["blueprint/roadmap/Algebra/rings/commutative-ring.md",
                          "blueprint/roadmap/Algebra/rings/ring-homomorphism.md",
                          "blueprint/roadmap/Algebra/rings/ideals/prime-ideal.md",
                          "blueprint/roadmap/Algebra/rings/ideals/maximal-ideal.md"])

    def test_a_page_the_layout_loses_doubles_or_leaves_unnamed_is_refused_by_name(self) -> None:
        # The layout's invariant: every page of the manifest is laid out once, with a path of its own, so a
        # regression is refused, naming the page, and never written or a crash.
        rows = [planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
                planned("maximal-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals")]
        real_order, real_name = importer.generator_order, importer.name_page

        def chosen(kid) -> bool:
            return isinstance(kid, importer.Page) and kid.row.key == "maximal-ideal"

        def lost(*args) -> list:
            return [kid for kid in real_order(*args) if not chosen(kid)]

        def doubled(*args) -> list:
            kids = real_order(*args)
            return kids + [kid for kid in kids if chosen(kid)]

        def unnamed(page, *args) -> None:
            if not chosen(page):
                real_name(page, *args)

        for name, patcher, message in (
                ("lost", patch.object(importer, "generator_order", lost), "the layout gives its page no place, not one"),
                ("doubled", patch.object(importer, "generator_order", doubled),
                 "the layout gives its page 2 places, not one"),
                ("unnamed", patch.object(importer, "name_page", unnamed),
                 "the layout gives its page no path of its own")):
            with self.subTest(name), patcher:
                err = self.refused(rows, f"manifest line 2 (maximal-ideal): {message}, so nothing is written")
                self.assertNotIn("manifest line 1", err)


class Parts(Fixture):
    def test_a_new_topic_folder_above_twenty_pages_is_split_into_transparent_parts(self) -> None:
        keys = [f"sylow-{number:02d}" for number in range(1, 22)]
        self.applied([planned(key, page_dir="blueprint/roadmap/Algebra/groups/sylow-theorems") for key in keys])
        # Parts of a list in dependency order are named by number, as generate_wiki names them.
        first = "".join(f"- [Title of {key}](part-01/{key}.md)\n" for key in keys[:20])
        self.assertEqual(self.page("Algebra/groups/sylow-theorems/README.md"),
                         "# Sylow theorems\n\n## [Part 1 of 2](part-01/README.md)\n\n"
                         f"{first}\n## [Part 2 of 2](part-02/README.md)\n\n- [Title of sylow-21](part-02/sylow-21.md)\n")
        self.assertEqual(self.page("Algebra/groups/sylow-theorems/part-02/README.md"),
                         "# Part 2 of 2\n\n- [Title of sylow-21](sylow-21.md)\n")
        parts = {row["subject"][0]["uri"]: row for row in self.rows() if "/part-0" in row["subject"][0]["uri"]}
        self.assertEqual(parts["../roadmap/Algebra/groups/sylow-theorems/part-01/README.md"]["extensions"],
                         {"org.autoform": {"navigation": "transparent"}})

    def test_a_field_pushed_above_24_children_gets_its_new_children_in_a_part(self) -> None:
        for number in range(20):  # 23 children with cosets, lagrange and actions
            self.write(f"blueprint/roadmap/Algebra/groups/extra-{number:02d}.md", f"# Extra {number}\n\nText.\n")
        out = self.applied([planned(key) for key in ("gamma", "alpha", "beta")])
        # Titled by its number, as its folder is named, its children in the manifest's order.
        self.assertEqual(self.page("Algebra/groups/README.md"), GROUPS + "- [Part 1](part-01/README.md)\n")
        self.assertEqual(self.page("Algebra/groups/part-01/README.md"),
                         "# Part 1\n\n- [Title of gamma](gamma.md)\n- [Title of alpha](alpha.md)\n"
                         "- [Title of beta](beta.md)\n")
        self.assertIn("blueprint/roadmap/Algebra/groups/part-01/alpha.md\n      the planned page of alpha, in the existing "
                      "folder blueprint/roadmap/Algebra/groups, in its new transparent part part-01", out)

    def test_a_folder_that_parts_cannot_keep_within_its_limit_is_refused(self) -> None:
        for number in range(21):  # 24 children with cosets, lagrange and actions
            self.write(f"blueprint/roadmap/Algebra/groups/extra-{number:02d}.md", f"# Extra {number}\n\nText.\n")
        self.refused([planned("alpha"), planned("beta")], "blueprint/roadmap/Algebra/groups has 24 direct children")


class Lists(Fixture):
    """A folder and its transparent parts have one list: one set of names, and a folder page that copies each part's
    list."""

    def split_topic(self) -> str:
        """The Sylow theorems topic of the groups field, split into two transparent parts, whose folder page copies
        each part's list under the heading that links the part, as generate_wiki writes it."""
        folder, sections = "Algebra/groups/sylow-theorems", []
        for part, title, stems in (("part-01", "Alpha to Beta", ("alpha", "beta")),
                                   ("part-02", "Gamma to Delta", ("gamma", "delta"))):
            self.write(f"blueprint/roadmap/{folder}/{part}/README.md",
                       f"# {title}\n\n" + "".join(f"- [{stem.title()}]({stem}.md)\n" for stem in stems))
            self.annotate(f"{folder}/{part}/README.md", extensions={"org.autoform": {"navigation": "transparent"}})
            for stem in stems:
                self.write(f"blueprint/roadmap/{folder}/{part}/{stem}.md", f"# {stem.title()}\n\nThe {stem} result.\n")
                self.annotate(f"{folder}/{part}/{stem}.md")
            sections.append(f"## [{title}]({part}/README.md)\n\n"
                            + "".join(f"- [{stem.title()}]({part}/{stem}.md)\n" for stem in stems))
        self.write(f"blueprint/roadmap/{folder}/README.md", "# Sylow theorems\n\n" + "\n".join(sections))
        self.annotate(f"{folder}/README.md")
        return folder

    def test_two_existing_parts_of_one_folder_share_its_names(self) -> None:
        folder = self.split_topic()
        err = self.refused([planned("limit-a", page_dir=f"blueprint/roadmap/{folder}/part-01", stem="limit"),
                            planned("limit-b", page_dir=f"blueprint/roadmap/{folder}/part-02", stem="limit"),
                            planned("gamma-again", page_dir=f"blueprint/roadmap/{folder}/part-01", stem="gamma")],
                           "manifest line 2 (limit-b): its stem limit collides with the new page "
                           f"blueprint/roadmap/{folder}/part-01/limit.md, in blueprint/roadmap/{folder}/part-02; a stem "
                           "is never numbered", "manifest line 3 (gamma-again): its stem gamma collides with the existing "
                           f"page blueprint/roadmap/{folder}/part-02/gamma.md, in blueprint/roadmap/{folder}/part-01")
        self.assertNotIn("manifest line 1", err)

    def test_a_page_that_joins_an_existing_part_joins_its_copy_on_the_folder_page(self) -> None:
        folder = self.split_topic()
        out = self.applied([planned("limit", page_dir=f"blueprint/roadmap/{folder}/part-01"),
                            planned("bound", page_dir=f"blueprint/roadmap/{folder}/part-02")])
        self.assertEqual(self.page(f"{folder}/part-01/README.md"),
                         "# Alpha to Beta\n\n- [Alpha](alpha.md)\n- [Beta](beta.md)\n- [Title of limit](limit.md)\n")
        self.assertEqual(self.page(f"{folder}/README.md"),
                         "# Sylow theorems\n\n## [Alpha to Beta](part-01/README.md)\n\n- [Alpha](part-01/alpha.md)\n"
                         "- [Beta](part-01/beta.md)\n- [Title of limit](part-01/limit.md)\n\n"
                         "## [Gamma to Delta](part-02/README.md)\n\n- [Gamma](part-02/gamma.md)\n"
                         "- [Delta](part-02/delta.md)\n- [Title of bound](part-02/bound.md)\n")
        self.assertIn(f"blueprint/roadmap/{folder}/README.md: - [Title of limit](part-01/limit.md)\n"
                      "      copies the part's new item, as sync_wiki.with_part_lists keeps a part's list", out)

    def test_a_copy_that_is_not_its_parts_list_is_refused(self) -> None:
        folder = self.split_topic()
        readme = wiki.ROADMAP / folder / "README.md"
        readme.write_text(readme.read_text().replace("- [Beta](part-01/beta.md)\n", ""))
        self.refused([planned("limit", page_dir=f"blueprint/roadmap/{folder}/part-01")],
                     f"blueprint/roadmap/{folder}/README.md: its copy of the list of blueprint/roadmap/{folder}/part-01/ "
                     "cannot be kept in step with the part's new items")

    def existing_part(self) -> None:
        """A transparent part of the groups field, beside 22 other children: 23 in all."""
        self.write("blueprint/roadmap/Algebra/groups/part-01/README.md", "# Old\n\n- [Old](old.md)\n")
        self.annotate("Algebra/groups/part-01/README.md", extensions={"org.autoform": {"navigation": "transparent"}})
        self.write("blueprint/roadmap/Algebra/groups/part-01/old.md", "# Old\n\nText.\n")
        for number in range(19):
            self.write(f"blueprint/roadmap/Algebra/groups/extra-{number:02d}.md", f"# Extra {number}\n\nText.\n")

    def test_an_existing_part_and_a_new_part_share_their_folder_names(self) -> None:
        self.existing_part()
        self.refused([planned("alpha"), planned("beta"),
                      planned("alpha-again", page_dir="blueprint/roadmap/Algebra/groups/part-01", stem="alpha")],
                     "manifest line 3 (alpha-again): its stem alpha collides with the new page "
                     "blueprint/roadmap/Algebra/groups/part-02/alpha.md, in blueprint/roadmap/Algebra/groups/part-01")
        self.applied([planned("alpha"), planned("beta"),
                      planned("gamma", page_dir="blueprint/roadmap/Algebra/groups/part-01")])
        # The new part is numbered after the part the field has.
        self.assertEqual(self.page("Algebra/groups/part-02/README.md"), "# Part 2\n\n"
                         "- [Title of alpha](alpha.md)\n- [Title of beta](beta.md)\n")
        self.assertEqual(self.page("Algebra/groups/part-01/README.md"), "# Old\n\n- [Old](old.md)\n"
                         "- [Title of gamma](gamma.md)\n")
        self.assertEqual(self.page("Algebra/groups/README.md"),
                         GROUPS + "- [Part 2](part-02/README.md)\n")

    def test_no_new_folder_takes_a_parts_name(self) -> None:
        taxonomy = json.loads(json.dumps(TAXONOMY))
        taxonomy["placements"]["Mathlib/GroupTheory/Part3"] = {"to": "Algebra/groups", "title": "Part 3"}
        self.write("scripts/taxonomy.json", json.dumps(taxonomy))
        self.refused([planned(key, page_dir="blueprint/roadmap/Algebra/groups/part-3") for key in ("a", "b")],
                     "blueprint/roadmap/Algebra/groups/part-3/ cannot be made a folder: it collides with a name "
                     "reserved for folder pages and the generator's parts")
        # A new part takes the number after the field's parts; a path in the way is refused, never written over.
        self.existing_part()
        (wiki.ROADMAP / "Algebra/groups/part-02").mkdir()
        self.refused([planned("alpha"), planned("beta")],
                     "blueprint/roadmap/Algebra/groups/part-02/ cannot be made a folder: it collides with "
                     "blueprint/roadmap/Algebra/groups/part-02, which is there")


class Endpoints(Fixture):
    """A dependency is another planned row of the manifest, or an existing page bound to its reviewed identity."""

    def test_an_existing_page_whose_statement_changed_under_the_same_name(self) -> None:
        self.write("blueprint/roadmap/Algebra/groups/cosets.md", "# Cosets\n\nThe right cosets partition the group.\n")
        self.refused([planned("double-cosets", depends=[on_page("Algebra/groups/cosets.md", COSETS)])],
                     "manifest line 1 (double-cosets): depends/0: blueprint/roadmap/Algebra/groups/cosets.md: the "
                     f"SHA-256 of its statement as Autoform reads it is {digest('The right cosets partition the group.')}, "
                     f"not the reviewed target_statement_sha256 {digest(COSETS)}")

    def test_an_existing_page_whose_annotation_changed(self) -> None:
        dependency = on_page("Algebra/groups/cosets.md", COSETS)
        rows = self.rows()
        for row in rows:
            if row["subject"][0]["uri"] == "../roadmap/Algebra/groups/cosets.md":
                row["object"] = [{"location": {"declaration": "QuotientGroup.rightRel"}}]
        (sync.LINKS / "Algebra.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.refused([planned("double-cosets", depends=[dependency])],
                     "depends/0: blueprint/roadmap/Algebra/groups/cosets.md: the SHA-256 of its annotation row as "
                     f"canonical JSON is {annotation_digest('Algebra/groups/cosets.md')}, not the reviewed "
                     f"target_annotation_sha256 {dependency['target_annotation_sha256']}")

    def test_an_existing_page_without_id_may_be_a_dependency(self) -> None:
        self.write("blueprint/roadmap/Algebra/groups/is-normal.md", "# Normal subgroup\n\nA normal subgroup.\n")
        self.annotate("Algebra/groups/is-normal.md", object=[{"location": {"declaration": "Subgroup.Normal"}}])
        self.applied([planned("quotient-group", depends=[on_page("Algebra/groups/is-normal.md", "A normal subgroup.")])])
        self.assertIn("## Depends on\n\n- [Normal subgroup](is-normal.md)\n", self.page("Algebra/groups/quotient-group.md"))

    def test_an_existing_page_with_two_annotation_rows(self) -> None:
        self.annotate("Algebra/groups/cosets.md", id=f"af_{97:024x}")
        self.refused([planned("double-cosets", depends=[on_page("Algebra/groups/cosets.md", COSETS)])],
                     "depends/0: blueprint/roadmap/Algebra/groups/cosets.md has more than one annotation row")

    def test_a_held_page(self) -> None:
        rows = self.rows()
        for row in rows:
            if row["subject"][0]["uri"] == "../roadmap/Algebra/groups/cosets.md":
                del row["object"]
                row["extensions"] = {"org.atlas-wiki": {"held": {
                    "declaration": "QuotientGroup.leftRel", "reason": "mis-specified", "issue": 1}}}
        (sync.LINKS / "Algebra.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.refused([planned("double-cosets", depends=[on_page("Algebra/groups/cosets.md", COSETS)])],
                     "depends/0: blueprint/roadmap/Algebra/groups/cosets.md is held back, and unlinked until its "
                     "declaration is fixed")

    def test_a_folder_page_a_page_without_annotation_and_a_missing_page(self) -> None:
        self.write("blueprint/roadmap/Algebra/groups/stray.md", "# Stray\n\nA statement.\n")
        folder = {**on_page("Algebra/groups/README.md", "Groups and their actions."), "kind": "statement"}
        stray = {"target": "blueprint/roadmap/Algebra/groups/stray.md", "kind": "statement",
                 "target_statement_sha256": digest("A statement."), "target_annotation_sha256": digest("{}")}
        absent = {**stray, "target": "blueprint/roadmap/Algebra/groups/absent.md"}
        self.refused([planned("a", depends=[folder, stray, absent, on("no-such-result")])],
                     "depends/0: blueprint/roadmap/Algebra/groups/README.md is a folder page, which states no result",
                     "depends/1: blueprint/roadmap/Algebra/groups/stray.md has no annotation, so no identity to bind",
                     "depends/2: blueprint/roadmap/Algebra/groups/absent.md is no page of the wiki",
                     "depends/3: no-such-result is no row of this manifest")

    def test_a_page_target_carries_its_identity_and_a_row_target_none(self) -> None:
        unbound = {"target": "blueprint/roadmap/Algebra/groups/cosets.md", "kind": "proof"}
        stamped = {**on("b"), "target_annotation_sha256": digest("{}")}
        self.refused([planned("a", depends=[unbound]), planned("b"), planned("c", depends=[stamped])],
                     "manifest line 1 (a): depends/0: 'target_statement_sha256' is a required property",
                     "manifest line 1 (a): depends/0: 'target_annotation_sha256' is a required property",
                     "manifest line 3 (c): depends/0/target_annotation_sha256 is allowed only for a target that is an "
                     "existing page")

    def test_a_row_that_fails_its_checks_is_no_target(self) -> None:
        self.refused([planned("a", statement_sha256=digest("another statement")),
                      planned("b", depends=[on("a")]), planned("c", depends=[on("d")]), {"key": "d", "kind": "alias"}],
                     "manifest line 2 (b): depends/0: a is a row of this manifest that fails its checks",
                     "manifest line 3 (c): depends/0: d is a row of this manifest that fails its checks",
                     "manifest line 4 (d): kind: 'alias' is not one of ['planned', 'mathlib']")

    def test_a_pending_prerequisite_that_the_manifest_writes(self) -> None:
        self.refused([planned("a"), planned("b", pending=[missing("a")], not_ready=True, prose_missing="It uses a.")],
                     "manifest line 2 (b): pending/0: a is a row of this manifest, an active endpoint, so it belongs in "
                     "depends, not in pending")

    def test_a_pending_prerequisite_the_map_records_as_imported(self) -> None:
        # A key the map holds was imported already: never pending, but a dependency on the page the map names, which
        # the manifest gives with its reviewed identity; the importer never links it on its own.
        self.applied([planned("p-group")])
        page = "blueprint/roadmap/Algebra/groups/p-group.md"
        waiting = planned("sylow-existence", pending=[missing("p-group")], not_ready=True,
                          prose_missing="It uses p-groups.")
        for mode in ("--check", "--apply"):
            with self.subTest(mode=mode):
                self.refused([waiting], "manifest line 1 (sylow-existence): pending/0: pending key p-group was imported "
                             f"already (map line 1, imported at {page}); name its page, at its current path, under "
                             "depends with its reviewed identity (`--identity <page>`)", mode=mode)
        # Under depends, with the identity --identity prints, the imported page is linked.
        self.applied([planned("sylow-existence", depends=[on_page("Algebra/groups/p-group.md", "The statement of p-group.")])])
        self.assertIn("## Depends on\n\n- [Title of p-group](p-group.md)\n", self.page("Algebra/groups/sylow-existence.md"))
        # A pending key that is neither a row of the manifest nor a key the map holds stays pending.
        self.applied([planned("sylow-conjugacy", pending=[missing("class-equation")], not_ready=True,
                              prose_missing="It uses the class equation.")])
        self.assertEqual(self.mapped()[-1]["pending"], [missing("class-equation")])

    def test_a_pending_list_that_names_the_row_or_a_key_twice(self) -> None:
        # The rules of pending_problems, which a line of the map is held to as well.
        self.refused([planned("a", pending=[missing("a")], not_ready=True, prose_missing="It uses a."),
                      planned("b", pending=[missing("p-group"), missing("p-group", "proof")], not_ready=True,
                              prose_missing="It uses p-groups.")],
                     "manifest line 1 (a): pending/0: a is the row itself",
                     "manifest line 2 (b): pending/1: p-group is pending twice")

    def test_a_dependency_named_twice(self) -> None:
        self.refused([planned("a"), planned("b", depends=[on("a"), on("a", "proof")])],
                     "manifest line 2 (b): depends/1 names the page depends/0 names")


class FailClosed(Fixture):
    def test_a_missing_or_empty_manifest(self) -> None:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = importer.main(["--check", "--manifest", str(self.tmp / "absent.jsonl"),
                                  "--manifest-sha256", digest("")])
        self.assertEqual(code, 1)
        self.assertIn("there is no such manifest", err.getvalue())
        self.refused([], "the manifest is empty")

    def test_a_manifest_without_the_reviewed_digest(self) -> None:
        self.refused([planned("sylow-existence")], "not the reviewed", sha=digest("another manifest"))

    def test_a_row_the_schema_refuses(self) -> None:
        row = planned("sylow-existence", note="extra", reference_sha256="the reference", edges_sha256=None)
        del row["title"], row["mg_statement_sha256"]
        self.refused([row, {"kind": "planned"}, ["not", "an", "object"]],
                     "manifest line 1 (sylow-existence): 'title' is a required property",
                     "manifest line 1 (sylow-existence): 'mg_statement_sha256' is a required property",
                     "Additional properties are not allowed ('note' was unexpected)",
                     "manifest line 1 (sylow-existence): reference_sha256: 'the reference' does not match",
                     "manifest line 1 (sylow-existence): edges_sha256: None is not of type 'string'",
                     "manifest line 2: 'key' is a required property", "manifest line 3: not a JSON object")

    def test_a_field_that_ends_in_a_line_break_is_refused(self) -> None:
        # A JSON Schema validator searches for a pattern, and `$` also matches before a final line break: the
        # importer matches each pattern against the whole string, so a key, an id, a revision, a digest, a path or a
        # line that ends in a line break is refused, and so is text that does.
        rows = [planned("sylow-existence", sketch="Induct on the order of the group.",
                        depends=[on_page("Algebra/groups/cosets.md", COSETS), on("sylow-conjugacy", "proof")],
                        pending=[missing("p-group")], not_ready=True, prose_missing="It uses p-groups."),
                planned("sylow-conjugacy")]
        code, out, err = self.run_importer(rows, mode="--check")
        self.assertEqual((code, err), (0, ""))
        for field in ("key", "seed/node", "seed/revision", "title", "statement", "sketch", "sources/0", "page_dir",
                      "stem", "prose_missing", "statement_sha256", "sketch_sha256", "mg_statement_sha256",
                      "mg_sketch_sha256", "reference_sha256", "edges_sha256", "depends/0/target",
                      "depends/0/target_statement_sha256", "depends/0/target_annotation_sha256", "depends/1/target",
                      "pending/0/key"):
            with self.subTest(field=field):
                row = json.loads(json.dumps(rows[0]))
                *path, last = [int(part) if part.isdigit() else part for part in field.split("/")]
                holder = row
                for part in path:
                    holder = holder[part]
                holder[last] += "\n"
                label = '"sylow-existence\\n"' if field == "key" else "sylow-existence"
                if field.endswith("/target") or field in ("sketch", "prose_missing"):
                    message = f"{field}: {holder[last]!r} is not valid under any of the given schemas ("
                else:
                    message = f"{field}: {holder[last]!r} does not match"
                err = self.refused([row, rows[1]], f"manifest line 1 ({label}): {message}", "as a whole string")
                self.assertNotIn("manifest line 2", err)

    def test_a_duplicate_key(self) -> None:
        self.refused([planned("sylow-existence"), planned("sylow-existence")],
                     "manifest lines 1, 2: the key sylow-existence appears more than once")

    def test_a_topic_folder_that_no_placement_defines(self) -> None:
        self.refused([planned(key, page_dir="blueprint/roadmap/Algebra/groups/no-such-topic") for key in ("a", "b")],
                     "no topic folder a placement defines")

    def test_a_stem_that_is_taken_is_refused_and_never_numbered(self) -> None:
        self.write("blueprint/roadmap/Algebra/groups/part-01/README.md", "# Part\n\n- [Old](old.md)\n")
        self.write("blueprint/roadmap/Algebra/groups/part-01/old.md", "# Old\n\nText.\n")
        self.refused([planned("lagrange-theorem", stem="lagrange"), planned("group-actions", stem="actions"),
                      planned("readme-page", stem="readme"), planned("second-part", stem="part-02"),
                      planned("old-result", stem="old"), planned("first"), planned("second", stem="first")],
                     "manifest line 1 (lagrange-theorem): its stem lagrange collides with the existing page "
                     "blueprint/roadmap/Algebra/groups/lagrange.md, in blueprint/roadmap/Algebra/groups; a stem is never "
                     "numbered", "manifest line 2 (group-actions): its stem actions collides with the existing folder "
                     "blueprint/roadmap/Algebra/groups/actions/",
                     "manifest line 3 (readme-page): its stem readme collides with a name reserved for folder pages",
                     "manifest line 4 (second-part): its stem part-02 collides with a name reserved",
                     "manifest line 5 (old-result): its stem old collides with the existing page "
                     "blueprint/roadmap/Algebra/groups/part-01/old.md",
                     "manifest line 7 (second): its stem first collides with the new page "
                     "blueprint/roadmap/Algebra/groups/first.md")

    def test_a_folder_whose_name_a_page_takes(self) -> None:
        self.write("blueprint/roadmap/Algebra/rings.md", "# Rings\n\nA page.\n")
        self.refused([planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings")],
                     "blueprint/roadmap/Algebra/rings/ cannot be made a folder: blueprint/roadmap/Algebra/rings.md is there")

    def test_an_existing_page_is_never_written_over(self) -> None:
        path, sha = self.manifest([planned("sylow-existence")])
        plan = importer.make_plan(path, sha)
        target = wiki.ROADMAP / "Algebra/groups/sylow-existence.md"
        self.assertIn(target, plan.creates)
        target.write_text("# A page written meanwhile\n")
        before = self.snapshot()
        with self.assertRaises(importer.Refused) as refused:
            importer.apply(plan)
        self.assertEqual(refused.exception.problems, ["blueprint/roadmap/Algebra/groups/sylow-existence.md exists now"])
        self.assertEqual(self.snapshot(), before)

    def test_a_folder_page_only_gains_lines(self) -> None:
        def rewrite(readme: Path, line: str, before=(), after=(), section=()) -> str:
            readme.write_text(readme.read_text().replace("# Groups", "# Groups and more") + line + "\n")
            return ""

        with patch.object(sync, "add_to_listing", rewrite):
            self.refused([planned("sylow-existence")], "the listing would change an existing line")

    def test_a_cycle_among_new_pages_or_through_an_existing_one(self) -> None:
        self.refused([planned("a", depends=[on("b")]), planned("b", depends=[on("a", "proof")])],
                     "the new dependencies close a cycle: blueprint/roadmap/Algebra/groups/a.md -> "
                     "blueprint/roadmap/Algebra/groups/b.md -> blueprint/roadmap/Algebra/groups/a.md")
        lagrange = wiki.ROADMAP / "Algebra/groups/lagrange.md"
        lagrange.write_text(lagrange.read_text() + "\n## Informally uses\n\n- [Sylow](sylow-existence.md)\n")
        self.refused([planned("sylow-existence", depends=[on_page("Algebra/groups/lagrange.md", LAGRANGE)])],
                     "close a cycle: blueprint/roadmap/Algebra/groups/sylow-existence.md -> "
                     "blueprint/roadmap/Algebra/groups/lagrange.md -> blueprint/roadmap/Algebra/groups/sylow-existence.md")

    def test_an_internal_reference_in_public_text(self) -> None:
        self.refused([planned("sylow-existence", statement="As in D" + "123456789, every group has one.")],
                     "statement holds a reference the Public references check reports (internal-reference, line 1)")

    def test_an_id_collision(self) -> None:
        self.annotate("Algebra/groups/elsewhere.md", id=importer.article_id(seed("sylow-existence")))
        self.refused([planned("sylow-existence")], f"{importer.article_id(seed('sylow-existence'))}, is already an annotation's")

    def test_digests_readiness_and_a_definitions_proof(self) -> None:
        self.refused([planned("a", statement_sha256=digest("another statement")),
                      planned("b", pending=[missing("p-group")], prose_missing="It uses p-groups."),
                      planned("c", pending=[missing("p-group")], not_ready=True),
                      planned("d", mg_kind="definition", sketch="A construction."),
                      planned("e", mg_kind="definition", depends=[on_page("Algebra/groups/cosets.md", COSETS, "proof")]),
                      planned("f", seed={**seed("f"), "node": importer.mathgraph_id("g")})],
                     "manifest line 1 (a): statement_sha256 is not the SHA-256 of its statement",
                     "manifest line 2 (b): not_ready is false but its pending list is not empty",
                     "manifest line 3 (c): prose_missing is null but its pending list is not empty",
                     "manifest line 4 (d): a definition has no proof, so no sketch",
                     "manifest line 5 (e): a definition has no proof, so no proof prerequisite",
                     "manifest line 6 (f): seed node")

    def test_a_result_the_map_holds(self) -> None:
        row = map_row("sylow-existence", page="blueprint/roadmap/Algebra/groups/elsewhere.md")
        self.write("scripts/mathgraph-map.jsonl", importer.map_line(row) + "\n")
        self.refused([planned("sylow-existence")], "scripts/mathgraph-map.jsonl already maps sylow-existence")

    def test_text_that_links_a_page_opens_a_section_or_would_be_published_as_typed(self) -> None:
        self.refused([planned("a", statement="It refines [Lagrange's theorem](lagrange.md)."),
                      planned("b", statement="It holds.\n\n## Proof\n\nClear.")],
                     "statement links to 'lagrange.md'", "statement has a line that is a Markdown heading")
        # Underscores pair up as emphasis outside math, and the braces after the second one read as an attribute list.
        self.refused([planned("c", prose_missing="It uses the sums ⊕_{i+j=n} H_i and ⊕_{i+j=n−1} H_i.",
                              pending=[missing("graded-sum")], not_ready=True)],
                     "blueprint/roadmap/Algebra/groups/c.md: render would show it as typed, as Autoform's check of "
                     "what the site may publish finds: line 7: attribute list {i+j=n−1} is not allowed")

    def test_text_links_and_shows_only_https_addresses(self) -> None:
        # Judged on the text as the site renders it: reference links, autolinks and images too, and a reference
        # definition, which on the page would also serve a reference in another section.
        err = self.refused([planned("a", statement="See [cosets][r].\n\n[r]: cosets.md"),
                            planned("b", statement="See <http://example.com/a>."),
                            planned("c", statement="See ![a picture](../../../theme/logo.png)."),
                            planned("d", statement="See [cosets][r].", sketch="It is clear.\n\n[r]: lagrange.md"),
                            planned("e", statement="See [the book](https://example.com/book).")],
                           "manifest line 1 (a): statement links to 'cosets.md'",
                           "manifest line 1 (a): statement defines a link to 'cosets.md'",
                           "manifest line 2 (b): statement links to 'http://example.com/a'",
                           "manifest line 3 (c): statement shows an image from '../../../theme/logo.png'",
                           "manifest line 4 (d): sketch defines a link to 'lagrange.md'")
        self.assertNotIn("manifest line 5", err)

    def test_a_title_that_would_break_the_links_to_its_page(self) -> None:
        # A title ending in a backslash escapes the bracket that closes every link to its page.
        self.refused([planned("aaa", title="Quotient by \\")],
                     "manifest line 1 (aaa): title ends in a backslash, which would escape the bracket that closes "
                     "every link to its page")
        # Every link the importer writes is read as one link to its target, or its row is refused: on a new folder page
        # and in a dependency section, which the title check is lifted here to reach.
        rows = [planned("aaa", title="Quotient by \\", page_dir="blueprint/roadmap/Algebra/rings"),
                planned("bbb", depends=[on("aaa")], page_dir="blueprint/roadmap/Algebra/rings")]
        with patch.object(importer, "text_problems", lambda row: []):
            self.refused(rows, "manifest line 1 (aaa): blueprint/roadmap/Algebra/rings/README.md would not list it as "
                         "one link to aaa.md", "manifest line 2 (bbb): '- [Quotient by \\\\](aaa.md)' would not be "
                         "one link to aaa.md")
        # So does the heading of an existing page, which no title check reaches, where a dependency links it.
        self.write("blueprint/roadmap/Algebra/groups/quotient.md", "# Quotient by \\\n\nThe statement of quotient.\n")
        self.annotate("Algebra/groups/quotient.md", id="af_" + "e" * 24)
        self.refused([planned("ccc", depends=[on_page("Algebra/groups/quotient.md", "The statement of quotient.")])],
                     "manifest line 1 (ccc): '- [Quotient by \\\\](quotient.md)' would not be one link to "
                     "quotient.md")

    def test_a_source_that_would_make_a_rule(self) -> None:
        sources = ("---", "* * *", "- -", "___")
        self.refused([planned(f"s{number}", sources=[source, SOURCE]) for number, source in enumerate(sources)],
                     *(f"manifest line {number + 1} (s{number}): sources/0 would make a rule, not a source, in the "
                       "page's list of sources" for number in range(len(sources))))

    def test_a_line_that_would_make_a_heading_or_a_rule_is_refused(self) -> None:
        # A setext underline below a line of text makes it a heading; a thematic break ends the paragraph and draws a
        # rule. Either would end the section the prose is written in.
        lines = {"setext =": "Claim\n=====", "setext -": "Claim\n-----", "***": "Claim.\n\n***",
                 "- - -": "Claim.\n- - -"}
        for field in ("statement", "sketch", "prose_missing"):
            for name, text in lines.items():
                with self.subTest(field=field, line=name):
                    fields = {field: text}
                    if field == "prose_missing":
                        fields.update(pending=[missing("p-group")], not_ready=True)
                    self.refused([planned("sylow-existence", **fields)],
                                 f"manifest line 1 (sylow-existence): {field} has a line that would make a Markdown "
                                 "heading or a rule, which would end its section")

    def test_a_list_or_a_dash_in_prose_is_accepted(self) -> None:
        text = "It holds in two cases:\n- n is even;\n- n is odd.\n\nSo a - b and -1 stay as they are."
        self.applied([planned("sylow-existence", statement=text, sketch=text, pending=[missing("p-group")],
                              not_ready=True, prose_missing=text)])
        self.assertEqual(self.page("Algebra/groups/sylow-existence.md").count(text), 3)

    def test_a_page_that_autoform_would_read_otherwise_is_refused(self) -> None:
        # A comment that never closes hides every heading after it from Autoform, which would read the sections as
        # part of the statement: the importer reads each page back and refuses it.
        self.refused([planned("sylow-existence", statement="Every finite group has one <!-- as below.")],
                     "manifest line 1 (sylow-existence): Autoform would read the statement or the sections of its page "
                     "otherwise than the importer writes them, so its text would change the page's structure")

    def test_a_page_is_never_placed_in_a_card(self) -> None:
        rows = self.rows()
        for row in rows:
            if row["subject"][0]["uri"] == "../roadmap/Algebra/groups/actions/README.md":
                row["extensions"] = {"org.atlas-wiki": {"card": {
                    "kind": "result", "main_article_id": f"af_{6:024x}", "importance": "key", "level": "undergraduate"}}}
        (sync.LINKS / "Algebra.jsonl").write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows))
        self.refused([planned("orbit-counting", page_dir="blueprint/roadmap/Algebra/groups/actions")],
                     "its folder blueprint/roadmap/Algebra/groups/actions is in the card "
                     "blueprint/roadmap/Algebra/groups/actions/, which holds only the statements its editors place in it")

    def test_an_address_the_card_move_ledger_records_is_never_taken(self) -> None:
        self.write("scripts/card-moves.jsonl", "".join(json.dumps(row) + "\n" for row in (
            {"page": "Algebra/groups/sylow-existence", "to": "Algebra/groups/actions/sylow-existence",
             "article_id": f"af_{99:024x}"},
            {"card": f"af_{98:024x}", "folder": "Algebra/rings", "replaced_by": f"af_{97:024x}"})))
        self.refused([planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings")],
                     "blueprint/roadmap/Algebra/rings/ cannot be made a folder: scripts/card-moves.jsonl records the address")
        self.refused([planned("sylow-existence")], "its stem sylow-existence collides with the address "
                     "blueprint/roadmap/Algebra/groups/sylow-existence, which scripts/card-moves.jsonl records")

    def test_a_folder_page_the_sync_only_appends_to_gets_a_checked_insertion_that_the_plan_names(self) -> None:
        # An item that runs on to an indented line is no simple page, so the sync would only append at the end.
        groups = GROUPS.replace("](lagrange.md)\n", "](lagrange.md): a subgroup's order\n  divides the group's.\n")
        groups += "\n## Related topics\n\n- [Rings](../rings/README.md)\n"
        self.write("blueprint/roadmap/Algebra/groups/README.md", groups)
        out = self.applied([planned("sylow-existence")])
        self.assertEqual(self.page("Algebra/groups/README.md"), groups.replace(
            "](actions/README.md)\n", "](actions/README.md)\n- [Title of sylow-existence](sylow-existence.md)\n"))
        self.assertIn("blueprint/roadmap/Algebra/groups/README.md: - [Title of sylow-existence](sylow-existence.md)\n"
                      "      fallback insertion on a non-simple folder page", out)

    def test_a_folder_page_the_sync_cannot_list_on(self) -> None:
        self.write("blueprint/roadmap/Algebra/groups/README.md", GROUPS + "\n<div>Groups</div>\n")
        self.refused([planned("sylow-existence")], "cannot be listed")


class Modes(Fixture):
    def test_check_prints_the_plan_with_its_rules_and_writes_nothing(self) -> None:
        before = self.snapshot()
        code, out, err = self.run_importer([planned("sylow-existence")], mode="--check")
        self.assertEqual((code, err), (0, ""))
        self.assertEqual(self.snapshot(), before)
        self.assertIn("blueprint/roadmap/Algebra/groups/sylow-existence.md\n      the planned page of sylow-existence, "
                      "in the existing folder blueprint/roadmap/Algebra/groups", out)
        self.assertIn("blueprint/roadmap/Algebra/groups/README.md: - [Title of sylow-existence](sylow-existence.md)\n"
                      "      lists a new child", out)
        self.assertIn("Nothing written (--check).", out)

    def test_identity_refuses_a_page_no_manifest_can_name(self) -> None:
        self.write("blueprint/roadmap/Algebra/groups/Odd_Name.md", "# Odd\n\nAn odd page.\n")
        self.annotate("Algebra/groups/Odd_Name.md", id="af_" + "e" * 24)
        code, out, err = self.run_identity("blueprint/roadmap/Algebra/groups/Odd_Name.md")
        self.assertEqual((code, out), (1, ""))
        self.assertIn("blueprint/roadmap/Algebra/groups/Odd_Name.md is no page a manifest can name", err)

    def test_identity_prints_what_a_dependency_on_a_page_is_bound_to(self) -> None:
        before = self.snapshot()
        code, out, err = self.run_identity("blueprint/roadmap/Algebra/groups/cosets.md")
        self.assertEqual((code, err), (0, ""))
        self.assertEqual(json.loads(out), {"path": "blueprint/roadmap/Algebra/groups/cosets.md",
                                           "statement_sha256": digest(COSETS),
                                           "annotation_sha256": annotation_digest("Algebra/groups/cosets.md")})
        code, out, err = self.run_identity(str(wiki.ROADMAP / "Algebra/groups/README.md"))
        self.assertEqual((code, out), (1, ""))
        self.assertIn("blueprint/roadmap/Algebra/groups/README.md is a folder page", err)
        self.assertEqual(self.snapshot(), before)

    def test_a_second_apply_of_a_manifest_is_refused(self) -> None:
        self.applied([planned("sylow-existence")])
        self.refused([planned("sylow-existence")], "is already an annotation's", "already maps sylow-existence")


class Transaction(Fixture):
    ROWS = [planned("sylow-existence", page_dir="blueprint/roadmap/Algebra/groups/sylow-theorems"),
            planned("sylow-conjugacy", page_dir="blueprint/roadmap/Algebra/groups/sylow-theorems"),
            planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals"),
            planned("maximal-ideal", page_dir="blueprint/roadmap/Algebra/rings/ideals")]

    def writes(self) -> int:
        path, sha = self.manifest(self.ROWS)
        plan = importer.make_plan(path, sha)
        return len(plan.creates) + len(plan.edits)

    def test_a_failed_write_is_rolled_back_whichever_file_it_fails_on(self) -> None:
        before, writes = self.snapshot(), self.writes()
        self.assertGreater(writes, 5)
        for call in range(1, writes + 1):
            with self.subTest(call=call), self.failing(call):
                code, out, err = self.run_importer(self.ROWS)
                self.assertEqual(code, 1, out)
                self.assertIn("error: the write failed (OSError: [Errno 28] No space left on device); every change "
                              "was undone, so the tree is as it was", err)
                self.assertEqual(self.snapshot(), before)
        # Unhindered, the same run writes the change, and an edited file keeps its mode.
        readme = wiki.ROADMAP / "Algebra/groups/README.md"
        readme.chmod(0o640)
        self.applied(self.ROWS)
        self.assertEqual(stat.S_IMODE(readme.stat().st_mode), 0o640)
        self.assertTrue((wiki.ROADMAP / "Algebra/rings/ideals/maximal-ideal.md").is_file())

    def test_a_change_that_cannot_be_undone_is_named(self) -> None:
        real = os.rmdir

        def stuck(path, *args, **kwargs) -> None:
            # The run's own folders, which undo removes in their parents; any other folder goes as it would.
            if os.fspath(path) in ("ideals", "rings"):
                raise OSError(16, "Device or resource busy")
            real(path, *args, **kwargs)

        with self.failing(self.writes()), patch.object(os, "rmdir", stuck):
            code, out, err = self.run_importer(self.ROWS)
        self.assertEqual(code, 1, out)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/rings/ideals ([Errno 16]", err)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/rings ([Errno 16]", err)
        self.assertIn("the tree is NOT as it was: restore it with `git checkout -- . && git clean -fd`", err)
        # Every file was put back; only the folders that could not be removed are left, and they are empty.
        left = sorted(path.relative_to(wiki.ROADMAP).as_posix() for path in (wiki.ROADMAP / "Algebra/rings").rglob("*"))
        self.assertEqual(left, ["Algebra/rings/ideals"])
        self.assertEqual(self.page("Algebra/groups/README.md"), GROUPS)


class SymbolicLinks(Fixture):
    """No path is read or written through a symbolic link: a link, dangling or not, on a path the importer reads or
    writes is refused, and stays as it was."""

    def link(self, relative: str, target: str | Path) -> Path:
        path = self.tmp / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        os.symlink(target, path)
        return path

    def moved(self, relative: str) -> tuple[Path, Path]:
        """A file or folder of the fixture moved out of the wiki, with a link to it in its place."""
        path, elsewhere = self.tmp / relative, self.tmp / "elsewhere" / relative
        elsewhere.parent.mkdir(parents=True, exist_ok=True)
        path.rename(elsewhere)
        os.symlink(elsewhere, path)
        return path, elsewhere

    def refused_with_link(self, rows: list, link: Path, *messages: str) -> None:
        """Refused by --check and by --apply, which write nothing and leave the link as it was."""
        target = os.readlink(link)
        for mode in ("--check", "--apply"):
            with self.subTest(mode=mode):
                self.refused(rows, *messages, mode=mode)
                self.assertEqual(os.readlink(link), target)

    def test_a_dangling_link_at_a_path_it_creates(self) -> None:
        link = self.link("blueprint/roadmap/Algebra/groups/sylow-existence.md", "nowhere.md")
        self.refused_with_link([planned("sylow-existence")], link,
                               "manifest line 1 (sylow-existence): its stem sylow-existence collides with the symbolic "
                               "link blueprint/roadmap/Algebra/groups/sylow-existence.md")
        link.unlink()
        mapped = self.link("scripts/mathgraph-map.jsonl", "nowhere.jsonl")
        self.refused_with_link([planned("sylow-existence")], mapped, "scripts/mathgraph-map.jsonl is a symbolic link; "
                               "the importer reads and writes no path through one")

    def test_a_link_to_a_file_at_a_path_it_edits(self) -> None:
        for relative, message in (
                ("blueprint/roadmap/Algebra/groups/README.md", "manifest line 1 (sylow-existence): "
                 "blueprint/roadmap/Algebra/groups/README.md is a symbolic link; the importer reads and writes no "
                 "path through one"),
                ("blueprint/links/Algebra.jsonl", "blueprint/links/Algebra.jsonl is a symbolic link")):
            with self.subTest(path=relative):
                link, elsewhere = self.moved(relative)
                bytes_before = elsewhere.read_bytes()
                self.refused_with_link([planned("sylow-existence")], link, message)
                self.assertEqual(elsewhere.read_bytes(), bytes_before)
                link.unlink()
                elsewhere.rename(link)

    def test_a_link_on_the_way_to_a_path_it_writes(self) -> None:
        link, _ = self.moved("blueprint/roadmap/Algebra/groups/actions")
        self.refused_with_link([planned("orbit-counting", page_dir="blueprint/roadmap/Algebra/groups/actions")], link,
                               "manifest line 1 (orbit-counting): blueprint/roadmap/Algebra/groups/actions/README.md: "
                               "its folder blueprint/roadmap/Algebra/groups/actions is a symbolic link")
        link.unlink()
        links, _ = self.moved("blueprint/links")
        self.refused_with_link([planned("sylow-existence")], links, "blueprint/links is a symbolic link")

    def test_a_linked_page_is_no_dependency_and_has_no_identity(self) -> None:
        dependency = on_page("Algebra/groups/cosets.md", COSETS)
        link, elsewhere = self.moved("blueprint/roadmap/Algebra/groups/cosets.md")
        self.refused_with_link([planned("double-cosets", depends=[dependency])], link,
                               "manifest line 1 (double-cosets): depends/0: blueprint/roadmap/Algebra/groups/cosets.md "
                               "is a symbolic link; the importer reads and writes no path through one")
        for argument in ("blueprint/roadmap/Algebra/groups/cosets.md", str(link)):
            code, out, err = self.run_identity(argument)
            self.assertEqual((code, out), (1, ""))
            self.assertIn("error: blueprint/roadmap/Algebra/groups/cosets.md is a symbolic link", err)
        self.assertEqual(os.readlink(link), str(elsewhere))

    def test_a_dangling_link_at_a_new_folder_path(self) -> None:
        field = self.link("blueprint/roadmap/Algebra/rings", "nowhere")
        self.refused_with_link([planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings")], field,
                               "manifest line 1 (prime-ideal): blueprint/roadmap/Algebra/rings/README.md: its folder "
                               "blueprint/roadmap/Algebra/rings is a symbolic link")
        field.unlink()
        page = self.link("blueprint/roadmap/Algebra/rings.md", "nowhere.md")
        self.refused_with_link([planned("prime-ideal", page_dir="blueprint/roadmap/Algebra/rings")], page,
                               "blueprint/roadmap/Algebra/rings/ cannot be made a folder: "
                               "blueprint/roadmap/Algebra/rings.md is there, a symbolic link")
        topic = self.link("blueprint/roadmap/Algebra/groups/sylow-theorems", "nowhere")
        self.refused_with_link([planned(key, page_dir="blueprint/roadmap/Algebra/groups/sylow-theorems")
                                for key in ("sylow-existence", "sylow-conjugacy")], topic,
                               "blueprint/roadmap/Algebra/groups/sylow-theorems/README.md: its folder "
                               "blueprint/roadmap/Algebra/groups/sylow-theorems is a symbolic link")

    def test_a_link_that_turns_up_after_the_check_is_refused_before_writing(self) -> None:
        path, sha = self.manifest([planned("sylow-existence")])
        plan = importer.make_plan(path, sha)
        page = self.link("blueprint/roadmap/Algebra/groups/sylow-existence.md", "nowhere.md")
        readme, _ = self.moved("blueprint/roadmap/Algebra/groups/README.md")
        before = self.snapshot()
        with self.assertRaises(importer.Refused) as refused:
            importer.apply(plan)
        for link in (page, readme):
            self.assertIn(f"{link.relative_to(self.tmp).as_posix()} is a symbolic link; the importer reads and writes "
                          "no path through one", refused.exception.problems)
        self.assertEqual(refused.exception.outcome, "nothing written")
        self.assertEqual(self.snapshot(), before)

    def test_a_link_that_turns_up_while_writing_is_left_as_it_is(self) -> None:
        mapped, real = importer.MAP, os.link

        def before_its_turn(source, target, *args, **kwargs):
            result = real(source, target, *args, **kwargs)
            if not os.path.lexists(mapped):
                os.symlink("nowhere.jsonl", mapped)
            return result

        def at_its_link(source, target, *args, **kwargs):
            if os.fspath(target) == mapped.name:
                os.symlink("nowhere.jsonl", mapped)
            return real(source, target, *args, **kwargs)

        for hook, error in ((before_its_turn, "SymlinkFound: scripts/mathgraph-map.jsonl is a symbolic link"),
                            (at_its_link, "FileExistsError: [Errno 17] File exists")):
            with self.subTest(hook=hook.__name__):
                before = self.snapshot()
                with patch.object(os, "link", hook):
                    code, out, err = self.run_importer(Transaction.ROWS)
                self.assertEqual(code, 1, out)
                self.assertIn(error, err)
                self.assertIn("every change was undone, so the tree is as it was", err)
                self.assertEqual(self.snapshot(),
                                 {**before, "scripts/mathgraph-map.jsonl": ("symlink", "nowhere.jsonl")})
                mapped.unlink()


class Manifests(Fixture):
    """A manifest that is itself a symbolic link is refused before any byte of it is read, and so is one in the
    repository below a link; the folders above a manifest outside the repository are not checked, its digest binding
    its content."""

    def outside(self) -> Path:
        folder = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, folder)
        return folder

    def run_manifest(self, path: Path | str, sha: str, mode: str = "--apply") -> tuple[int, str, str, list[str]]:
        """Run the importer on the manifest at *path*, with every path it opens, through os.open or open."""
        opened, real_open, real_builtin = [], os.open, open

        def spy_open(file, flags, *args, **kwargs):
            opened.append(os.fspath(file))
            return real_open(file, flags, *args, **kwargs)

        def spy_builtin(file, *args, **kwargs):
            if isinstance(file, (str, os.PathLike)):
                opened.append(os.fspath(file))
            return real_builtin(file, *args, **kwargs)

        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err), patch.object(os, "open", spy_open), \
                patch("builtins.open", spy_builtin):
            code = importer.main([mode, "--manifest", str(path), "--manifest-sha256", sha])
        return code, out.getvalue(), err.getvalue(), opened

    def test_a_manifest_that_is_a_link_is_refused_unread(self) -> None:
        text = json.dumps(planned("sylow-existence")) + "\n"
        for place in (self.outside(), self.tmp):
            with self.subTest(inside=place == self.tmp):
                real = self.outside() / "real.jsonl"
                real.write_text(text)
                link = place / "linked.jsonl"
                os.symlink(real, link)
                before = self.snapshot()
                code, out, err, opened = self.run_manifest(link, digest(text))
                self.assertEqual((code, out), (1, ""))
                self.assertIn(f"{link.relative_to(self.tmp).as_posix() if place == self.tmp else link} is a symbolic "
                              "link", err)
                self.assertIn("nothing written", err)
                self.assertNotIn(str(real), opened)
                self.assertEqual(self.snapshot(), before)
                self.assertEqual(os.readlink(link), str(real))

    def test_a_manifest_in_the_repository_below_a_link_is_refused(self) -> None:
        text = json.dumps(planned("sylow-existence")) + "\n"
        real = self.tmp / "manifests"
        real.mkdir()
        (real / "manifest.jsonl").write_text(text)
        os.symlink(real, self.tmp / "linked")
        before = self.snapshot()
        code, out, err, opened = self.run_manifest(self.tmp / "linked" / "manifest.jsonl", digest(text))
        self.assertEqual((code, out), (1, ""))
        self.assertIn("error: linked/manifest.jsonl: its folder linked is a symbolic link", err)
        self.assertNotIn(str(self.tmp / "linked" / "manifest.jsonl"), opened)
        self.assertEqual(self.snapshot(), before)

    def test_the_manifest_checked_is_the_manifest_opened(self) -> None:
        # The path given goes through a link and back up: made absolute without resolving links, it names the manifest
        # in the repository, while the system, resolving it, would reach the folder above the link's target.
        text, other = (json.dumps(planned(key)) + "\n" for key in ("sylow-existence", "sylow-conjugacy"))
        outside = self.outside()
        (outside / "folder").mkdir()
        (outside / "manifest.jsonl").write_text(other)
        os.symlink(outside / "folder", self.tmp / "linked")
        manifest = self.tmp / "manifest.jsonl"
        manifest.write_text(text)
        argument = f"{self.tmp}/linked/../manifest.jsonl"
        checked, real = [], importer.symlink_problem

        def spy(path: Path) -> str | None:
            checked.append(path)
            return real(path)

        with patch.object(importer, "symlink_problem", spy):
            code, out, err, opened = self.run_manifest(argument, digest(text))
        self.assertEqual((code, err), (0, ""))
        self.assertEqual([path for path in checked if path.name == "manifest.jsonl"], [manifest])
        self.assertEqual([path for path in opened if path.endswith("manifest.jsonl")], [str(manifest)])
        self.assertNotIn(str(outside / "manifest.jsonl"), opened)
        self.assertIn(f"Manifest {manifest}: SHA-256 {digest(text)}", out)
        self.assertTrue((wiki.ROADMAP / "Algebra/groups/sylow-existence.md").is_file())
        self.assertFalse((wiki.ROADMAP / "Algebra/groups/sylow-conjugacy.md").exists())

    def test_a_manifest_outside_the_repository_below_a_link_is_bound_by_its_digest(self) -> None:
        text = json.dumps(planned("sylow-existence")) + "\n"
        outside = self.outside()
        (outside / "real").mkdir()
        (outside / "real" / "manifest.jsonl").write_text(text)
        os.symlink(outside / "real", outside / "linked")
        path = outside / "linked" / "manifest.jsonl"
        before = self.snapshot()
        code, out, err, _ = self.run_manifest(path, digest(text + "\n"))
        self.assertEqual(code, 1, out)
        self.assertIn(f"not the reviewed {digest(text + chr(10))}", err)
        self.assertEqual(self.snapshot(), before)
        code, out, err, _ = self.run_manifest(path, digest(text))
        self.assertEqual((code, err), (0, ""))
        self.assertTrue((wiki.ROADMAP / "Algebra/groups/sylow-existence.md").is_file())


class Recovery(Fixture):
    """A rollback undoes each step only in the folder it was taken in, reached from the repository root without
    following a link, and only on the file or folder the run made; anything else found there is left as it is, and
    the rollback says the tree is not as it was, naming each path."""

    def interrupted(self, mutate) -> str:
        """Apply Transaction.ROWS with its last write failing, *mutate* changing the tree before the rollback; stderr."""
        path, sha = self.manifest(Transaction.ROWS)
        plan = importer.make_plan(path, sha)
        real = importer.undo

        def undo(plan, steps):
            mutate()
            return real(plan, steps)

        with self.failing(len(plan.creates) + len(plan.edits)), patch.object(importer, "undo", undo):
            code, out, err = self.run_importer(Transaction.ROWS)
        self.assertEqual(code, 1, out)
        self.assertIn("error: the write failed (OSError: [Errno 28] No space left on device)", err)
        self.assertIn("the tree is NOT as it was: restore it with `git checkout -- . && git clean -fd`", err)
        return err

    def moved(self, path: Path) -> Path:
        elsewhere = self.tmp / "elsewhere" / path.name
        elsewhere.parent.mkdir(parents=True, exist_ok=True)
        path.rename(elsewhere)
        return elsewhere

    def test_a_file_in_the_place_of_one_the_run_made_is_left(self) -> None:
        page = wiki.ROADMAP / "Algebra/groups/sylow-theorems/sylow-existence.md"

        def mutate() -> None:
            other = page.with_name("other.md")
            other.write_text("# Another page\n")
            other.replace(page)

        err = self.interrupted(mutate)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/groups/sylow-theorems/"
                      "sylow-existence.md (it is not the file this run made, so it is left as it is)", err)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/groups/sylow-theorems ([Errno 39]",
                      err)
        self.assertEqual(page.read_text(), "# Another page\n")
        self.assertEqual(sorted(path.name for path in page.parent.iterdir()), ["sylow-existence.md"])
        self.assertEqual(self.page("Algebra/groups/README.md"), GROUPS)

    def test_an_edited_file_that_became_a_link_is_not_restored(self) -> None:
        readme, kept = wiki.ROADMAP / "Algebra/groups/README.md", {}

        def mutate() -> None:
            kept["bytes"], kept["at"] = readme.read_bytes(), self.moved(readme)
            os.symlink(kept["at"], readme)

        err = self.interrupted(mutate)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/groups/README.md (it is not the "
                      "file this run wrote, so it is not restored)", err)
        self.assertEqual(os.readlink(readme), str(kept["at"]))
        self.assertEqual(kept["at"].read_bytes(), kept["bytes"])
        self.assertFalse((wiki.ROADMAP / "Algebra/groups/sylow-theorems").exists())

    def test_a_folder_that_became_a_link_is_not_followed(self) -> None:
        ideals, kept = wiki.ROADMAP / "Algebra/rings/ideals", {}

        def mutate() -> None:
            kept["at"] = self.moved(ideals)
            kept["files"] = {path.name: path.read_bytes() for path in kept["at"].iterdir()}
            os.symlink(kept["at"], ideals)

        err = self.interrupted(mutate)
        for name in ("README.md", "prime-ideal.md", "maximal-ideal.md"):
            self.assertIn(f"error: could not undo the change to blueprint/roadmap/Algebra/rings/ideals/{name} "
                          "(blueprint/roadmap/Algebra/rings/ideals is a symbolic link; nothing is undone through it)",
                          err)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/rings/ideals (it is not the folder "
                      "this run made, so it is left as it is)", err)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/rings ([Errno 39]", err)
        self.assertEqual(os.readlink(ideals), str(kept["at"]))
        self.assertEqual({path.name: path.read_bytes() for path in kept["at"].iterdir()}, kept["files"])
        self.assertEqual(self.page("Algebra/groups/README.md"), GROUPS)

    def test_a_folder_in_the_place_of_one_the_run_made_is_left(self) -> None:
        topic, kept = wiki.ROADMAP / "Algebra/groups/sylow-theorems", {}

        def mutate() -> None:
            kept["at"] = self.moved(topic)
            kept["files"] = {path.name: path.read_bytes() for path in kept["at"].iterdir()}
            topic.mkdir()

        err = self.interrupted(mutate)
        for name in ("README.md", "sylow-existence.md", "sylow-conjugacy.md"):
            self.assertIn(f"error: could not undo the change to blueprint/roadmap/Algebra/groups/sylow-theorems/{name} "
                          "(its folder blueprint/roadmap/Algebra/groups/sylow-theorems is not the one the change was "
                          "written in, so nothing is undone in it)", err)
        self.assertIn("error: could not undo the change to blueprint/roadmap/Algebra/groups/sylow-theorems (it is not "
                      "the folder this run made, so it is left as it is)", err)
        self.assertEqual(list(topic.iterdir()), [])
        self.assertEqual({path.name: path.read_bytes() for path in kept["at"].iterdir()}, kept["files"])
        self.assertEqual(self.page("Algebra/groups/README.md"), GROUPS)


class TemporaryFiles(Fixture):
    """The temporary file beside a file the importer writes is a step of the transaction: a rollback removes it if it
    is left, and only if it is the one the run made."""

    def interrupted(self, before_undo=None, **hooks) -> tuple[int, str, str]:
        """Apply Transaction.ROWS with os.open, os.link, os.unlink or os.replace replaced, while the change is written,
        by the function *hooks* give it, called with the real one; *before_undo* runs just before the rollback, which
        runs unhindered."""
        real = {name: getattr(os, name) for name in ("open", "link", "unlink", "replace")}
        undoing = []

        def hindered(name):
            def call(*args, **kwargs):
                if name not in hooks or undoing:
                    return real[name](*args, **kwargs)
                return hooks[name](real[name], *args, **kwargs)
            return call

        real_undo = importer.undo

        def undo(plan, steps):
            undoing.append(True)
            if before_undo:
                before_undo()
            return real_undo(plan, steps)

        with patch.multiple(os, **{name: hindered(name) for name in real}), patch.object(importer, "undo", undo):
            return self.run_importer(Transaction.ROWS)

    def temporary(self, relative: str) -> Path:
        """The temporary file the importer writes beside *relative* before putting it in place."""
        path = self.tmp / relative
        return path.with_name(f".{path.name}.{os.getpid()}.part")

    def undone(self, code: int, out: str, err: str, error: str, before: dict) -> None:
        self.assertEqual(code, 1, out)
        self.assertIn(f"error: the write failed ({error}); every change was undone, so the tree is as it was", err)
        self.assertEqual(self.snapshot(), before)

    def test_a_temporary_file_that_an_interrupted_cleanup_leaves_is_removed(self) -> None:
        # The cleanup after os.link: interrupted before it unlinks the temporary file, and after.
        def before(real, name, *args, **kwargs):
            if os.fspath(name).endswith(".part"):
                raise KeyboardInterrupt
            return real(name, *args, **kwargs)

        def after(real, name, *args, **kwargs):
            real(name, *args, **kwargs)
            if os.fspath(name).endswith(".part"):
                raise KeyboardInterrupt

        for hook in (before, after):
            with self.subTest(hook=hook.__name__):
                snapshot = self.snapshot()
                self.undone(*self.interrupted(unlink=hook), "KeyboardInterrupt: ", snapshot)

    def test_a_temporary_file_beside_an_edited_file_is_removed(self) -> None:
        # os.replace fails and leaves the temporary file, its cleanup interrupted; and os.replace moves it into place,
        # interrupted just after: the edited file gets its bytes back, and no temporary file is left.
        replaced = []

        def failing(real, source, target, *args, **kwargs):
            replaced.append(target)
            raise OSError(28, "No space left on device")

        def cleanup(real, name, *args, **kwargs):
            if replaced and os.fspath(name).endswith(".part"):
                raise KeyboardInterrupt
            return real(name, *args, **kwargs)

        def moved(real, source, target, *args, **kwargs):
            real(source, target, *args, **kwargs)
            raise KeyboardInterrupt

        for name, hooks, error in (("failed", {"replace": failing, "unlink": cleanup},
                                    "OSError: [Errno 28] No space left on device"),
                                   ("moved", {"replace": moved}, "KeyboardInterrupt: ")):
            with self.subTest(name):
                snapshot = self.snapshot()
                self.undone(*self.interrupted(**hooks), error, snapshot)

    def test_a_temporary_file_that_is_not_the_runs_is_left_and_reported(self) -> None:
        # The map's temporary file, left by an interrupted cleanup, then replaced by another file before the rollback.
        temporary, before = self.temporary("scripts/mathgraph-map.jsonl"), self.snapshot()

        def cleanup(real, name, *args, **kwargs):
            if os.fspath(name) == temporary.name:
                raise KeyboardInterrupt
            return real(name, *args, **kwargs)

        def replace() -> None:
            other = temporary.with_name("other")
            other.write_text("another file\n")
            other.replace(temporary)

        code, out, err = self.interrupted(before_undo=replace, unlink=cleanup)
        self.assertEqual(code, 1, out)
        relative = temporary.relative_to(self.tmp).as_posix()
        self.assertIn(f"error: could not undo the change to {relative} (it is not the temporary file this run made, so "
                      "it is left as it is)", err)
        self.assertIn("the tree is NOT as it was: restore it with `git checkout -- . && git clean -fd`", err)
        self.assertEqual(self.snapshot(), {**before, relative: b"another file\n"})

    def test_a_temporary_file_whose_record_was_interrupted_is_left_and_reported(self) -> None:
        # os.open makes the map's temporary file, and the run is interrupted before it records the file's identity.
        temporary, before = self.temporary("scripts/mathgraph-map.jsonl"), self.snapshot()

        def interrupted(real, name, *args, **kwargs):
            descriptor = real(name, *args, **kwargs)
            if os.fspath(name) == temporary.name:
                os.close(descriptor)
                raise KeyboardInterrupt
            return descriptor

        code, out, err = self.interrupted(open=interrupted)
        self.assertEqual(code, 1, out)
        relative = temporary.relative_to(self.tmp).as_posix()
        self.assertIn(f"error: could not undo the change to {relative} (this run did not record it, its creation "
                      "interrupted before the record, so it is left as it is)", err)
        self.assertEqual(self.snapshot(), {**before, relative: b""})


class MkdirWindow(Fixture):
    """An interruption in the instant after the importer's mkdir and before it records the new folder: the folder is
    taken for the run's own under the exclusive-worktree assumption, and removed only if it is empty."""

    FOLDER = "blueprint/roadmap/Algebra/groups/sylow-theorems"

    def interrupted_after_mkdir(self, before_undo=None) -> tuple[int, str, str]:
        """Apply Transaction.ROWS with KeyboardInterrupt right after the importer's first mkdir succeeds, which makes
        sylow-theorems/; *before_undo* runs just before the rollback."""
        real_mkdir, real_undo, calls = os.mkdir, importer.undo, []

        def mkdir(path, *args, dir_fd=None, **kwargs):
            real_mkdir(path, *args, dir_fd=dir_fd, **kwargs)
            # The importer makes folders in their parent's descriptor; tempfile's own folders go as they would.
            if dir_fd is not None and not calls:
                calls.append(path)
                raise KeyboardInterrupt

        def undo(plan, steps):
            self.assertEqual(steps[-1][:2], ["folder", self.tmp / self.FOLDER])
            self.assertIsNone(steps[-1][3])
            if before_undo:
                before_undo()
            return real_undo(plan, steps)

        with patch.object(os, "mkdir", mkdir), patch.object(importer, "undo", undo):
            code, out, err = self.run_importer(Transaction.ROWS)
        self.assertEqual(calls, ["sylow-theorems"])
        return code, out, err

    def test_an_empty_folder_made_in_the_window_is_removed_and_named(self) -> None:
        before = self.snapshot()
        code, out, err = self.interrupted_after_mkdir()
        self.assertEqual(code, 1, out)
        self.assertIn("error: the write failed (KeyboardInterrupt: ); every change was undone, so the tree is as it was",
                      err)
        self.assertIn(f"error: {self.FOLDER} was removed as the folder this run made, under the exclusive-worktree "
                      "assumption: it appeared in the instant between the importer's mkdir and its record, and it was "
                      "empty, in the verified parent", err)
        self.assertEqual(self.snapshot(), before)

    def test_a_folder_made_in_the_window_that_holds_anything_is_left_and_reported(self) -> None:
        before = self.snapshot()
        stray = self.tmp / self.FOLDER / "stray.md"
        code, out, err = self.interrupted_after_mkdir(lambda: stray.write_text("# Stray\n"))
        self.assertEqual(code, 1, out)
        self.assertIn(f"error: could not undo the change to {self.FOLDER} (this run did not record it, its mkdir "
                      "interrupted before the record, and it is not empty, so it is left as it is)", err)
        self.assertIn("the tree is NOT as it was: restore it with `git checkout -- . && git clean -fd`", err)
        self.assertNotIn("exclusive-worktree assumption", err)
        self.assertEqual(self.snapshot(), {**before, self.FOLDER: None, f"{self.FOLDER}/stray.md": b"# Stray\n"})


class MapFixture(Fixture):
    """The fixture with the map's helpers: writing it, checking it, and committing the fixture as a base."""

    def write_map(self, *lines: str, end: str = "\n") -> None:
        self.write("scripts/mathgraph-map.jsonl", "\n".join(lines) + end)

    def check_map(self, *argv: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = importer.main(["--check-map", *argv])
        return code, out.getvalue(), err.getvalue()

    def map_refused(self, message: str, *argv: str) -> str:
        before = self.snapshot()
        code, out, err = self.check_map(*argv)
        self.assertEqual((code, out), (1, ""), err)
        self.assertIn(message, err)
        self.assertIn("nothing written", err)
        self.assertEqual(self.snapshot(), before)
        return err

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.tmp), "-c", "user.name=Test", "-c", "user.email=test@example.com",
                               "-c", "commit.gpgsign=false", *args], capture_output=True, text=True,
                              check=True).stdout.strip()

    def commit(self) -> str:
        """The fixture as a commit of a new repository, its map as it stands; that commit."""
        if not (self.tmp / ".git").exists():
            self.git("init", "-q")
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "base")
        return self.git("rev-parse", "HEAD")


class Map(MapFixture):
    """Every line of the map is as the importer writes it, and on a pull request the map only grows: the importer and
    --check-map refuse a map with any other line, naming it, and --check-map --base a map whose base lines changed."""

    def test_a_map_the_importer_writes_passes(self) -> None:
        self.applied([planned("sylow-existence", pending=[missing("p-group", "proof", "not-imported")], not_ready=True,
                              prose_missing="It uses p-groups."), planned("sylow-conjugacy")])
        code, out, err = self.check_map()
        self.assertEqual((code, err), (0, ""))
        self.assertIn("scripts/mathgraph-map.jsonl: 2 valid lines", out)
        lines = importer.MAP.read_text().splitlines()
        self.assertEqual(lines, [importer.map_line(row) for row in self.mapped()])
        # The next import appends to it.
        self.applied([planned("lagrange-corollary")])
        self.assertEqual(importer.MAP.read_text().splitlines()[:2], lines)
        self.assertEqual(self.check_map()[0], 0)

    def test_each_kind_of_wrong_line_is_refused_by_name(self) -> None:
        alpha, beta = map_row("alpha"), map_row("beta")
        without = {name: value for name, value in alpha.items() if name != "edges_sha256"}
        swapped = {"node": alpha["node"], **{name: value for name, value in alpha.items() if name != "node"}}
        line = "scripts/mathgraph-map.jsonl line"
        cases = {
            "missing field": ([json.dumps(without, ensure_ascii=False)], f"{line} 1: 'edges_sha256' is a required property"),
            "extra field": ([json.dumps({**alpha, "note": "x"}, ensure_ascii=False)],
                            f"{line} 1: Additional properties are not allowed ('note' was unexpected)"),
            "bad digest": ([importer.map_line({**alpha, "statement_sha256": "abc"})],
                           f"{line} 1: statement_sha256: 'abc' does not match"),
            "node mismatch": ([importer.map_line({**alpha, "node": importer.mathgraph_id("other")})],
                              f"{line} 1: node {importer.mathgraph_id('other')} is not mathgraph's id of the result alpha"),
            "duplicate key": ([importer.map_line(alpha), importer.map_line({**alpha, "page": beta["page"]})],
                              f"{line} 2: its key alpha is line 1's too"),
            "duplicate page": ([importer.map_line(alpha), importer.map_line({**beta, "page": alpha["page"]})],
                               f"{line} 2: its page {alpha['page']} is line 1's too"),
            "compact separators": ([json.dumps(alpha, ensure_ascii=False, separators=(",", ":"))],
                                   f"{line} 1: it is not written as the importer writes its row"),
            "fields out of order": ([json.dumps(swapped, ensure_ascii=False)],
                                    f"{line} 1: it is not written as the importer writes its row"),
            "a value ending in a line break": ([importer.map_line({**alpha, "revision": REVISION + "\n"})],
                                               f"{line} 1: revision: '{REVISION}\\n' does not match"),
            "a line that is not JSON": (["{not json"], f"{line} 1: not a JSON object"),
            "no final line break": ([importer.map_line(alpha)], f"{line} 1: the map does not end in a line break"),
            "its own key pending": ([importer.map_line({**alpha, "pending": [missing("p-group"), missing("alpha")]})],
                                    f"{line} 1: pending/1: alpha is the row itself"),
            "a key pending twice": ([importer.map_line({**alpha, "pending": [missing("p-group"),
                                                                             missing("p-group", "proof")]})],
                                    f"{line} 1: pending/1: p-group is pending twice"),
            **{f"a page named {name}": ([importer.map_line({**alpha, "page": f"blueprint/roadmap/Algebra/groups/{name}"})],
                                        f"{line} 1: page: its file name {name} is a name reserved for folder pages and "
                                        "parts") for name in ("part-02.md", "index.md", "readme.md")},
            "a page in a subject folder": ([importer.map_line({**alpha, "page": "blueprint/roadmap/Algebra/alpha.md"})],
                                           f"{line} 1: page: its folder blueprint/roadmap/Algebra is no folder a "
                                           "manifest's page_dir can name"),
        }
        for name, (lines, message) in cases.items():
            with self.subTest(name):
                self.write_map(*lines, end="" if name == "no final line break" else "\n")
                self.refused([planned("sylow-existence")], message, mode="--check")
                self.refused([planned("sylow-existence")], message)
                self.map_refused(message)

    def test_a_pending_key_is_checked_against_earlier_lines_only(self) -> None:
        # A line that pends the key of an earlier line is one the importer could not have written: it refuses a pending
        # key the map holds. The message names both lines.
        imported = importer.map_line(map_row("p-group", pending=[]))
        waiting = importer.map_line(map_row("sylow-existence", pending=[missing("p-group")]))
        self.write_map(imported, waiting)
        message = ("scripts/mathgraph-map.jsonl line 2 (sylow-existence): pending/0: p-group is the key of line 1, an "
                   "earlier line, and a row may not list as pending a key the map holds")
        self.map_refused(message)
        for mode in ("--check", "--apply"):
            with self.subTest(mode=mode):
                self.refused([planned("sylow-conjugacy")], message, mode=mode)
        # The other order is the map's history: an earlier line keeps its pending list when that prerequisite is
        # imported later, and a later line is never evidence against it.
        self.write_map(waiting, imported)
        code, out, err = self.check_map()
        self.assertEqual((code, err), (0, ""), err)
        before = importer.MAP.read_bytes()
        self.applied([planned("sylow-conjugacy")])
        self.assertTrue(importer.MAP.read_bytes().startswith(before))

    def test_a_row_and_a_line_of_the_map_share_their_pending_rules(self) -> None:
        # One function states the rules a pending list is held to on its own, for a manifest row and a line alike.
        def verdict(key: str, pending: list) -> list:
            return [(0, "the shared verdict")] if pending else []

        self.write_map(importer.map_line(map_row("alpha")))
        with patch.object(importer, "pending_problems", verdict):
            self.map_refused("scripts/mathgraph-map.jsonl line 1: pending/0: the shared verdict")
            importer.MAP.unlink()
            self.refused([planned("b", pending=[missing("p-group")], not_ready=True, prose_missing="It uses p-groups.")],
                         "manifest line 1 (b): pending/0: the shared verdict")

    def test_a_head_that_drops_the_final_line_break_is_named(self) -> None:
        alpha, beta = (importer.map_line(map_row(key, pending=[])) for key in ("alpha", "beta"))
        self.write_map(alpha, beta)
        base = self.commit()
        self.write_map(alpha, beta, end="")
        self.map_refused(f"scripts/mathgraph-map.jsonl line 2: line 2 no longer ends in a line break, as it does in the "
                         f"map at {base}", "--base", base)

    def test_the_map_a_change_would_write_is_checked_too(self) -> None:
        # A line of the map holds the page that a new row would write, which no longer exists: two lines would have it.
        self.write_map(importer.map_line(map_row("old-result", page="blueprint/roadmap/Algebra/groups/sylow-existence.md")))
        self.refused([planned("sylow-existence")], "the map the change would write is refused: scripts/mathgraph-map.jsonl "
                     "line 2: its page blueprint/roadmap/Algebra/groups/sylow-existence.md is line 1's too")

    def test_an_older_line_keeps_its_pending_prerequisite_once_that_is_imported(self) -> None:
        # Only an incoming row is refused for a pending key the map holds: a line written before its pending
        # prerequisite was imported stays as written, the map only growing, and so does its page.
        self.applied([planned("sylow-existence", pending=[missing("p-group")], not_ready=True,
                              prose_missing="It uses p-groups.")])
        first, page, base = importer.MAP.read_bytes(), self.page("Algebra/groups/sylow-existence.md"), self.commit()
        self.applied([planned("p-group")])
        self.assertTrue(importer.MAP.read_bytes().startswith(first))
        self.assertEqual([row["pending"] for row in self.mapped()], [[missing("p-group")], []])
        self.assertEqual(self.page("Algebra/groups/sylow-existence.md"), page)
        for argv in ((), ("--base", base)):
            with self.subTest(argv=argv):
                code, out, err = self.check_map(*argv)
                self.assertEqual((code, err), (0, ""))
        self.assertIn("the 1 lines of the map at", self.check_map("--base", base)[1])

    def test_the_map_only_grows_from_the_base(self) -> None:
        rule = "the map only grows: lines are appended to it, never edited, removed or moved"
        empty = self.commit()
        # The base has no map, and the change imports two results, as the first content PR does: the map is valid and
        # its lines are appended, each recording a page the change adds.
        self.applied([planned("alpha"), planned("beta", sketch="It follows.", pending=[missing("p-group")],
                                                    not_ready=True, prose_missing="It uses p-groups.")])
        code, out, err = self.check_map("--base", empty)
        self.assertEqual((code, err), (0, ""))
        self.assertIn(f"the 0 lines of the map at {empty} are its first, unchanged, and 2 are appended, each recording "
                      "a page this change adds", out)
        base = self.commit()
        # Lines appended by a later import.
        self.applied([planned("gamma")])
        code, out, err = self.check_map("--base", base)
        self.assertEqual((code, err), (0, ""))
        self.assertIn(f"the 2 lines of the map at {base} are its first, unchanged, and 1 are appended", out)
        alpha, beta, gamma = importer.MAP.read_text().splitlines()
        edited = importer.map_line({**json.loads(beta), "statement_sha256": digest("another statement")})
        for name, lines, message in (
                ("edited", (alpha, edited, gamma), f"line 2: not line 2 of the map at {base}: that line is edited or "
                                                   f"removed; {rule}"),
                ("removed", (alpha,), f"line 2: line 2 of the map at {base} is gone; {rule}"),
                ("reordered", (beta, alpha), f"line 1: not line 1 of the map at {base}: that line is now line 2; {rule}"),
                ("invalid line appended", (alpha, beta, gamma.replace('"gamma"', '"Gamma"', 1)),
                 "scripts/mathgraph-map.jsonl line 3: key: 'Gamma' does not match"),
                ("base key repeated", (alpha, beta, importer.map_line(map_row("alpha", page="blueprint/roadmap/Algebra/"
                                                                              "groups/other.md"))),
                 "scripts/mathgraph-map.jsonl line 3: its key alpha is line 1's too")):
            with self.subTest(name):
                self.write_map(*lines)
                self.map_refused(message, "--base", base)
        self.write_map(alpha, beta)
        self.map_refused("--base 'no-such-commit' names no commit of the repository", "--base", "no-such-commit")
        self.map_refused("--base '--all' names no commit of the repository", "--base=--all")


class AppendedLines(MapFixture):
    """With --base, each line appended to the map since that commit records a page the same change adds: the page,
    absent at the commit, has one annotation, with the line's seed, the id that seed gives and the line's pending list,
    and the line's statement and sketch digests are the page's. The lines of the map at the commit are never checked
    against the pages."""

    def where(self, base: str, number: int = 1, key: str = "alpha") -> str:
        return f"scripts/mathgraph-map.jsonl line {number} ({key}), appended since {base}"

    def imported(self) -> tuple[str, dict, Path, str]:
        """The fixture committed, then a result imported with a sketch and a pending prerequisite: the base commit, the
        map's line, the links file and the links file's text."""
        base = self.commit()
        self.applied([planned("alpha", sketch="It follows.", pending=[missing("p-group")], not_ready=True,
                              prose_missing="It uses p-groups.")])
        code, out, err = self.check_map("--base", base)
        self.assertEqual((code, err), (0, ""))
        links = sync.LINKS / "Algebra.jsonl"
        return base, json.loads(importer.MAP.read_text()), links, links.read_text()

    def test_a_line_for_no_page_or_for_a_page_the_base_has(self) -> None:
        base = self.commit()
        self.write_map(importer.map_line(map_row("alpha", pending=[])))
        # Without --base, the lines alone are checked.
        code, out, err = self.check_map()
        self.assertEqual((code, err), (0, ""))
        self.map_refused(f"{self.where(base)}: its page blueprint/roadmap/Algebra/groups/alpha.md is no file in the "
                         "worktree, so this change did not add it", "--base", base)
        self.write_map(importer.map_line(map_row("lagrange", page="blueprint/roadmap/Algebra/groups/lagrange.md",
                                                 pending=[])))
        self.map_refused(f"{self.where(base, key='lagrange')}: its page blueprint/roadmap/Algebra/groups/lagrange.md is "
                         f"in the tree of {base} already, so this change did not add it", "--base", base)

    def test_a_line_whose_digests_seed_or_pending_list_differ_from_its_page(self) -> None:
        base, line, _, _ = self.imported()
        where, other = self.where(base), digest("another statement")
        cases = {
            "statement": ({**line, "statement_sha256": other},
                          f"{where}: statement_sha256 is {other}, but its page's statement, as Autoform reads it, has "
                          f"the SHA-256 {line['statement_sha256']}"),
            "sketch": ({**line, "sketch_sha256": digest("")},
                       f"{where}: sketch_sha256 is {digest('')}, but its page's sketch, as Autoform reads it (the empty "
                       f"string when it has none), has the SHA-256 {line['sketch_sha256']}"),
            "pending": ({**line, "pending": []}, f"{where}: its pending list is not that of its page's annotation, "
                                                 f"{json.dumps([missing('p-group')])}"),
            "revision": ({**line, "revision": "f" * 40}, f"{where}: the seed of its page's annotation is"),
        }
        for name, (row, message) in cases.items():
            with self.subTest(name):
                self.write_map(importer.map_line(row))
                self.map_refused(message, "--base", base)
        # The page's own text, read as Autoform reads it.
        self.write_map(importer.map_line(line))
        page = wiki.ROADMAP / "Algebra/groups/alpha.md"
        text = page.read_text()
        page.write_text(text.replace("The statement of alpha.", "Another statement."))
        self.map_refused(f"{where}: statement_sha256 is {line['statement_sha256']}, but its page's statement",
                         "--base", base)
        page.write_text(text.replace("## Proof sketch\n\nIt follows.\n", "## Proof sketch\n\nIt follows.\n\n## Proof "
                                     "sketch\n\nAgain.\n"))
        self.map_refused(f"{where}: its page has more than one `## Proof sketch` section", "--base", base)
        page.unlink()
        page.symlink_to(self.write("elsewhere.md", text))
        self.map_refused(f"{where}: blueprint/roadmap/Algebra/groups/alpha.md is a symbolic link", "--base", base)

    def test_a_line_whose_page_has_no_matching_annotation(self) -> None:
        base, line, links, text = self.imported()
        where = self.where(base)
        rows = [json.loads(entry) for entry in text.splitlines()]
        mine = next(row for row in rows if row["subject"][0]["uri"].endswith("/alpha.md"))
        other_seed = {**mine["extensions"][sync.OWN]["seed"], "revision": "e" * 40}

        def with_rows(*replaced: dict) -> str:
            return "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in replaced)

        cases = {
            "another seed": (with_rows(*[row if row is not mine else
                                         {**mine, "extensions": {**mine["extensions"],
                                                                 sync.OWN: {**mine["extensions"][sync.OWN],
                                                                            "seed": other_seed}}} for row in rows]),
                             f"{where}: the seed of its page's annotation is {json.dumps(other_seed)}, not the line's "
                             f"{json.dumps(mine['extensions'][sync.OWN]['seed'])}"),
            "another id": (with_rows(*[row if row is not mine else {**mine, "id": "af_" + "0" * 24} for row in rows]),
                           f"{where}: its page's annotation id is \"af_{'0' * 24}\", not {mine['id']}, which the line's "
                           "seed gives"),
            "no annotation": (with_rows(*[row for row in rows if row is not mine]),
                              f"{where}: its page blueprint/roadmap/Algebra/groups/alpha.md has no annotation"),
            "two annotations": (text + with_rows(mine),
                                f"{where}: its page blueprint/roadmap/Algebra/groups/alpha.md has more than one "
                                "annotation row"),
        }
        for name, (written, message) in cases.items():
            with self.subTest(name):
                links.write_text(written)
                self.map_refused(message, "--base", base)
        links.write_text(text)
        self.assertEqual(self.check_map("--base", base)[0], 0)

    def test_lines_of_the_base_map_are_never_checked_against_the_pages(self) -> None:
        # A line's page may move or go after it was written: the line keeps its snapshot, and only the lines appended
        # since the base are checked.
        self.applied([planned("alpha")])
        base = self.commit()
        self.applied([planned("beta")])
        links = sync.LINKS / "Algebra.jsonl"
        (wiki.ROADMAP / "Algebra/groups/alpha.md").unlink()
        links.write_text("".join(entry + "\n" for entry in links.read_text().splitlines() if "/alpha.md" not in entry))
        code, out, err = self.check_map("--base", base)
        self.assertEqual((code, err), (0, ""))
        self.assertIn(f"the 1 lines of the map at {base} are its first, unchanged, and 1 are appended", out)


MATHLIB_REV = "56a005855ea17e0b0958f73ec801ae140b0a1679"


def credited(key: str, declaration: str = "irrational_sqrt_two", module: str = "Mathlib.NumberTheory.Real.Irrational",
             **fields) -> dict:
    """A Mathlib-credited row: a page that states what *declaration*, in *module*, states."""
    return planned(key, kind="mathlib", mathlib={"declaration": declaration, "module": module}, **fields)


class MathlibRows(MapFixture):
    """A `mathlib` row writes a page credited to one Mathlib declaration, in the format sync_wiki reads (docs/BLUEPRINT.md,
    "Mathlib-credited pages"), here beside a page the wiki already credits to Mathlib, and with Mathlib pinned in
    lake-manifest.json."""

    def setUp(self) -> None:
        super().setUp()
        self.write("lake-manifest.json", json.dumps({"version": 7, "packages": [{"name": "mathlib", "rev": MATHLIB_REV}]}))
        self.write("blueprint/roadmap/Algebra/groups/card-dvd.md",
                   "# The order of a subgroup\n\nThe order of a subgroup divides the order of the group.\n")
        self.annotate("Algebra/groups/card-dvd.md", id="af_" + "c" * 24, object=[
            {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "Subgroup.card_subgroup_dvd_card",
                                                               "module": "Mathlib.GroupTheory.Coset.Card"}}],
            extensions={"org.autoform": {"mathlib": True}})

    def row_of(self, page: str) -> dict:
        return next(row for row in self.rows() if row["subject"][0]["uri"] == f"../roadmap/{page}")

    def test_a_mathlib_row_writes_a_page_credited_as_the_format_says(self) -> None:
        base = self.commit()
        out = self.applied([credited("sqrt-two-irrational", title="The square root of two is irrational",
                                     statement="The square root of 2 is irrational.")])
        # The plan names the kind of each row and of each page.
        self.assertIn(", 1 rows (0 planned, 1 Mathlib-credited)", out)
        self.assertIn("blueprint/roadmap/Algebra/groups/sqrt-two-irrational.md\n      the Mathlib-credited page of "
                      "sqrt-two-irrational, in the existing folder blueprint/roadmap/Algebra/groups", out)
        self.assertEqual(self.page("Algebra/groups/sqrt-two-irrational.md"), "# The square root of two is irrational\n\n"
                         f"The square root of 2 is irrational.\n\n## Sources\n\n- {SOURCE}\n")
        row = self.row_of("Algebra/groups/sqrt-two-irrational.md")
        self.assertEqual(row, {
            "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/sqrt-two-irrational.md"}],
            "id": importer.article_id(seed("sqrt-two-irrational")),
            "object": [{"type": "lean", "uri": "https://github.com/leanprover-community/mathlib4",
                        "location": {"declaration": "irrational_sqrt_two", "module": "Mathlib.NumberTheory.Real.Irrational"}}],
            "extensions": {"org.atlas-wiki": {"seed": seed("sqrt-two-irrational")}, "org.autoform": {"mathlib": True}}})
        line = json.loads(importer.MAP.read_text())
        self.assertEqual(list(line)[-2:], ["pending", "mathlib"])
        self.assertEqual(line["mathlib"], {"declaration": "irrational_sqrt_two", "module": "Mathlib.NumberTheory.Real.Irrational",
                                           "rev": MATHLIB_REV})
        # sync_wiki's readers credit it, as mathlib-names and the cards read credit.
        names, problems = sync.credited_mathlib(sync.read_annotations())
        self.assertEqual(problems, [])
        self.assertEqual(names["irrational_sqrt_two"], ("Mathlib.NumberTheory.Real.Irrational",
                                                        "Algebra/groups/sqrt-two-irrational.md"))
        listed = self.tmp / "names.txt"
        with redirect_stdout(io.StringIO()):
            self.assertEqual(sync.main(["mathlib-names", str(listed)]), 0)
        self.assertIn("irrational_sqrt_two", listed.read_text().split())
        self.assertEqual((cards.credit(row), cards.declaration(row)), ("mathlib", "irrational_sqrt_two"))
        # The map's line records the page, its annotation and its credit, as the check of an appended line finds them.
        code, out, err = self.check_map("--base", base)
        self.assertEqual((code, err), (0, ""))

    def test_a_planned_row_may_depend_on_a_mathlib_rows_page(self) -> None:
        self.applied([credited("sqrt-two-irrational"), planned("uses-it", depends=[on("sqrt-two-irrational")])])
        self.assertIn("## Depends on\n\n- [Title of sqrt-two-irrational](sqrt-two-irrational.md)\n",
                      self.page("Algebra/groups/uses-it.md"))
        self.assertNotIn("## Depends on", self.page("Algebra/groups/sqrt-two-irrational.md"))

    def test_a_mathlib_row_has_a_statement_and_sources_only(self) -> None:
        self.refused([credited("a", sketch="It follows."), credited("b", depends=[on("a")]),
                      credited("c", pending=[missing("p-group")], not_ready=True, prose_missing="It uses p-groups."),
                      planned("d", mathlib={"declaration": "Foo.bar", "module": "Mathlib.Foo"}),
                      planned("e", kind="mathlib"), credited("f", declaration="two words", module="Batteries.Data.List")],
                     "manifest line 1 (a): sketch: 'It follows.' is not of type 'null'",
                     "manifest line 2 (b): depends: [{'target': 'a', 'kind': 'statement'}] is expected to be empty",
                     "manifest line 3 (c): pending: ", "manifest line 3 (c): not_ready: False was expected",
                     "manifest line 3 (c): prose_missing: 'It uses p-groups.' is not of type 'null'",
                     "manifest line 4 (d): mathlib is allowed only on a row of kind mathlib",
                     "manifest line 5 (e): 'mathlib' is a required property",
                     "manifest line 6 (f): mathlib/declaration: 'two words' does not match",
                     "manifest line 6 (f): mathlib/module: 'Batteries.Data.List' does not match")

    def test_the_names_a_row_may_give(self) -> None:
        # A module component may hold an apostrophe, as sync_wiki's own pattern allows (sync_wiki.mathlib_module).
        self.applied([credited("primed", declaration="Foo.bar'", module="Mathlib.Foo'")])
        self.assertEqual(sync.page_owner(self.row_of("Algebra/groups/primed.md")), ("mathlib", "Foo.bar'", "Mathlib.Foo'"))
        # Narrower than sync_wiki on purpose: a name with whitespace, as a «»-quoted Lean name may have, and a module
        # outside Mathlib are refused.
        self.refused([credited("quoted", declaration="Foo.«bar baz»", module="Mathlib.Foo"),
                      credited("elsewhere", declaration="List.foo", module="Batteries.Data.List")],
                     "manifest line 1 (quoted): mathlib/declaration: 'Foo.«bar baz»' does not match",
                     "manifest line 2 (elsewhere): mathlib/module: 'Batteries.Data.List' does not match")

    def test_a_declaration_has_one_page(self) -> None:
        self.refused([credited("a", declaration="Subgroup.card_subgroup_dvd_card",
                               module="Mathlib.GroupTheory.Coset.Card"), credited("b"), credited("c"),
                      credited("d", declaration="QuotientGroup.leftRel", module="Mathlib.GroupTheory.Coset.Defs")],
                     "manifest line 1 (a): mathlib/declaration: blueprint/roadmap/Algebra/groups/card-dvd.md credits "
                     "Subgroup.card_subgroup_dvd_card to Mathlib too; a declaration has one page",
                     "manifest line 3 (c): mathlib/declaration irrational_sqrt_two is also that of manifest line 2 (b); "
                     "a declaration has one page",
                     "manifest line 4 (d): mathlib/declaration: blueprint/roadmap/Algebra/groups/cosets.md credits "
                     "QuotientGroup.leftRel as a declaration of this project too; a declaration has one page")

    def test_a_declaration_has_one_page_whoever_credits_it(self) -> None:
        # A page that credits the name as a declaration of this project is a claimant as much as a Mathlib-credited
        # one: the importer refuses the row, and --check-map --base the appended line, with one message.
        message = ("blueprint/roadmap/Algebra/groups/cosets.md credits irrational_sqrt_two as a declaration of this "
                   "project too; a declaration has one page")
        links = sync.LINKS / "Algebra.jsonl"
        text = links.read_text()
        cosets = self.row_of("Algebra/groups/cosets.md")
        claimed = "".join(json.dumps({**cosets, "object": [{"location": {"declaration": "irrational_sqrt_two"}}]}
                                     if row == cosets else row, ensure_ascii=False) + "\n"
                          for row in map(json.loads, text.splitlines()))
        links.write_text(claimed)
        self.assertEqual(sync.page_owner(self.row_of("Algebra/groups/cosets.md")), ("atlas", "irrational_sqrt_two", None))
        self.refused([credited("sqrt-two-irrational")], f"manifest line 1 (sqrt-two-irrational): mathlib/declaration: "
                     f"{message}")
        links.write_text(text)
        base = self.commit()
        self.applied([credited("sqrt-two-irrational")])
        after = links.read_text()
        links.write_text(after.replace(text, claimed, 1))
        self.map_refused(f"scripts/mathgraph-map.jsonl line 1 (sqrt-two-irrational), appended since {base}: {message}",
                         "--base", base)

    def test_a_mathlib_link_without_the_flag_is_a_reference_not_a_claim(self) -> None:
        # A Mathlib link on a row without the `mathlib` flag, and with no role `states`, is a reference (docs/BLUEPRINT.md,
        # "Mathlib-credited pages"): it credits nothing, so the declaration may still have its page.
        self.write("blueprint/roadmap/Algebra/groups/notes.md", "# Notes\n\nThe square root of 2 is irrational.\n")
        self.annotate("Algebra/groups/notes.md", id="af_" + "f" * 24, object=[
            {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": "irrational_sqrt_two",
                                                               "module": "Mathlib.NumberTheory.Real.Irrational"}}])
        self.assertEqual(sync.page_owner(self.row_of("Algebra/groups/notes.md")), ("none", None, None))
        base = self.commit()
        self.applied([credited("sqrt-two-irrational")])
        code, out, err = self.check_map("--base", base)
        self.assertEqual((code, err), (0, ""))

    def test_credits_the_links_folder_leaves_ambiguous(self) -> None:
        self.write("blueprint/roadmap/Algebra/groups/both.md", "# Both\n\nIt states two results.\n")
        self.annotate("Algebra/groups/both.md", id="af_" + "d" * 24, object=[
            {"type": "lean", "uri": sync.MATHLIB, "location": {"declaration": name, "module": "Mathlib.Foo"}}
            for name in ("Foo.one", "Foo.two")], extensions={"org.autoform": {"mathlib": True}})
        self.refused([credited("x")], "the links folder's credits are ambiguous, as sync_wiki.py mathlib-names reads "
                     "them: Algebra/groups/both.md sets `mathlib` but names 2 Mathlib declarations")

    def test_a_mathlib_row_needs_the_mathlib_revision_lake_manifest_pins(self) -> None:
        (self.tmp / "lake-manifest.json").unlink()
        self.refused([credited("x")], "lake-manifest.json pins no Mathlib commit; the map records the Mathlib revision "
                     "for a Mathlib-credited row")
        # A file sync_wiki cannot read is refused by name, never a traceback.
        self.write("lake-manifest.json", "{not json")
        self.refused([credited("x")], "lake-manifest.json cannot be read as sync_wiki reads it: Expecting property name")
        self.write("lake-manifest.json", json.dumps({"version": 7, "packages": [{"name": "mathlib", "rev": "main"}]}))
        self.refused([credited("x")], "lake-manifest.json pins no Mathlib commit")
        with patch.object(sync, "mathlib_revision", side_effect=PermissionError(13, "Permission denied")):
            self.refused([credited("x")], "lake-manifest.json cannot be read as sync_wiki reads it: [Errno 13] "
                         "Permission denied")
        (self.tmp / "lake-manifest.json").unlink()
        (self.tmp / "lake-manifest.json").mkdir()
        self.refused([credited("x")], "lake-manifest.json pins no Mathlib commit")
        (self.tmp / "lake-manifest.json").rmdir()
        # A planned row needs no Mathlib revision.
        self.applied([planned("y")])

    def test_the_rows_the_change_writes_are_read_as_sync_wiki_reads_them(self) -> None:
        # The links folder already has a row for the new page's path: the page would have two rows.
        self.annotate("Algebra/groups/x.md", id="af_" + "e" * 24)
        self.refused([credited("x")], "the links folder as the change would leave it: Algebra/groups/x.md has 2 rows, "
                     "which Autoform reads together; a page has one row")
        # A declaration sync_wiki cannot read as text names no Mathlib declaration.
        self.refused([credited("y", declaration="irrational\u200bsqrt_two")],
                     "manifest line 1 (y): Algebra/groups/y.md sets `mathlib` but names 0 Mathlib declarations")

    def test_a_line_with_a_mathlib_credit(self) -> None:
        line = map_row("alpha", pending=[], sketch_sha256=digest(""),
                       mathlib={"declaration": "Foo.bar", "module": "Mathlib.Foo", "rev": MATHLIB_REV})
        self.write_map(importer.map_line(line))
        code, out, err = self.check_map()
        self.assertEqual((code, err), (0, ""))
        moved = json.dumps({**{name: line[name] for name in importer.MAP_FIELDS if name != "pending"},
                            "mathlib": line["mathlib"], "pending": []}, ensure_ascii=False)
        for name, written, message in (
                ("a pending entry", importer.map_line({**line, "pending": [missing("p-group")]}), "line 1: pending: "),
                ("a sketch", importer.map_line({**line, "sketch_sha256": digest("A sketch.")}), "line 1: sketch_sha256: "),
                ("another revision", importer.map_line({**line, "mathlib": {**line["mathlib"], "rev": "main"}}),
                 "line 1: mathlib/rev: 'main' does not match"),
                ("its fields out of order", moved, "line 1: it is not written as the importer writes its row")):
            with self.subTest(name):
                self.write_map(written)
                self.map_refused(f"scripts/mathgraph-map.jsonl {message}")

    def test_an_appended_line_and_its_pages_credit_agree(self) -> None:
        base = self.commit()
        self.applied([credited("sqrt-two-irrational"), planned("alpha")])
        self.assertEqual(self.check_map("--base", base)[0], 0)
        links = sync.LINKS / "Algebra.jsonl"
        text = links.read_text()
        rows = [json.loads(entry) for entry in text.splitlines()]
        mine = self.row_of("Algebra/groups/sqrt-two-irrational.md")
        planned_row = self.row_of("Algebra/groups/alpha.md")

        def where(number: int, key: str) -> str:
            return f"scripts/mathgraph-map.jsonl line {number} ({key}), appended since {base}"

        unflagged = {**mine, "extensions": {"org.atlas-wiki": mine["extensions"]["org.atlas-wiki"]}}
        moved = {**mine, "object": [{**mine["object"][0], "location": {"declaration": "irrational_sqrt_two",
                                                                       "module": "Mathlib.Other"}}]}
        claimed = {**planned_row, "object": mine["object"], "extensions": {**planned_row["extensions"],
                                                                          "org.autoform": {"mathlib": True}}}
        for name, old, new, message in (
                ("a credited page that lost its flag", mine, unflagged,
                 f"{where(1, 'sqrt-two-irrational')}: its page's annotation credits no declaration, as sync_wiki reads "
                 "it, not the Mathlib declaration irrational_sqrt_two in Mathlib.NumberTheory.Real.Irrational"),
                ("a credited page with another module", mine, moved,
                 f"{where(1, 'sqrt-two-irrational')}: its page's annotation credits the Mathlib declaration "
                 "irrational_sqrt_two in Mathlib.Other, as sync_wiki reads it, not the Mathlib declaration "
                 "irrational_sqrt_two in Mathlib.NumberTheory.Real.Irrational"),
                ("a planned page that credits a declaration", planned_row, claimed,
                 f"{where(2, 'alpha')}: its page's annotation credits the Mathlib declaration irrational_sqrt_two in "
                 "Mathlib.NumberTheory.Real.Irrational, as sync_wiki reads it, not no declaration")):
            with self.subTest(name):
                links.write_text("".join(json.dumps(new if row == old else row, ensure_ascii=False) + "\n"
                                         for row in rows))
                self.map_refused(message, "--base", base)
        # Another page that credits the same declaration, which sync_wiki refuses: a declaration has one page.
        cosets = self.row_of("Algebra/groups/cosets.md")
        links.write_text("".join(json.dumps({**cosets, "object": mine["object"], "extensions": {
            "org.autoform": {"mathlib": True}}} if row == cosets else row, ensure_ascii=False) + "\n" for row in rows))
        self.map_refused(f"{where(1, 'sqrt-two-irrational')}: blueprint/roadmap/Algebra/groups/cosets.md credits "
                         "irrational_sqrt_two to Mathlib too; a declaration has one page", "--base", base)
        links.write_text(text)
        self.write("lake-manifest.json", json.dumps({"version": 7, "packages": [{"name": "mathlib", "rev": "f" * 40}]}))
        self.map_refused(f"{where(1, 'sqrt-two-irrational')}: mathlib/rev is {MATHLIB_REV}, not the Mathlib revision "
                         f"lake-manifest.json pins: {'f' * 40}", "--base", base)
        self.write("lake-manifest.json", "{not json")
        self.map_refused(f"{where(1, 'sqrt-two-irrational')}: mathlib/rev is {MATHLIB_REV}, not the Mathlib revision "
                         "lake-manifest.json pins: lake-manifest.json cannot be read as sync_wiki reads it", "--base", base)


class Documentation(unittest.TestCase):
    def test_the_documented_schemas_are_the_ones_checked(self) -> None:
        text = (Path(__file__).resolve().parent.parent / "docs" / "mathgraph-import.md").read_text()
        blocks = {schema["title"]: schema for schema in (
            json.loads(block) for block in re.findall(r"```json\n(\{\n  \"\$schema\".*?)\n```", text, re.S))}
        self.assertEqual(blocks, {importer.MANIFEST_SCHEMA["title"]: importer.MANIFEST_SCHEMA,
                                  importer.MAP_SCHEMA["title"]: importer.MAP_SCHEMA})
        for schema in blocks.values():
            jsonschema.Draft202012Validator.check_schema(schema)


if __name__ == "__main__":
    unittest.main()
