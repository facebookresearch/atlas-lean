import hashlib
import json
import os
import re
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import graph_work, import_mathgraph, sync_wiki as sync


def article_id(name):
    """A distinct, well-formed article id for each page name."""
    return "af_" + hashlib.sha256(name.encode()).hexdigest()[:24]


# An import's record of the result it imported (docs/mathgraph-import.md, Annotations), and the id its seed gives.
SEED = {"source": "mathgraph", "node": "mg_" + "0" * 24, "revision": "0" * 40}
PENDING = [{"key": "prerequisite", "kind": "proof", "reason": "under-review"}]
IMPORTED = import_mathgraph.article_id(SEED)


class GraphWorkTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.links = self.root / "blueprint/links"
        self.links.mkdir(parents=True)
        self.roadmap = self.root / "blueprint/roadmap"
        self.roadmap.mkdir()
        for module, name, value in ((sync, "LINKS", self.links), (sync.wiki, "ROOT", self.root)):
            handle = patch.object(module, name, value)
            handle.start()
            self.addCleanup(handle.stop)
        (self.links / "_defaults.json").write_text(json.dumps({"object": {"type": "lean", "uri": "../.."}}))

    def row(self, name, *, flag=True, own=None, **fields):
        (self.roadmap / name).write_text("# Article\n\nIts statement.\n")
        return {"subject": [{"uri": f"../roadmap/{name}"}], "id": article_id(name),
                "extensions": {"org.autoform": {"not_ready": flag}, "org.atlas-wiki": own or {}}, **fields}

    def save(self, *rows):
        (self.links / "roadmap.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))

    def test_separates_expansion_from_imported_prerequisites(self):
        self.save(self.row("b.md", own={"seed": SEED, "pending": PENDING}, id=IMPORTED), self.row("a.md"))
        before = (self.links / "roadmap.jsonl").read_bytes()
        report = graph_work.inventory()
        self.assertEqual([item["kind"] for item in report], ["expand", "review-pending-prerequisites"])
        self.assertEqual(report[0]["path"], "blueprint/roadmap/a.md")
        self.assertEqual(report[0]["article_id"], article_id("a.md"))
        self.assertEqual(report[1]["article_id"], IMPORTED)
        self.assertEqual(report[1]["pending"], PENDING)
        self.assertEqual((self.links / "roadmap.jsonl").read_bytes(), before)

    def test_pending_prerequisites_need_an_imports_record(self):
        for own, given, reason in (
                ({"pending": PENDING}, IMPORTED, "'seed' is a required property"),
                ({"seed": {**SEED, "source": "elsewhere"}, "pending": PENDING}, IMPORTED, "seed/source: "),
                ({"seed": SEED, "pending": [None]}, IMPORTED, "pending/0: None is not of type 'object'"),
                ({"seed": SEED, "pending": [{**PENDING[0], "reason": "later"}]}, IMPORTED, "pending/0/reason: "),
                ({"seed": SEED, "pending": "prerequisite"}, IMPORTED, "pending: "),
                ({"seed": SEED, "pending": PENDING}, article_id("topic.md"),
                 f"its article ID is not {IMPORTED}, the one its seed gives"),
                ({"seed": SEED, "pending": PENDING * 2}, IMPORTED, "pending/1: prerequisite is pending twice")):
            with self.subTest(own=own, id=given):
                self.save(self.row("topic.md", own=own, id=given))
                with self.assertRaises(ValueError) as raised:
                    graph_work.inventory()
                self.assertRegex(str(raised.exception),
                                 r"^blueprint/roadmap/topic\.md: its pending prerequisites are not an import's: ")
                self.assertIn(reason, str(raised.exception))

    def test_omits_unmarked_folders_held_pages_and_credited_declarations(self):
        self.save(self.row("unmarked.md", flag=False), self.row("README.md"),
                  self.row("held.md", own={"held": {"declaration": "X.held"}}),
                  self.row("legacy.md", own={"module": "X", "name": "legacy"}),
                  self.row("linked.md", object=[{"location": {"declaration": "X.linked"}}]),
                  self.row("reference.md", object=[{"role": "uses", "location": {"declaration": "X.reference"}}]))
        self.assertEqual([item["path"] for item in graph_work.inventory()], ["blueprint/roadmap/reference.md"])

    def test_empty_inventory_is_valid(self):
        self.save(self.row("complete.md", flag=False))
        self.assertEqual(graph_work.inventory(), [])

    def test_missing_or_malformed_article_id_fails_with_the_path(self):
        for id_fields in ({}, {"id": None}, {"id": 123}, {"id": "af_short"}, {"id": "af_" + "A" * 24}):
            with self.subTest(id_fields=id_fields):
                row = self.row("topic.md")
                row.pop("id")
                self.save({**row, **id_fields})
                with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/topic\.md: expected its own article ID"):
                    graph_work.inventory()

    def test_a_listed_row_needs_its_own_id_not_the_defaults(self):
        row = self.row("topic.md")
        row.pop("id")
        (self.links / "_defaults.json").write_text(json.dumps({"object": {"type": "lean", "uri": "../.."},
                                                               "id": article_id("topic.md")}))
        self.save(row)
        with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/topic\.md: expected its own article ID.*"
                                                r"sync_wiki\.py ids"):
            graph_work.inventory()

    def test_an_imported_row_without_its_id_is_told_to_restore_the_seeds(self):
        row = self.row("topic.md", own={"seed": SEED, "pending": PENDING})
        row.pop("id")
        self.save(row)
        with self.assertRaises(ValueError) as raised:
            graph_work.inventory()
        self.assertRegex(str(raised.exception), r"^blueprint/roadmap/topic\.md: expected its own article ID")
        self.assertIn("the one its seed gives", str(raised.exception))
        self.assertNotIn("sync_wiki.py ids", str(raised.exception))

    def test_an_id_two_annotations_share_fails_with_both_pages(self):
        for marked in (True, False):
            with self.subTest(second_marked=marked):
                first, second = self.row("a.md"), self.row("b.md", flag=marked)
                self.save(first, {**second, "id": first["id"]})
                with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/a\.md: its article ID af_[0-9a-f]{24} is "
                                                        r"also the ID of blueprint/roadmap/b\.md$"):
                    graph_work.inventory()

    def test_an_id_the_defaults_give_another_annotation_fails(self):
        first, second = self.row("a.md"), self.row("b.md", flag=False)
        second.pop("id")
        (self.links / "_defaults.json").write_text(json.dumps({"object": {"type": "lean", "uri": "../.."},
                                                               "id": first["id"]}))
        self.save(first, second)
        with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/a\.md: its article ID af_[0-9a-f]{24} is also "
                                                r"the ID of blueprint/roadmap/b\.md$"):
            graph_work.inventory()

    def test_an_id_in_the_frontmatter_of_an_unannotated_article_fails(self):
        listed = self.row("a.md")
        (self.roadmap / "plain.md").write_text(f"---\narticle_id: {listed['id']}\n---\n# Plain\n\nIts statement.\n")
        self.save(listed)
        with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/a\.md: its article ID af_[0-9a-f]{24} is also "
                                                r"the ID of blueprint/roadmap/plain\.md$"):
            graph_work.inventory()

    def test_a_page_autoform_skips_as_hidden_fails(self):
        for name in (".draft.md", ".drafts/topic.md"):
            with self.subTest(name=name):
                (self.roadmap / name).parent.mkdir(parents=True, exist_ok=True)
                self.save(self.row(name))
                with self.assertRaisesRegex(ValueError, rf"^blueprint/roadmap/{re.escape(name)}: Autoform reads no "
                                                        r"article there"):
                    graph_work.inventory()

    def test_a_roadmap_with_a_symbolic_link_fails(self):
        self.save(self.row("a.md"))
        (self.roadmap / "b.md").symlink_to(self.roadmap / "a.md")
        with self.assertRaisesRegex(ValueError, r"^Autoform reads no articles: roadmap contains a symbolic link: "
                                                r"roadmap/b\.md"):
            graph_work.inventory()

    def test_a_listed_page_that_is_not_utf8_fails(self):
        self.save(self.row("bad.md"))
        (self.roadmap / "bad.md").write_bytes(b"# Bad\n\n\xff\n")
        with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/bad\.md: Autoform cannot read this article: "):
            graph_work.inventory()

    def test_a_pipe_in_the_roadmap_is_not_read(self):
        self.save(self.row("a.md"))
        os.mkfifo(self.roadmap / "draft.md")
        self.assertEqual([item["path"] for item in graph_work.inventory()], ["blueprint/roadmap/a.md"])

    def test_a_links_folder_autoform_does_not_read_fails(self):
        self.save(self.row("a.md"))
        (self.root / "elsewhere").mkdir()
        self.links.rename(self.root / "elsewhere/links")
        self.links.symlink_to(self.root / "elsewhere/links", target_is_directory=True)
        with self.assertRaisesRegex(ValueError, r"^Autoform reads no annotations: blueprint/links is missing, is a "
                                                r"symbolic link"):
            graph_work.inventory()

    def test_a_listed_page_with_another_annotation_fails_whichever_comes_first(self):
        marked, unmarked = self.row("a.md"), {**self.row("a.md", flag=False), "id": article_id("other")}
        for rows in ((unmarked, marked), (marked, unmarked)):
            with self.subTest(first_marked=rows[0] is marked):
                self.save(*rows)
                with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/a\.md: expected one annotation of this "
                                                        r"page, found 2"):
                    graph_work.inventory()

    def test_a_line_autoform_leaves_out_fails_with_its_file_and_line(self):
        row = json.dumps(self.row("topic.md"))
        (self.links / "roadmap.jsonl").write_text(f'{row[:-1]}, "id": "{article_id("other")}"}}\n')
        with self.assertRaisesRegex(ValueError, r"links/roadmap\.jsonl:1 \(duplicate key 'id'"):
            graph_work.inventory()

    def test_a_row_that_is_not_json_fails_with_its_file_and_line(self):
        self.save(self.row("a.md"))
        (self.links / "second.jsonl").write_text(json.dumps(self.row("b.md")) + "\n\n{\n")
        with self.assertRaisesRegex(ValueError, r"links/second\.jsonl:3 \(not JSON: "):
            graph_work.inventory()

    def test_an_annotation_file_the_sync_does_not_read_fails(self):
        self.save(self.row("a.md"))
        (self.links / "more").mkdir()
        (self.links / "more/b.jsonl").write_text(json.dumps(self.row("b.md")) + "\n")
        with self.assertRaisesRegex(ValueError, r"^Autoform reads blueprint/links/more/b\.jsonl, which the sync does "
                                                r"not"):
            graph_work.inventory()

    def test_missing_marked_page_fails(self):
        self.save(self.row("gone.md"))
        (self.roadmap / "gone.md").unlink()
        with self.assertRaisesRegex(ValueError, "cannot read a marked article"):
            graph_work.inventory()
