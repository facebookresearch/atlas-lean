import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import graph_work, sync_wiki as sync


def article_id(name):
    """A distinct, well-formed article id for each page name."""
    return "af_" + hashlib.sha256(name.encode()).hexdigest()[:24]


# An import's record of the result it imported (docs/mathgraph-import.md, Annotations).
SEED = {"source": "mathgraph", "node": "mg_" + "0" * 24, "revision": "0" * 40}
PENDING = [{"key": "prerequisite", "kind": "proof", "reason": "under-review"}]


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
        self.save(self.row("b.md", own={"seed": SEED, "pending": PENDING}), self.row("a.md"))
        before = (self.links / "roadmap.jsonl").read_bytes()
        report = graph_work.inventory()
        self.assertEqual([item["kind"] for item in report], ["expand", "review-pending-prerequisites"])
        self.assertEqual(report[0]["path"], "blueprint/roadmap/a.md")
        self.assertEqual(report[0]["article_id"], article_id("a.md"))
        self.assertEqual(report[1]["pending"], PENDING)
        self.assertEqual((self.links / "roadmap.jsonl").read_bytes(), before)

    def test_pending_prerequisites_need_an_imports_record(self):
        for own in ({"pending": PENDING}, {"seed": {**SEED, "source": "elsewhere"}, "pending": PENDING},
                    {"seed": SEED, "pending": [None]}, {"seed": SEED, "pending": [{**PENDING[0], "reason": "later"}]},
                    {"seed": SEED, "pending": "prerequisite"}):
            with self.subTest(own=own):
                self.save(self.row("topic.md", own=own))
                with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/topic\.md: its pending prerequisites are "
                                                        r"not an import's: "):
                    graph_work.inventory()

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
                with self.assertRaisesRegex(ValueError, r"blueprint/roadmap/topic\.md: expected an article ID"):
                    graph_work.inventory()

    def test_an_id_two_annotations_share_fails_with_both_pages(self):
        for marked in (True, False):
            with self.subTest(second_marked=marked):
                first, second = self.row("a.md"), self.row("b.md", flag=marked)
                self.save(first, {**second, "id": first["id"]})
                with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/a\.md: its article ID af_[0-9a-f]{24} is "
                                                        r"also the ID of blueprint/roadmap/b\.md$"):
                    graph_work.inventory()

    def test_a_listed_page_with_another_annotation_fails_whichever_comes_first(self):
        marked, unmarked = self.row("a.md"), {**self.row("a.md", flag=False), "id": article_id("other")}
        for rows in ((unmarked, marked), (marked, unmarked)):
            with self.subTest(first_marked=rows[0] is marked):
                self.save(*rows)
                with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/a\.md: expected one annotation of this "
                                                        r"page, found 2"):
                    graph_work.inventory()

    def test_a_listed_annotation_autoform_leaves_out_fails(self):
        row = json.dumps(self.row("topic.md"))
        (self.links / "roadmap.jsonl").write_text(f'{row[:-1]}, "id": "{article_id("other")}"}}\n')
        with self.assertRaisesRegex(ValueError, r"^blueprint/roadmap/topic\.md: Autoform leaves its annotation at "
                                                r"blueprint/links/roadmap\.jsonl:1 out: duplicate key 'id'"):
            graph_work.inventory()

    def test_a_row_that_is_not_json_fails_with_its_file_and_line(self):
        self.save(self.row("a.md"))
        (self.links / "second.jsonl").write_text(json.dumps(self.row("b.md")) + "\n\n{\n")
        with self.assertRaisesRegex(ValueError, r"^blueprint/links/second\.jsonl:3: the row is not JSON: "):
            graph_work.inventory()

    def test_missing_marked_page_fails(self):
        self.save(self.row("gone.md"))
        (self.roadmap / "gone.md").unlink()
        with self.assertRaisesRegex(ValueError, "cannot read a marked article"):
            graph_work.inventory()
