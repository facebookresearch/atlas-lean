import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import graph_work, sync_wiki as sync


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
        return {"subject": [{"uri": f"../roadmap/{name}"}], "id": "af_" + "1" * 24,
                "extensions": {"org.autoform": {"not_ready": flag}, "org.atlas-wiki": own or {}}, **fields}

    def save(self, *rows):
        (self.links / "roadmap.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))

    def test_separates_expansion_from_imported_prerequisites(self):
        pending = [{"key": "prerequisite", "kind": "proof", "reason": "under-review"}]
        self.save(self.row("b.md", own={"pending": pending}), self.row("a.md"))
        before = (self.links / "roadmap.jsonl").read_bytes()
        report = graph_work.inventory()
        self.assertEqual([item["kind"] for item in report], ["expand", "review-pending-prerequisites"])
        self.assertEqual(report[0]["path"], "blueprint/roadmap/a.md")
        self.assertEqual(report[0]["article_id"], "af_" + "1" * 24)
        self.assertEqual(report[1]["pending"], pending)
        self.assertEqual((self.links / "roadmap.jsonl").read_bytes(), before)

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

    def test_missing_marked_page_fails(self):
        self.save(self.row("gone.md"))
        (self.roadmap / "gone.md").unlink()
        with self.assertRaisesRegex(ValueError, "cannot read a marked article"):
            graph_work.inventory()
