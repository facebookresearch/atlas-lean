"""Which compiled uses become an article's statement and proof dependencies."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import extract_v2_lean_dependencies as extract


def row(name: str, kind: str, type_uses: list[str], value_uses: list[str]) -> dict:
    return {"name": name, "module": "MathlibExt.T", "kind": kind, "private": False, "doc": True,
            "instance": False, "type": type_uses, "value": value_uses}


def run_extract(rows: list[dict], articles: list[str]) -> dict:
    with tempfile.TemporaryDirectory() as directory:
        dump = Path(directory) / "dump.jsonl"
        dump.write_text("".join(json.dumps(r) + "\n" for r in rows))
        output = Path(directory) / "lean-dependencies.json"
        with patch.object(extract, "article_manifest", lambda: set(articles)), \
                patch("sys.argv", ["extract", str(dump), str(output)]):
            assert extract.main() == 0
        return json.loads(output.read_text())["articles"]


class Buckets(unittest.TestCase):
    def test_theorem_proof_uses_stay_proof_dependencies(self) -> None:
        found = run_extract([row("A", "def", [], []), row("B", "def", [], []), row("T", "theorem", ["A"], ["A", "B"])],
                            ["A", "B", "T"])
        self.assertEqual((found["T"]["statement"], found["T"]["proof"]), (["A"], ["B"]))

    def test_definition_body_is_part_of_the_statement(self) -> None:
        found = run_extract([row("A", "def", [], []), row("B", "def", [], []), row("D", "def", ["A"], ["B"])],
                            ["A", "B", "D"])
        self.assertEqual((found["D"]["statement"], found["D"]["proof"]), (["A", "B"], []))

    def test_structure_fields_are_part_of_the_statement(self) -> None:
        # The dump gives an inductive type its constructors' types as its value.
        found = run_extract([row("C", "def", [], []), row("S", "inductive", [], ["C", "S"])], ["C", "S"])
        self.assertEqual((found["S"]["statement"], found["S"]["proof"]), (["C"], []))

    def test_body_reaches_articles_through_helpers(self) -> None:
        found = run_extract([row("E", "def", [], []), row("helper", "def", ["E"], []), row("D", "def", [], ["helper"])],
                            ["E", "D"])
        self.assertEqual(found["D"]["statement"], ["E"])


class Mutual(unittest.TestCase):
    def test_mutual_definitions_drop_their_edges_to_each_other(self) -> None:
        found = run_extract(
            [row("E", "def", [], []), row("Win", "def", [], ["Lose", "E"]), row("Lose", "def", [], ["Win"])],
            ["E", "Win", "Lose"])
        self.assertEqual((found["Win"]["statement"], found["Lose"]["statement"]), (["E"], []))

    def test_groups(self) -> None:
        edges = {"a": {"b"}, "b": {"c"}, "c": {"a"}, "d": {"a"}, "e": {"e"}, "f": set()}
        self.assertEqual(extract.mutual_groups(edges), [["a", "b", "c"]])


if __name__ == "__main__":
    unittest.main()
