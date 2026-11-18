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
            "type": type_uses, "value": value_uses}


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


class Frontiers(unittest.TestCase):
    def test_a_helper_cycle_reaches_every_article_of_the_cycle(self) -> None:
        # Non-articles a -> {b, X} and b -> a, with X an article: b reaches X through a, in any visiting order.
        rows = {"a": row("a", "def", ["b", "X"], []), "b": row("b", "def", ["a"], []), "X": row("X", "def", [], [])}
        for order in (["a", "b", "X"], ["b", "a", "X"], ["X", "b", "a"], ["X", "a", "b"]):
            with self.subTest(order=order):
                reach = extract.frontiers({name: rows[name] for name in order}, {"X"})
                self.assertEqual((reach["a"], reach["b"]), (frozenset({"X"}), frozenset({"X"})))

    def test_an_article_using_a_helper_cycle_depends_on_what_the_cycle_reaches(self) -> None:
        found = run_extract(
            [row("X", "def", [], []), row("a", "def", ["b", "X"], []), row("b", "def", ["a"], []),
             row("T", "theorem", ["b"], [])],
            ["X", "T"])
        self.assertEqual(found["T"]["statement"], ["X"])


class MissingRows(unittest.TestCase):
    def test_a_missing_name_outside_the_library_namespaces_reaches_lean_facts(self) -> None:
        # The article links `CategoryTheory.foo`, which the sources declare but the dump lacks.
        from types import SimpleNamespace

        from scripts import sync_wiki

        with tempfile.TemporaryDirectory() as directory:
            dump = Path(directory) / "dump.jsonl"
            dump.write_text(json.dumps(row("MathlibExt.T.bar", "def", [], [])) + "\n")
            output = Path(directory) / "lean-dependencies.json"
            with patch.object(extract, "article_manifest", lambda: {"MathlibExt.T.bar", "CategoryTheory.foo"}), \
                    patch("sys.argv", ["extract", str(dump), str(output)]):
                self.assertEqual(extract.main(), 0)
            extracted = json.loads(output.read_text())
        self.assertEqual(extracted["missing_articles"][extract.UNPREFIXED], ["CategoryTheory.foo"])
        index = SimpleNamespace(declarations={"CategoryTheory.foo": None, "MathlibExt.T.bar": None})
        self.assertEqual(sync_wiki.uncompiled_articles(extracted, index), ["CategoryTheory.foo"])


class Mutual(unittest.TestCase):
    def test_a_hidden_theorem_gives_a_statement_what_it_states_not_how_it_is_proved(self) -> None:
        # T's statement uses the undocumented theorem h, whose type uses A and whose proof uses B: T's statement
        # depends on A only, and a proof of T that uses h depends on B as well.
        rows = [row("A", "def", [], []), row("B", "def", [], []), row("h", "theorem", ["A"], ["B"]),
                row("T", "theorem", ["h"], ["h"]), row("D", "def", ["h"], [])]
        found = run_extract(rows, ["A", "B", "T", "D"])
        self.assertEqual((found["T"]["statement"], found["T"]["proof"]), (["A"], ["B"]))
        self.assertEqual((found["D"]["statement"], found["D"]["proof"]), (["A"], []))

    def test_an_opaque_body_gives_proof_dependencies_only(self) -> None:
        # Lean cannot unfold an opaque constant, so its body is like a proof: a published opaque O states only its
        # type, and an opaque helper o reaches B only through a proof that uses it.
        rows = [row("A", "def", [], []), row("B", "def", [], []), row("O", "opaque", ["A"], ["B"]),
                row("o", "opaque", ["A"], ["B"]), row("D", "def", ["o"], []), row("T", "theorem", ["o"], ["o"])]
        found = run_extract(rows, ["A", "B", "O", "D", "T"])
        self.assertEqual((found["O"]["statement"], found["O"]["proof"]), (["A"], ["B"]))
        self.assertEqual((found["D"]["statement"], found["D"]["proof"]), (["A"], []))
        self.assertEqual((found["T"]["statement"], found["T"]["proof"]), (["A"], ["B"]))

    def test_a_hidden_definition_body_stays_part_of_a_statement(self) -> None:
        rows = [row("A", "def", [], []), row("d", "def", [], ["A"]), row("T", "theorem", ["d"], [])]
        self.assertEqual(run_extract(rows, ["A", "T"])["T"]["statement"], ["A"])

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
