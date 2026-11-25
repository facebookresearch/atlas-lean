"""Which compiled uses become an article's statement and proof dependencies."""

from __future__ import annotations

import errno
import hashlib
import io
import json
import os
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from scripts import extract_v2_lean_dependencies as extract


def row(name: str, kind: str, type_uses: list[str], value_uses: list[str]) -> dict:
    return {"name": name, "module": "MathlibExt.T", "kind": kind, "private": False, "doc": True,
            "type": type_uses, "value": value_uses}


def sources(declared: set[str] | None) -> dict:
    """How a test patches extract.lean_index: an index declaring *declared*, or, given none, one no test may read."""
    if declared is None:
        return {"side_effect": AssertionError("read the Lean sources")}
    return {"return_value": SimpleNamespace(declarations=set(declared))}


def run_extract(rows: list[dict], articles: list[str], duplicates: dict[str, str] | None = None,
                declared: set[str] | None = None) -> dict:
    with tempfile.TemporaryDirectory() as directory:
        dump = Path(directory) / "dump.jsonl"
        dump.write_text("".join(json.dumps(r) + "\n" for r in rows))
        output = Path(directory) / "lean-dependencies.json"
        with patch.object(extract, "article_manifest", lambda: set(articles)), \
                patch.object(extract, "article_aliases", lambda: dict(duplicates or {})), \
                patch.object(extract, "lean_index", **sources(declared)), \
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
                    patch.object(extract, "article_aliases", dict), \
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


class Duplicates(unittest.TestCase):
    """A declaration a page's row lists as a duplicate states the page's result again (sync_wiki.duplicate_names): any
    other article's way stops at it as at the page's own declaration, and a use of it is a use of that article; for
    that article it is part of the article, which depends on what it uses."""

    def test_an_article_that_uses_only_the_duplicate_depends_on_its_article(self) -> None:
        # C and its duplicate c define one function, c by a body that uses the article X. A's statement names c, and
        # B's proof reaches c through the hidden theorem h: both depend on C, and neither on X.
        rows = [row("X", "def", [], []), row("C", "def", [], []), row("c", "def", [], ["X"]),
                row("h", "theorem", [], ["c"]), row("A", "theorem", ["c"], []), row("B", "theorem", [], ["h"])]
        found = run_extract(rows, ["X", "C", "A", "B"], {"c": "C"})
        self.assertEqual((found["A"]["statement"], found["A"]["proof"]), (["C"], []))
        self.assertEqual((found["B"]["statement"], found["B"]["proof"]), ([], ["C"]))
        # Unlisted, c is a hidden definition like any other, and its body leads to X.
        found = run_extract(rows, ["X", "C", "A", "B"])
        self.assertEqual((found["A"]["statement"], found["B"]["proof"]), (["X"], ["X"]))

    def test_an_article_depends_on_what_its_own_duplicate_uses(self) -> None:
        # C is proved through its duplicate c, whose proof uses the page B: C's proof depends on B, as it did before c
        # was listed, and never on C. So it does when c's statement is part of C's, and when C reaches c through the
        # hidden theorem h. Another article, E, which uses c, still depends on C only.
        cases = {
            "C's proof uses c": ([row("B", "def", [], []), row("c", "theorem", [], ["B"]),
                                  row("C", "theorem", [], ["c"])], ([], ["B"])),
            "C's statement uses c": ([row("A", "def", [], []), row("B", "def", [], []),
                                      row("c", "theorem", ["A"], ["B"]), row("C", "theorem", ["c"], [])], (["A"], [])),
            "C's proof reaches c through h": ([row("B", "def", [], []), row("c", "theorem", [], ["B"]),
                                               row("h", "theorem", [], ["c"]), row("C", "theorem", [], ["h"])],
                                              ([], ["B"])),
        }
        for case, (rows, edges) in cases.items():
            with self.subTest(case=case):
                articles = [r["name"] for r in rows if r["name"] not in ("c", "h")]
                found = run_extract(rows, articles, {"c": "C"})
                self.assertEqual((found["C"]["statement"], found["C"]["proof"]), edges)
                self.assertEqual(found["C"], run_extract(rows, articles)["C"])
        rows = [row("B", "def", [], []), row("c", "theorem", [], ["B"]), row("C", "theorem", [], ["c"]),
                row("E", "theorem", [], ["c"])]
        found = run_extract(rows, ["B", "C", "E"], {"c": "C"})
        self.assertEqual((found["C"]["proof"], found["E"]["proof"]), (["B"], ["C"]))

    def test_an_article_and_its_own_duplicate_that_use_each_other_end(self) -> None:
        # C and its duplicate c use each other, so do c and C's second duplicate d, and so do c and the hidden theorem
        # h: C depends on the page B, which c's proof uses, and never on itself.
        cases = {
            "C and c": ([row("B", "def", [], []), row("c", "theorem", [], ["C", "B"]), row("C", "theorem", [], ["c"])],
                        {"c": "C"}),
            "c and d": ([row("B", "def", [], []), row("c", "theorem", [], ["d"]), row("d", "theorem", [], ["c", "B"]),
                         row("C", "theorem", [], ["c"])], {"c": "C", "d": "C"}),
            "c and h": ([row("B", "def", [], []), row("h", "theorem", [], ["c"]), row("c", "theorem", [], ["h", "B"]),
                         row("C", "theorem", [], ["h"])], {"c": "C"}),
        }
        for case, (rows, duplicates) in cases.items():
            with self.subTest(case=case):
                found = run_extract(rows, ["B", "C"], duplicates)
                self.assertEqual((found["C"]["statement"], found["C"]["proof"]), ([], ["B"]))

    def test_a_private_duplicate_is_read_by_its_source_name(self) -> None:
        # The dump names a declaration outside a module's public section by its private name.
        rows = [row("C", "def", [], []), {**row("_private.MathlibExt.T.0.c", "def", [], []), "private": True},
                row("A", "theorem", ["_private.MathlibExt.T.0.c"], [])]
        self.assertEqual(run_extract(rows, ["C", "A"], {"c": "C"})["A"]["statement"], ["C"])

    def test_a_duplicate_the_dump_cannot_count_as_its_article_stops_the_extraction(self) -> None:
        # A use of a duplicate counts as a use of its article only when a constant of the dump, one only, has the name
        # of each and no page stands for the duplicate. A row the dump lacks for a name the Lean sources still declare
        # means an incomplete dump: the extraction writes nothing, rather than follow the duplicate's own uses.
        def private(name: str, module: str, type_uses: list[str], value_uses: list[str]) -> dict:
            return {**row(f"_private.{module}.0.{name}", "theorem", type_uses, value_uses), "module": module,
                    "private": True}

        twins = [private("Ext.twin", "MathlibExt.T", [], []), private("Ext.twin", "MathlibExt.U", [], [])]
        cases = {
            "the duplicate without a row": ({"C"}, {"Ext.gone": "C"}, [row("C", "def", [], [])], {"C", "Ext.gone"},
                                            "the compiled dependency dump has no row for Ext.gone, and the Lean "
                                            "sources declare it: make the dump again"),
            "its article without a row": ({"C", "A"}, {"c": "C"}, [row("c", "def", [], ["X"]), row("X", "def", [], []),
                                                                   row("A", "theorem", ["c"], [])], {"C", "c", "A"},
                                          "the compiled dependency dump has no row for C, and the Lean sources declare "
                                          "it: make the dump again"),
            "a page standing for the duplicate": ({"C", "c"}, {"c": "C"}, [row("C", "def", [], []),
                                                                           row("c", "def", [], [])], None,
                                                  "a page stands for c"),
            "two private constants of the duplicate's name": (
                {"C", "A", "B"}, {"Ext.twin": "C"},
                [row("C", "def", [], []), *twins, row("A", "theorem", [], ["_private.MathlibExt.T.0.Ext.twin"]),
                 row("B", "theorem", [], ["_private.MathlibExt.U.0.Ext.twin"])], None,
                "the compiled dependency dump has several private constants named Ext.twin, which one name cannot tell "
                "apart: _private.MathlibExt.T.0.Ext.twin, _private.MathlibExt.U.0.Ext.twin"),
            "two private constants of the article's name": (
                {"Ext.twin", "A"}, {"c": "Ext.twin"}, [row("c", "def", [], []), *twins, row("A", "theorem", ["c"], [])],
                None, "the compiled dependency dump has several private constants named Ext.twin, which one name "
                      "cannot tell apart: _private.MathlibExt.T.0.Ext.twin, _private.MathlibExt.U.0.Ext.twin"),
        }
        for case, (manifest, aliases, rows, declared, message) in cases.items():
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                dump = Path(directory) / "dump.jsonl"
                dump.write_text("".join(json.dumps(r) + "\n" for r in rows))
                output = Path(directory) / "lean-dependencies.json"
                with patch.object(extract, "article_manifest", lambda: set(manifest)), \
                        patch.object(extract, "article_aliases", lambda: dict(aliases)), \
                        patch.object(extract, "lean_index", **sources(declared)), \
                        patch("sys.argv", ["extract", str(dump), str(output)]), \
                        redirect_stderr(io.StringIO()) as errors, redirect_stdout(io.StringIO()):
                    self.assertEqual(extract.main(), 1)
                self.assertFalse(output.exists())
                name, article = next(iter(aliases.items()))
                self.assertIn(f"error: the wiki lists {name} as a duplicate of {article}, but {message}",
                              errors.getvalue())

    def test_each_end_the_dump_lacks_is_judged_on_its_own(self) -> None:
        # The dump lacks both C and its duplicate c. The Lean deleted c; while it still declares C, which P's proof
        # uses, the dump is incomplete, and the extraction writes nothing, whatever became of c. Once the Lean deleted
        # both, it warns, naming both, and builds.
        cases = {"C declared": ([row("P", "theorem", [], ["C"])], {"C", "P"}, 1,
                                "error: the wiki lists c as a duplicate of C, but the compiled dependency dump has no "
                                "row for C, and the Lean sources declare it: make the dump again"),
                 "both deleted": ([row("P", "theorem", [], [])], {"P"}, 0,
                                  "warning: the Lean no longer declares c, which the wiki lists as a duplicate of C, "
                                  "nor C: the entry counts for nothing; drop it from the row's `duplicates`")}
        for case, (rows, declared, status, message) in cases.items():
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                dump = Path(directory) / "dump.jsonl"
                dump.write_text("".join(json.dumps(r) + "\n" for r in rows))
                output = Path(directory) / "lean-dependencies.json"
                with patch.object(extract, "article_manifest", lambda: {"C", "P"}), \
                        patch.object(extract, "article_aliases", lambda: {"c": "C"}), \
                        patch.object(extract, "lean_index", **sources(declared)), \
                        patch("sys.argv", ["extract", str(dump), str(output)]), \
                        redirect_stderr(io.StringIO()) as errors, redirect_stdout(io.StringIO()):
                    self.assertEqual(extract.main(), status, errors.getvalue())
                self.assertEqual(output.exists(), status == 0)
                self.assertIn(message, errors.getvalue())
                self.assertNotIn("no longer declares c, which the wiki lists as a duplicate of C: ", errors.getvalue())

    def test_a_duplicate_the_lean_no_longer_declares_is_left_out_with_a_warning(self) -> None:
        # The Lean deleted Ext.gone, which C's row lists: a Lean change, which fails no build. The extraction warns,
        # naming both, and the edges are those of a wiki without the entry.
        rows = [row("C", "def", [], []), row("A", "theorem", ["C"], [])]
        with redirect_stderr(io.StringIO()) as errors:
            found = run_extract(rows, ["C", "A"], {"Ext.gone": "C"}, declared={"C", "A"})
        self.assertEqual(found, run_extract(rows, ["C", "A"]))
        self.assertIn("warning: the Lean no longer declares Ext.gone, which the wiki lists as a duplicate of C: the "
                      "entry counts for nothing; drop it from the row's `duplicates`", errors.getvalue())

    def test_a_duplicate_whose_article_the_lean_no_longer_declares_still_stops_the_way(self) -> None:
        # The Lean deleted C, and its duplicate c, whose body uses X, stays. A, which uses only c, depends on no page
        # through it: neither on C, which is gone, nor on X, which c's body uses. The extraction warns, naming both.
        rows = [row("X", "def", [], []), row("c", "def", [], ["X"]), row("A", "theorem", ["c"], ["c"])]
        with redirect_stderr(io.StringIO()) as errors:
            found = run_extract(rows, ["C", "A", "X"], {"c": "C"}, declared={"c", "A", "X"})
        self.assertEqual((found["A"]["statement"], found["A"]["proof"]), ([], []))
        self.assertIn("warning: the Lean no longer declares C, whose page lists c as a duplicate: a use of c counts "
                      "for no page; relink the page or drop the entry", errors.getvalue())
        # Unlisted, c is a hidden definition, and A depends on X through it.
        self.assertEqual(run_extract(rows, ["C", "A", "X"])["A"]["statement"], ["X"])

    def test_an_article_that_is_no_article_is_named_as_such(self) -> None:
        # With both rows compiled, an article missing from the manifest is no repair of the dump's.
        alias, problems, warnings = extract.resolve_aliases({"c": "C"}, {"A"}, {"A": {}, "C": {}, "c": {}},
                                                            lambda name: True)
        self.assertEqual((alias, problems, warnings), ({}, [
            "the wiki lists c as a duplicate of C, but C is not among the articles, so a use of c could count for no "
            "page"], []))


PIN = "a" * 40


def framed(rows: list[dict], rev: str = PIN) -> list[dict]:
    """A dump made with a names list: its header and its closing counts around its rows."""
    registered = sum(1 for r in rows if r.get("registered"))
    return [{**extract.DUMP_FORMAT, "mathlib_rev": rev, "names": registered}, *rows,
            {"end": True, "rows": len(rows) - registered, "names": registered}]


def run_registry(rows: list[dict], articles: list[str], names: list[str] | None = None,
                 status: int = 0, frame=framed, duplicates: dict[str, str] | None = None,
                 declared: set[str] | None = None) -> tuple[dict, dict]:
    with tempfile.TemporaryDirectory() as directory:
        dump = Path(directory) / "dump.jsonl"
        dump.write_text("".join(json.dumps(r) + "\n" for r in frame(rows)))
        names_file = Path(directory) / "names.txt"
        asked = names if names is not None else [r["name"] for r in rows if r.get("registered")]
        # As sync_wiki.py mathlib-names writes it: a module beside each name, but a missing one's whose module it
        # did not give.
        plain = {r["name"] for r in rows if r.get("registered") and r.get("module_given") is False}
        names_file.write_text("".join(f"{name}\n" if name in plain else f"{name}\tMathlib.T\n" for name in asked))
        output, registry = Path(directory) / "lean-dependencies.json", Path(directory) / "registry.json"
        with patch.object(extract, "article_manifest", lambda: set(articles)), \
                patch.object(extract, "article_aliases", lambda: dict(duplicates or {})), \
                patch.object(extract, "lean_index", **sources(declared)), \
                patch.object(extract, "mathlib_revision", lambda: PIN), \
                patch("sys.argv", ["extract", str(dump), str(output), "--registry", str(registry),
                                   "--names", str(names_file)]):
            assert extract.main() == status
        if status:
            assert not registry.exists()
            return {}, {}
        found = json.loads(registry.read_text())
        # The digest of the names alone, sorted: the modules a checkout has do not change it.
        assert found["inputs"]["names_sha256"] == hashlib.sha256(
            "".join(f"{name}\n" for name in sorted(asked)).encode()).hexdigest()
        assert (found["inputs"]["requested"], found["inputs"]["mathlib_rev"]) == (len(asked), PIN)
        return json.loads(output.read_text()), found


def extract_files(rows: list[dict], articles: set[str], *options: str, found: list[str] | None = None,
                  registered: list[dict] | None = None, frame=None, names_text: str | None = None
                  ) -> tuple[int, str, list[str]]:
    """Run the extractor with a registry over *rows* and the rows for credited names: *registered*, or a found row for
    each name in *found* (by default, every name the rows list), framed by *frame* (the dump's header and footer by
    default), with the names file *names_text* (as sync_wiki.py writes it for those rows by default). Its exit
    status, what it printed on stderr, and every file of its directory afterwards."""
    if registered is None:
        if found is None:
            found = sorted({name for r in rows for key in r if key.startswith("mathlib_") and isinstance(r[key], list)
                            for name in r[key]})
        registered = [credited(name, "theorem", [], []) for name in found]
    with tempfile.TemporaryDirectory() as directory:
        dump, names = Path(directory) / "dump.jsonl", Path(directory) / "names.txt"
        dump.write_text("".join(json.dumps(r) + "\n" for r in (frame or framed)(rows + registered)))
        names.write_text(names_text if names_text is not None else "".join(
            f"{r['name']}\n" if r.get("module_given") is False else f"{r['name']}\tMathlib.T\n" for r in registered))
        output, registry = Path(directory) / "out" / "lean-dependencies.json", Path(directory) / "registry.json"
        with patch.object(extract, "article_manifest", lambda: set(articles)), \
                patch.object(extract, "article_aliases", dict), \
                patch.object(extract, "mathlib_revision", lambda: PIN), \
                patch("sys.argv", ["extract", str(dump), str(output), "--registry", str(registry), "--names",
                                   str(names), *options]), \
                redirect_stderr(io.StringIO()) as errors, redirect_stdout(io.StringIO()):
            status = extract.main()
        written = sorted(path.relative_to(directory).as_posix() for path in Path(directory).rglob("*")
                         if path.is_file())
    return status, errors.getvalue(), written


INPUTS = ["dump.jsonl", "names.txt"]
OUTPUTS = ["dump.jsonl", "names.txt", "out/lean-dependencies.json", "registry.json"]


def with_mathlib(base: dict, type_uses: list[str], value_uses: list[str], state_uses: list[str] | None = None,
                 direct: list[str] | None = None, type_direct: list[str] | None = None) -> dict:
    # What a type reaches through all uses includes what it reaches through what constants state, and what a type
    # or a value names itself (`type_direct`, `direct`, nothing unless given) is among what it reaches. As in the
    # dump, a definition's or an inductive type's row also lists what its value reaches as part of what it states
    # (nothing unless given).
    assert set(direct or []) <= set(value_uses) and set(type_direct or []) <= set(type_uses), (direct, type_direct)
    row = {**base, "mathlib_type": type_uses, "mathlib_type_used": type_uses, "mathlib_value": value_uses,
           "mathlib_type_direct": type_direct or [], "mathlib_value_direct": direct or []}
    if state_uses is None and base["kind"] in extract.STATEMENT_VALUE:
        state_uses = []
    return row if state_uses is None else {**row, "mathlib_state": state_uses}


def credited(name: str, kind: str, type_uses: list[str], value_uses: list[str], state_uses: list[str] | None = None,
             **flags) -> dict:
    # A found credited name's row, as the dump writes it: a definition's or an inductive type's also lists what its
    # value reaches as part of what it states (nothing unless given).
    if state_uses is None and kind in extract.STATEMENT_VALUE:
        state_uses = []
    row = {"name": name, "module": "Mathlib.T", "kind": kind, "registered": True, "type": [], "value": [],
           "mathlib_type": type_uses, "mathlib_type_used": type_uses, "mathlib_value": value_uses,
           "proposition": kind == "theorem", "structure": False, "class": False, **flags}
    return row if state_uses is None else {**row, "mathlib_state": state_uses}


class Registry(unittest.TestCase):
    def test_bridges_follow_the_article_rules_and_leave_the_v2_output_unchanged(self) -> None:
        rows = [
            with_mathlib(row("helper", "def", [], []), ["M.measure"], [], []),
            with_mathlib(row("hidden", "theorem", [], []), ["M.space"], ["M.fubini"]),
            with_mathlib(row("T", "theorem", ["helper", "hidden"], ["hidden"]), ["M.space"], ["M.space", "M.fubini"],
                         direct=["M.fubini"], type_direct=["M.space"]),
            with_mathlib(row("D", "def", ["A"], []), [], ["M.space", "M.fubini"], ["M.space"], direct=["M.space"]),
            with_mathlib(row("A", "def", [], []), [], []),
            credited("M.space", "inductive", [], [], [], structure=True),
            credited("M.measure", "def", ["M.space"], ["M.space"], ["M.space"]),
            credited("M.fubini", "theorem", ["M.measure"], ["M.space", "M.measure"]),
            {"name": "M.gone", "registered": True, "missing": True, "module_given": True},
        ]
        output, registry = run_registry(rows, ["T", "D", "A"])
        plain = run_extract([{k: v for k, v in r.items() if not k.startswith("mathlib_")} for r in rows
                             if not r.get("registered")], ["T", "D", "A"])
        self.assertEqual(output["articles"], plain)
        # T's type names M.space itself, and its statement reaches M.measure only through helper's statement; its proof
        # names M.fubini itself (the hidden theorem's proof counts only for proofs). M.measure is a statement bridge
        # left out, not a proof one.
        self.assertEqual(registry["bridges"]["T"], {"statement": ["M.space"], "proof": ["M.fubini"]})
        self.assertEqual(registry["left_out"]["T"], {"statement": ["M.measure"], "proof": []})
        # D's body is part of what it states, and names M.space itself; what its body's proofs use (M.fubini) is not a
        # dependency of a definition, kept or left out.
        self.assertEqual(registry["bridges"]["D"], {"statement": ["M.space"], "proof": []})
        self.assertNotIn("D", registry["left_out"])
        self.assertNotIn("A", registry["bridges"])
        # Between credited declarations, a proof gives an edge to what it reaches through other constants too.
        self.assertEqual(registry["mathlib"]["M.fubini"],
                         {"module": "Mathlib.T", "kind": "theorem", "proposition": True, "statement": ["M.measure"],
                          "proof": ["M.space"]})
        self.assertEqual(registry["mathlib"]["M.measure"]["statement"], ["M.space"])
        self.assertEqual(registry["mathlib"]["M.space"]["kind"], "structure")
        self.assertEqual(registry["missing"], ["M.gone"])
        self.assertEqual(registry["project"], [])

    def test_a_credited_name_of_the_project_never_replaces_its_row(self) -> None:
        # A page credits the project's own A as Mathlib's: the dump answers it as missing, beside A's row.
        rows = [row("T", "theorem", ["A"], []), row("A", "def", [], []),
                {"name": "A", "registered": True, "missing": True, "module_given": False, "project": True}]
        output, registry = run_registry([with_mathlib(r, [], []) if not r.get("registered") else r for r in rows],
                                        ["T", "A"])
        self.assertEqual(output["articles"], run_extract(rows[:2], ["T", "A"]))
        self.assertEqual(output["articles"]["T"]["statement"], ["A"])
        self.assertEqual((registry["missing"], registry["project"]), (["A"], ["A"]))

    def test_the_dump_answers_exactly_the_credited_names(self) -> None:
        rows = [with_mathlib(row("T", "theorem", [], []), [], []), credited("M.a", "def", [], [], [])]
        run_registry(rows, ["T"], names=["M.a", "M.b"], status=1)
        run_registry(rows, ["T"], names=[], status=1)
        run_registry(rows + [credited("M.a", "def", [], [], [])], ["T"], status=1)

    def test_only_a_whole_dump_of_the_current_format_at_this_pin(self) -> None:
        rows = [with_mathlib(row("T", "theorem", [], []), [], []), credited("M.a", "def", [], [], [])]
        run_registry(rows, ["T"], status=1, frame=lambda rows: rows)  # an older dump, with no header
        run_registry(rows, ["T"], status=1, frame=lambda rows: framed(rows, rev="b" * 40))
        run_registry(rows, ["T"], status=1, frame=lambda rows: framed(rows)[:-1])  # cut before its counts
        run_registry(rows, ["T"], status=1, frame=lambda rows: framed(rows)[:1] + framed(rows)[2:])  # a row lost

    def test_a_project_row_of_another_format_is_refused_before_anything_is_written(self) -> None:
        # A dump framed as the current format, with the right pins and counts, whose rows are not all of it: what a
        # value or a type names itself missing, given as a string, not among what it reaches, or not found. Read
        # with a default, the first two would turn a direct use into one through other constants; nothing is
        # written, neither the registry nor the article dependencies. An explicit empty list is no problem.
        def without(base: dict, key: str) -> dict:
            return {name: value for name, value in base.items() if name != key}

        good = [with_mathlib(row("W", "theorem", [], []), [], ["M.a"], direct=["M.a"]),
                with_mathlib(row("E", "theorem", [], []), [], ["M.a"], direct=[])]
        bad = [without(with_mathlib(row("T", "theorem", [], []), [], ["M.a"], direct=["M.a"]), "mathlib_value_direct"),
               {**with_mathlib(row("U", "theorem", [], []), [], ["M.a"]), "mathlib_value_direct": "M.a"},
               {**with_mathlib(row("V", "theorem", [], []), [], []), "mathlib_value_direct": ["M.a"]},
               with_mathlib(row("X", "theorem", [], []), [], ["M.unknown"], direct=["M.unknown"]),
               without(with_mathlib(row("Y", "theorem", [], []), ["M.a"], [], type_direct=["M.a"]),
                       "mathlib_type_direct"),
               {**with_mathlib(row("Z", "theorem", [], []), [], []), "mathlib_type_direct": ["M.a"]}]

        status, errors, written = extract_files(good + bad, {r["name"] for r in good + bad}, found=["M.a"])
        self.assertEqual((status, written), (1, INPUTS))
        for message in ("the dump's row for T has no list of names `mathlib_value_direct`",
                        "the dump's row for U has no list of names `mathlib_value_direct`",
                        "the dump's row for V lists ['M.a'] under `mathlib_value_direct` but not under `mathlib_value`",
                        "the dump's row for X lists ['M.unknown'] under `mathlib_value`, which it did not find",
                        "the dump's row for X lists ['M.unknown'] under `mathlib_value_direct`, which it did not find",
                        "the dump's row for Y has no list of names `mathlib_type_direct`",
                        "the dump's row for Z lists ['M.a'] under `mathlib_type_direct` but not under `mathlib_type`",
                        "7 problems in the rows of"):
            self.assertIn(message, errors)
        self.assertNotIn("row for W", errors)
        self.assertNotIn("row for E", errors)
        status, errors, written = extract_files(good, {r["name"] for r in good}, found=["M.a"])
        self.assertEqual((status, written), (0, OUTPUTS))

    def test_a_definition_s_body_and_an_inductive_type_s_constructors_are_checked_as_what_they_state(self) -> None:
        # Two rows of a real dump: a definition and an inductive type (a structure), whose body and constructors
        # name Measurable, which is then a statement bridge. As dumped, they pass. Taken out of
        # what the value reaches as a statement (`mathlib_state`) while kept in what it names (`mathlib_value_direct`),
        # Measurable would be in neither the kept bridges nor those left out; a type's lists are chained the same way.
        # Each is refused before either output is written.
        definition = {"doc": True, "kind": "def", "mathlib_state": ["Measurable", "MeasurableSpace", "borel"],
                      "mathlib_type": [], "mathlib_type_direct": [], "mathlib_type_used": [],
                      "mathlib_value": ["Measurable", "MeasurableSpace", "borel"],
                      "mathlib_value_direct": ["Measurable"],
                      "module": "MathlibExt.Probability.Geometry.ThinShell",
                      "name": "MathlibExt.Probability.ThinShell.IsLogConcaveDensity", "private": False, "type": [],
                      "value": []}
        inductive = {"doc": True, "kind": "inductive", "mathlib_state": ["Measurable", "MeasurableSpace", "borel"],
                     "mathlib_type": ["MeasurableSpace"], "mathlib_type_direct": ["MeasurableSpace"],
                     "mathlib_type_used": ["MeasurableSpace"],
                     "mathlib_value": ["Measurable", "MeasurableSpace", "borel"],
                     "mathlib_value_direct": ["Measurable", "MeasurableSpace"],
                     "module": "MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.EValues",
                     "name": "MathlibExt.Probability.Statistics.MultipleTesting.IsEValue", "private": False, "type": [],
                     "value": ["MathlibExt.Probability.Statistics.MultipleTesting.IsEValue"]}
        articles = {definition["name"], inductive["name"]}
        status, errors, written = extract_files([definition, inductive], articles)
        self.assertEqual((status, errors, written), (0, "", OUTPUTS))
        cases = [({**definition, "mathlib_state": ["MeasurableSpace", "borel"]}, inductive,
                  f"the dump's row for {definition['name']} lists ['Measurable'] under `mathlib_value_direct` but not "
                  "under `mathlib_state`"),
                 (definition, {**inductive, "mathlib_state": ["MeasurableSpace", "borel"]},
                  f"the dump's row for {inductive['name']} lists ['Measurable'] under `mathlib_value_direct` but not "
                  "under `mathlib_state`"),
                 (definition, {**inductive, "mathlib_value": ["MeasurableSpace", "borel"]},
                  f"the dump's row for {inductive['name']} lists ['Measurable'] under `mathlib_state` but not under "
                  "`mathlib_value`"),
                 (definition, {**inductive, "mathlib_type_used": []},
                  f"the dump's row for {inductive['name']} lists ['MeasurableSpace'] under `mathlib_type` but not "
                  "under `mathlib_type_used`")]
        for first, second, message in cases:
            with self.subTest(message=message):
                status, errors, written = extract_files([first, second], articles)
                self.assertEqual((status, written), (1, INPUTS))
                self.assertIn(message, errors)

    def test_a_malformed_row_for_a_credited_name_is_refused_before_anything_is_written(self) -> None:
        # The dump's rows for credited names, framed as the current format: one without its module, its kind or a
        # flag, one whose lists are no list of names, name a declaration the dump did not find or do not nest, and a
        # missing name's row that does not say whether its module was given. Each is refused, and neither the
        # article dependencies nor the registry is written. As the dump writes them, they pass.
        source = with_mathlib(row("T", "theorem", [], []), ["M.a"], [], type_direct=["M.a"])
        good = [credited("M.a", "theorem", [], []), credited("M.d", "def", ["M.a"], ["M.a"], ["M.a"]),
                {"name": "M.gone", "registered": True, "missing": True, "module_given": True}]
        self.assertEqual(extract_files([source], {"T"}, registered=good)[0::2], (0, OUTPUTS))

        def without(entry: dict, key: str) -> dict:
            return {name: value for name, value in entry.items() if name != key}

        a, d, gone = good
        cases = {
            "no module": ([without(a, "module"), d, gone], "the dump's row for the credited name M.a names no Mathlib "
                                                          "module"),
            "no kind": ([without(a, "kind"), d, gone], "the dump's row for the credited name M.a has no kind of "
                                                      "declaration the dump writes"),
            "no structure flag": ([without(a, "structure"), d, gone],
                                  "the dump's row for the credited name M.a does not say whether it is a `structure`"),
            "a list that is a string": (
                [{**a, "mathlib_value": "M.d"}, d, gone],
                "the dump's row for the credited name M.a has no list of names `mathlib_value`"),
            "no list of what a type uses": ([without(a, "mathlib_type_used"), d, gone],
                                            "the dump's row for the credited name M.a has no list of names "
                                            "`mathlib_type_used`"),
            "a definition without what its body states": (
                [a, without(d, "mathlib_state"), gone],
                "the dump's row for the credited name M.d has no list of names `mathlib_state`"),
            "a name not found": ([{**a, "mathlib_value": ["M.other"]}, d, gone],
                                 "the dump's row for the credited name M.a lists ['M.other'] under `mathlib_value`, "
                                 "which it did not find"),
            "lists that do not nest": ([a, {**d, "mathlib_type_used": []}, gone],
                                       "the dump's row for the credited name M.d lists ['M.a'] under `mathlib_type` "
                                       "but not under `mathlib_type_used`"),
            "a body's statement outside its uses": ([a, {**d, "mathlib_value": []}, gone],
                                                    "the dump's row for the credited name M.d lists ['M.a'] under "
                                                    "`mathlib_state` but not under `mathlib_value`"),
            "a missing name without its module flag": ([a, d, without(gone, "module_given")],
                                                       "the dump's row for the credited name M.gone is malformed"),
        }
        for case, (registered, message) in cases.items():
            with self.subTest(case=case):
                status, errors, written = extract_files([source], {"T"}, registered=registered)
                self.assertEqual((status, written), (1, INPUTS))
                self.assertIn(message, errors)

    def test_both_outputs_are_written_together_or_not_at_all(self) -> None:
        # Earlier outputs stay as they were when a run fails, after the article dependencies are made but before the
        # registry is, or on a refused dump; a run that succeeds replaces both, and no temporary file is left behind.
        rows = [with_mathlib(row("T", "theorem", [], []), ["M.a"], [], type_direct=["M.a"]),
                credited("M.a", "theorem", [], [])]
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            dump, names = folder / "dump.jsonl", folder / "names.txt"
            output, registry_file = folder / "out" / "lean-dependencies.json", folder / "registry.json"
            names.write_text("M.a\tMathlib.T\n")
            output.parent.mkdir()
            for path in (output, registry_file):
                path.write_text("earlier\n")

            errors = io.StringIO()

            def run(dumped: list[dict], **patches) -> int:
                dump.write_text("".join(json.dumps(r) + "\n" for r in framed(dumped)))
                errors.seek(0)
                errors.truncate()
                with patch.object(extract, "article_manifest", lambda: {"T"}), \
                        patch.object(extract, "article_aliases", dict), \
                        patch.object(extract, "mathlib_revision", lambda: PIN), \
                        patch("sys.argv", ["extract", str(dump), str(output), "--registry", str(registry_file),
                                           "--names", str(names)]), \
                        redirect_stderr(errors), redirect_stdout(io.StringIO()):
                    if patches:
                        with patch.object(extract, "registry", **patches), self.assertRaises(RuntimeError):
                            extract.main()
                        return -1
                    return extract.main()

            def outputs() -> dict[str, str]:
                return {path.relative_to(folder).as_posix(): path.read_text() for path in folder.rglob("*")
                        if path.is_file() and path not in (dump, names)}

            run(rows, side_effect=RuntimeError("the registry fails"))
            self.assertEqual(outputs(), {"out/lean-dependencies.json": "earlier\n", "registry.json": "earlier\n"})
            # The registry cannot take its place once the article dependencies have: the run fails, and both are as
            # they were.
            real_replace = Path.replace
            calls = []

            def failing_second(path: Path, target):
                calls.append(target)
                if len(calls) == 2:
                    raise OSError(errno.EIO, "injected", str(target))
                return real_replace(path, target)

            with patch.object(Path, "replace", failing_second):
                self.assertEqual(run(rows), 1)
            self.assertEqual(outputs(), {"out/lean-dependencies.json": "earlier\n", "registry.json": "earlier\n"})
            # And putting the article dependencies back fails too: the run says the outputs may be mixed and where
            # their earlier bytes are kept, never that they are as they were.
            real_os_replace = os.replace
            calls.clear()

            def failing_undo(source, target):
                if str(source).endswith(".previous"):
                    raise OSError(errno.EIO, "undo")
                return real_os_replace(source, target)

            with patch.object(Path, "replace", failing_second), patch.object(extract.os, "replace", failing_undo):
                self.assertEqual(run(rows), 1)
            kept = sorted(Path(directory).rglob("*.previous"))
            self.assertEqual([path.read_text() for path in kept], ["earlier\n"])
            self.assertIn(f"putting the earlier outputs back failed too, so they may be new and old mixed: their "
                          f"earlier bytes are kept in {kept[0]}", errors.getvalue())
            self.assertNotIn("as they were", errors.getvalue())
            kept[0].replace(output)  # as a person would put it back
            self.assertEqual(outputs(), {"out/lean-dependencies.json": "earlier\n", "registry.json": "earlier\n"})
            self.assertEqual(run([rows[0], {**rows[1], "mathlib_value": "M.a"}]), 1)
            self.assertEqual(outputs(), {"out/lean-dependencies.json": "earlier\n", "registry.json": "earlier\n"})
            self.assertEqual(run(rows), 0)
            written = outputs()
            self.assertEqual(sorted(written), ["out/lean-dependencies.json", "registry.json"])
            self.assertEqual(json.loads(written["registry.json"])["bridges"],
                             {"T": {"statement": ["M.a"], "proof": []}})
            self.assertIn("T", json.loads(written["out/lean-dependencies.json"])["articles"])

    def test_a_credited_name_s_row_must_be_one_lean_could_write(self) -> None:
        # Rows for credited names, each well typed, that no environment gives: a kind the dump does not write (the
        # display name `definition`), a theorem's kind on a row that lists what a body states, a theorem marked a
        # structure or whose type is no proposition, an empty module, a found row marked missing as well, a
        # missing row that says the name is the project's when the dump has no row for it, or not when it has, or
        # that the list did not give its module when it did. Each is refused before anything is written; a credited
        # name of the project, missing from Mathlib beside its project row, is no contradiction.
        source = with_mathlib(row("T", "theorem", [], []), ["M.a"], [], type_direct=["M.a"])
        a, d = credited("M.a", "theorem", [], []), credited("M.d", "def", ["M.a"], ["M.a"], ["M.a"])
        gone = {"name": "M.gone", "registered": True, "missing": True, "module_given": True}
        about = "the dump's row for the credited name"
        cases = {
            "a display kind": ([a, {**d, "kind": "definition"}, gone],
                               f"{about} M.d has no kind of declaration the dump writes"),
            "a theorem's kind beside a body's statement": (
                [a, {**d, "kind": "theorem", "proposition": True}, gone],
                f"{about} M.d lists `mathlib_state`, but the value of a theorem is no part of its statement"),
            "a theorem marked a structure": ([{**a, "structure": True}, d, gone],
                                             f"{about} M.a is a structure but no inductive type"),
            "a theorem that is no proposition": ([{**a, "proposition": False}, d, gone],
                                                 f"{about} M.a is a theorem whose type is not a proposition"),
            "an empty module": ([{**a, "module": ""}, d, gone], f"{about} M.a names no Mathlib module"),
            "a module outside Mathlib": ([{**a, "module": "MathlibExt.T"}, d, gone],
                                         f"{about} M.a names no Mathlib module"),
            "found and missing": ([{**a, "missing": True, "module_given": True}, d, gone], f"{about} M.a is malformed"),
            "a project the dump has no row for": ([a, d, {**gone, "project": True}],
                                                  f"{about} M.gone says the name is a constant of the project, which "
                                                  "the dump's own rows do not"),
        }
        for case, (registered, message) in cases.items():
            with self.subTest(case=case):
                status, errors, written = extract_files([source], {"T"}, registered=registered)
                self.assertEqual((status, written), (1, INPUTS))
                self.assertIn(message, errors)
        # A missing name the list gave a module for, whose row says it did not.
        status, errors, written = extract_files([source], {"T"}, registered=[a, d, {**gone, "module_given": False}],
                                                names_text="M.a\tMathlib.T\nM.d\tMathlib.T\nM.gone\tMathlib.T\n")
        self.assertEqual((status, written), (1, INPUTS))
        self.assertIn(f"{about} M.gone says the names list did not give its module, but the list does", errors)
        # T, credited as Mathlib's, is a constant of the project: its missing row must say so, and then stands beside
        # T's own row.
        twin = {"name": "T", "registered": True, "missing": True, "module_given": True}
        status, errors, written = extract_files([source], {"T"}, registered=[a, twin])
        self.assertEqual((status, written), (1, INPUTS))
        self.assertIn(f"{about} T does not say the name is a constant of the project, which the dump's own rows do",
                      errors)
        self.assertEqual(extract_files([source], {"T"}, registered=[a, {**twin, "project": True}])[0::2], (0, OUTPUTS))
        # A project row of a kind the dump does not write, or a theorem's row that lists what a body states.
        for broken, message in (({**source, "kind": "lemma"}, "the dump's row for T has no kind of declaration the "
                                                               "dump writes"),
                                ({**source, "mathlib_state": []}, "the dump's row for T lists `mathlib_state`, but the "
                                                                  "value of a theorem is no part of its statement")):
            status, errors, written = extract_files([broken], {"T"}, registered=[a])
            self.assertEqual((status, written), (1, INPUTS))
            self.assertIn(message, errors)

    def test_a_dump_made_with_a_names_list_is_one_whole_stream(self) -> None:
        # One header first, one footer `"end": true` last with whole-number counts, and rows between them: a second
        # header or footer (one an older format, one with wrong counts), a footer that says `"end": false` or comes
        # before the rows, a line that is both, an empty value, a `registered` that is not true, or counts written as
        # Booleans are each refused before anything is written. A dump made without a names list still passes over
        # empty values, as it always did.
        source = with_mathlib(row("T", "theorem", [], []), ["M.a"], [], type_direct=["M.a"])
        a = credited("M.a", "theorem", [], [])
        header, end = framed([source, a])[0], framed([source, a])[-1]
        old = {**header, "format": 4}
        cases = {
            "an older header before the current one": ([old, header, source, a, end], "is a second header or footer"),
            "a footer with wrong counts before the right one": (
                [header, source, a, {**end, "rows": 7}, end], "is a second header or footer"),
            "a footer that says it is no end": ([header, source, a, {**end, "end": False}], "is cut or mixed"),
            "a footer before the rows": ([header, end, source, a], "does not open with its header and close with its "
                                                                   "footer"),
            "a line both header and footer": ([{**header, **end}, source, a, end], "does not open with its header and "
                                                                                 "close with its footer"),
            "counts written as Booleans": ([header, source, a, {**end, "rows": True, "names": True}],
                                           "is cut or mixed"),
            "a registered that is not true": ([header, source, {**a, "registered": "false"}, end], "is no row"),
        }
        for nonrow in (None, False, 0, [], {}, ""):
            cases[f"the empty value {nonrow!r}"] = ([header, source, nonrow, a, end], "line 3 of the dump is no row")
        for case, (lines, message) in cases.items():
            with self.subTest(case=case):
                status, errors, written = extract_files([], {"T"}, registered=[], frame=lambda _: lines,
                                                        names_text="M.a\tMathlib.T\n")
                self.assertEqual((status, written), (1, INPUTS))
                self.assertIn(message, errors)
        self.assertEqual(extract_files([], {"T"}, registered=[], frame=lambda _: [header, source, a, end],
                                       names_text="M.a\tMathlib.T\n")[0::2], (0, OUTPUTS))
        self.assertEqual(run_extract([row("T", "theorem", [], []), None, {}, row("A", "def", [], [])], ["T"]),
                         run_extract([row("T", "theorem", [], []), row("A", "def", [], [])], ["T"]))

    def test_an_output_that_cannot_take_its_place_undoes_the_others(self) -> None:
        # Both outputs are written, but the second cannot take its output's place: the first, which did, is undone,
        # put back to its earlier bytes when it had some and removed when it had none, so both are new or both as
        # they were, and no temporary file or kept copy is left.
        real_replace = Path.replace

        def failing_second(path: Path, target):
            failing_second.calls += 1
            if failing_second.calls == 2:
                raise OSError(errno.EIO, "injected", str(target))
            return real_replace(path, target)

        for earlier in (True, False):
            with self.subTest(earlier=earlier), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                first, second = folder / "out" / "first.json", folder / "second.json"
                if earlier:
                    first.parent.mkdir()
                    first.write_text("earlier first\n")
                    second.write_text("earlier second\n")
                failing_second.calls = 0
                with patch.object(Path, "replace", failing_second), self.assertRaises(OSError):
                    extract.write_whole({first: "new first\n", second: "new second\n"})
                left = {path.relative_to(folder).as_posix(): path.read_text() for path in folder.rglob("*")
                        if path.is_file()}
                self.assertEqual(left, {"out/first.json": "earlier first\n", "second.json": "earlier second\n"}
                                 if earlier else {})
        with tempfile.TemporaryDirectory() as directory:
            # A destination that is there but is no regular file (a folder) is refused before anything is written.
            folder = Path(directory)
            first, second = folder / "first.json", folder / "second.json"
            first.write_text("earlier first\n")
            second.mkdir()
            with self.assertRaises(ValueError):
                extract.write_whole({first: "new first\n", second: "new second\n"})
            self.assertEqual(sorted(path.name for path in folder.iterdir()), ["first.json", "second.json"])
            self.assertEqual(first.read_text(), "earlier first\n")
        # Were the undoing to fail too, the kept copy of the earlier output stays beside it, for a person to put back.
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            first, second = folder / "first.json", folder / "second.json"
            first.write_text("earlier first\n")
            failing_second.calls = 0
            real_os_replace = os.replace

            def failing_undo(source, target):
                if str(source).endswith(".previous"):
                    raise OSError(errno.EIO, "undo")
                return real_os_replace(source, target)

            with patch.object(Path, "replace", failing_second), patch.object(extract.os, "replace", failing_undo), \
                    self.assertRaises(extract.UndoError) as raised:
                extract.write_whole({first: "new first\n", second: "new second\n"})
            kept = [path for path in folder.iterdir() if path.name.endswith(".previous")]
            self.assertEqual([path.read_text() for path in kept], ["earlier first\n"])
            self.assertEqual(raised.exception.kept, {first: kept[0]})
        # The ordinary case: both replaced, nothing left beside them.
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            first, second = folder / "first.json", folder / "second.json"
            first.write_text("earlier first\n")
            extract.write_whole({first: "new first\n", second: "new second\n"})
            self.assertEqual({path.name: path.read_text() for path in folder.iterdir()},
                             {"first.json": "new first\n", "second.json": "new second\n"})

    def test_two_outputs_that_are_one_file_are_refused_before_anything_is_written(self) -> None:
        # OUTPUT.json and REGISTRY.json one file, by the same path, another spelling of it, a symbolic link or a hard
        # link, or an output that is an input; or an output that is itself a symbolic link, dangling or not, which
        # installing would replace by a regular file: the extractor refuses before it reads or writes anything, and
        # write_whole refuses them too. A file that happens to have a staging-like name beside an output is left alone.
        rows = [with_mathlib(row("T", "theorem", [], []), [], []), credited("M.a", "theorem", [], [])]
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            dump, names = folder / "dump.jsonl", folder / "names.txt"
            dump.write_text("".join(json.dumps(r) + "\n" for r in framed(rows)))
            names.write_text("M.a\tMathlib.T\n")
            target = folder / "deps.json"
            target.write_text("earlier\n")
            (folder / "alias.json").symlink_to(target)
            (folder / "dangling.json").symlink_to(folder / "nowhere.json")
            os.link(target, folder / "hard.json")
            os.link(dump, folder / "dump-hard.jsonl")
            same, link = "are one file", "is a symbolic link"
            cases = ((target, target, same), (target, folder / "out" / ".." / "deps.json", same),
                     (target, folder / "hard.json", same), (target, folder / "dump-hard.jsonl", same),
                     (target, dump, same), (names, folder / "r.json", same),
                     (folder / "alias.json", folder / "r.json", link), (target, folder / "dangling.json", link))
            before = {path.name: (path.is_symlink(), path.read_bytes() if path.exists() else None)
                      for path in folder.iterdir()}
            for output, registry_file, message in cases:
                with self.subTest(output=output.name, registry=registry_file.name), \
                        patch.object(extract, "article_manifest", lambda: {"T"}), \
                        patch.object(extract, "article_aliases", dict), \
                        patch.object(extract, "mathlib_revision", lambda: PIN), \
                        patch("sys.argv", ["extract", str(dump), str(output), "--registry", str(registry_file),
                                           "--names", str(names)]), \
                        redirect_stderr(io.StringIO()) as errors, redirect_stdout(io.StringIO()):
                    self.assertEqual(extract.main(), 2)
                    self.assertIn(message, errors.getvalue())
                    self.assertEqual({path.name: (path.is_symlink(), path.read_bytes() if path.exists() else None)
                                      for path in folder.iterdir()}, before)
            for outputs in ({target: "new\n", folder / "alias.json": "new\n"},
                            {target: "new\n", folder / "hard.json": "new\n"},
                            {folder / "alias.json": "new\n", folder / "r.json": "new\n"},
                            {folder / "dangling.json": "new\n", folder / "r.json": "new\n"}):
                with self.subTest(outputs=sorted(path.name for path in outputs)), self.assertRaises(ValueError):
                    extract.write_whole(outputs)
                self.assertEqual({path.name: (path.is_symlink(), path.read_bytes() if path.exists() else None)
                                  for path in folder.iterdir()}, before)
            # Staging takes a name no file has.
            bystander = folder / ".deps.json.partial"
            bystander.write_text("someone else's\n")
            extract.write_whole({target: "new\n", folder / "registry.json": "new registry\n"})
            self.assertEqual((target.read_text(), bystander.read_text()), ("new\n", "someone else's\n"))
            self.assertEqual(sorted(path.name for path in folder.iterdir()),
                             [".deps.json.partial", "alias.json", "dangling.json", "deps.json", "dump-hard.jsonl",
                              "dump.jsonl", "hard.json", "names.txt", "registry.json"])

    def test_a_file_that_cannot_be_written_leaves_every_output_as_it_was(self) -> None:
        # The second output cannot be written (its folder is a file): the first keeps its earlier bytes, and no
        # temporary file is left.
        with tempfile.TemporaryDirectory() as directory:
            first, blocker = Path(directory) / "first.json", Path(directory) / "blocker"
            first.write_text("earlier\n")
            blocker.write_text("a file\n")
            with self.assertRaises(OSError):
                extract.write_whole({first: "new\n", blocker / "second.json": "new\n"})
            self.assertEqual(sorted(path.name for path in Path(directory).iterdir()), ["blocker", "first.json"])
            self.assertEqual(first.read_text(), "earlier\n")

    def test_a_found_declaration_without_its_proposition_flag_is_refused(self) -> None:
        rows = [with_mathlib(row("T", "theorem", [], []), [], []), credited("M.a", "def", [], [], [])]
        del rows[1]["proposition"]
        run_registry(rows, ["T"], status=1)

    def test_a_proof_through_a_hidden_constant_reaches_what_its_type_uses(self) -> None:
        # T's proof uses the hidden theorem H, whose type uses a Mathlib theorem whose proof uses M.r: the dump
        # lists M.r among what H's type reaches through all uses, not through what it states. T's proof reaches M.r
        # only through H, so it gives no bridge (BridgeConvention).
        rows = [{**with_mathlib(row("H", "theorem", [], []), [], []), "mathlib_type_used": ["M.r"]},
                with_mathlib(row("T", "theorem", [], ["H"]), [], []),
                credited("M.r", "theorem", [], [])]
        _, registry = run_registry(rows, ["T"])
        self.assertEqual((registry["bridges"], registry["left_out"]), ({}, {"T": {"statement": [], "proof": ["M.r"]}}))

    def test_a_credited_definition_has_no_proof_edges(self) -> None:
        rows = [with_mathlib(row("T", "theorem", [], []), [], []), credited("M.b", "theorem", [], []),
                credited("M.a", "def", [], ["M.b"], [])]
        _, registry = run_registry(rows, ["T"])
        self.assertEqual(registry["mathlib"]["M.a"], {"module": "Mathlib.T", "kind": "def", "proposition": False,
                                                       "statement": [], "proof": []})

    def test_an_article_stops_the_way_to_a_bridge(self) -> None:
        # T uses the article A, which uses M.space: T's bridge is A's, not T's own.
        rows = [with_mathlib(row("A", "def", [], []), ["M.space"], [], type_direct=["M.space"]),
                with_mathlib(row("T", "theorem", ["A"], []), [], []), credited("M.space", "def", [], [])]
        _, registry = run_registry(rows, ["A", "T"])
        self.assertEqual(sorted(registry["bridges"]), ["A"])



class BridgeConvention(unittest.TestCase):
    """An article bridges only to a credited declaration its statement or its proof names itself: the dump's
    `mathlib_type_direct` and, for a definition's body or an inductive type's constructors, `mathlib_value_direct`
    for a statement; `mathlib_value_direct` for a proof. A bridge's kind is decided first, a statement one when the
    statement reaches the declaration at all; one reached only through other constants (the project's ones no page
    credits, or Mathlib's) is listed under `left_out`, by kind, and no page gets it."""

    def registry(self, rows: list[dict], articles: list[str]) -> dict:
        with redirect_stdout(io.StringIO()):
            return run_registry(rows, articles)[1]

    def test_a_statement_bridge_through_another_constant_is_dropped(self) -> None:
        # T's type names M.d itself, and reaches M.s through a Mathlib constant no page credits (the dump's
        # `mathlib_type`) and M.h through the project's definition H, which is no article.
        rows = [with_mathlib(row("H", "def", [], []), ["M.h"], [], []),
                with_mathlib(row("T", "theorem", ["H"], []), ["M.d", "M.s"], [], type_direct=["M.d"]),
                *(credited(name, "def", [], [], []) for name in ("M.d", "M.h", "M.s"))]
        found = self.registry(rows, ["T"])
        self.assertEqual((found["bridges"], found["left_out"]),
                         ({"T": {"statement": ["M.d"], "proof": []}},
                          {"T": {"statement": ["M.h", "M.s"], "proof": []}}))

    def test_a_definition_names_in_its_body_what_it_states(self) -> None:
        # D's body names M.b itself, and reaches M.c only through another constant: part of what D states, so M.b is
        # a statement bridge and M.c one left out.
        rows = [with_mathlib(row("D", "def", [], []), [], ["M.b", "M.c"], ["M.b", "M.c"], direct=["M.b"]),
                credited("M.b", "def", [], [], []), credited("M.c", "def", [], [], [])]
        found = self.registry(rows, ["D"])
        self.assertEqual((found["bridges"], found["left_out"]),
                         ({"D": {"statement": ["M.b"], "proof": []}}, {"D": {"statement": ["M.c"], "proof": []}}))

    def test_a_proof_bridge_through_another_constant_is_dropped(self) -> None:
        # T's proof reaches M.p through a Mathlib constant no page credits, and M.q through the project's theorem H,
        # which is no article and whose proof names M.q itself: T's proof names neither, so neither is a bridge.
        rows = [with_mathlib(row("H", "theorem", [], []), [], ["M.q"], direct=["M.q"]),
                with_mathlib(row("T", "theorem", [], ["H"]), [], ["M.p"]),
                credited("M.p", "theorem", [], []), credited("M.q", "theorem", [], [])]
        found = self.registry(rows, ["T"])
        self.assertEqual((found["bridges"], found["left_out"]), ({}, {"T": {"statement": [], "proof": ["M.p", "M.q"]}}))

    def test_a_bridge_through_a_duplicate_is_its_article_s(self) -> None:
        # C's type names M.space itself; its duplicate c, the same result, names M.space in its type and M.fubini in
        # its proof. A's statement uses c and the hidden definition h, whose statement reaches M.measure, and A's proof
        # uses c and names M.space itself. A depends on C, whose bridge M.space is: what c reaches neither takes
        # M.space for A's statement, which names it not, from A's own proof bridge, nor counts again for A as left
        # out. What h reaches stays left out, as A names none of it.
        rows = [with_mathlib(row("C", "theorem", [], []), ["M.space"], [], type_direct=["M.space"]),
                with_mathlib(row("c", "theorem", [], []), ["M.space"], ["M.fubini"], direct=["M.fubini"],
                             type_direct=["M.space"]),
                with_mathlib(row("h", "def", [], []), ["M.measure"], [], [], type_direct=["M.measure"]),
                with_mathlib(row("A", "theorem", ["c", "h"], ["c"]), [], ["M.space"], direct=["M.space"]),
                *(credited(name, "theorem", [], []) for name in ("M.fubini", "M.measure", "M.space"))]
        with redirect_stdout(io.StringIO()):
            output, found = run_registry(rows, ["C", "A"], duplicates={"c": "C"})
        self.assertEqual(output["articles"]["A"]["statement"], ["C"])
        # The registry records which duplicates its edges count as their articles.
        self.assertEqual(found["inputs"]["aliases_sha256"], hashlib.sha256(b'[["C",["c"]]]').hexdigest())
        self.assertEqual(found["bridges"], {"A": {"statement": [], "proof": ["M.space"]},
                                            "C": {"statement": ["M.space"], "proof": []}})
        self.assertEqual(found["left_out"], {"A": {"statement": ["M.measure"], "proof": []}})
        # Unlisted, c's statement takes M.space for A's statement: A keeps no bridge, and all c reaches is left out.
        with redirect_stdout(io.StringIO()):
            _, found = run_registry(rows, ["C", "A"])
        self.assertEqual(found["inputs"]["aliases_sha256"], hashlib.sha256(b"[]").hexdigest())
        self.assertEqual(found["bridges"], {"C": {"statement": ["M.space"], "proof": []}})
        self.assertEqual(found["left_out"], {"A": {"statement": ["M.measure", "M.space"], "proof": ["M.fubini"]}})

    def test_an_article_bridges_to_what_its_own_duplicate_names(self) -> None:
        # C states and proves its result through its duplicate c, whose type names M.space and whose proof names
        # M.fubini: c is part of C, so C bridges to both, by kind, and leaves none out. When C's proof reaches its
        # duplicate only through the hidden theorem h, C's proof names neither: what it reaches through h is left out.
        duplicate = with_mathlib(row("c", "theorem", [], []), ["M.space"], ["M.fubini"], direct=["M.fubini"],
                                 type_direct=["M.space"])
        mathlib = [credited(name, "theorem", [], []) for name in ("M.fubini", "M.space")]
        rows = [duplicate, with_mathlib(row("C", "theorem", ["c"], ["c"]), [], []), *mathlib]
        with redirect_stdout(io.StringIO()):
            _, found = run_registry(rows, ["C"], duplicates={"c": "C"})
        self.assertEqual((found["bridges"], found["left_out"]),
                         ({"C": {"statement": ["M.space"], "proof": ["M.fubini"]}}, {}))
        rows = [duplicate, with_mathlib(row("h", "theorem", [], ["c"]), [], []),
                with_mathlib(row("C", "theorem", [], ["h"]), [], []), *mathlib]
        with redirect_stdout(io.StringIO()):
            _, found = run_registry(rows, ["C"], duplicates={"c": "C"})
        self.assertEqual((found["bridges"], found["left_out"]),
                         ({}, {"C": {"statement": [], "proof": ["M.fubini", "M.space"]}}))

    def test_only_a_duplicate_the_article_names_itself_names_for_it(self) -> None:
        # C lists c and d as duplicates. C names c, c names d, and d's type names M.s and its proof M.p: C reaches both
        # through c, but names neither, so both are left out, by kind. When C names d itself as well, it bridges to
        # each, once.
        mathlib = [credited(name, "theorem", [], []) for name in ("M.p", "M.s")]
        duplicates = [with_mathlib(row("c", "theorem", ["d"], ["d"]), [], []),
                      with_mathlib(row("d", "theorem", [], []), ["M.s"], ["M.p"], direct=["M.p"], type_direct=["M.s"])]
        for named, bridges, left_out in ((["c"], {}, {"C": {"statement": ["M.s"], "proof": ["M.p"]}}),
                                         (["c", "d"], {"C": {"statement": ["M.s"], "proof": ["M.p"]}}, {})):
            with self.subTest(named=named):
                rows = [with_mathlib(row("C", "theorem", named, named), [], []), *duplicates, *mathlib]
                with redirect_stdout(io.StringIO()):
                    _, found = run_registry(rows, ["C"], duplicates={"c": "C", "d": "C"})
                self.assertEqual((found["bridges"], found["left_out"]), (bridges, left_out))

    def test_the_registry_records_the_duplicates_lists_it_was_made_for(self) -> None:
        # C's proof uses the hidden theorem h, which names M itself. Listed as C's duplicate, h is part of C, and M
        # becomes a proof bridge, while the extraction stays byte for byte the same, its digest with it. The registry
        # records the lists it was made for, as the rows give them (sync_wiki.listed_duplicates), in a format of its
        # own, so that a consumer can refuse it after a `duplicates` edit (sync_wiki.registry_problems).
        rows = [with_mathlib(row("C", "theorem", [], ["h"]), [], []),
                with_mathlib(row("h", "theorem", [], []), [], ["M"], direct=["M"]), credited("M", "theorem", [], [])]
        with redirect_stdout(io.StringIO()):
            unlisted, before = run_registry(rows, ["C"])
            listed, after = run_registry(rows, ["C"], duplicates={"h": "C"})
        self.assertEqual(unlisted, listed)
        self.assertEqual(before["inputs"]["extraction_sha256"], after["inputs"]["extraction_sha256"])
        self.assertEqual(((before["bridges"], before["left_out"]), (after["bridges"], after["left_out"])),
                         (({}, {"C": {"statement": [], "proof": ["M"]}}),
                          ({"C": {"statement": [], "proof": ["M"]}}, {})))
        self.assertEqual((before["inputs"]["aliases_sha256"], after["inputs"]["aliases_sha256"]),
                         (hashlib.sha256(b"[]").hexdigest(), hashlib.sha256(b'[["C",["h"]]]').hexdigest()))
        self.assertEqual((before["inputs"]["format"], extract.REGISTRY_FORMAT), (6, 6))
        self.assertNotEqual(extract.REGISTRY_FORMAT, extract.DUMP_FORMAT["format"])

    def test_the_duplicates_digest_spells_each_list_one_way_only(self) -> None:
        # One `name<TAB>article` line per duplicate let a tab and a line feed in a name, or in an article, pass for the
        # separators: each pair below gave the same lines, so a registry made for one list passed for the other. The
        # digest hashes compact JSON instead, each character past ASCII escaped, so any strings at all encode.
        lines = lambda aliases: "".join(f"{name}\t{article}\n" for name, article in sorted(aliases.items()))
        for first, second in (({"a": "C", "b": "C"}, {"a\tC\nb": "C"}), ({"a": "C", "b": "C"}, {"a": "C\nb\tC"})):
            with self.subTest(second=second):
                self.assertEqual(lines(first), lines(second))
                self.assertNotEqual(extract.aliases_digest(first), extract.aliases_digest(second))
        self.assertEqual(extract.aliases_digest({"d": "C", "c": "C", "\u03b1\ud800": "E"}),
                         hashlib.sha256(b'[["C",["c","d"]],["E",["\\u03b1\\ud800"]]]').hexdigest())

    def test_a_duplicate_whose_article_is_gone_gives_no_bridge(self) -> None:
        # The Lean deleted C, whose row lists c as a duplicate; c's type names M.space and its proof M.fubini. A uses
        # only c: the way stops there, so A neither bridges to them nor leaves them out. The registry's inputs record
        # the list the rows give, whatever the Lean has.
        rows = [with_mathlib(row("c", "theorem", [], []), ["M.space"], ["M.fubini"], direct=["M.fubini"],
                             type_direct=["M.space"]),
                with_mathlib(row("A", "theorem", ["c"], ["c"]), [], []),
                *(credited(name, "theorem", [], []) for name in ("M.fubini", "M.space"))]
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            output, found = run_registry(rows, ["C", "A"], duplicates={"c": "C"}, declared={"c", "A"})
        self.assertEqual(output["articles"]["A"], {"module": "MathlibExt.T", "statement": [], "proof": []})
        self.assertEqual((found["bridges"], found["left_out"]), ({}, {}))
        self.assertEqual(found["inputs"]["aliases_sha256"], hashlib.sha256(b'[["C",["c"]]]').hexdigest())
        # Unlisted, c is a hidden theorem: A reaches through it what its proof names.
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            _, found = run_registry(rows, ["C", "A"])
        self.assertEqual(found["left_out"], {"A": {"statement": ["M.space"], "proof": ["M.fubini"]}})

    def test_direct_statement_and_proof_bridges_are_kept(self) -> None:
        # T's type names M.s itself; its proof names M.d and M.s itself and reaches M.p only through another constant.
        # M.s is then one statement bridge, M.d a proof bridge, and M.p no bridge.
        rows = [with_mathlib(row("T", "theorem", [], []), ["M.s"], ["M.d", "M.p", "M.s"], direct=["M.d", "M.s"],
                             type_direct=["M.s"]),
                *(credited(name, "theorem", [], []) for name in ("M.d", "M.p", "M.s"))]
        with redirect_stdout(io.StringIO()) as printed:
            _, found = run_registry(rows, ["T"])
        self.assertEqual((found["bridges"], found["left_out"]),
                         ({"T": {"statement": ["M.s"], "proof": ["M.d"]}}, {"T": {"statement": [], "proof": ["M.p"]}}))
        self.assertIn("2 bridge edges (1 statement, 1 proof), 1 more reached only through other constants left out "
                      "(0 statement, 1 proof)", printed.getvalue())
        self.assertNotIn("bridge_rule", found["inputs"])


class QuotedArticleNames(unittest.TestCase):
    def run_join(self, rows: list[dict], articles: set[str], *, lean_sources: dict[str, str],
                 duplicates: dict[str, str] | None = None, registered: list[dict] | None = None,
                 index_error: OSError | None = None, expect_no_join: bool = False,
                 toolchain: str | None = "leanprover/lean4:v4.36.0"
                 ) -> tuple[int, bytes, bytes, str]:
        # Use the real pinned source scanner (and ordinary module paths), not a normalization mock.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            if toolchain is not None:
                (root / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
            for path, source in lean_sources.items():
                file = root / path
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text(source, encoding="utf-8")
            dump, output, registry, names = (root / label for label in ("dump", "output", "registry", "names"))
            payload = rows if registered is None else framed(rows + registered)
            dump.write_text("".join(json.dumps(record) + "\n" for record in payload), encoding="utf-8")
            output.write_bytes(b"original output")
            registry.write_bytes(b"original registry")
            argv = ["extract", str(dump), str(output)]
            if registered is not None:
                names.write_text("".join(record["name"] + "\n" for record in registered), encoding="utf-8")
                argv += ["--registry", str(registry), "--names", str(names)]
            index = extract.lean_index
            with patch.object(extract, "article_manifest", return_value=articles), \
                    patch.object(extract, "article_aliases", return_value=duplicates or {}), \
                    patch.object(extract, "mathlib_revision", return_value=PIN), \
                    patch.object(extract, "ROOT", root), \
                    patch.object(extract, "BLUEPRINT", root / "blueprint"), \
                    patch.object(extract, "lean_index", wraps=index, side_effect=index_error) as source_index, \
                    patch.object(extract, "join_missing_quoted_articles",
                                 wraps=extract.join_missing_quoted_articles) as join, \
                    patch("sys.argv", argv), redirect_stderr(io.StringIO()) as errors, redirect_stdout(io.StringIO()):
                status = extract.main()
                if expect_no_join:
                    join.assert_not_called()
                    source_index.assert_not_called()
            return status, output.read_bytes(), registry.read_bytes(), errors.getvalue()

    def test_only_authored_quotes_can_fall_back(self) -> None:
        sources = {"MathlibExt/T.lean": "namespace A\ndef x := 0\nend A\n"}
        quoted = row("A.«x»", "def", [], [])
        for payload in ([quoted], [quoted, row("A.x", "theorem", [], [])]):
            with self.subTest(exact=len(payload) == 2):
                status, out, _, errors = self.run_join(payload, {"A.x"}, lean_sources=sources, expect_no_join=True)
                self.assertEqual(status, 0)
                got = json.loads(out)
                self.assertEqual(set(got["articles"]), {"A.x"} if len(payload) == 2 else set())
                self.assertEqual(got["missing_articles"]["unprefixed"], [] if len(payload) == 2 else ["A.x"])
                self.assertEqual("A.x" in errors, len(payload) == 1)

    def test_stock_exact_quoted_and_private_resolution_take_precedence(self) -> None:
        source = {"MathlibExt/T.lean": "namespace A\ndef «x» := 0\nend A\n"}
        quoted = "A.«x»"
        for exact in (quoted, "_private.MathlibExt.T.0." + quoted):
            with self.subTest(exact=exact):
                payload = [row("A.x", "def", ["Canonical"], []), row(exact, "def", ["Exact"], []),
                           row("Canonical", "def", [], []), row("Exact", "def", [], [])]
                payload[1]["private"] = exact != quoted
                status, out, _, errors = self.run_join(payload, {quoted, "Exact", "Canonical"},
                                                      lean_sources=source, expect_no_join=True)
                self.assertEqual((status, errors), (0, ""))
                self.assertEqual(json.loads(out)["articles"][quoted]["statement"], ["Exact"])

    def test_renderer_exception_is_not_a_source_equivalence(self) -> None:
        # For both names the pinned Lean renderer suppresses escaping at `_inaccessible`.
        first, second = "A.«b.c»._inaccessible", "A.b.«c»._inaccessible"
        source = {"MathlibExt/T.lean": f"def {first} := 0\ndef {second} := 1\n"}
        status, out, _, errors = self.run_join([row("A.b.c._inaccessible", "def", ["Unrelated"], [])],
                                              {second}, lean_sources=source)
        self.assertEqual(status, 0)
        self.assertEqual(json.loads(out)["articles"], {})
        self.assertEqual(json.loads(out)["missing_articles"]["unprefixed"], [second])
        self.assertIn(second, errors)
        self.assertIsNone(extract.compiled_spelling(first))
        self.assertIsNone(extract.compiled_spelling(second))

    def test_preexisting_dangling_project_references_refuse_before_writes(self) -> None:
        source = {"MathlibExt/T.lean": "def A.«x» := 0\n"}
        quoted = "A.«x»"
        for field in ("type", "value"):
            with self.subTest(field=field):
                consumer = row("Consumer", "theorem", [], [])
                consumer[field] = [quoted]
                rows = [with_mathlib(record, [], []) for record in [row("A.x", "def", [], []), consumer]]
                status, out, registry, errors = self.run_join(rows, {quoted, "Consumer"}, lean_sources=source,
                                                             registered=[])
                self.assertEqual((status, out, registry), (1, b"original output", b"original registry"))
                self.assertIn(f"dangling {field} reference", errors)

    def test_ordinary_fallback_preserves_both_dependency_directions_and_registry(self) -> None:
        raw, quoted = "A.x", "A.«x»"
        source = {"MathlibExt/T.lean": "def A.«x» := 0\n"}
        payload = [with_mathlib(row(raw, "def", ["Index"], []), ["M.fact"], [], type_direct=["M.fact"]),
                   with_mathlib(row("Index", "def", [], []), [], []),
                   with_mathlib(row("Consumer", "theorem", [raw], []), [], [])]
        status, out, registry, errors = self.run_join(payload, {quoted, "Index", "Consumer"}, lean_sources=source,
                                                     registered=[credited("M.fact", "theorem", [], [])])
        self.assertEqual((status, errors), (0, ""))
        articles = json.loads(out)["articles"]
        self.assertEqual(articles[quoted]["statement"], ["Index"])
        self.assertEqual(articles["Consumer"]["statement"], [quoted])
        self.assertNotIn(raw, articles)
        payload = json.loads(registry)
        self.assertEqual(payload["bridges"][quoted]["statement"], ["M.fact"])
        self.assertNotIn(raw, payload["bridges"])
        self.assertEqual(payload["inputs"]["extraction_sha256"], hashlib.sha256(out).hexdigest())

    def test_no_general_name_decoder(self) -> None:
        self.assertEqual(extract.compiled_spelling("CategoryTheory.«prefix»"), "CategoryTheory.prefix")
        self.assertEqual(extract.compiled_spelling("«A».«x2».y_z"), "A.x2.y_z")
        for name in ("A.x", "A.«b.c»", "A.«with space»", "A.«1»", "A.«»", "A.«α»", "«A».1",
                     "A.«foo'»", "A.«x!»", "A.«b«c»", "A.«x»,y", "A.«x", "A.x»", "A..«x»", "A.«x».\n",
                     "_root_.A.«x»", "«_root_».A.«x»", "A.«x»._inaccessible", "A.«x✝»", "A.«x»._hyg"):
            with self.subTest(name=name):
                self.assertIsNone(extract.compiled_spelling(name))

    def test_competing_article_or_source_claims_refuse_before_writes(self) -> None:
        raw, quoted, competing = "A.x", "A.«x»", "«A».x"
        source = {"MathlibExt/T.lean": "def A.«x» := 0\n"}
        cases = [({quoted, raw}, [raw], source, "article"),
                 ({quoted, competing}, [raw, competing], source, "article"),
                 ({quoted}, [raw, competing], source, "compiled"),
                 ({quoted}, [raw], {**source, "MathlibExt/U.lean": "def A.x := 1\n"}, "source")]
        for articles, names, lean_sources, reason in cases:
            with self.subTest(reason=reason):
                status, out, registry, errors = self.run_join([row(name, "def", [], []) for name in names], articles,
                                                             lean_sources=lean_sources)
                self.assertEqual((status, out, registry), (1, b"original output", b"original registry"))
                self.assertIn(f"competing {reason}", errors)

    def test_overlap_wrong_owner_or_private_row_refuses_before_writes(self) -> None:
        raw, quoted = "A.x", "A.«x»"
        source = {"MathlibExt/T.lean": "def A.«x» := 0\n"}
        normal = with_mathlib(row(raw, "def", [], []), [], [])
        cases = [([normal], {"Twin": quoted}, [], source, "duplicate or registry"),
                 ([normal], {}, [{"name": raw, "registered": True, "missing": True,
                                  "module_given": False, "project": True}], source, "duplicate or registry"),
                 ([normal], {}, [], {"MathlibExt/U.lean": "def A.«x» := 0\n"}, "unique public source owner"),
                 ([{**normal, "private": True}], {}, [], source, "unique public source owner"),
                 ([normal, {**normal, "name": "_private.MathlibExt.T.0.A.x", "private": True}], {}, [], source,
                  "private row")]
        for rows, duplicates, registered, lean_sources, reason in cases:
            with self.subTest(reason=reason):
                status, out, registry, errors = self.run_join(rows, {quoted}, lean_sources=lean_sources,
                                                             duplicates=duplicates, registered=registered)
                self.assertEqual((status, out, registry), (1, b"original output", b"original registry"))
                self.assertIn(reason, errors)

    def test_fallback_requires_the_pinned_lean_toolchain(self) -> None:
        quoted = "A.«x»"
        source = {"MathlibExt/T.lean": "def A.«x» := 0\n"}
        for toolchain in (None, "leanprover/lean4:v4.37.0"):
            with self.subTest(toolchain=toolchain):
                status, out, _, errors = self.run_join([row("A.x", "def", [], [])], {quoted},
                                                       lean_sources=source, toolchain=toolchain)
                self.assertEqual(status, 0)
                self.assertEqual(json.loads(out)["missing_articles"]["unprefixed"], [quoted])
                self.assertIn(quoted, errors)

    def test_missing_target_remains_missing_and_index_error_is_safe(self) -> None:
        from scripts import sync_wiki
        from autoform_cli.lean import LeanSourceError

        quoted = "A.«x»"
        source = {"MathlibExt/T.lean": "def A.«x» := 0\n"}
        status, out, _, _ = self.run_join([], {quoted}, lean_sources=source)
        self.assertEqual(status, 0)
        self.assertEqual(sync_wiki.uncompiled_articles(json.loads(out), SimpleNamespace(declarations={quoted})),
                         [quoted])
        status, out, registry, errors = self.run_join([row("A.x", "def", [], [])], {quoted}, lean_sources=source,
                                                     index_error=LeanSourceError("MathlibExt/T.lean changed"))
        self.assertEqual((status, out, registry), (1, b"original output", b"original registry"))
        self.assertEqual(errors, "error: Lean sources could not be indexed: MathlibExt/T.lean changed\n")


if __name__ == "__main__":
    unittest.main()
