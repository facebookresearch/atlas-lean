"""The Mathlib layer of the graph: which constants are nodes, and which edges connect them."""

from __future__ import annotations

import gzip
import io
import json
import tempfile
import unittest
from contextlib import ExitStack, redirect_stderr, redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from scripts import extract_mathlib_graph as graph
from scripts import extract_v2_lean_dependencies as v2


def row(name: str, kind: str = "theorem", type_uses=(), value_uses=(), module: str = "Mathlib.T", **extra) -> dict:
    """A dump row with the defaults of a plain public declaration."""
    base = {"name": name, "module": module, "kind": kind, "private": False, "aux": None, "instance": False,
            "class": False, "structure": False, "projection": None, "parent_projection": None,
            "deprecated": None, "reducibility": "semireducible", "unsafe": False, "meta": False,
            "prop": kind == "theorem", "head": None, "ctors": None, "mutual": None, "doc": None, "line": 1,
            "name_line": 1, "to_additive": None, "to_dual": None, "simp": False, "type_meta": [],
            "signature": f"{name} : P", "type": list(type_uses), "value": list(value_uses)}
    base.update(extra)
    return base


def write_dump(directory: Path, rows: list[dict], name: str = "dump.jsonl.gz") -> Path:
    path = directory / name
    graph.write_jsonl_gz(path, rows)
    return path


def run_graph(rows: list[dict]) -> tuple[dict, list[dict], dict]:
    with tempfile.TemporaryDirectory() as directory:
        dump = write_dump(Path(directory), rows)
        out = Path(directory) / "out"
        with patch("sys.stdout"):
            assert graph.main(["graph", str(dump), str(out)]) == 0
        nodes = {node["name"]: node for node in graph.read_jsonl(out / "nodes.jsonl.gz")}
        edges = list(graph.read_jsonl(out / "edges.jsonl.gz"))
        meta = json.loads((out / "graph-meta.json").read_text())
    return nodes, edges, meta


def targets(edges: list[dict], source: str, kind: str) -> list[str]:
    return sorted(edge["target"] for edge in edges if edge["source"] == source and edge["kind"] == kind)


def edge(edges: list[dict], source: str, target: str) -> dict:
    (found,) = [e for e in edges if e["source"] == source and e["target"] == target]
    return found


class Rules(unittest.TestCase):
    def test_each_rule_names_what_it_removes(self) -> None:
        cases = {
            "excluded_module": [row("a", module="Mathlib.Tactic.Ring.Basic"), row("b", module="Mathlib.Tactic"),
                                row("c", module="Mathlib.Init"), row("d", module="Mathlib.Util.Notation3")],
            "private": [row("_private.Mathlib.T.0.helper", private=True)],
            "lean:internal": [row("foo._proof_1", aux="internal")],
            "lean:aux_recursor": [row("Foo.casesOn", "def", aux="aux_recursor")],
            "constructor": [row("Foo.mk", "constructor")],
            "generated": [row("Foo.mk.injEq", line=None)],
            "deprecated": [row("old", deprecated={"new": "new", "since": "2026-01-01"})],
            "metaprogramming": [row("Foo.«term_∘_»", "def", meta=True), row("Mathlib.Meta.NormNum.isNat_foo"),
                                row("Expr.instAdd", "def", type_meta=["Lean.Expr"]),
                                row("Ring.toGrindRing", "def", instance=True, head="Lean.Grind.Ring"),
                                row("Foo.instRepr", "def", instance=True, head="Repr")],
            "data_field": [row("Norm.norm", "def", prop=False,
                               projection={"structure": "Norm", "field": "norm", "subobject": False,
                                           "from_class": True})],
        }
        for rule, rows in cases.items():
            for case in rows:
                with self.subTest(rule=rule, name=case["name"]):
                    self.assertEqual(graph.removal_rule(case), rule)
        for module in ("Mathlib.TacticExtra", "Mathlib.Initial", "Mathlib.Topology.Basic"):
            self.assertEqual(graph.removal_rule(row("x", module=module)), graph.NODE)

    def test_mathematics_that_mentions_lean_namespaces_stays(self) -> None:
        # A statement may use `•` through Lean's `grind` classes, or carry a proof term from Aesop.
        for case in (row("BitVec.toFin_nsmul", type_meta=["Lean.Grind.NatModule.nsmul"]),
                     row("asEmptyCone_π_app", type_meta=["Aesop.BuiltinRules.pEmpty_false"])):
            self.assertEqual(graph.removal_rule(case), graph.NODE)

    def test_node_kinds(self) -> None:
        field = {"structure": "Semigroup", "field": "mul_assoc", "subobject": False, "from_class": True}
        parent = {"structure": "RingHom", "field": "toMonoidHom", "subobject": True, "from_class": False}
        cases = {
            "instance": row("Nat.instCommRing", "def", instance=True, reducibility="instance_reducible"),
            "field": row("Semigroup.mul_assoc", projection=field),
            "class": row("Group", "inductive", **{"class": True, "structure": True}),
            "structure": row("Subgroup", "inductive", structure=True),
            "inductive": row("Relation.ReflTransGen", "inductive"),
            "abbreviation": row("Set.Icc'", "def", reducibility="reducible"),
            "definition": row("Nat.Prime", "def"),
            "theorem": row("Nat.prime_two"),
        }
        for kind, case in cases.items():
            with self.subTest(kind=kind):
                self.assertEqual(graph.removal_rule(case), graph.NODE)
                self.assertEqual(graph.node_kind(case), kind)
        # A structure's parent projection is a definition in its own right, and a class's is an instance.
        structure_parent = row("RingHom.toMonoidHom", "def", prop=False, projection=parent,
                               parent_projection="RingHom")
        class_parent = row("Ring.toSemiring", "def", prop=False, instance=True, parent_projection="Ring",
                           projection={**parent, "structure": "Ring", "from_class": True})
        self.assertEqual((graph.removal_rule(structure_parent), graph.node_kind(structure_parent)),
                         (graph.NODE, "definition"))
        self.assertEqual((graph.removal_rule(class_parent), graph.node_kind(class_parent)), (graph.NODE, "instance"))


class Edges(unittest.TestCase):
    def test_semantics_match_the_v2_extractor(self) -> None:
        # Definitions, inductive types, a theorem's statement and proof, hidden helpers and theorems, an opaque
        # body and a hidden cycle: collapsed onto the same nodes, both extractors give the same edges.
        rows = [
            row("A", "def"), row("B", "def"), row("C", "def"),
            row("h", "theorem", ["A"], ["B"], aux="internal"),
            row("d", "def", [], ["C"], private=True),
            row("o", "opaque", ["A"], ["B"], private=True),
            row("x", "def", ["y", "C"], [], private=True), row("y", "def", ["x"], [], private=True),
            row("T", "theorem", ["h", "d"], ["h", "o", "B"]),
            row("D", "def", ["h"], ["d", "x"]),
            row("S", "inductive", [], ["A", "S"], structure=True),
            row("O", "opaque", ["A"], ["B"]),
            row("Win", "def", [], ["Lose", "A"]), row("Lose", "def", [], ["Win"]),
        ]
        nodes, edges, meta = run_graph(rows)
        with tempfile.TemporaryDirectory() as directory:
            dump = write_dump(Path(directory), rows)
            output = Path(directory) / "v2.json"
            with patch.object(v2, "article_manifest", lambda: set(nodes)), patch.object(v2, "article_aliases", dict), \
                    patch("sys.argv", ["extract", str(dump), str(output)]), patch("sys.stdout"):
                self.assertEqual(v2.main(), 0)
            expected = json.loads(output.read_text())
        for name, entry in expected["articles"].items():
            with self.subTest(name=name):
                self.assertEqual(targets(edges, name, "statement"), entry["statement"])
                self.assertEqual(targets(edges, name, "proof"), entry["proof"])
        self.assertEqual(meta["mutual_groups"], expected["mutual"])
        self.assertEqual(meta["mutual_groups"], [["Lose", "Win"]])

    def test_an_instance_node_stops_statements_from_reaching_its_proof_fields(self) -> None:
        # The instance of a class of data compiles to a definition whose body uses the lemma L as a proof field.
        # A theorem whose statement uses the instance depends on the instance, not on L; the instance's own
        # statement includes its body, so it has no proof edges.
        rows = [row("Monoid", "inductive", **{"class": True}), row("L"),
                row("inst", "def", ["Monoid"], ["L"], instance=True, reducibility="instance_reducible"),
                row("T", "theorem", ["inst"], [])]
        nodes, edges, _ = run_graph(rows)
        self.assertEqual(nodes["inst"]["kind"], "instance")
        self.assertEqual(targets(edges, "T", "statement"), ["inst"])
        self.assertEqual(targets(edges, "inst", "statement"), ["L", "Monoid"])
        self.assertEqual(targets(edges, "inst", "proof"), [])
        self.assertEqual(edge(edges, "inst", "L")["part"], "value")

    def test_an_instance_of_a_proposition_states_its_type_and_has_proof_edges(self) -> None:
        # `instance : Fact (Nat.Prime 2)` compiles to a theorem: the class applied is what it states, and the
        # proof gives proof edges, as for any theorem.
        rows = [row("Fact", "inductive", structure=True), row("Nat.Prime", "def"), row("Nat.prime_two"),
                row("fact_prime_two", "theorem", ["Fact", "Nat.Prime"], ["Nat.prime_two"], instance=True,
                    head="Fact"),
                row("T", "theorem", ["fact_prime_two"], [])]
        nodes, edges, _ = run_graph(rows)
        self.assertEqual((nodes["fact_prime_two"]["kind"], nodes["fact_prime_two"]["lean_kind"]),
                         ("instance", "theorem"))
        self.assertEqual(targets(edges, "fact_prime_two", "statement"), ["Fact", "Nat.Prime"])
        self.assertEqual(targets(edges, "fact_prime_two", "proof"), ["Nat.prime_two"])
        self.assertEqual(targets(edges, "T", "statement"), ["fact_prime_two"])

    def test_a_parent_projection_keeps_the_axioms_it_rebuilds_out_of_statements(self) -> None:
        # `Monoid.toMulOneClass` rebuilds `MulOneClass` from `Monoid`'s fields, axioms included.
        axiom = {"structure": "Monoid", "field": "one_mul", "subobject": False, "from_class": True}
        rows = [row("Monoid", "inductive", **{"class": True}), row("MulOneClass", "inductive", **{"class": True}),
                row("Monoid.one_mul", projection=axiom),
                row("Monoid.toMulOneClass", "def", ["Monoid", "MulOneClass"], ["Monoid.one_mul"], instance=True,
                    parent_projection="Monoid", prop=False),
                row("T", "theorem", ["Monoid.toMulOneClass"], [])]
        nodes, edges, _ = run_graph(rows)
        self.assertEqual(targets(edges, "T", "statement"), ["Monoid.toMulOneClass"])
        # Not a projection function, but a parent projection of `Monoid` all the same.
        self.assertEqual((nodes["Monoid.toMulOneClass"]["projection_of"],
                          nodes["Monoid.toMulOneClass"]["parent_projection"]), ("Monoid", True))

    def test_edges_say_which_part_gives_them_and_what_they_pass_through(self) -> None:
        rows = [row("A", "def"), row("B", "def"), row("h", "def", ["B"], [], aux="internal"),
                row("D", "def", ["A"], ["h", "A"])]
        _, edges, meta = run_graph(rows)
        self.assertEqual(edge(edges, "D", "A"), {"source": "D", "target": "A", "kind": "statement", "part": "type",
                                                 "direct": True, "through": []})
        self.assertEqual(edge(edges, "D", "B"), {"source": "D", "target": "B", "kind": "statement", "part": "value",
                                                 "direct": False, "through": ["lean:internal"]})
        self.assertEqual(meta["only_through"]["statement"], {"lean:internal": 1})

    def test_proofs_reach_through_tactic_lemmas(self) -> None:
        # `ring` leaves lemmas of Mathlib/Tactic in proofs: not nodes, but what they use still counts.
        rows = [row("CommRing", "inductive", **{"class": True}), row("add_comm"),
                row("Mathlib.Tactic.Ring.add_pf", "theorem", ["CommRing"], ["add_comm"], module="Mathlib.Tactic.Ring"),
                row("T", "theorem", ["CommRing"], ["Mathlib.Tactic.Ring.add_pf"])]
        _, edges, _ = run_graph(rows)
        self.assertEqual(targets(edges, "T", "proof"), ["add_comm"])
        self.assertEqual(edge(edges, "T", "add_comm")["through"], ["excluded_module"])

    def test_statement_graph_is_acyclic_after_mutual_groups(self) -> None:
        rows = [row("E", "inductive", [], ["O"]), row("O", "inductive", [], ["E"]), row("T", "theorem", ["E"], ["O"])]
        _, edges, meta = run_graph(rows)
        self.assertEqual(meta["mutual_groups"], [["E", "O"]])
        self.assertEqual((meta["statement_cycles_after_mutual"], meta["cycles_statement_and_proof"]), ([], []))
        self.assertEqual(targets(edges, "E", "statement"), [])

    def test_translation_partners_and_flags(self) -> None:
        rows = [row("mul_one", to_additive="add_zero", simp=True, doc="One is neutral."), row("add_zero"),
                row("le_refl", to_dual="ge_refl"), row("ge_refl")]
        nodes, _, _ = run_graph(rows)
        self.assertEqual((nodes["mul_one"]["additive"], nodes["add_zero"]["multiplicative"]), ("add_zero", "mul_one"))
        self.assertEqual((nodes["le_refl"]["dual"], nodes["ge_refl"]["dual"]), ("ge_refl", "le_refl"))
        self.assertEqual((nodes["mul_one"]["simp"], nodes["mul_one"]["has_doc"], nodes["add_zero"]["has_doc"]),
                         (True, True, False))

    def test_outputs_are_byte_identical_across_runs(self) -> None:
        rows = [row("A", "def"), row("h", "def", ["A"], [], private=True), row("T", "theorem", ["h"], ["A"]),
                row("U", "theorem", ["T"], ["T", "h"])]
        outputs = []
        for order in (rows, list(reversed(rows))):
            with tempfile.TemporaryDirectory() as directory:
                dump = write_dump(Path(directory), order)
                out = Path(directory) / "out"
                with patch("sys.stdout"):
                    graph.main(["graph", str(dump), str(out)])
                outputs.append([(out / f).read_bytes() for f in ("nodes.jsonl.gz", "edges.jsonl.gz")])
        self.assertEqual(outputs[0], outputs[1])
        self.assertEqual(gzip.decompress(outputs[0][1]).count(b"\n"), 3)  # T -> A, U -> T, and U's proof -> A


class Join(unittest.TestCase):
    placements = {
        "Mathlib/Topology": {"to": "Topology/general-topology", "title": "Topological spaces"},
        "Mathlib/Topology/Algebra": {"to": "Topology/topological-groups", "title": "Topological groups"},
        "Mathlib/Topology/Algebra/Ring/Basic": {"to": "Topology/topological-groups", "title": "Topological rings"},
        "Mathlib/Data/Nat": {"exclude": "re-exports"},
        "Mathlib/Data/Nat/Prime": {"to": "NumberTheory/primes-primality", "title": "Prime numbers"},
        "Mathlib": {"exclude": "the root import file"},
    }

    def test_the_committed_taxonomy_places_mathlib_where_a_strict_join_accepts(self) -> None:
        # What `join --strict` reads from scripts/taxonomy.json by default, on the committed file: a PR that changes
        # only the taxonomy skips the Mathlib layer's build, so its unit tests catch what that join would refuse.
        placements = graph.load_placements([graph.TAXONOMY])
        scopes = graph.defined_scopes(graph.read_json_object(graph.TAXONOMY, "taxonomy"), str(graph.TAXONOMY))
        self.assertTrue(scopes)
        unknown = sorted(key for key, entry in placements.items() if "to" in entry and entry["to"] not in scopes)
        self.assertEqual(unknown, [])

    def test_a_module_takes_its_own_key_else_its_nearest_placed_directory(self) -> None:
        cases = {
            "Mathlib/Topology/Algebra/Ring/Basic": "Mathlib/Topology/Algebra/Ring/Basic",
            "Mathlib/Topology/Algebra/Group/Basic": "Mathlib/Topology/Algebra",
            "Mathlib/Topology/Compactness/Compact": "Mathlib/Topology",
            "Mathlib/Data/Nat/Prime/Defs": "Mathlib/Data/Nat/Prime",
            "Mathlib/Data/Nat/Basic": "Mathlib/Data/Nat",
            "Mathlib": "Mathlib",
        }
        for key, placed in cases.items():
            with self.subTest(key=key):
                self.assertEqual(graph.resolve(key, self.placements)[0], placed)
        # The bare root key never stands in for a directory, so a new folder stays visible as unplaced.
        self.assertIsNone(graph.resolve("Mathlib/Algebra/Group/Basic", self.placements))

    def test_resolution_agrees_with_generate_wiki(self) -> None:
        try:
            from scripts import generate_wiki
        except ImportError:  # Autoform is not installed
            self.skipTest("generate_wiki needs autoform_cli")
        for key in ("Mathlib/Topology/Algebra/Ring/Basic", "Mathlib/Topology/Algebra/Group/Basic",
                    "Mathlib/Data/Nat/Prime/Defs", "Mathlib/Data/Nat/Basic", "Mathlib/Topology/Order"):
            with self.subTest(key=key):
                self.assertEqual(graph.resolve(key, self.placements),
                                 generate_wiki.placement(tuple(key.split("/")), self.placements))

    def test_placements_and_exclusions_load_from_taxonomy_shaped_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            taxonomy = Path(directory) / "taxonomy.json"
            taxonomy.write_text(json.dumps({
                "placements": {"MathlibExt/Foo": {"to": "Algebra/x", "title": "An ATLAS topic"},
                               "Mathlib/Order": {"to": "Order/lattices", "title": "Orders"}},
                "mathlib_exclusions": {"Mathlib/Tactic": "tactics"}}))
            proposal = Path(directory) / "proposal.json"
            proposal.write_text(json.dumps({"placements": {"Mathlib/Control": {"exclude": "programming"}}}))
            loaded = graph.load_placements([taxonomy, proposal])
            self.assertEqual(loaded, {"Mathlib/Order": {"to": "Order/lattices", "title": "Orders"},
                                      "Mathlib/Tactic": {"exclude": "tactics"},
                                      "Mathlib/Control": {"exclude": "programming"}})
            clash = Path(directory) / "clash.json"
            clash.write_text(json.dumps({"mathlib_exclusions": {"Mathlib/Order": "not mathematics"}}))
            with self.assertRaisesRegex(SystemExit, "placed and excluded"):
                graph.load_placements([taxonomy, clash])

    def run_join(self, nodes: list[dict], files: dict[str, dict], *args: str) -> tuple[int, dict, dict]:
        """Join *nodes* with the placement files *files* (name -> content); return the exit code, rows, report."""
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            graph.write_jsonl_gz(out / "nodes.jsonl.gz", nodes)
            for name, content in files.items():
                (out / name).write_text(json.dumps(content))
            argv = ["join", *[a.replace("DIR", directory) for a in args], str(out)]
            with patch("sys.stdout"), patch("sys.stderr"):
                code = graph.main(argv + [str(out / name) for name in files if name != "taxonomy.json"])
            topics = {row["name"]: row for row in graph.read_jsonl(out / "topics.jsonl.gz")}
            report = json.loads((out / "join-report.json").read_text())
        return code, topics, report

    taxonomy = {"subjects": {
        "Topology": {"fields": [{"slug": "general-topology", "subfields": []},
                                {"slug": "topological-groups", "subfields": []}]},
        "NumberTheory": {"fields": [{"slug": "primes-primality", "subfields": []}]}}}

    def test_join_reports_placed_excluded_and_unplaced_nodes(self) -> None:
        nodes = [{"name": "Nat.Prime", "key": "Mathlib/Data/Nat/Prime/Defs"},
                 {"name": "Nat.succ_le", "key": "Mathlib/Data/Nat/Basic"},
                 {"name": "Group", "key": "Mathlib/Algebra/Group/Defs"}]
        code, topics, report = self.run_join(
            nodes, {"taxonomy.json": self.taxonomy, "placements.json": {"placements": self.placements}},
            "--strict", "--taxonomy", "DIR/taxonomy.json")
        self.assertEqual(code, 0)  # an unplaced node is reported, never an error
        self.assertEqual(topics["Nat.Prime"], {"name": "Nat.Prime", "key": "Mathlib/Data/Nat/Prime/Defs",
                                               "placement": "Mathlib/Data/Nat/Prime",
                                               "to": "NumberTheory/primes-primality", "title": "Prime numbers"})
        self.assertEqual(topics["Nat.succ_le"]["exclude"], "re-exports")
        self.assertIsNone(topics["Group"]["placement"])
        self.assertEqual(report["nodes"], {"excluded": 1, "placed": 1, "unplaced": 1})
        self.assertEqual(report["unplaced_modules"], ["Mathlib/Algebra/Group/Defs"])
        self.assertIn("Mathlib/Topology", report["keys_matching_no_node"])
        self.assertEqual(report["targets_not_in_taxonomy"], {})

    def test_strict_join_fails_on_a_target_that_names_no_field(self) -> None:
        nodes = [{"name": "Nat.Prime", "key": "Mathlib/Data/Nat/Prime/Defs"}]
        placements = {"placements": {"Mathlib/Data/Nat/Prime": {"to": "NumberTheory/no-such-field", "title": "P"},
                                     "Mathlib/Order": {"to": "Order/lattices", "title": "Orders"}}}
        files = {"taxonomy.json": self.taxonomy, "placements.json": placements}
        expected = {"NumberTheory/no-such-field": ["Mathlib/Data/Nat/Prime"], "Order/lattices": ["Mathlib/Order"]}
        code, _, report = self.run_join(nodes, files, "--taxonomy", "DIR/taxonomy.json")
        self.assertEqual((code, report["targets_not_in_taxonomy"], report["strict"]), (0, expected, False))
        code, _, report = self.run_join(nodes, files, "--strict", "--taxonomy", "DIR/taxonomy.json")
        self.assertEqual((code, report["targets_not_in_taxonomy"], report["strict"]), (1, expected, True))

    def test_proposals_add_the_fields_and_subfields_they_create(self) -> None:
        nodes = [{"name": "Lattice", "key": "Mathlib/Order/Lattice"},
                 {"name": "Filter", "key": "Mathlib/Order/Filter/Basic"}]
        proposal = {
            "placements": {"Mathlib/Order": {"to": "Order/lattices", "title": "Lattices"},
                           "Mathlib/Order/Filter": {"to": "Topology/general-topology/filters", "title": "Filters"}},
            "new_fields": [{"subject": "Order", "after": None,
                            "field": {"slug": "lattices", "title": "Lattices", "description": "", "msc": [],
                                      "subfields": []}}],
            "new_subfields": [{"subject": "Topology", "field": "general-topology", "after": None,
                               "subfield": {"slug": "filters", "title": "Filters", "description": ""}}]}
        code, topics, report = self.run_join(
            nodes, {"taxonomy.json": self.taxonomy, "proposal.json": proposal}, "--strict", "--taxonomy",
            "DIR/taxonomy.json")
        self.assertEqual((code, report["targets_not_in_taxonomy"]), (0, {}))
        self.assertEqual(topics["Filter"]["to"], "Topology/general-topology/filters")

    def test_join_refuses_inputs_it_cannot_check(self) -> None:
        nodes = [{"name": "Nat.Prime", "key": "Mathlib/Data/Nat/Prime/Defs"}]
        good = {"placements": {"Mathlib/Data/Nat/Prime": {"to": "NumberTheory/primes-primality", "title": "P"}}}
        cases = {
            "no such taxonomy": ({"placements.json": good}, "no such taxonomy"),
            "a taxonomy without fields": ({"taxonomy.json": {"subjects": {}}, "placements.json": good},
                                          "defines no fields"),
            "a value without a title": ({"taxonomy.json": self.taxonomy, "placements.json": {
                "placements": {"Mathlib/Data": {"to": "NumberTheory/primes-primality"}}}}, "expected"),
            "a target without a field": ({"taxonomy.json": self.taxonomy, "placements.json": {
                "placements": {"Mathlib/Data": {"to": "NumberTheory", "title": "Numbers"}}}}, "expected"),
            "an empty reason": ({"taxonomy.json": self.taxonomy, "placements.json": {
                "mathlib_exclusions": {"Mathlib/Tactic": ""}}}, "expected"),
            "an exclusion of another library": ({"taxonomy.json": self.taxonomy, "placements.json": {
                "mathlib_exclusions": {"MathlibExt/Foo": "not Mathlib"}}}, "not a Mathlib"),
            "a malformed key": ({"taxonomy.json": self.taxonomy, "placements.json": {
                "placements": {"Mathlib//Data": {"to": "NumberTheory/primes-primality", "title": "P"}}}},
                "not a module or directory key"),
            "a malformed proposal": ({"taxonomy.json": self.taxonomy, "placements.json": {
                **good, "new_fields": [{"subject": "Order"}]}}, "malformed"),
        }
        for case, (files, message) in cases.items():
            with self.subTest(case=case), self.assertRaisesRegex(SystemExit, message):
                self.run_join(nodes, files, "--strict", "--taxonomy", "DIR/taxonomy.json")


class Bridge(unittest.TestCase):
    def test_articles_reach_mathlib_nodes_through_hidden_constants_of_both_libraries(self) -> None:
        mathlib = [row("Group", "inductive", **{"class": True}), row("mul_comm"), row("Nat.Prime", "def"),
                   row("_private.Mathlib.T.0.aux", "theorem", ["Nat.Prime"], ["mul_comm"], private=True)]
        atlas = [row("MathlibExt.helper", "def", ["Group"], [], module="MathlibExt.A"),
                 row("MathlibExt.D", "def", ["MathlibExt.helper"], [], module="MathlibExt.A"),
                 row("MathlibExt.T", "theorem", ["MathlibExt.D", "_private.Mathlib.T.0.aux"],
                     ["_private.Mathlib.T.0.aux"], module="MathlibExt.A")]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            mathlib_dump = write_dump(root, mathlib, "mathlib.jsonl.gz")
            atlas_dump = write_dump(root, atlas, "v2.jsonl.gz")
            articles = root / "articles.txt"
            articles.write_text("MathlibExt.D\nMathlibExt.T\n")
            # The v2 extractor's view of the same build: only the ATLAS edges.
            v2_dump = write_dump(root, [{**r, "type": [u for u in r["type"] if u.startswith("MathlibExt")],
                                         "value": [u for u in r["value"] if u.startswith("MathlibExt")]}
                                        for r in atlas], "v2-only.jsonl.gz")
            v2_output = root / "lean-dependencies.json"
            with patch.object(v2, "article_manifest", lambda: {"MathlibExt.D", "MathlibExt.T"}), \
                    patch.object(v2, "article_aliases", dict), \
                    patch("sys.argv", ["extract", str(v2_dump), str(v2_output)]), patch("sys.stdout"):
                self.assertEqual(v2.main(), 0)
            with patch("sys.stdout"):
                self.assertEqual(graph.main(["bridge", str(atlas_dump), str(root / "out"), "--mathlib-dump",
                                             str(mathlib_dump), "--articles", str(articles),
                                             "--check-v2", str(v2_output)]), 0)
            bridge = list(graph.read_jsonl(root / "out" / "bridge-edges.jsonl.gz"))
            meta = json.loads((root / "out" / "bridge-meta.json").read_text())
        found = sorted((e["source"], e["target"], e["kind"], tuple(e["through"])) for e in bridge)
        self.assertEqual(found, [("MathlibExt.D", "Group", "statement", ("atlas_non_article",)),
                                 ("MathlibExt.T", "Nat.Prime", "statement", ("private",)),
                                 ("MathlibExt.T", "mul_comm", "proof", ("private",))])
        self.assertEqual({e["library"] for e in bridge}, {"MathlibExt"})
        self.assertEqual(meta["v2_agreement"]["articles_differing"], 0)


    def test_a_duplicate_counts_as_its_article_as_in_the_v2_extraction(self) -> None:
        # The annotations list MathlibExt.d as a duplicate of MathlibExt.D: T, whose statement names d, depends on D, as
        # in the v2 extraction, and reaches through d no Mathlib node of its own; the check against that extraction
        # passes.
        mathlib = [row("Group", "inductive", **{"class": True}), row("Monoid", "inductive", **{"class": True})]
        atlas = [row("MathlibExt.D", "def", ["Group"], [], module="MathlibExt.A"),
                 row("MathlibExt.d", "def", ["Monoid"], [], module="MathlibExt.A"),
                 row("MathlibExt.T", "theorem", ["MathlibExt.d"], [], module="MathlibExt.A")]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            v2_dump = write_dump(root, [{**r, "type": [u for u in r["type"] if u.startswith("MathlibExt")],
                                         "value": [u for u in r["value"] if u.startswith("MathlibExt")]}
                                        for r in atlas], "v2-only.jsonl.gz")
            v2_output = root / "lean-dependencies.json"
            # The bridge reads the annotations through its own import of the v2 extractor.
            with patch.object(v2, "article_manifest", lambda: {"MathlibExt.D", "MathlibExt.T"}), \
                    patch.object(v2, "article_aliases", lambda: {"MathlibExt.d": "MathlibExt.D"}), \
                    patch.object(graph.v2, "article_manifest", lambda: {"MathlibExt.D", "MathlibExt.T"}), \
                    patch.object(graph.v2, "article_aliases", lambda: {"MathlibExt.d": "MathlibExt.D"}), \
                    patch("sys.stdout"):
                with patch("sys.argv", ["extract", str(v2_dump), str(v2_output)]):
                    self.assertEqual(v2.main(), 0)
                self.assertEqual(graph.main(["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")), str(root / "out"),
                                             "--mathlib-dump", str(write_dump(root, mathlib, "mathlib.jsonl.gz")),
                                             "--check-v2", str(v2_output)]), 0)
            bridge = list(graph.read_jsonl(root / "out" / "bridge-edges.jsonl.gz"))
            meta = json.loads((root / "out" / "bridge-meta.json").read_text())
            expected = json.loads(v2_output.read_text())["articles"]
        self.assertEqual(expected["MathlibExt.T"]["statement"], ["MathlibExt.D"])
        self.assertEqual(sorted((e["source"], e["target"]) for e in bridge), [("MathlibExt.D", "Group")])
        self.assertEqual(meta["v2_agreement"]["articles_differing"], 0)

    def test_an_article_reaches_what_its_own_duplicate_uses_in_the_bridge_as_in_the_v2_extraction(self) -> None:
        # D states and proves its result through its duplicate d, whose type uses the Mathlib node Group and whose proof
        # uses the page B and the Mathlib node mul_comm: d is part of D, so D's statement uses Group, and its proof
        # mul_comm, directly; its proof depends on B, as in the v2 extraction, and the check against it passes.
        mathlib = [row("Group", "inductive", **{"class": True}), row("mul_comm")]
        atlas = [row("MathlibExt.B", "theorem", module="MathlibExt.A"),
                 row("MathlibExt.d", "theorem", ["Group"], ["MathlibExt.B", "mul_comm"], module="MathlibExt.A"),
                 row("MathlibExt.D", "theorem", ["MathlibExt.d"], ["MathlibExt.d"], module="MathlibExt.A")]
        articles, aliases = {"MathlibExt.B", "MathlibExt.D"}, {"MathlibExt.d": "MathlibExt.D"}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            v2_dump = write_dump(root, [{**r, "type": [u for u in r["type"] if u.startswith("MathlibExt")],
                                         "value": [u for u in r["value"] if u.startswith("MathlibExt")]}
                                        for r in atlas], "v2-only.jsonl.gz")
            v2_output = root / "lean-dependencies.json"
            # The bridge reads the annotations through its own import of the v2 extractor.
            with patch.object(v2, "article_manifest", lambda: set(articles)), \
                    patch.object(v2, "article_aliases", lambda: dict(aliases)), \
                    patch.object(graph.v2, "article_manifest", lambda: set(articles)), \
                    patch.object(graph.v2, "article_aliases", lambda: dict(aliases)), patch("sys.stdout"):
                with patch("sys.argv", ["extract", str(v2_dump), str(v2_output)]):
                    self.assertEqual(v2.main(), 0)
                self.assertEqual(graph.main(["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")), str(root / "out"),
                                             "--mathlib-dump", str(write_dump(root, mathlib, "mathlib.jsonl.gz")),
                                             "--check-v2", str(v2_output)]), 0)
            bridge = list(graph.read_jsonl(root / "out" / "bridge-edges.jsonl.gz"))
            meta = json.loads((root / "out" / "bridge-meta.json").read_text())
            expected = json.loads(v2_output.read_text())["articles"]
        self.assertEqual(expected["MathlibExt.D"], {"module": "MathlibExt.A", "statement": [],
                                                    "proof": ["MathlibExt.B"]})
        self.assertEqual(sorted((e["source"], e["target"], e["kind"], e["direct"]) for e in bridge),
                         [("MathlibExt.D", "Group", "statement", True), ("MathlibExt.D", "mul_comm", "proof", True)])
        self.assertEqual(meta["v2_agreement"]["articles_differing"], 0)

    def test_a_duplicate_reached_through_another_gives_no_direct_edge(self) -> None:
        # D lists d and e as duplicates. D names e, e names d, and d's type uses Group and its proof the page B and
        # mul_comm: D reaches all three, as in the v2 extraction, but Group and mul_comm through d, as through a hidden
        # constant. When D names d itself as well, each is one direct edge. The check against the v2 extraction passes.
        mathlib = [row("Group", "inductive", **{"class": True}), row("mul_comm")]
        articles = {"MathlibExt.B", "MathlibExt.D"}
        aliases = {"MathlibExt.d": "MathlibExt.D", "MathlibExt.e": "MathlibExt.D"}
        for named, direct, through in ((["MathlibExt.e"], False, ("atlas_non_article",)),
                                       (["MathlibExt.e", "MathlibExt.d"], True, ())):
            atlas = [row("MathlibExt.B", "theorem", module="MathlibExt.A"),
                     row("MathlibExt.d", "theorem", ["Group"], ["MathlibExt.B", "mul_comm"], module="MathlibExt.A"),
                     row("MathlibExt.e", "theorem", ["MathlibExt.d"], ["MathlibExt.d"], module="MathlibExt.A"),
                     row("MathlibExt.D", "theorem", named, named, module="MathlibExt.A")]
            with self.subTest(named=named), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                v2_dump = write_dump(root, [{**r, "type": [u for u in r["type"] if u.startswith("MathlibExt")],
                                             "value": [u for u in r["value"] if u.startswith("MathlibExt")]}
                                            for r in atlas], "v2-only.jsonl.gz")
                v2_output = root / "lean-dependencies.json"
                # The bridge reads the annotations through its own import of the v2 extractor.
                with patch.object(v2, "article_manifest", lambda: set(articles)), \
                        patch.object(v2, "article_aliases", lambda: dict(aliases)), \
                        patch.object(graph.v2, "article_manifest", lambda: set(articles)), \
                        patch.object(graph.v2, "article_aliases", lambda: dict(aliases)), patch("sys.stdout"):
                    with patch("sys.argv", ["extract", str(v2_dump), str(v2_output)]):
                        self.assertEqual(v2.main(), 0)
                    self.assertEqual(graph.main(["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")),
                                                 str(root / "out"), "--mathlib-dump",
                                                 str(write_dump(root, mathlib, "mathlib.jsonl.gz")),
                                                 "--check-v2", str(v2_output)]), 0)
                bridge = list(graph.read_jsonl(root / "out" / "bridge-edges.jsonl.gz"))
                expected = json.loads(v2_output.read_text())["articles"]
                self.assertEqual(expected["MathlibExt.D"]["proof"], ["MathlibExt.B"])
                self.assertEqual(sorted((e["source"], e["target"], e["kind"], e["direct"], tuple(e["through"]))
                                        for e in bridge),
                                 [("MathlibExt.D", "Group", "statement", direct, through),
                                  ("MathlibExt.D", "mul_comm", "proof", direct, through)])

    def test_a_listed_duplicate_the_dump_lacks_stops_the_bridge_unless_the_lean_deleted_it(self) -> None:
        # The annotations list c as a duplicate of C, and no article uses c, so comparing edges with the v2 extraction
        # cannot show that the bridge's dump lacks it. While the Lean sources declare c, the dump is incomplete and the
        # bridge refuses it before it writes anything; once the Lean deleted c, it warns and builds.
        for declared, message in (({"C", "c"}, "the wiki lists c as a duplicate of C, but the compiled dependency dump "
                                               "has no row for c, and the Lean sources declare it"),
                                  ({"C"}, "warning: the Lean no longer declares c, which the wiki lists as a duplicate "
                                          "of C")):
            with self.subTest(declared=sorted(declared)), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                expected = root / "lean-dependencies.json"
                expected.write_text(json.dumps({"missing_articles": {}, "mutual": [], "articles": {
                    "C": {"module": "MathlibExt.A", "statement": [], "proof": []}}}))
                arguments = ["bridge", str(write_dump(root, [row("C", module="MathlibExt.A")], "v2.jsonl.gz")),
                             str(root / "out"), "--mathlib-dump", str(write_dump(root, [row("X")], "mathlib.jsonl.gz")),
                             "--check-v2", str(expected)]
                with patch.object(graph.v2, "article_manifest", lambda: {"C"}), \
                        patch.object(graph.v2, "article_aliases", lambda: {"c": "C"}), \
                        patch.object(graph.v2, "lean_index", lambda: SimpleNamespace(declarations=declared)), \
                        redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()) as errors:
                    if "c" in declared:
                        with self.assertRaises(SystemExit) as raised:
                            graph.main(arguments)
                        self.assertIn(message, str(raised.exception))
                        self.assertFalse((root / "out" / "bridge-edges.jsonl.gz").exists())
                    else:
                        self.assertEqual(graph.main(arguments), 0)
                        self.assertIn(message, errors.getvalue())

    def test_each_end_the_bridge_s_dump_lacks_is_judged_on_its_own(self) -> None:
        # As in the v2 extraction: the bridge's dump lacks C and its duplicate c, and the Lean deleted c. While the Lean
        # declares C, which P's proof uses, the bridge refuses the dump before writing, though the v2 extraction it is
        # checked against has the same gap; once the Lean deleted both, it warns and builds.
        for declared, value_uses in (({"MathlibExt.C", "MathlibExt.P"}, ["MathlibExt.C"]), ({"MathlibExt.P"}, [])):
            with self.subTest(declared=sorted(declared)), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                expected = root / "lean-dependencies.json"
                expected.write_text(json.dumps({"missing_articles": {"MathlibExt": ["MathlibExt.C"]}, "mutual": [],
                                                "articles": {"MathlibExt.P": {"module": "MathlibExt.A",
                                                                              "statement": [], "proof": []}}}))
                atlas = [row("MathlibExt.P", "theorem", [], value_uses, module="MathlibExt.A")]
                arguments = ["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")), str(root / "out"),
                             "--mathlib-dump", str(write_dump(root, [row("X")], "mathlib.jsonl.gz")),
                             "--check-v2", str(expected)]
                with patch.object(graph.v2, "article_manifest", lambda: {"MathlibExt.C", "MathlibExt.P"}), \
                        patch.object(graph.v2, "article_aliases", lambda: {"MathlibExt.c": "MathlibExt.C"}), \
                        patch.object(graph.v2, "lean_index", lambda: SimpleNamespace(declarations=declared)), \
                        redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()) as errors:
                    if "MathlibExt.C" in declared:
                        with self.assertRaises(SystemExit) as raised:
                            graph.main(arguments)
                        self.assertIn("the compiled dependency dump has no row for MathlibExt.C, and the Lean sources "
                                      "declare it", str(raised.exception))
                        self.assertFalse((root / "out").exists())
                    else:
                        self.assertEqual(graph.main(arguments), 0)
                        self.assertIn("warning: the Lean no longer declares MathlibExt.c, which the wiki lists as a "
                                      "duplicate of MathlibExt.C, nor MathlibExt.C", errors.getvalue())

    def test_a_duplicate_whose_article_is_gone_reaches_nothing_in_the_bridge(self) -> None:
        # The Lean deleted C, whose row lists c as a duplicate; c's type uses the Mathlib node Group. T, which uses only
        # c, gets no edge through it, to C or to Group, in the bridge as in the v2 extraction, and the two agree.
        mathlib = [row("Group", "inductive", **{"class": True})]
        atlas = [row("MathlibExt.c", "def", ["Group"], [], module="MathlibExt.A"),
                 row("MathlibExt.T", "theorem", ["MathlibExt.c"], [], module="MathlibExt.A")]
        aliases, declared = {"MathlibExt.c": "MathlibExt.C"}, {"MathlibExt.c", "MathlibExt.T"}
        runs = {}
        for form, listed in (("listed", aliases), ("unlisted", {})):
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                v2_dump = write_dump(root, [{**r, "type": [u for u in r["type"] if u.startswith("MathlibExt")]}
                                            for r in atlas], "v2-only.jsonl.gz")
                v2_output = root / "lean-dependencies.json"
                with patch.object(v2, "article_manifest", lambda: {"MathlibExt.C", "MathlibExt.T"}), \
                        patch.object(v2, "article_aliases", lambda: dict(listed)), \
                        patch.object(v2, "lean_index", lambda: SimpleNamespace(declarations=declared)), \
                        patch.object(graph.v2, "article_manifest", lambda: {"MathlibExt.C", "MathlibExt.T"}), \
                        patch.object(graph.v2, "article_aliases", lambda: dict(listed)), \
                        patch.object(graph.v2, "lean_index", lambda: SimpleNamespace(declarations=declared)), \
                        redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()) as errors:
                    with patch("sys.argv", ["extract", str(v2_dump), str(v2_output)]):
                        self.assertEqual(v2.main(), 0)
                    code = graph.main(["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")), str(root / "out"),
                                       "--mathlib-dump", str(write_dump(root, mathlib, "mathlib.jsonl.gz")),
                                       "--check-v2", str(v2_output)])
                runs[form] = (code, json.loads(v2_output.read_text())["articles"]["MathlibExt.T"]["statement"],
                              sorted((e["source"], e["target"])
                                     for e in graph.read_jsonl(root / "out" / "bridge-edges.jsonl.gz")),
                              errors.getvalue().count("warning: the Lean no longer declares MathlibExt.C, whose page "
                                                      "lists MathlibExt.c as a duplicate"))
        self.assertEqual(runs["listed"], (0, [], [], 2))
        self.assertEqual(runs["unlisted"], (0, [], [("MathlibExt.T", "Group")], 0))

    def test_the_bridge_refuses_a_duplicate_it_cannot_count(self) -> None:
        # Two private constants of the duplicate's name, which one name cannot tell apart; with an explicit manifest, a
        # row the dump lacks, which no Lean source can explain, and an article missing from the manifest, though both
        # rows are compiled.
        twin = [{**row(f"_private.MathlibExt.{module}.0.MathlibExt.c", "def", module=f"MathlibExt.{module}"),
                 "private": True} for module in ("A", "B")]
        both = [row("MathlibExt.C", "def", module="MathlibExt.A"), row("MathlibExt.c", "def", module="MathlibExt.A")]
        cases = {
            "two private constants": (twin + [row("MathlibExt.C", "def", module="MathlibExt.A")], False,
                                      "MathlibExt.C\n", "the compiled dependency dump has several private constants "
                                                         "named MathlibExt.c, which one name cannot tell apart: "
                                                         "_private.MathlibExt.A.0.MathlibExt.c, "
                                                         "_private.MathlibExt.B.0.MathlibExt.c"),
            "an explicit manifest's missing row": ([row("MathlibExt.C", "def", module="MathlibExt.A")], True,
                                                   "MathlibExt.C\n", "the compiled dependency dump has no row for "
                                                                     "MathlibExt.c, and nothing here tells whether the "
                                                                     "Lean still declares it"),
            "an article missing from the manifest": (both, True, "MathlibExt.T\n",
                                                     "MathlibExt.C is not among the articles, so a use of MathlibExt.c "
                                                     "could count for no page"),
        }
        for case, (atlas, explicit, articles, message) in cases.items():
            with self.subTest(case=case), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "articles.txt").write_text(articles)
                (root / "aliases.txt").write_text("MathlibExt.c\tMathlibExt.C\n")
                options = ["--articles", str(root / "articles.txt"), "--aliases", str(root / "aliases.txt")]
                with patch.object(graph.v2, "article_manifest", lambda: {"MathlibExt.C"}), \
                        patch.object(graph.v2, "article_aliases", lambda: {"MathlibExt.c": "MathlibExt.C"}), \
                        patch.object(graph.v2, "lean_index", side_effect=AssertionError("read the Lean sources")), \
                        redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as raised:
                    graph.main(["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")), str(root / "out"),
                                "--mathlib-dump", str(write_dump(root, [row("X")], "mathlib.jsonl.gz")),
                                *(options if explicit else [])])
                self.assertIn(f"the wiki lists MathlibExt.c as a duplicate of MathlibExt.C, but {message}",
                              str(raised.exception))
                self.assertFalse((root / "out" / "bridge-edges.jsonl.gz").exists())

    def test_an_explicit_manifest_takes_its_duplicates_from_a_file(self) -> None:
        # T's statement uses c, a duplicate of C. Read from the annotations, or from --articles and --aliases, the
        # duplicates give the v2 extraction's edges, and the same bridge; --articles alone reads none, and no
        # annotation, so T's edge to C is then missing.
        mathlib = [row("Group", "inductive", **{"class": True})]
        atlas = [row("MathlibExt.C", "def", ["Group"], [], module="MathlibExt.A"),
                 row("MathlibExt.c", "def", ["Group"], [], module="MathlibExt.A"),
                 row("MathlibExt.T", "theorem", ["MathlibExt.c"], [], module="MathlibExt.A")]
        aliases = {"MathlibExt.c": "MathlibExt.C"}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            v2_dump = write_dump(root, [{**r, "type": [u for u in r["type"] if u.startswith("MathlibExt")],
                                         "value": [u for u in r["value"] if u.startswith("MathlibExt")]}
                                        for r in atlas], "v2-only.jsonl.gz")
            v2_output = root / "lean-dependencies.json"
            articles, aliases_file = root / "articles.txt", root / "aliases.txt"
            articles.write_text("MathlibExt.C\nMathlibExt.T\n")
            aliases_file.write_text("MathlibExt.c\tMathlibExt.C\n")
            inputs = [str(write_dump(root, atlas, "v2.jsonl.gz")), "--mathlib-dump",
                      str(write_dump(root, mathlib, "mathlib.jsonl.gz")), "--check-v2", str(v2_output)]
            runs = {}
            explicit = ["--articles", str(articles), "--aliases", str(aliases_file)]
            for form, options, read in (("annotations", [], True), ("explicit", explicit, False),
                                        ("articles alone", explicit[:2], False)):
                def stub(value) -> dict:
                    return {"new": value} if read else {"side_effect": AssertionError("read the annotations")}

                with patch.object(graph.v2, "article_manifest", **stub(lambda: {"MathlibExt.C", "MathlibExt.T"})), \
                        patch.object(graph.v2, "article_aliases", **stub(lambda: dict(aliases))), \
                        patch.object(v2, "article_manifest", lambda: {"MathlibExt.C", "MathlibExt.T"}), \
                        patch.object(v2, "article_aliases", lambda: dict(aliases)), \
                        patch("sys.stdout"), patch("sys.stderr"):
                    if not v2_output.exists():
                        with patch("sys.argv", ["extract", str(v2_dump), str(v2_output)]):
                            self.assertEqual(v2.main(), 0)
                    code = graph.main(["bridge", inputs[0], str(root / form), *inputs[1:], *options])
                runs[form] = (code, sorted((e["source"], e["target"], e["direct"])
                                           for e in graph.read_jsonl(root / form / "bridge-edges.jsonl.gz")))
            expected = json.loads(v2_output.read_text())["articles"]
        self.assertEqual(expected["MathlibExt.T"]["statement"], ["MathlibExt.C"])
        self.assertEqual(runs["annotations"], (0, [("MathlibExt.C", "Group", True)]))
        self.assertEqual(runs["explicit"], runs["annotations"])
        self.assertEqual(runs["articles alone"][0], 1)

    def run_bridge_against(self, expected: dict) -> tuple[int, dict]:
        """Run the bridge on two articles, checking it against a v2 extraction whose articles are *expected*."""
        mathlib = [row("Group", "inductive", **{"class": True})]
        atlas = [row("MathlibExt.D", "def", ["Group"], [], module="MathlibExt.A"),
                 row("MathlibExt.T", "theorem", ["MathlibExt.D"], [], module="MathlibExt.A")]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            articles = root / "articles.txt"
            articles.write_text("MathlibExt.D\nMathlibExt.T\n")
            v2_output = root / "lean-dependencies.json"
            v2_output.write_text(json.dumps({"missing_articles": {}, "mutual": [], "articles": expected}))
            with patch("sys.stdout"), patch("sys.stderr"):
                code = graph.main(["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")), str(root / "out"),
                                   "--mathlib-dump", str(write_dump(root, mathlib, "mathlib.jsonl.gz")),
                                   "--articles", str(articles), "--check-v2", str(v2_output)])
            agreement = json.loads((root / "out" / "bridge-meta.json").read_text())["v2_agreement"]
        return code, agreement

    def test_the_v2_check_compares_the_whole_article_set(self) -> None:
        d = {"module": "MathlibExt.A", "statement": [], "proof": []}
        t = {"module": "MathlibExt.A", "statement": ["MathlibExt.D"], "proof": []}
        code, agreement = self.run_bridge_against({"MathlibExt.D": d, "MathlibExt.T": t})
        self.assertEqual((code, agreement["articles_compared"], agreement["missing_articles"],
                          agreement["unexpected_articles"], agreement["articles_differing"]), (0, 2, 0, 0, 0))
        # The v2 extraction has an article the bridge's dump lacks, as when the dump left out a module.
        code, agreement = self.run_bridge_against({"MathlibExt.D": d, "MathlibExt.T": t, "MathlibExt.U": d})
        self.assertEqual((code, agreement["missing_articles"], agreement["missing_examples"]), (1, 1, ["MathlibExt.U"]))
        # The bridge has an article the v2 extraction lacks.
        code, agreement = self.run_bridge_against({"MathlibExt.D": d})
        self.assertEqual((code, agreement["unexpected_articles"], agreement["unexpected_examples"]),
                         (1, 1, ["MathlibExt.T"]))
        # The same articles with other edges.
        code, agreement = self.run_bridge_against({"MathlibExt.D": d, "MathlibExt.T": d})
        self.assertEqual((code, agreement["articles_differing"], agreement["examples"]), (1, 1, ["MathlibExt.T"]))


class QuotedArticles(unittest.TestCase):
    """An article the annotations name with redundant quotes, joined to its compiled row as in the v2 extraction."""

    QUOTED, RAW = "A.«x»", "A.x"
    # The Lean sources test_extract_v2_lean_dependencies.QuotedArticleNames gives the real source scanner.
    SOURCE = {"MathlibExt/T.lean": "def A.«x» := 0\n"}
    MATHLIB = [row("Group", "inductive", **{"class": True}), row("mul_comm")]
    ARTICLES = {QUOTED, "MathlibExt.S", "MathlibExt.P"}
    # Unjoined, A.x is a hidden constant that S and P reach Group and mul_comm through.
    HIDDEN = [("MathlibExt.P", "Group", "proof", ("atlas_non_article",)),
              ("MathlibExt.P", "mul_comm", "proof", ("atlas_non_article",)),
              ("MathlibExt.S", "Group", "statement", ("atlas_non_article",))]
    # Mathlib constants of either spelling, one for each way the Mathlib layer can take a constant.
    CLASSES = {"node": {}, "excluded_module": {"module": "Mathlib.Tactic.Hidden"}, "lean:reserved": {"aux": "reserved"},
               "constructor": {"kind": "constructor"}, "generated": {"line": None},
               "deprecated": {"deprecated": {"new": "A.y", "since": "2026-01-01"}}, "metaprogramming": {"meta": True}}

    def run_bridge(self, atlas: list[dict], articles: set[str], *, lean_sources: dict[str, str] | None = None,
                   aliases: dict[str, str] | None = None, mathlib: list[dict] | None = None,
                   toolchain: str = "leanprover/lean4:v4.36.0", check_v2: bool = True, explicit: bool = False,
                   index_error: OSError | None = None
                   ) -> tuple[int | str, dict | None, list[dict], dict | None, bool]:
        """Run the v2 extraction (with *check_v2*) and the bridge over *atlas*, the annotations giving *articles* and
        *aliases*, the checkout *lean_sources* and *toolchain*: the bridge's exit code, or its SystemExit message, its
        meta and edges, the v2 extraction's articles, and whether the bridge wrote anything."""
        aliases = aliases or {}
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory)
            (root / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
            for path, source in (self.SOURCE if lean_sources is None else lean_sources).items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_text(source, encoding="utf-8")
            project = {r["name"] for r in atlas}
            for module in (v2, graph.v2):  # the test's import of the v2 extractor, and the bridge's own
                stack.enter_context(patch.object(module, "ROOT", root))
                stack.enter_context(patch.object(module, "BLUEPRINT", root / "blueprint"))
                stack.enter_context(patch.object(module, "article_manifest", lambda: set(articles)))
                stack.enter_context(patch.object(module, "article_aliases", lambda: dict(aliases)))
            if explicit:
                for name in ("article_manifest", "article_aliases", "lean_index", "join_missing_quoted_articles"):
                    stack.enter_context(patch.object(graph.v2, name, side_effect=AssertionError(f"called {name}")))
            elif index_error is not None:
                stack.enter_context(patch.object(graph.v2, "lean_index", side_effect=index_error))
            stack.enter_context(redirect_stdout(io.StringIO()))
            stack.enter_context(redirect_stderr(io.StringIO()))
            out = root / "out"
            arguments = ["bridge", str(write_dump(root, atlas, "v2.jsonl.gz")), str(out), "--mathlib-dump",
                         str(write_dump(root, self.MATHLIB if mathlib is None else mathlib, "mathlib.jsonl.gz"))]
            expected = None
            if check_v2:
                # The v2 extractor's view of the same build: only the project's uses.
                v2_rows = [{**r, **{field: [u for u in r[field] if u in project] for field in ("type", "value")}}
                           for r in atlas]
                v2_dump = write_dump(root, v2_rows, "v2-only.jsonl.gz")
                with patch("sys.argv", ["extract", str(v2_dump), str(root / "lean-dependencies.json")]):
                    self.assertEqual(v2.main(), 0)
                expected = json.loads((root / "lean-dependencies.json").read_text())["articles"]
                arguments += ["--check-v2", str(root / "lean-dependencies.json")]
            if explicit:
                (root / "articles.txt").write_text("".join(f"{name}\n" for name in sorted(articles)), encoding="utf-8")
                arguments += ["--articles", str(root / "articles.txt")]
            try:
                code: int | str = graph.main(arguments)
            except SystemExit as error:
                code = str(error)
            wrote = out.exists()
            meta = json.loads((out / "bridge-meta.json").read_text()) if (out / "bridge-meta.json").exists() else None
            edges = list(graph.read_jsonl(out / "bridge-edges.jsonl.gz")) if (out / "bridge-edges.jsonl.gz").exists() \
                else []
        return code, meta, edges, expected, wrote

    def statement_and_proof_rows(self, kind: str = "theorem", module: str = "MathlibExt.T", **extra) -> list[dict]:
        # A.x states with Group and uses mul_comm in its value; S states with it, and P proves with it.
        return [row(self.RAW, kind, ["Group"], ["mul_comm"], module=module, **extra),
                row("MathlibExt.S", "theorem", [self.RAW], [], module="MathlibExt.T"),
                row("MathlibExt.P", "theorem", [], [self.RAW], module="MathlibExt.T")]

    def assert_refused(self, result: tuple, message: str) -> None:
        code, meta, edges, _, wrote = result
        self.assertIsInstance(code, str)
        self.assertIn(message, code)
        self.assertEqual((wrote, meta, edges), (False, None, []))

    def test_a_quoted_article_bridges_and_agrees_with_the_v2_extraction(self) -> None:
        # The v2 extraction joins A.«x» to the row A.x; the bridge must too, or its check against that extraction fails
        # with A.«x» missing. A theorem's value gives proof edges; a definition's value is part of what it states.
        for kind, found in (("theorem", [(self.QUOTED, "Group", "statement", True),
                                         (self.QUOTED, "mul_comm", "proof", True)]),
                            ("def", [(self.QUOTED, "Group", "statement", True),
                                     (self.QUOTED, "mul_comm", "statement", True)])):
            with self.subTest(kind=kind):
                code, meta, edges, expected, _ = self.run_bridge(self.statement_and_proof_rows(kind), self.ARTICLES)
                self.assertEqual((expected["MathlibExt.S"]["statement"], expected["MathlibExt.P"]["proof"]),
                                 ([self.QUOTED], [self.QUOTED]))
                self.assertEqual(code, 0, meta and meta.get("v2_agreement"))
                self.assertEqual(sorted((e["source"], e["target"], e["kind"], e["direct"]) for e in edges), found)
                self.assertEqual({e["library"] for e in edges}, {"MathlibExt"})
                self.assertEqual((meta["articles"], meta["manifest_without_v2_row"], meta["atlas_edges"]), (3, 0, 2))
                agreement = meta["v2_agreement"]
                self.assertEqual((agreement["articles_compared"], agreement["missing_articles"],
                                  agreement["unexpected_articles"], agreement["articles_differing"]), (3, 0, 0, 0))

    def test_the_join_s_checks_stop_the_bridge_before_it_writes(self) -> None:
        source, other = self.SOURCE, {"MathlibExt/U.lean": "def A.«x» := 0\n"}
        rows = self.statement_and_proof_rows()
        quoted_use = row("MathlibExt.Q", "theorem", [self.QUOTED], [], module="MathlibExt.T")
        cases = {
            "wrong source owner": (self.statement_and_proof_rows(module="MathlibExt.Wrong")[:1] + rows[1:], {},
                                   source, f"cannot bind {self.RAW} to the unique public source owner of "
                                           f"{self.QUOTED}"),
            "two source owners": (rows, {}, {**source, **other}, "unique public source owner"),
            "a private row": (self.statement_and_proof_rows(private=True)[:1] + rows[1:], {}, source,
                              "unique public source owner"),
            "a competing source spelling": (rows, {}, {**source, "MathlibExt/U.lean": "def A.x := 1\n"},
                                            "competing source spelling"),
            "a duplicate endpoint": (rows, {"MathlibExt.Twin": self.QUOTED}, source,
                                     "quoted-name fallback overlaps a duplicate or registry endpoint"),
            "a dangling use of the quoted spelling": (rows + [quoted_use], {}, source,
                                                      "MathlibExt.Q has a dangling type reference"),
        }
        for case, (atlas, aliases, lean_sources, message) in cases.items():
            with self.subTest(case=case):
                self.assert_refused(self.run_bridge(atlas, self.ARTICLES, lean_sources=lean_sources, aliases=aliases,
                                                    check_v2=False), message)
        # Both spellings credited: the articles compete.
        self.assert_refused(self.run_bridge(rows, {self.QUOTED, self.RAW}, check_v2=False),
                            f"competing article spellings for {self.RAW}")

    def test_neither_spelling_of_a_joined_article_may_be_a_mathlib_constant(self) -> None:
        # Mathlib's copy of a compiled spelling that is not a node used to be dropped from the v2 rows as a constant
        # realised in both dumps, before the join: the article then lost its row and the bridge wrote without it.
        for spelling in (self.RAW, self.QUOTED):
            for rule, extra in self.CLASSES.items():
                constant = row(spelling, **{"module": "Mathlib.T", **extra})
                self.assertEqual(graph.removal_rule(constant), rule)
                for check_v2 in (False, True):
                    with self.subTest(spelling=spelling, rule=rule, check_v2=check_v2):
                        self.assert_refused(self.run_bridge(self.statement_and_proof_rows(), self.ARTICLES,
                                                            mathlib=self.MATHLIB + [constant], check_v2=check_v2),
                                            f"quoted articles whose compiled or authored names are in the Mathlib "
                                            f"dump: ['{spelling}']")

    def test_a_constant_realised_in_both_dumps_is_still_dropped_beside_a_joined_article(self) -> None:
        # A generated lemma both dumps realise, which P's proof uses, is Mathlib's, as before: P reaches mul_comm
        # through it, and the quoted article still joins and agrees with the v2 extraction.
        shared = "AddMonoidHom.mk.congr_simp"
        realised = row(shared, "theorem", [], ["mul_comm"], aux="reserved")
        atlas = self.statement_and_proof_rows()
        atlas[2] = row("MathlibExt.P", "theorem", [], [self.RAW, shared], module="MathlibExt.T")
        code, meta, edges, _, _ = self.run_bridge(atlas + [{**realised, "module": "MathlibExt.T"}], self.ARTICLES,
                                                  mathlib=self.MATHLIB + [realised])
        self.assertEqual(code, 0, meta and meta.get("v2_agreement"))
        self.assertEqual(meta["realised_in_both_dumps"], [shared])
        self.assertEqual(sorted((e["source"], e["target"], e["kind"]) for e in edges),
                         [(self.QUOTED, "Group", "statement"), (self.QUOTED, "mul_comm", "proof"),
                          ("MathlibExt.P", "mul_comm", "proof")])
        self.assertEqual(meta["v2_agreement"]["missing_articles"], 0)
        self.assertEqual(meta["v2_agreement"]["articles_differing"], 0)

    def test_the_join_needs_the_pinned_toolchain_and_safe_index_errors(self) -> None:
        from autoform_cli.lean import LeanSourceError

        # Under another toolchain neither side joins: both leave A.«x» out, and agree; A.x is then a hidden constant.
        code, meta, edges, expected, _ = self.run_bridge(self.statement_and_proof_rows(), self.ARTICLES,
                                                         toolchain="leanprover/lean4:v4.37.0")
        self.assertEqual((code, sorted(expected), meta["manifest_without_v2_row"]),
                         (0, ["MathlibExt.P", "MathlibExt.S"], 1))
        self.assertEqual(sorted((e["source"], e["target"], e["kind"], tuple(e["through"])) for e in edges),
                         self.HIDDEN)
        self.assert_refused(self.run_bridge(self.statement_and_proof_rows(), self.ARTICLES, check_v2=False,
                                            index_error=LeanSourceError("MathlibExt/T.lean changed")),
                            "Lean sources could not be indexed: MathlibExt/T.lean changed")

    def test_an_explicit_manifest_takes_its_names_as_given_and_reads_no_lean_sources(self) -> None:
        # --articles comes with no Lean sources: the bridge reads neither them nor the annotations, does not join, and
        # its check against the v2 extraction, which the annotations' sources let join, fails with A.«x» missing.
        code, meta, edges, _, _ = self.run_bridge(self.statement_and_proof_rows(), self.ARTICLES, explicit=True)
        self.assertEqual((code, meta["v2_agreement"]["missing_examples"], meta["manifest_without_v2_row"]),
                         (1, [self.QUOTED], 1))
        self.assertEqual(sorted((e["source"], e["target"], e["kind"], tuple(e["through"])) for e in edges),
                         self.HIDDEN)

    def test_exact_ordinary_and_private_articles_need_no_join(self) -> None:
        quoted_row = {**self.statement_and_proof_rows()[0], "name": self.QUOTED}
        private_row = {**quoted_row, "name": f"_private.MathlibExt.T.0.{self.QUOTED}", "private": True}
        for case, first, article in (("exact quoted row", quoted_row, self.QUOTED),
                                     ("published private row", private_row, self.QUOTED),
                                     ("ordinary name", self.statement_and_proof_rows()[0], self.RAW)):
            join_wrapper = patch.object(graph.v2, "join_missing_quoted_articles",
                                        wraps=graph.v2.join_missing_quoted_articles)
            with self.subTest(case=case), join_wrapper as join, \
                    patch.object(graph.v2, "lean_index", wraps=graph.v2.lean_index) as index:
                uses = [{**r, "type": [first["name"] if u == self.RAW else u for u in r["type"]],
                         "value": [first["name"] if u == self.RAW else u for u in r["value"]]}
                        for r in self.statement_and_proof_rows()[1:]]
                code, meta, edges, _, _ = self.run_bridge([first, *uses], {article, "MathlibExt.S", "MathlibExt.P"},
                                                          lean_sources={}, check_v2=False)
                join.assert_not_called()
                index.assert_not_called()
                self.assertEqual((code, meta["articles"]), (0, 3))
                self.assertEqual(sorted((e["source"], e["target"]) for e in edges),
                                 [(article, "Group"), (article, "mul_comm")])


class Stats(unittest.TestCase):
    def test_the_layers_atlas_commit_is_the_v2_dumps(self) -> None:
        # The Mathlib dump depends only on the pins, and the workflow may restore it from a cache made at another
        # commit; the Mathlib pages check the layer's ATLAS commit against the site's.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = root / "out"
            with patch("sys.stdout"):
                self.assertEqual(graph.main(["graph", str(write_dump(root, [row("A", "def")])), str(out)]), 0)
                for name, commit in (("mathlib-dump", "a" * 40), ("v2-mathlib-dump", "b" * 40)):
                    graph.write_json(out / f"{name}-meta.json", {"lean_version": "v", "mathlib_rev": "c" * 40,
                                                                 "atlas_commit": commit, "dump": {"seconds": 1.0}})
                    self.assertEqual(graph.main(["stats", str(out)]), 0)
                    stats = json.loads((out / "stats.json").read_text())
                    self.assertEqual(stats["versions"]["atlas_commit"], commit)
        self.assertEqual(set(stats["seconds"]), {"graph", "mathlib-dump", "v2-mathlib-dump"})

if __name__ == "__main__":
    unittest.main()
