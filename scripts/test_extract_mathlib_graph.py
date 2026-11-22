"""The Mathlib layer of the graph: which constants are nodes, and which edges connect them."""

from __future__ import annotations

import gzip
import json
import tempfile
import unittest
from pathlib import Path
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
            with patch.object(v2, "article_manifest", lambda: set(nodes)), \
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

if __name__ == "__main__":
    unittest.main()
