#!/usr/bin/env python3
"""Tests for scripts/graph_batch.py: the parts on their own, then make, verify and base on a repository of a few files
whose main merges pull requests, with copies of the real scripts. Run with a Python that has Autoform installed."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

if __package__:
    from . import graph_batch as batch
    from . import sync_wiki as sync
else:
    import graph_batch as batch
    import sync_wiki as sync

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent


class Trailers(unittest.TestCase):
    def test_both_trailers_once_each(self) -> None:
        base, through = "a" * 40, "b" * 40
        message = f"Sync the graph\n\nText.\n\nGraph-sync-base: {base}\nGraph-sync-through: {through}\n"
        self.assertEqual(batch.trailers(message), {"Graph-sync-base": base, "Graph-sync-through": through})
        self.assertEqual(batch.trailers(f"Graph-sync-base: {base}\n"), {})
        self.assertEqual(batch.trailers(message + f"Graph-sync-through: {'c' * 40}\n"), {})
        # A short or upper-case commit name is no trailer.
        self.assertEqual(batch.trailers(f"Graph-sync-base: {base[:12]}\nGraph-sync-through: {through}\n"), {})
        self.assertEqual(batch.trailers(f"Graph-sync-base: {base.upper()}\nGraph-sync-through: {through}\n"), {})


class PlaceLines(unittest.TestCase):
    def test_lines_of_a_description(self) -> None:
        body = ("Graph: new\r\nPlace: MathlibExt/A/B -> Algebra/groups\r\n"
                "Not a Place: line\n  Place:   MathlibExt/A/C   ->   Algebra/groups | Group basics  \n")
        self.assertEqual(batch.place_lines(body), ["MathlibExt/A/B -> Algebra/groups",
                                                   "MathlibExt/A/C   ->   Algebra/groups | Group basics"])

    def test_a_module_a_field_and_maybe_a_topic(self) -> None:
        self.assertEqual(batch.parse_place("MathlibExt/Algebra/Rings -> Algebra/groups"),
                         ("MathlibExt/Algebra/Rings", "Algebra/groups", None))
        self.assertEqual(batch.parse_place("MathlibExt/Algebra/Rings -> Algebra/groups/finite | Rings: a | b"),
                         ("MathlibExt/Algebra/Rings", "Algebra/groups/finite", "Rings: a | b"))

    def test_anything_else_is_refused(self) -> None:
        for value in ("MathlibExt/Algebra/Rings Algebra/groups",
                      "MathlibExt/Algebra/Rings ->",
                      "MathlibExt/Algebra/Rings -> Algebra/groups |",
                      "MathlibExt/Algebra/Rings -> Algebra/groups extra words",
                      "Mathlib/Algebra/Group -> Algebra/groups",
                      "MathlibExt/Algebra/Rings.lean -> Algebra/groups",
                      "MathlibExt -> Algebra/groups",
                      "MathlibExt\\Algebra\\Rings -> Algebra/groups",
                      "MathlibExt/Algebra/Rings -> Algebra/groups | " + "T" * 161,
                      "MathlibExt/Algebra/Rings -> Algebra/groups | T\x07"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                batch.parse_place(value)


TAXONOMY_TEXT = ('{\n "schema": "atlas-wiki-taxonomy/v1",\n "subjects": {"Algebra": {"fields": []}},\n'
                 ' "placements": {\n'
                 '  "MathlibExt/B": {"to": "Algebra/groups", "title": "B"},\n'
                 '  "MathlibExt/D": {"to": "Algebra/groups", "title": "D"},\n'
                 '  "MathlibExt/C": {"to": "Algebra/groups", "title": "C"}\n'
                 ' },\n "mathlib_exclusions": {}\n}\n')


class EditPlacements(unittest.TestCase):
    def test_an_entry_goes_after_the_last_one_before_it(self) -> None:
        spot = {"to": "Algebra/groups", "title": "Ç"}
        edited = batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/Ca": spot}, [])
        # After MathlibExt/C, the last entry before it in the file's own order, which is not sorted: one line added,
        # and a comma where a line stopped being the last.
        self.assertEqual(edited, TAXONOMY_TEXT.replace(
            '"title": "C"}\n', '"title": "C"},\n  "MathlibExt/Ca": {"to": "Algebra/groups", "title": "Ç"}\n'))
        # After the greatest module before its own, MathlibExt/D, wherever the file has it, not after the last line
        # whose module sorts before it.
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/E": spot}, []), TAXONOMY_TEXT.replace(
            '"title": "D"},\n', '"title": "D"},\n  "MathlibExt/E": {"to": "Algebra/groups", "title": "Ç"},\n'))
        first = batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/A": spot}, [])
        self.assertEqual(first, TAXONOMY_TEXT.replace(
            ' "placements": {\n', ' "placements": {\n  "MathlibExt/A": {"to": "Algebra/groups", "title": "Ç"},\n'))
        self.assertEqual(json.loads(first)["placements"]["MathlibExt/A"], spot)

    def test_a_dropped_entry_takes_only_its_line(self) -> None:
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {}, ["MathlibExt/D"]),
                         TAXONOMY_TEXT.replace('  "MathlibExt/D": {"to": "Algebra/groups", "title": "D"},\n', ""))
        # The last entry: the one before it loses its comma.
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {}, ["MathlibExt/C"]),
                         TAXONOMY_TEXT.replace('"title": "D"},\n  "MathlibExt/C": {"to": "Algebra/groups", "title": "C"}\n',
                                               '"title": "D"}\n'))
        self.assertEqual(batch.edit_placements(TAXONOMY_TEXT, {}, []), TAXONOMY_TEXT)

    def test_it_refuses_what_it_cannot_do_exactly(self) -> None:
        spot = {"to": "Algebra/groups", "title": "B"}
        with self.assertRaises(ValueError):
            batch.edit_placements(TAXONOMY_TEXT, {"MathlibExt/B": spot}, [])
        with self.assertRaises(ValueError):
            batch.edit_placements(TAXONOMY_TEXT, {}, ["MathlibExt/Z"])
        with self.assertRaises(ValueError):
            batch.edit_placements(TAXONOMY_TEXT.replace('  "MathlibExt/D"', '  "MathlibExt/D" '), {}, [])

    def test_the_committed_taxonomy_is_one_entry_per_line(self) -> None:
        text = (ROOT / "scripts" / "taxonomy.json").read_text(encoding="utf-8")
        self.assertEqual(batch.edit_placements(text, {}, []), text)


class Fields(unittest.TestCase):
    def test_fields_and_subfields(self) -> None:
        taxonomy = {"subjects": {"Algebra": {"fields": [{"slug": "groups", "subfields": [{"slug": "finite"}]},
                                                        {"slug": "rings", "subfields": []}]}}}
        self.assertEqual(batch.fields_of(taxonomy), {"Algebra/groups", "Algebra/groups/finite", "Algebra/rings"})


TAXONOMY = {"schema": "atlas-wiki-taxonomy/v1", "regions": {"Algebra & Number Theory": ["Algebra"]},
            "subjects": {"Algebra": {"title": "Algebra", "description": "Operations.", "fields": [
                {"slug": "groups", "title": "Groups", "description": "Groups.", "subfields": []},
                {"slug": "rings", "title": "Rings", "description": "Rings.", "subfields": []}]}},
            "placements": {"MathlibExt/Algebra/Groups": {"to": "Algebra/groups", "title": "Group basics"},
                           "WantedExt/Algebra/SylowWanted": {"to": "Algebra/groups", "title": "Sylow theorems"}},
            "mathlib_exclusions": {}}
PAGES = {"README.md": "# ATLAS roadmap\n\n## Algebra & Number Theory\n\n- [Algebra](Algebra/README.md)\n",
         "Algebra/README.md": "# Algebra\n\nOperations.\n\n- [Groups](groups/README.md)\n- [Rings](rings/README.md)\n",
         "Algebra/groups/README.md": "# Groups\n\nGroups.\n\n- [Group basics](group-basics/README.md)\n"
                                     "- [Sylow theorems](sylow-theorems/README.md)\n",
         "Algebra/groups/group-basics/README.md": "# Group basics\n\n- [Lagrange](lagrange.md)\n",
         "Algebra/groups/group-basics/lagrange.md": "# Lagrange\n\nThe order of a subgroup divides the order of the group.\n",
         "Algebra/groups/sylow-theorems/README.md": "# Sylow theorems\n\n- [Sylow](sylow.md)\n",
         "Algebra/groups/sylow-theorems/sylow.md": "# Sylow\n\nSylow subgroups exist.\n",
         "Algebra/rings/README.md": "# Rings\n\nRings.\n"}
DECLARATIONS = {"Algebra/groups/group-basics/lagrange.md": "Ext.lagrange", "Algebra/groups/sylow-theorems/sylow.md": "Ext.sylow"}
LEAN = {"MathlibExt/Algebra/Groups.lean": "namespace Ext\n\n/-- The order of a subgroup divides the order of the group. -/\n"
                                         "theorem lagrange : True := trivial\n\nend Ext\n",
        "WantedExt/Algebra/SylowWanted.lean": "namespace Ext\n\n/-- Sylow subgroups exist. -/\ntheorem sylow : True := "
                                              "trivial\n\n/-- Sylow subgroups are conjugate. -/\ntheorem sylow_conj : True := "
                                              "trivial\n\nend Ext\n"}


@unittest.skipUnless(shutil.which("git"), "git is not installed")
class Batches(unittest.TestCase):
    """make, verify and base on a repository whose main merges pull requests as the merge queue does."""

    def setUp(self) -> None:
        self.root = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.root, True)
        for name in ("graph_batch.py", "sync_wiki.py", "generate_wiki.py", "extract_v2_lean_dependencies.py"):
            self.write(f"scripts/{name}", (SCRIPTS / name).read_text())
        self.write("mkdocs.yml", (ROOT / "mkdocs.yml").read_text())
        self.write(".gitignore", "__pycache__/\n")
        self.write("scripts/taxonomy.json", self.taxonomy_text(TAXONOMY))
        for path, text in LEAN.items():
            self.write(path, text)
        rows = []
        for number, (page, text) in enumerate(PAGES.items(), 1):
            self.write(f"blueprint/roadmap/{page}", text)
            row = {"subject": [{"type": "generic", "uri": f"../roadmap/{page}"}], "id": f"af_{number:024x}"}
            if page in DECLARATIONS:
                row["object"] = [{"location": {"declaration": DECLARATIONS[page]}}]
            rows.append(row)
        self.write("blueprint/links/roadmap.jsonl", json.dumps(rows[0]) + "\n")
        self.write("blueprint/links/Algebra.jsonl", "".join(json.dumps(row) + "\n" for row in rows[1:]))
        self.write("blueprint/links/_defaults.json", json.dumps(sync.DEFAULTS) + "\n")
        self.write("scripts/wiki-sync.json", json.dumps({"docstrings": {
            "Ext.lagrange": sync.digest("The order of a subgroup divides the order of the group."),
            "Ext.sylow": sync.digest("Sylow subgroups exist.")}}, indent=0) + "\n")
        self.git("init", "-q", "-b", "main")
        self.base = self.commit("base")
        self.bodies: dict[str, str] = {}

    @staticmethod
    def taxonomy_text(taxonomy: dict) -> str:
        """The taxonomy as the repository writes it: one placement per line."""
        placements = ",\n".join(f"  {json.dumps(key)}: {json.dumps(value)}" for key, value in taxonomy["placements"].items())
        rest = {key: value for key, value in taxonomy.items() if key != "placements"}
        head = json.dumps({key: rest[key] for key in ("schema", "regions", "subjects")}, indent=1)[:-2]
        return f"{head},\n \"placements\": {{\n{placements}\n }},\n \"mathlib_exclusions\": {{}}\n}}\n"

    def write(self, path: str, text: str) -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), "-c", "user.name=t", "-c", "user.email=t@t", *args],
                              check=True, capture_output=True, text=True).stdout.strip()

    def commit(self, message: str) -> str:
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", "HEAD")

    def merge(self, number: int, change, body: str = "Graph: new\n") -> str:
        """Merge a pull request whose branch makes *change*, as the merge queue does: a merge commit on main."""
        self.git("switch", "-q", "-c", f"topic-{number}")
        change()
        self.commit(f"Pull request {number}")
        self.git("switch", "-q", "main")
        self.git("merge", "-q", "--no-ff", "-m", f"Merge pull request #{number} from someone/topic-{number}",
                 f"topic-{number}")
        self.bodies[str(number)] = body
        return self.git("rev-parse", "HEAD")

    def tool(self, *args: str) -> subprocess.CompletedProcess:
        bodies = self.root.parent / f"{self.root.name}-bodies.json"
        bodies.write_text(json.dumps(self.bodies))
        self.addCleanup(bodies.unlink, True)
        extra = ["--bodies", str(bodies)] if args[0] in ("make", "verify") else []
        return subprocess.run([sys.executable, str(self.root / "scripts" / "graph_batch.py"), *args, *extra],
                              cwd=self.root, capture_output=True, text=True)

    def lean_only_merges(self) -> None:
        # A new documented module that nothing places; a proof that moves a wanted statement, with its name, into a new
        # module, whose Place: line names the wanted module's field but no topic; a second one that takes the wanted
        # module's last declaration and deletes it, with no Place: line; and a new module that its Place: line places,
        # beside a line about a module the pull request does not change.
        self.merge(1, lambda: self.write("MathlibExt/Algebra/Fields.lean", "namespace Ext\n\n/-- Fields are rings. -/\n"
                                         "theorem fields : True := trivial\n\n/-- Fields have no zero divisors. -/\n"
                                         "theorem fields_domain : True := trivial\n\nend Ext\n"))
        self.merge(2, lambda: (self.write("MathlibExt/Algebra/Sylow.lean", "namespace Ext\n\n/-- Sylow subgroups exist. -/\n"
                                          "theorem sylow : True := trivial\n\n/-- Sylow counting. -/\ntheorem sylow_count : True "
                                          ":= trivial\n\nend Ext\n"),
                               self.write("WantedExt/Algebra/SylowWanted.lean", "namespace Ext\n\n/-- Sylow subgroups are "
                                          "conjugate. -/\ntheorem sylow_conj : True := trivial\n\nend Ext\n")),
                   "Graph: new\nPlace: MathlibExt/Algebra/Sylow -> Algebra/groups\n")
        self.merge(3, lambda: (self.write("MathlibExt/Algebra/SylowConj.lean", "namespace Ext\n\n/-- Sylow subgroups are "
                                          "conjugate. -/\ntheorem sylow_conj : True := trivial\n\n/-- Conjugates of a Sylow "
                                          "subgroup are Sylow. -/\ntheorem sylow_conj_sylow : True := trivial\n\nend Ext\n"),
                               (self.root / "WantedExt/Algebra/SylowWanted.lean").unlink()))
        self.merge(4, lambda: self.write("MathlibExt/Algebra/Units.lean", "/-!\n# Units of a ring\n-/\n\nnamespace Ext\n\n"
                                         "/-- Units form a group. -/\ntheorem units : True := trivial\n\n/-- Units are not "
                                         "zero. -/\ntheorem units_ne_zero : True := trivial\n\nend Ext\n"),
                   "Graph: new\nPlace: MathlibExt/Algebra/Units -> Algebra/rings\n"
                   "Place: MathlibExt/Algebra/Fields -> Algebra/rings | Not mine\n")

    def test_a_batch_places_syncs_and_checks_what_main_merged(self) -> None:
        self.lean_only_merges()
        head = self.git("rev-parse", "HEAD")
        body = self.root.parent / f"{self.root.name}-body.md"
        self.addCleanup(body.unlink, True)
        result = self.tool("make", "--base", self.base, "--body", str(body))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        commit = self.git("rev-parse", "HEAD")
        self.assertEqual(self.git("rev-parse", "HEAD^"), head)
        message = self.git("log", "-1", "--format=%B")
        self.assertIn(f"Graph-sync-base: {self.base}\nGraph-sync-through: {head}", message)
        changed = self.git("diff", "--name-only", head, commit).splitlines()
        self.assertTrue(all(batch.batch_path(path) for path in changed), changed)
        placements = json.loads((self.root / "scripts/taxonomy.json").read_text())["placements"]
        # The proofs' modules take their wanted statements' place and topic, the deleted module loses its own, the
        # Place: line places its own module, with its heading as topic, and not another pull request's, and the module
        # nothing places stays unplaced.
        self.assertEqual(placements["MathlibExt/Algebra/Sylow"], {"to": "Algebra/groups", "title": "Sylow theorems"})
        self.assertEqual(placements["MathlibExt/Algebra/SylowConj"], {"to": "Algebra/groups", "title": "Sylow theorems"})
        self.assertNotIn("WantedExt/Algebra/SylowWanted", placements)
        self.assertEqual(placements["MathlibExt/Algebra/Units"], {"to": "Algebra/rings", "title": "Units of a ring"})
        self.assertNotIn("MathlibExt/Algebra/Fields", placements)
        roadmap = self.root / "blueprint/roadmap"
        self.assertEqual(sorted(path.name for path in (roadmap / "Algebra/groups/sylow-theorems").iterdir()),
                         ["README.md", "sylow-conj-sylow.md", "sylow-count.md", "sylow.md"])
        self.assertIn("sylow-count.md", (roadmap / "Algebra/groups/sylow-theorems/README.md").read_text())
        self.assertEqual(sorted(path.name for path in (roadmap / "Algebra/rings/units-of-a-ring").iterdir()),
                         ["README.md", "units-ne-zero.md", "units.md"])
        self.assertEqual(sorted(path.name for path in (roadmap / "Algebra/not-yet-classified/fields").iterdir()),
                         ["README.md", "fields-domain.md", "fields.md"])
        text = body.read_text()
        self.assertTrue(text.startswith("Graph: batch\n"), text)
        self.assertIn("| `MathlibExt/Algebra/Sylow` | `Algebra/groups` | Sylow theorems | #2 |", text)
        self.assertIn("| `MathlibExt/Algebra/SylowConj` | `Algebra/groups` | Sylow theorems | "
                      "WantedExt/Algebra/SylowWanted |", text)
        self.assertIn("| `MathlibExt/Algebra/Units` | `Algebra/rings` | Units of a ring | #4 |", text)
        self.assertIn("#4: MathlibExt/Algebra/Fields is left unplaced: the pull request's merge does not change it", text)
        self.assertIn("- `WantedExt/Algebra/SylowWanted`", text)
        # verify agrees, and base names the batch.
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = self.tool("base")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(f"The next batch starts from {head}.", result.stdout)

    def test_the_next_batch_starts_where_the_last_one_ended(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        first = self.git("rev-parse", "HEAD")
        # The batch lands as a pull request, then main merges more Lean.
        self.git("switch", "-q", "-c", "batch-1")
        self.git("switch", "-q", "main")
        self.git("reset", "-q", "--hard", "HEAD^")
        self.git("merge", "-q", "--no-ff", "-m", "Merge pull request #5 from someone/batch-1", "batch-1")
        self.bodies["5"] = "Graph: batch\n"
        self.merge(6, lambda: self.write("MathlibExt/Algebra/Groups.lean", LEAN["MathlibExt/Algebra/Groups.lean"].replace(
            "end Ext", "/-- Cosets partition the group. -/\ntheorem cosets : True := trivial\n\nend Ext")))
        result = self.tool("make")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        message = self.git("log", "-1", "--format=%B")
        self.assertIn(f"Graph-sync-base: {self.git('rev-parse', first + '^')}", message)
        changed = self.git("diff", "--name-only", "HEAD^", "HEAD").splitlines()
        self.assertEqual(sorted(changed), ["blueprint/links/Algebra.jsonl",
                                           "blueprint/roadmap/Algebra/groups/group-basics/README.md",
                                           "blueprint/roadmap/Algebra/groups/group-basics/cosets.md",
                                           "scripts/wiki-sync.json"])
        # Nothing more to do on a main the batch has caught up with.
        self.git("switch", "-q", "-c", "batch-2")
        self.git("switch", "-q", "main")
        self.git("reset", "-q", "--hard", "HEAD^")
        self.git("merge", "-q", "--no-ff", "-m", "Merge pull request #7 from someone/batch-2", "batch-2")
        self.merge(8, lambda: self.write("README.md", "Docs.\n"))
        result = self.tool("make")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Nothing to sync", result.stdout)
        self.assertEqual(self.git("log", "-1", "--format=%s"), "Merge pull request #8 from someone/topic-8")

    def test_verify_refuses_a_batch_that_is_not_exactly_the_tools(self) -> None:
        self.lean_only_merges()
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        message = self.git("log", "-1", "--format=%B")
        # A page edited by hand after the run.
        page = self.root / "blueprint/roadmap/Algebra/not-yet-classified/fields/fields.md"
        page.write_text(page.read_text() + "\nMore prose.\n")
        self.git("commit", "-q", "-a", "--amend", "-m", message)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("does not find the batch's wiki exactly the sync's", result.stderr)
        # A placement the plan does not make.
        self.git("reset", "-q", "--hard", "HEAD^")
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        taxonomy = self.root / "scripts/taxonomy.json"
        taxonomy.write_text(taxonomy.read_text().replace('"title": "Units of a ring"', '"title": "Unit groups"'))
        self.git("commit", "-q", "-a", "--amend", "-m", message)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("not main's with the placement plan applied", result.stderr)
        # A commit that changes a file a batch never changes is no batch.
        self.write("README.md", "Docs.\n")
        self.git("add", "README.md")
        self.git("commit", "-q", "--amend", "-m", message)
        result = self.tool("verify")
        self.assertEqual(result.returncode, 1)
        self.assertIn("is not a batch", result.stderr)

    def test_verify_from_a_newer_main_checks_the_merge(self) -> None:
        self.lean_only_merges()
        through = self.git("rev-parse", "HEAD")
        self.assertEqual(self.tool("make", "--base", self.base).returncode, 0)
        commit = self.git("rev-parse", "HEAD")
        self.git("branch", "batch", commit)

        def main_merges(number: int, change) -> None:
            self.git("reset", "-q", "--hard", through)
            self.merge(number, change)

        # A Lean pull request merged after the batch was made: it still merges, and nothing breaks.
        main_merges(9, lambda: self.write("MathlibExt/Algebra/Other.lean", "namespace Ext\n\n/-- Other. -/\n"
                                          "theorem other : True := trivial\n\nend Ext\n"))
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merges cleanly into", result.stdout)

        # A graph pull request that gave one of the batch's declarations a page of its own: two pages for one
        # declaration once both merge, which the check finds though the files merge cleanly.
        def hand_page() -> None:
            self.write("blueprint/roadmap/Algebra/groups/group-basics/fields-by-hand.md", "# Fields\n\nFields are rings.\n")
            readme = self.root / "blueprint/roadmap/Algebra/groups/group-basics/README.md"
            readme.write_text(readme.read_text() + "- [Fields](fields-by-hand.md)\n")
            # Its row among the others in path order, as the sync puts one, away from the rows the batch adds.
            links = self.root / "blueprint/links/Algebra.jsonl"
            lines = links.read_text().splitlines(keepends=True)
            lines.insert(3, json.dumps({
                "subject": [{"type": "generic", "uri": "../roadmap/Algebra/groups/group-basics/fields-by-hand.md"}],
                "id": "af_" + "e" * 24, "object": [{"location": {"declaration": "Ext.fields"}}]}) + "\n")
            links.write_text("".join(lines))

        main_merges(10, hand_page)
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("the batch breaks what the scoped check reads", result.stderr)
        self.assertIn("Ext.fields", result.stderr)

        # A change to a folder page the batch also extends: no clean merge.
        main_merges(11, lambda: self.write("blueprint/roadmap/Algebra/README.md",
                                           PAGES["Algebra/README.md"] + "- [Fields](fields/README.md)\n"))
        result = self.tool("verify", commit)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("no longer merges cleanly", result.stderr)

    def test_make_needs_a_clean_checkout_and_an_older_base(self) -> None:
        self.lean_only_merges()
        self.write("MathlibExt/Algebra/Fields.lean", "-- edited\n")
        result = self.tool("make", "--base", self.base)
        self.assertEqual(result.returncode, 1)
        self.assertIn("needs a clean checkout", result.stderr)
        self.git("checkout", "--", ".")
        result = self.tool("make")
        self.assertEqual(result.returncode, 1)
        self.assertIn("give the first batch's base with --base", result.stderr)
        result = self.tool("make", "--base", "HEAD")
        self.assertEqual(result.returncode, 1)
        self.assertIn("is not an older commit", result.stderr)


if __name__ == "__main__":
    unittest.main()
