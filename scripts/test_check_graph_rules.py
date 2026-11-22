"""The graph's mechanical rules ("Graph rules" in docs/BLUEPRINT.md) each catch what they name, and pass a well-formed vault."""

from __future__ import annotations

import io
import json
import os
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts import check_graph_rules as rules

TAXONOMY = {
    "schema": "test",
    "regions": {"Foundations": ["CategoryTheory", "Physics"]},
    "subjects": {
        "CategoryTheory": {"title": "Category Theory", "fields": [{"slug": "topos-theory", "subfields": []}]},
        "Physics": {"title": "Physics", "fields": []},
    },
    "placements": {},
}
PLANNED = {rules.AUTOFORM: {rules.NOT_READY: True}}


class Vault:
    """A small vault: CategoryTheory/topos-theory with two linked articles, and Physics with one planned node."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.write("scripts/taxonomy.json", json.dumps(TAXONOMY))
        self.write("blueprint/roadmap/README.md", "# ATLAS roadmap\n\n- [Category Theory](CategoryTheory/README.md)\n- [Physics](Physics/README.md)\n")
        self.write("blueprint/roadmap/CategoryTheory/README.md", "# Category Theory\n\n- [Topos theory](topos-theory/README.md)\n")
        self.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/README.md",
            "# Topos theory\n\n- [Elementary topos](is-topos.md)\n- [Fundamental theorem](fundamental.md)\n",
        )
        self.write("blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md", "# Elementary topos\n\nA topos.\n")
        self.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/fundamental.md",
            "# Fundamental theorem\n\nSlices.\n\n## Informally uses\n\n- [Elementary topos](is-topos.md)\n",
        )
        self.write("blueprint/roadmap/Physics/README.md", "# Physics\n\n- [Mechanics](mechanics.md)\n")
        self.write("blueprint/roadmap/Physics/mechanics.md", "# Mechanics\n\nNewton.\n")
        self.annotations = {
            "roadmap": [self.row("README.md", id="af_" + "0" * 24)],
            "CategoryTheory": [
                self.row("CategoryTheory/README.md"),
                self.row("CategoryTheory/topos-theory/README.md"),
                self.row("CategoryTheory/topos-theory/is-topos.md", declaration="X.IsTopos", id="af_" + "1" * 24),
                self.row("CategoryTheory/topos-theory/fundamental.md", declaration="X.fundamental"),
            ],
            "Physics": [self.row("Physics/README.md"), self.row("Physics/mechanics.md", extensions=PLANNED)],
        }
        self.save()

    @staticmethod
    def row(page: str, declaration: str | None = None, **extra) -> dict:
        row = {"subject": [{"type": "generic", "uri": f"../roadmap/{page}"}]}
        if declaration:
            row["object"] = [{"location": {"declaration": declaration}}]
        row.update(extra)
        return row

    def write(self, path: str, text: str) -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def save(self) -> None:
        links = self.root / "blueprint" / "links"
        for old in links.glob("*.jsonl"):
            old.unlink()
        for name, rows in self.annotations.items():
            self.write(f"blueprint/links/{name}.jsonl", "".join(json.dumps(row) + "\n" for row in rows))

    def check(self) -> list[str]:
        return [str(finding) for finding in rules.check(self.root)]


class GraphRules(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.vault = Vault(Path(self.tmp.name))

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def findings(self) -> str:
        return "\n".join(self.vault.check())

    def test_a_well_formed_vault_passes(self) -> None:
        self.assertEqual(self.vault.check(), [])

    # Rule 5

    def test_annotations_name_existing_pages_once_in_their_subjects_file(self) -> None:
        self.vault.annotations["Physics"].append(Vault.row("Physics/gone.md"))
        self.vault.annotations["Physics"].append(Vault.row("Physics/mechanics.md"))
        self.vault.annotations["Physics"].append(Vault.row("CategoryTheory/topos-theory/README.md"))
        self.vault.annotations["Physics"].append({"subject": []})
        self.vault.save()
        found = self.findings()
        self.assertIn("Physics.jsonl:3: its annotation names a page that does not exist (rule 5)", found)
        self.assertIn("Physics.jsonl:4: the page has more than one annotation (rule 5)", found)
        self.assertIn("its annotation belongs in blueprint/links/CategoryTheory.jsonl", found)
        self.assertIn("a row names exactly one subject page", found)

    def test_ids_are_well_formed_and_unique_and_a_missing_one_is_fine(self) -> None:
        self.vault.annotations["Physics"][1]["id"] = "af_" + "1" * 24
        self.vault.annotations["CategoryTheory"][0]["id"] = "af_xyz"
        self.vault.save()
        found = self.findings()
        self.assertIn("id af_111111111111111111111111 is shared by blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md, "
                      "blueprint/roadmap/Physics/mechanics.md", found)
        self.assertIn("malformed id 'af_xyz'", found)
        self.assertNotIn("fundamental.md", found)  # it has no id, which is not a finding (#5524)

    def test_the_defaults_do_not_assign_a_page_id(self) -> None:
        defaults = "blueprint/links/_defaults.json"
        self.vault.write(defaults, json.dumps({"id": "af_" + "2" * 24}))
        self.assertEqual(self.vault.check(), [
            f"{defaults}: the defaults set a page ID; put each ID on its annotation row (rule 5)",
        ])

    def test_bad_subject_uris_are_findings_not_crashes(self) -> None:
        self.vault.annotations["Physics"].append({"subject": [{"type": "generic", "uri": None}]})
        self.vault.save()
        self.assertIn("subject None is not a page under blueprint/roadmap/", self.findings())

    def test_a_percent_escaped_subject_uri_is_a_finding_since_sync_and_autoform_disagree(self) -> None:
        # A literal `%6dechanics.md` beside `mechanics.md`: sync_wiki binds the row to the first, Autoform to the second.
        self.vault.write("blueprint/roadmap/Physics/%6dechanics.md", "# Other\n\nOther.\n")
        self.vault.write("blueprint/roadmap/Physics/README.md",
                         "# Physics\n\n- [Mechanics](mechanics.md)\n- [Other](%256dechanics.md)\n")
        self.vault.annotations["Physics"].append(Vault.row("Physics/%6dechanics.md", declaration="X.different"))
        self.vault.save()
        self.assertIn("subject '../roadmap/Physics/%6dechanics.md' has a percent-escape", self.findings())

    def test_a_link_no_file_can_have_is_skipped(self) -> None:
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n\n- [Mechanics](mechanics.md)\n- [Bad](%00bad.md)\n")
        self.assertEqual(self.vault.check(), [])

    def test_an_annotation_names_at_most_one_declaration(self) -> None:
        objects = self.vault.annotations["CategoryTheory"][2]["object"]
        objects.append({"type": "generic", "uri": "https://example.org/source"})
        self.vault.save()
        self.assertEqual(self.vault.check(), [])

        objects.append({"location": {"declaration": "X.other"}})
        self.vault.annotations["CategoryTheory"][3]["object"] = {"location": {"declaration": "X.fundamental"}}
        self.vault.save()
        found = self.findings()
        self.assertIn("CategoryTheory.jsonl:3: its annotation names more than one Lean declaration", found)
        self.assertIn("CategoryTheory.jsonl:4: its annotation's `object` is not a list of ends", found)

    def test_a_page_with_no_annotation_row_is_a_finding(self) -> None:
        self.vault.annotations["Physics"].pop(1)
        self.vault.save()
        self.assertIn("blueprint/roadmap/Physics/mechanics.md: the page has no annotation row in blueprint/links/ (rule 5)",
                      self.findings())

    # Rule 8

    def test_facts_lean_facts_adds_are_never_committed(self) -> None:
        self.vault.annotations["CategoryTheory"][2]["kind"] = "def"
        self.vault.annotations["CategoryTheory"][3]["status"] = "stated"
        self.vault.save()
        found = self.findings()
        self.assertIn("commits 'kind', which lean-facts adds at build time (rule 8)", found)
        self.assertIn("commits 'status'", found)

    def test_annotation_files_autoform_reads_besides_the_subject_files_are_findings(self) -> None:
        topos = Vault.row("CategoryTheory/topos-theory/is-topos.md", kind="theorem", status="formalized")
        self.vault.write("blueprint/links/000.json", json.dumps(topos))
        self.vault.write("blueprint/links/extra.ndjson", json.dumps(Vault.row("Physics/mechanics.md")) + "\n")
        self.vault.write("blueprint/links/nested/Physics.jsonl", json.dumps(Vault.row("Physics/mechanics.md")) + "\n")
        self.vault.write("blueprint/links/nested/_defaults.json", json.dumps({"status": "formalized"}))
        self.vault.write("blueprint/links/README.txt", "not an annotation file\n")
        found = self.findings()
        for name in ("000.json", "extra.ndjson", "nested/Physics.jsonl"):
            self.assertIn(f"blueprint/links/{name}: Autoform reads this file, but annotations go in", found)
        self.assertIn("blueprint/links/000.json: its annotation commits 'kind'", found)
        self.assertIn("blueprint/links/nested/_defaults.json: the defaults commit 'status'", found)
        self.assertIn("nested/_defaults.json: Autoform merges this defaults file too", found)
        self.assertNotIn("README.txt", found)
        # Autoform merges each of these rows with the page's own, wherever it sits.
        self.assertIn("blueprint/links/CategoryTheory.jsonl:3: the page has more than one annotation", found)
        self.assertIn("blueprint/links/extra.ndjson:1: the page has more than one annotation", found)

    def test_links_files_are_found_as_autoform_finds_them(self) -> None:
        self.vault.write("blueprint/links/.scratch/extra.json", json.dumps(Vault.row("Physics/mechanics.md")))
        target = self.vault.root / "elsewhere.json"
        target.write_text(json.dumps(Vault.row("Physics/mechanics.md", kind="theorem")))
        (self.vault.root / "blueprint/links/linked.json").symlink_to(target)
        # Autoform skips dot-named folders; it does not follow a symlink, and render refuses one.
        self.assertEqual(self.vault.check(), ["blueprint/links/linked.json: a symbolic link in blueprint/links/; "
                                              "Autoform does not follow it and render refuses it (rule 5)"])

    def test_a_symlinked_links_folder_is_a_finding_and_is_not_read(self) -> None:
        links = self.vault.root / "blueprint/links"
        links.rename(self.vault.root / "blueprint/saved-links")
        links.symlink_to("saved-links")
        found = self.findings()
        self.assertIn("blueprint/links: not a folder (a symbolic link or missing), so Autoform reads no annotation", found)
        self.assertNotIn("saved-links", found)

    def test_files_that_are_not_utf8_are_findings_not_crashes(self) -> None:
        links = self.vault.root / "blueprint/links/Physics.jsonl"
        links.write_bytes(links.read_bytes().replace(b"mechanics", b"m\xe9chanics"))
        page = self.vault.root / "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md"
        page.write_bytes(b"# Elementary topos\n\nA t\xf6pos.\n")
        found = self.findings()
        self.assertIn("blueprint/links/Physics.jsonl: not UTF-8", found)
        self.assertIn("topos-theory/is-topos.md: not UTF-8", found)

    def test_a_second_row_for_a_page_is_checked_in_full(self) -> None:
        self.vault.annotations["CategoryTheory"].append(
            Vault.row("CategoryTheory/topos-theory/is-topos.md", kind="theorem", status="formalized", id="af_bad",
                      extensions={rules.AUTOFORM: {rules.NOT_READY: "yes"}}))
        self.vault.save()
        found = self.findings()
        self.assertIn("the page has more than one annotation", found)
        self.assertIn("its annotation commits 'kind'", found)
        self.assertIn("malformed id 'af_bad'", found)
        self.assertIn("not_ready takes true or false", found)

    def test_the_shared_defaults_commit_no_derived_facts(self) -> None:
        self.vault.write("blueprint/links/_defaults.json", json.dumps({"object": {"type": "lean", "uri": "../.."}, "kind": "theorem"}))
        self.assertIn("blueprint/links/_defaults.json: the defaults commit 'kind'", self.findings())

    # Rule 12

    def test_a_node_to_break_down_is_a_planned_article_marked_not_ready(self) -> None:
        self.vault.annotations["CategoryTheory"][2]["extensions"] = PLANNED  # names a declaration
        self.vault.annotations["CategoryTheory"][1]["extensions"] = PLANNED  # a folder page
        self.vault.annotations["Physics"][1]["extensions"] = {rules.AUTOFORM: {rules.NOT_READY: "yes"}}
        self.vault.save()
        found = self.findings()
        self.assertIn("a node still to be broken down (not_ready) names no Lean declaration", found)
        self.assertIn("a folder page is not a node to break down", found)
        self.assertIn("takes true or false; Autoform drops any other value", found)

    def test_the_defaults_neither_mark_nor_link_every_page(self) -> None:
        defaults = "blueprint/links/_defaults.json"
        self.vault.write(defaults, json.dumps({"object": {"type": "lean", "uri": "../.."}}))
        self.assertEqual(self.vault.check(), [])
        self.vault.write(defaults, json.dumps({
            "object": {"type": "lean", "uri": "../..", "location": {"declaration": "X.all"}}, "extensions": PLANNED,
        }))
        found = self.findings()
        self.assertIn(f"{defaults}: the defaults name a Lean declaration for every page; name it on the page's own row "
                      "(rule 5)", found)
        self.assertIn(f"{defaults}: the defaults set not_ready for every page; mark each node to break down on its own "
                      "row (rule 12)", found)

    def test_not_ready_false_and_legacy_rows(self) -> None:
        self.vault.annotations["Physics"][1]["extensions"] = {rules.AUTOFORM: {rules.NOT_READY: False}}
        # A row an earlier sync wrote with only a module and a name counts as linked, as lean-facts reads it.
        self.vault.annotations["CategoryTheory"][3].pop("object")
        self.vault.annotations["CategoryTheory"][3]["extensions"] = {rules.OWN: {"module": "X.Mod", "name": "far"}, **PLANNED}
        self.vault.save()
        errors = self.vault.check()
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("names no Lean declaration", errors[0])

    # Rule 1

    def test_folders_follow_the_taxonomy(self) -> None:
        self.vault.write("blueprint/roadmap/Alchemy/README.md", "# Alchemy\n")
        self.vault.write("blueprint/roadmap/CategoryTheory/sheaves/README.md", "# Sheaves\n")
        self.vault.write("blueprint/roadmap/CategoryTheory/loose.md", "# Loose\n")
        found = self.findings()
        self.assertIn("Alchemy: not a subject", found)
        self.assertIn("CategoryTheory/sheaves: not a field of CategoryTheory", found)
        self.assertIn("CategoryTheory/loose.md: a page of a subject with fields goes in a field folder", found)

    def test_the_generators_unclassified_folders_and_subjects_without_fields_take_any_folder(self) -> None:
        self.vault.write("blueprint/roadmap/README.md", "# ATLAS roadmap\n\n- [Category Theory](CategoryTheory/README.md)\n"
                         "- [Physics](Physics/README.md)\n- [Not yet classified](not-yet-classified/README.md)\n")
        self.vault.write("blueprint/roadmap/not-yet-classified/README.md", "# Not yet classified\n")
        # generate_wiki.py puts a subject's unplaced modules in a field folder of this name.
        self.vault.write("blueprint/roadmap/CategoryTheory/README.md", "# Category Theory\n\n- [Topos theory](topos-theory/README.md)\n"
                         "- [Not yet classified](not-yet-classified/README.md)\n")
        self.vault.write("blueprint/roadmap/CategoryTheory/not-yet-classified/README.md", "# Not yet classified\n")
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n\n- [Mechanics](mechanics.md)\n- [Optics](optics/README.md)\n")
        self.vault.write("blueprint/roadmap/Physics/optics/README.md", "# Optics\n")
        self.vault.annotations["not-yet-classified"] = [Vault.row("not-yet-classified/README.md")]
        self.vault.annotations["Physics"].append(Vault.row("Physics/optics/README.md"))
        self.vault.annotations["CategoryTheory"].append(Vault.row("CategoryTheory/not-yet-classified/README.md"))
        self.vault.save()
        self.assertEqual(self.vault.check(), [])

    # Rule 2

    def test_every_page_and_folder_is_listed_on_its_folder_page(self) -> None:
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n")
        self.vault.write("blueprint/roadmap/CategoryTheory/README.md", "# Category Theory\n")
        found = self.findings()
        self.assertIn("Physics/mechanics.md: not listed on blueprint/roadmap/Physics/README.md", found)
        self.assertIn("CategoryTheory/topos-theory/README.md: not listed on", found)

    def test_listings_are_read_as_autoform_reads_links(self) -> None:
        readme = "blueprint/roadmap/Physics/README.md"
        for text in ("# Physics\n\n- [Mechanics][m]\n\n[m]: mechanics.md\n", "# Physics\n\n- [Mechanics](%6dechanics.md)\n"):
            self.vault.write(readme, text)
            self.assertEqual(self.vault.check(), [], text)
        for text in ("# Physics\n\n```markdown\n- [Mechanics](mechanics.md)\n```\n",
                     "# Physics\n\n<!-- - [Mechanics](mechanics.md) -->\n"):
            self.vault.write(readme, text)
            self.assertIn("Physics/mechanics.md: not listed", self.findings(), text)

    def test_a_folder_needs_its_folder_page(self) -> None:
        (self.vault.root / "blueprint/roadmap/Physics/README.md").unlink()
        self.vault.annotations["Physics"].pop(0)
        self.vault.save()
        self.assertIn("blueprint/roadmap/Physics: the folder has no README.md folder page", self.findings())

    def test_a_folder_with_only_subfolders_needs_its_folder_page(self) -> None:
        self.vault.write("blueprint/roadmap/Physics/classical/rigid/README.md", "# Rigid bodies\n")
        self.vault.annotations["Physics"].append(Vault.row("Physics/classical/rigid/README.md"))
        self.vault.save()
        self.assertIn("blueprint/roadmap/Physics/classical: the folder has no README.md folder page", self.findings())

    # Rules 9 and 10

    def test_lean_sections_are_never_committed_on_linked_pages(self) -> None:
        # Physics/mechanics.md is a planned page: it may write its own prerequisites (rule 10).
        self.vault.write("blueprint/roadmap/Physics/mechanics.md",
                         "# Mechanics\n\nNewton.\n\n## Depends on\n\n- [Topos](../CategoryTheory/topos-theory/is-topos.md)\n")
        # Headings are read case-folded, an empty section counts, and fenced code is not read.
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/fundamental.md",
            "# Fundamental theorem\n\nSlices.\n\n## proof depends on\n\n- [Elementary topos][t]\n\n[t]: is-topos.md\n",
        )
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md",
            "# Elementary topos\n\nA topos.\n\n## Depends on\n\nThis node has no prerequisites.\n\n"
            "```markdown\n## Proof depends on\n```\n",
        )
        errors = self.vault.check()
        self.assertEqual(len(errors), 2, errors)
        self.assertTrue(all("which lean-facts writes at build time (rule 9)" in error for error in errors), errors)
        self.assertIn("topos-theory/fundamental.md: commits `## Proof depends on`", errors[0])
        self.assertIn("topos-theory/is-topos.md: commits `## Depends on`", errors[1])

    def test_a_link_on_a_later_row_makes_the_page_linked(self) -> None:
        # Autoform merges a page's rows, so a declaration on a second row, here in an extra file, links planned
        # Mechanics: its own `## Depends on` is a finding, beside the second row's.
        page = "blueprint/roadmap/Physics/mechanics.md"
        self.vault.write("blueprint/links/extra.ndjson", json.dumps(Vault.row("Physics/mechanics.md", declaration="X.mechanics")) + "\n")
        self.vault.write(page, "# Mechanics\n\nNewton.\n\n## Depends on\n")
        found = self.findings()
        self.assertIn("extra.ndjson:1: the page has more than one annotation (rule 5)", found)
        self.assertIn(f"{page}: commits `## Depends on`, which lean-facts writes at build time (rule 9)", found)

    # Rule 11

    def test_informal_edges_link_pages_and_close_no_cycle(self) -> None:
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md",
            "# Elementary topos\n\nA topos.\n\n## INFORMALLY USES\n\n- [Fundamental](fundamental.md)\n"
            "- [Missing](missing.md)\n- [Itself](is-topos.md)\n",
        )
        found = self.findings()
        self.assertIn("topos-theory/fundamental.md: `## Informally uses` links "
                      "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md, which reaches back to it", found)
        self.assertIn("topos-theory/is-topos.md: `## Informally uses` links "
                      "blueprint/roadmap/CategoryTheory/topos-theory/fundamental.md, which reaches back to it", found)
        self.assertIn("informal target does not exist: 'missing.md'", found)
        self.assertIn("informally uses itself", found)

    def test_a_cycle_through_counted_and_informal_edges_is_found(self) -> None:
        # Fundamental -> Topos -> Mechanics informally, then Mechanics -> Fundamental through the planned page's own
        # `## Depends on`: no informal-only cycle, but a cycle all the same.
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md",
            "# Elementary topos\n\nA topos.\n\n## Informally uses\n\n- [Mechanics](../../Physics/mechanics.md)\n",
        )
        self.vault.write("blueprint/roadmap/Physics/mechanics.md",
                         "# Mechanics\n\nNewton.\n\n## Depends on\n\n- [Fundamental](../CategoryTheory/topos-theory/fundamental.md)\n")
        self.assertIn("which reaches back to it", self.findings())

    def test_the_built_check_reports_a_lean_cycle_with_two_informal_links(self) -> None:
        self.vault.annotations["Physics"][1] = Vault.row("Physics/mechanics.md", declaration="X.mechanics")
        self.vault.save()
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md",
            "# Elementary topos\n\n## Informally uses\n\n- [Mechanics](../../Physics/mechanics.md)\n",
        )
        self.assertEqual(self.vault.check(), [])

        # lean-facts completes Fundamental -> Topos -> Mechanics -> Fundamental.
        self.vault.write(
            "blueprint/roadmap/Physics/mechanics.md",
            "# Mechanics\n\n## Proof depends on\n\n- [Fundamental](../CategoryTheory/topos-theory/fundamental.md)\n",
        )
        summary = self.vault.root / "summary.md"
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(rules.main(["--root", str(self.vault.root), "--built", "--summary", str(summary)]), 0)
        text = summary.read_text(encoding="utf-8")
        self.assertIn("Informal dependencies on the built graph (report-only)", text)
        self.assertEqual(text.count("(rule 11)"), 2)
        self.assertNotIn("(rule 9)", text)  # the generated proof dependency belongs in the built graph

    def test_a_linked_folder_page_commits_no_lean_sections(self) -> None:
        self.vault.annotations["Physics"][0]["object"] = [{"location": {"declaration": "X.physics"}}]
        self.vault.save()
        self.vault.write("blueprint/roadmap/Physics/README.md",
                         "# Physics\n\n- [Mechanics](mechanics.md)\n\n## Depends on\n\nThis node has no prerequisites.\n")
        self.assertEqual(self.vault.check(), ["blueprint/roadmap/Physics/README.md: commits `## Depends on`, "
                                              "which lean-facts writes at build time (rule 9)"])

    def test_a_cycle_of_counted_edges_alone_is_left_to_autoform(self) -> None:
        groups = rules.strongly_connected({"a": {"b"}, "b": {"c"}, "c": {"a"}, "d": {"a"}})
        self.assertEqual(groups, [["a", "b", "c"]])

    def test_a_graph_autoform_cannot_load_is_reported_under_autoforms_format(self) -> None:
        self.vault.write("blueprint/roadmap/Physics/mechanics.md", "No title.\n")
        found = self.findings()
        self.assertIn("autoform cannot load the graph", found)
        self.assertIn("(Autoform's format)", found)


class GitRules(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.vault = Vault(self.root)
        self.git("init", "-q")
        self.commit()
        self.base = self.head()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True, text=True).stdout

    def commit(self) -> None:
        self.git("add", "-A")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "change", "--allow-empty")

    def head(self) -> str:
        return self.git("rev-parse", "HEAD").strip()

    def run_main(self, *args: str) -> int:
        """Run the script outside GitHub Actions, keeping what it prints in `self.output` and `self.errors`."""
        output, errors = io.StringIO(), io.StringIO()
        try:
            with patch.dict(os.environ, {"GITHUB_ACTIONS": ""}), redirect_stdout(output), redirect_stderr(errors):
                return rules.main(["--root", str(self.root), *args])
        finally:
            self.output, self.errors = output.getvalue(), errors.getvalue()

    def test_build_outputs_are_never_committed(self) -> None:
        self.vault.write("site/index.html", "<html></html>")
        self.vault.write("v2-modules.txt", "MathlibExt\n")
        self.vault.write("blueprint/site/keep.txt", "not a build output\n")
        self.commit()
        found = "\n".join(str(finding) for finding in rules.check(self.root))
        self.assertIn("site/index.html: a build output is committed (rule 8)", found)
        self.assertIn("v2-modules.txt: a build output is committed", found)
        self.assertNotIn("blueprint/site", found)

    def test_a_pr_changes_fewer_files_than_github_shows(self) -> None:
        self.assertEqual(rules.check(self.root, self.base), [])
        with patch.object(rules, "MAX_CHANGED_FILES", 3):
            for number in range(3):
                self.vault.write(f"notes/{number}.txt", "x\n")
            self.commit()
            errors = [str(finding) for finding in rules.check(self.root, self.base)]
        self.assertEqual(errors, ["the PR: changes 3 files; split it below 3, the most GitHub shows in one diff (rule 15)"])

    def test_malformed_taxonomy_is_reported_without_blocking(self) -> None:
        path = "scripts/taxonomy.json"
        for taxonomy, message in (
            ({"subjects": []}, "taxonomy subjects must be a JSON object"),
            ({"subjects": {"Physics": None}}, "must be an object with a list of fields"),
            ({"subjects": {"Physics": {"fields": None}}}, "must be an object with a list of fields"),
            ({"subjects": {"Physics": {"fields": [None]}}}, "must be an object with a nonempty string slug"),
            ({"subjects": {"Physics": {"fields": [{}]}}}, "must be an object with a nonempty string slug"),
        ):
            with self.subTest(taxonomy=taxonomy):
                self.vault.write(path, json.dumps(taxonomy))
                self.assertTrue(any(f.rule == 1 and f.subject == path and message in f.detail
                                    for f in rules.check(self.root)))
                self.assertEqual(self.run_main(), 0)
                self.assertIn(f"warning: {path}:", self.errors)

    def test_report_only_by_default_and_blocking_on_any_finding(self) -> None:
        self.assertEqual(self.run_main("--blocking"), 0)
        self.assertEqual(self.output, "graph rules: OK\n")
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n")
        self.assertEqual(self.run_main(), 0)  # report-only
        self.assertIn("warning: blueprint/roadmap/Physics/mechanics.md: not listed", self.errors)
        self.assertEqual(self.output, "graph rules: 1 finding(s), reported only; see Graph rules in docs/BLUEPRINT.md\n")
        # Main is kept clean, so any finding is the change's own: no base is needed to block.
        self.assertEqual(self.run_main("--blocking"), 1)
        self.assertIn("error: blueprint/roadmap/Physics/mechanics.md: not listed", self.errors)
        self.assertEqual(self.output, "graph rules: 1 finding(s); see Graph rules in docs/BLUEPRINT.md\n")
        with self.assertRaises(SystemExit) as stopped:
            self.run_main("--base", "no-such-commit")
        self.assertEqual(stopped.exception.code, 2)

    def test_malformed_input_is_reported_and_report_only_still_exits_zero(self) -> None:
        for change, message in (("uri", "subject None is not a page"), ("title", "autoform cannot load the graph")):
            self.git("reset", "-q", "--hard", self.base)
            if change == "uri":
                self.vault.annotations["Physics"].append({"subject": [{"type": "generic", "uri": None}]})
                self.vault.save()
            else:
                self.vault.write("blueprint/roadmap/Physics/mechanics.md", "No title.\n")
            self.commit()
            self.assertEqual(self.run_main("--base", self.base), 0, change)
            self.assertIn(message, self.errors, change)
            self.assertIn("reported only", self.output, change)
            self.vault = Vault(self.root)

    def test_the_summary_and_annotations(self) -> None:
        summary = self.root / "summary.md"
        with patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}), patch("sys.stderr"), patch("sys.stdout"):
            rules.main(["--root", str(self.root), "--summary", str(summary)])
        self.assertEqual(summary.read_text(), "## Graph rules (report-only)\n\nNo findings.\n")
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n")
        self.vault.annotations["Physics"] += [Vault.row(f"Physics/gone-{number}.md") for number in range(51)]
        self.vault.save()
        summary.unlink()
        with patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}), patch("sys.stderr") as stderr, patch("sys.stdout"):
            self.assertEqual(rules.main(["--root", str(self.root), "--blocking", "--summary", str(summary)]), 1)
        written = "".join(call.args[0] for call in stderr.write.call_args_list)
        self.assertIn("::error file=blueprint/roadmap/Physics/mechanics.md,title=Graph rule 2::", written)
        lines = summary.read_text().splitlines()
        self.assertEqual(lines[:2], ["## Graph rules (blocking)", ""])
        self.assertEqual(len(lines), 2 + 50 + 1)  # 52 findings: 50 listed, then the rest counted
        self.assertTrue(all(line.startswith("- ") for line in lines[2:]))
        self.assertEqual(lines[-1], "- … and 2 more in the step's log")

if __name__ == "__main__":
    unittest.main()
