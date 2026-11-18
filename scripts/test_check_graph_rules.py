"""The graph's mechanical rules ("Graph rules" in docs/BLUEPRINT.md) each catch what they name, and pass a well-formed vault."""

from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

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


class Vault:
    """A small vault: roadmap/CategoryTheory/topos-theory with two articles, and Physics with one."""

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
            "Physics": [
                self.row("Physics/README.md"),
                self.row("Physics/mechanics.md", extensions={rules.OWN: {rules.UNEXPANDED: True}}),
            ],
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

    def check(self, base: str | None = None) -> list[str]:
        return rules.check(self.root, base)


class GraphRules(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.vault = Vault(Path(self.tmp.name))

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def assertFinds(self, fragment: str) -> None:
        errors = self.vault.check()
        self.assertTrue(any(fragment in error for error in errors), errors)

    def test_a_well_formed_vault_passes(self) -> None:
        self.assertEqual(self.vault.check(), [])

    def test_annotations_name_existing_pages_once_in_their_subjects_file(self) -> None:
        self.vault.annotations["Physics"].append(Vault.row("Physics/gone.md"))
        self.vault.annotations["Physics"].append(Vault.row("Physics/mechanics.md"))
        self.vault.annotations["Physics"].append(Vault.row("CategoryTheory/topos-theory/README.md"))
        self.vault.annotations["Physics"].append({"subject": []})
        self.vault.save()
        errors = "\n".join(self.vault.check())
        self.assertIn("'../roadmap/Physics/gone.md' does not exist", errors)
        self.assertIn("Physics/mechanics.md is already annotated", errors)
        self.assertIn("belongs in blueprint/links/CategoryTheory.jsonl", errors)
        self.assertIn("exactly one subject page", errors)

    def test_article_ids_are_well_formed_and_unique(self) -> None:
        self.vault.annotations["Physics"][1]["id"] = "af_" + "1" * 24
        self.vault.annotations["CategoryTheory"][0]["id"] = "af_xyz"
        self.vault.save()
        errors = "\n".join(self.vault.check())
        self.assertIn("is already used", errors)
        self.assertIn("malformed article id 'af_xyz'", errors)

    def test_an_annotation_names_at_most_one_declaration(self) -> None:
        self.vault.annotations["CategoryTheory"][2]["object"].append({"location": {"declaration": "X.other"}})
        self.vault.save()
        self.assertFinds("at most one Lean declaration")

    def test_a_node_to_expand_is_an_article_with_no_declaration(self) -> None:
        marker = {rules.OWN: {rules.UNEXPANDED: True}}
        self.vault.annotations["CategoryTheory"][2]["extensions"] = marker
        self.vault.annotations["CategoryTheory"][1]["extensions"] = marker
        self.vault.annotations["Physics"][1]["extensions"] = {rules.OWN: {rules.UNEXPANDED: "yes"}}
        self.vault.save()
        errors = "\n".join(self.vault.check())
        self.assertIn("a node to expand names no Lean declaration", errors)
        self.assertIn("a folder page is not a node to expand", errors)
        self.assertIn("takes only true", errors)

    def test_folders_follow_the_taxonomy(self) -> None:
        self.vault.write("blueprint/roadmap/Alchemy/README.md", "# Alchemy\n")
        self.vault.write("blueprint/roadmap/CategoryTheory/sheaves/README.md", "# Sheaves\n")
        self.vault.write("blueprint/roadmap/CategoryTheory/loose.md", "# Loose\n")
        errors = "\n".join(self.vault.check())
        self.assertIn("Alchemy/: not a subject", errors)
        self.assertIn("CategoryTheory/sheaves/: not a field of CategoryTheory", errors)
        self.assertIn("CategoryTheory/loose.md: a page of a subject with fields goes in a field folder", errors)

    def test_unclassified_modules_and_subjects_without_fields_take_any_folder(self) -> None:
        self.vault.write("blueprint/roadmap/README.md", "# ATLAS roadmap\n\n- [Category Theory](CategoryTheory/README.md)\n"
                         "- [Physics](Physics/README.md)\n- [Not yet classified](not-yet-classified/README.md)\n")
        self.vault.write("blueprint/roadmap/not-yet-classified/README.md", "# Not yet classified\n")
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n\n- [Mechanics](mechanics.md)\n- [Optics](optics/README.md)\n")
        self.vault.write("blueprint/roadmap/Physics/optics/README.md", "# Optics\n")
        self.assertEqual(self.vault.check(), [])

    def test_every_page_and_folder_is_listed_on_its_folder_page(self) -> None:
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n")
        self.vault.write("blueprint/roadmap/CategoryTheory/README.md", "# Category Theory\n")
        errors = "\n".join(self.vault.check())
        self.assertIn("Physics/mechanics.md: not listed on Physics/README.md", errors)
        self.assertIn("CategoryTheory/topos-theory: not listed on CategoryTheory/README.md", errors)

    def test_a_folder_needs_its_folder_page(self) -> None:
        (self.vault.root / "blueprint/roadmap/Physics/README.md").unlink()
        self.vault.annotations["Physics"].pop(0)
        self.vault.save()
        self.assertFinds("Physics/: has no README.md folder page")

    def test_lean_sections_are_never_committed_on_declared_pages(self) -> None:
        # Physics/mechanics.md is a planned page: it may write its own prerequisites (rule 10).
        self.vault.write("blueprint/roadmap/Physics/mechanics.md",
                         "# Mechanics\n\nNewton.\n\n## Depends on\n\n- [Topos](../CategoryTheory/topos-theory/is-topos.md)\n")
        # Autoform reads headings case-folded and reference links, so the check does too; fenced code is not read.
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/fundamental.md",
            "# Fundamental theorem\n\nSlices.\n\n## proof depends on\n\n- [Elementary topos][t]\n\n[t]: is-topos.md\n",
        )
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md",
            "# Elementary topos\n\nA topos.\n\n```markdown\n## Depends on\n\n- [x](fundamental.md)\n```\n",
        )
        errors = self.vault.check()
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("topos-theory/fundamental.md: commits `## Depends on` or `## Proof depends on`", errors[0])

    def test_informal_edges_link_pages_and_close_no_cycle(self) -> None:
        self.vault.write(
            "blueprint/roadmap/CategoryTheory/topos-theory/is-topos.md",
            "# Elementary topos\n\nA topos.\n\n## INFORMALLY USES\n\n- [Fundamental](fundamental.md)\n"
            "- [Missing](missing.md)\n- [Itself](is-topos.md)\n",
        )
        errors = "\n".join(self.vault.check())
        self.assertIn("closes a cycle: CategoryTheory/topos-theory/fundamental -> CategoryTheory/topos-theory/is-topos", errors)
        self.assertIn("informal target does not exist: 'missing.md'", errors)
        self.assertIn("informally uses itself", errors)

    def test_a_graph_autoform_cannot_load_is_reported(self) -> None:
        self.vault.write("blueprint/roadmap/Physics/mechanics.md", "No title.\n")
        self.assertFinds("autoform cannot load the graph")

    def test_longer_informal_cycles_are_found_once(self) -> None:
        cycle = {name: [target] for name, target in (("a", "b"), ("b", "c"), ("c", "a"), ("d", "a"))}
        self.assertEqual(rules.informal_cycles(cycle), [["a", "b", "c", "a"]])


class GitRules(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.vault = Vault(self.root)
        self.git("init", "-q")
        self.git("add", "-A")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "base")
        self.base = self.git("rev-parse", "HEAD").strip()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True, text=True).stdout

    def commit(self) -> None:
        self.git("add", "-A")
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "change")

    def test_build_outputs_are_never_committed(self) -> None:
        self.vault.write("site/index.html", "<html></html>")
        self.vault.write("v2-modules.txt", "MathlibExt\n")
        self.vault.write("blueprint/site/keep.txt", "not a build output\n")
        self.commit()
        errors = "\n".join(rules.check(self.root))
        self.assertIn("site/index.html: a build output is committed", errors)
        self.assertIn("v2-modules.txt: a build output is committed", errors)
        self.assertNotIn("blueprint/site", errors)

    def test_a_pr_changes_fewer_files_than_github_shows(self) -> None:
        self.assertEqual(rules.check(self.root, self.base), [])
        original = rules.MAX_CHANGED_FILES
        rules.MAX_CHANGED_FILES = 3
        try:
            for number in range(3):
                self.vault.write(f"notes/{number}.txt", "x\n")
            self.commit()
            errors = rules.check(self.root, self.base)
        finally:
            rules.MAX_CHANGED_FILES = original
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("the PR changes 3 files", errors[0])

    def test_the_command_exits_nonzero_on_a_finding(self) -> None:
        self.assertEqual(rules.main(["--root", str(self.root)]), 0)
        self.vault.write("blueprint/roadmap/Physics/README.md", "# Physics\n")
        self.assertEqual(rules.main(["--root", str(self.root)]), 1)


class Repository(unittest.TestCase):
    def test_the_committed_vault_passes(self) -> None:
        self.assertEqual(rules.check(rules.ROOT), [])


if __name__ == "__main__":
    unittest.main()
