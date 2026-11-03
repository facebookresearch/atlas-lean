#!/usr/bin/env python3
"""Regression checks for publication discovery, build coverage, and proof auditing."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

from publications import discover


REPO_ROOT = Path(__file__).resolve().parent.parent


class PublicationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="atlas-publication-tests-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve() / "repo"
        (self.root / "scripts").mkdir(parents=True)
        for name in ("lakefile.toml", "lake-manifest.json"):
            shutil.copyfile(REPO_ROOT / name, self.root / name)
        for name in ("publications.py", "check_axioms.sh"):
            shutil.copyfile(REPO_ROOT / "scripts" / name, self.root / "scripts" / name)
        self.source = (self.root / "lakefile.toml").read_text()
        self.config = tomllib.loads(self.source)
        for library in self.config["lean_lib"]:
            (self.root / library["name"]).mkdir()
        self.capture = Path(self.temporary.name) / "capture.json"
        binary = Path(self.temporary.name) / "bin"
        binary.mkdir()
        lake = binary / "lake"
        lake.write_text(f"#!{sys.executable}\n" + '''
import json, os, sys, tomllib
from pathlib import Path
args = sys.argv[1:]
root = Path(args[args.index("-d") + 1])
path = Path(args[args.index("-f") + 1])
command = args[4:]
capture = {"root": str(root), "config_path": str(path),
           "config": tomllib.loads(path.read_text()), "command": command}
if command[:2] == ["env", "lean"]:
    capture["lean_input"] = Path(command[2]).read_text()
Path(os.environ["PUBLICATION_TEST_CAPTURE"]).write_text(json.dumps(capture))
print("Build completed successfully.")
raise SystemExit(int(os.environ.get("PUBLICATION_TEST_STATUS", "0")))
''')
        lake.chmod(0o755)
        self.environment = {
            **os.environ,
            "PATH": str(binary) + os.pathsep + os.environ["PATH"],
            "PUBLICATION_TEST_CAPTURE": str(self.capture),
            "PYTHONDONTWRITEBYTECODE": "1",
        }

    def paper(self, name: str, group: str = "Papers") -> Path:
        paper = self.root / "Formalized Publications" / group / name
        (paper / "Formalization" / name).mkdir(parents=True)
        (paper / "Papers").mkdir()
        (paper / "Comparator").mkdir()
        (paper / "Readme.md").write_text(f"# {name}\n")
        (paper / "Papers" / "citation.bib").write_text("@misc{example, year={2026}}\n")
        (paper / "Papers" / "paper.pdf").write_bytes(b"%PDF-1.7\n")
        (paper / "Papers" / "paper_interactive.html").write_text("<!doctype html>\n")
        (paper / "Formalization" / f"{name}.lean").write_text(f"import {name}.Result\n")
        (paper / "Formalization" / name / "Result.lean").write_text(
            f"namespace {name}\ntheorem result : 1 + 1 = 2 := rfl\nend {name}\n"
        )
        (paper / "Comparator" / "challenge.lean").write_text(
            "example : False := by sorry\n"
        )
        (paper / "Comparator" / "challenge.json").write_text("{}\n")
        return paper

    def run_helper(self, *arguments: str, status: int = 0) -> dict:
        result = subprocess.run(
            [sys.executable, self.root / "scripts" / "publications.py", *arguments],
            cwd=self.root,
            env={**self.environment, "PUBLICATION_TEST_STATUS": str(status)},
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, status, result.stdout + result.stderr)
        return json.loads(self.capture.read_text())

    def test_full_build_covers_papers_notes_and_unimported_sources(self) -> None:
        paper = self.paper("ExamplePaper")
        self.paper("ExampleNote", "Notes")
        (paper / "Formalization" / "ExamplePaper" / "Unused.lean").write_text(
            "theorem unused : True := True.intro\n"
        )
        capture = self.run_helper("build")
        libraries = capture["config"]["lean_lib"]
        names = [library["name"] for library in libraries]
        self.assertEqual(capture["command"], ["build", *names])
        self.assertEqual(capture["config"]["require"], self.config["require"])
        self.assertEqual(capture["config"]["leanOptions"], self.config["leanOptions"])
        self.assertEqual(capture["root"], str(self.root))
        publications = libraries[len(self.config["lean_lib"]):]
        self.assertEqual(len(publications), 2)
        for library in publications:
            source_dir = self.root / library["srcDir"]
            expected = {
                ".".join(path.relative_to(source_dir).with_suffix("").parts)
                for path in source_dir.rglob("*.lean")
            }
            self.assertEqual(set(library["globs"]), expected)
            self.assertEqual(library["roots"], [])
            self.assertNotIn("challenge", library["globs"])
        self.assertFalse(Path(capture["config_path"]).exists())
        self.assertEqual((self.root / "lakefile.toml").read_text(), self.source)

    def test_next_build_discovers_new_publications_and_modules(self) -> None:
        paper = self.paper("FirstPaper")
        first = self.run_helper("build")
        self.paper("LaterNote", "Notes")
        (paper / "Formalization" / "FirstPaper" / "Later.lean").write_text(
            "theorem later : True := True.intro\n"
        )
        later = self.run_helper("build")
        self.assertNotEqual(first["command"], later["command"])
        self.assertIn("Publication_Notes_LaterNote", later["command"])
        library = next(
            library for library in later["config"]["lean_lib"]
            if library["name"] == "Publication_Papers_FirstPaper"
        )
        self.assertIn("FirstPaper.Later", library["globs"])
        self.assertEqual((self.root / "lakefile.toml").read_text(), self.source)

    def test_axiom_check_imports_and_audits_every_publication_module(self) -> None:
        paper = self.paper("ExamplePaper")
        self.paper("ExampleNote", "Notes")
        section = paper / "Formalization" / "Section_1"
        section.mkdir()
        (section / "Introduction.lean").write_text("theorem intro : True := True.intro\n")
        result = subprocess.run(
            ["bash", self.root / "scripts" / "check_axioms.sh"],
            cwd=self.root, env=self.environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        lean_input = json.loads(self.capture.read_text())["lean_input"]
        for name in ("ExamplePaper", "ExamplePaper.Result", "ExampleNote",
                     "ExampleNote.Result", "Section_1.Introduction"):
            self.assertIn(f"import {name}\n", lean_input)
            self.assertIn(f"`{name}", lean_input)
        self.assertNotIn("challenge", lean_input)
        self.assertIn("publicationModules.contains name", lean_input)

    def test_namespace_collisions_fail_before_building(self) -> None:
        for name in ("FirstPaper", "SecondPaper"):
            paper = self.paper(name)
            shared = paper / "Formalization" / "SharedSection"
            shared.mkdir()
            (shared / f"{name}.lean").write_text("theorem result : True := True.intro\n")
        with self.assertRaisesRegex(ValueError, "unique module namespace"):
            discover(self.root, self.config)

    def test_incomplete_publications_are_not_silently_skipped(self) -> None:
        paper = self.root / "Formalized Publications" / "Papers" / "IncompletePaper"
        paper.mkdir(parents=True)
        (paper / "Readme.md").write_text("# Incomplete paper\n")
        with self.assertRaisesRegex(ValueError, "Formalization directory"):
            discover(self.root, self.config)

    def test_missing_root_module_fails(self) -> None:
        paper = self.paper("ExamplePaper")
        (paper / "Formalization" / "ExamplePaper.lean").unlink()
        with self.assertRaisesRegex(ValueError, "ExamplePaper.lean"):
            discover(self.root, self.config)

    def test_symlinks_cannot_redirect_publication_sources(self) -> None:
        paper = self.paper("ExamplePaper")
        archived = self.root / "Archived.lean"
        archived.write_text("axiom hidden : False\n")
        (paper / "Formalization" / "ExamplePaper" / "Linked.lean").symlink_to(archived)
        with self.assertRaisesRegex(ValueError, "symlinked paths"):
            discover(self.root, self.config)

    def test_publications_cannot_shadow_dependency_or_extension_modules(self) -> None:
        paper = self.paper("ExamplePaper")
        for name in ("Mathlib", "MathlibExt"):
            with self.subTest(name=name):
                path = paper / "Formalization" / f"{name}.lean"
                path.write_text("theorem hidden : True := True.intro\n")
                with self.assertRaisesRegex(ValueError, "shadows an existing library"):
                    discover(self.root, self.config)
                path.unlink()

    def test_publication_parent_directory_cannot_be_a_symlink(self) -> None:
        self.paper("ExamplePaper")
        directory = self.root / "Formalized Publications"
        target = self.root / "RedirectedPublications"
        directory.rename(target)
        directory.symlink_to(target, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlinked publication directory"):
            discover(self.root, self.config)

    def test_lake_failure_is_propagated_and_configuration_is_cleaned_up(self) -> None:
        self.paper("ExamplePaper")
        capture = self.run_helper("build", status=17)
        self.assertFalse(Path(capture["config_path"]).exists())
        self.assertEqual((self.root / "lakefile.toml").read_text(), self.source)


if __name__ == "__main__":
    unittest.main()
