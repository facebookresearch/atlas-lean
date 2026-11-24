#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Checks the import runner's protocol, source edits, and verification gate."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from optimize_imports import (
    Header,
    ImportSpec,
    ImportSpan,
    Proposal,
    Tools,
    compare_snapshots,
    decode_header,
    legacy_proposal,
    optimize_one,
    parse_import_array,
    parse_shake_output,
    rewrite_imports,
    recover_source_edit,
    run_command,
    source_path,
)


class ImportProtocolTests(unittest.TestCase):
    def test_modifiers_and_escaped_comma(self) -> None:
        imports = parse_import_array(
            "#[public meta import all A.«b, c».δ, import Mathlib.Data.Set.Basic]"
        )
        self.assertEqual(imports[0].module, "A.«b, c».δ")
        self.assertEqual(imports[0].modifiers, ("public", "meta", "all"))
        self.assertEqual(imports[1].render(), "import Mathlib.Data.Set.Basic")

    def test_rejects_unclosed_array_and_identifier(self) -> None:
        for text in ("#[import A", "#[import A.«B]", "#[import A,]"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_import_array(text)

    def test_selected_module_and_notes_are_distinct(self) -> None:
        path = Path("/project/Example.lean")
        proposal = parse_shake_output(
            "/project/Other.lean:\n  remove #[import Unrelated]\n"
            "/project/Example.lean:\n  remove #[public import Mathlib]\n"
            "  add #[public import Mathlib.Data.Set.Finite.Basic]\n"
            "  note: `public import Init` required\n    (no traced reason)\n",
            1,
            path,
        )
        self.assertEqual(proposal.remove, (ImportSpec("Mathlib", ("public",)),))
        self.assertEqual(proposal.add[0].module, "Mathlib.Data.Set.Finite.Basic")
        self.assertEqual(len(proposal.add), 1)

    def test_errors_cannot_masquerade_as_suggestions(self) -> None:
        output = "/project/Example.lean:\n  remove #[import Mathlib]\n"
        for text, code in (
            (output + "error: module Other not found\n", 1),
            (output, 143),
            ("", 0),
            ("/project/Other.lean:\n  remove #[import Mathlib]\n", 1),
        ):
            with self.subTest(text=text, code=code), self.assertRaises(ValueError):
                parse_shake_output(text, code, Path("/project/Example.lean"))

    def test_unchanged_module_has_a_positive_record(self) -> None:
        proposal = parse_shake_output(
            "/project/Example.lean:\n  note: `public import Init` required\n", 0,
            Path("/project/Example.lean"),
        )
        self.assertEqual(proposal.remove, ())
        self.assertEqual(proposal.add, ())

    def test_indented_fatal_error_rejects_partial_suggestions(self) -> None:
        output = "/project/Example.lean:\n  remove #[import Mathlib]\n"
        with self.assertRaises(ValueError):
            parse_shake_output(output + "  error: interrupted analysis\n", 1,
                               Path("/project/Example.lean"))


class ImportEditTests(unittest.TestCase):
    @staticmethod
    def header(source: bytes, directive: bytes) -> Header:
        start = source.index(directive)
        end = start + len(directive)
        boundary = source.index(b"\n", end) + 1
        return Header(
            True,
            (ImportSpan(ImportSpec.parse(directive.decode()), start, end),),
            boundary,
            boundary,
        )

    def test_unicode_and_trailing_comment_are_preserved(self) -> None:
        source = (
            "-- α source\nmodule -- shake: keep-downstream\n"
            "public import Mathlib -- explanation\n\n"
            "@[expose] public section\ndef claim : Prop := True\n"
        ).encode()
        header = self.header(source, b"public import Mathlib")
        changed = rewrite_imports(
            source, header, (ImportSpec("Mathlib", ("public",)),),
            (ImportSpec("Mathlib.Data.Set.Finite.Basic", ("public",)),),
        )
        self.assertIn(b"public import Mathlib.Data.Set.Finite.Basic\n", changed)
        self.assertIn(b"-- explanation\n", changed)
        self.assertIn(b"module -- shake: keep-downstream\n", changed)
        self.assertEqual(
            changed.split(b"@[expose]", 1)[1], source.split(b"@[expose]", 1)[1]
        )

    def test_interstitial_comments_require_manual_edit(self) -> None:
        source = b"module\npublic /- keep this -/ import Mathlib\ndef x := 0\n"
        start = source.index(b"public")
        stop = source.index(b"Mathlib") + len(b"Mathlib")
        header = Header(
            True, (ImportSpan(ImportSpec("Mathlib", ("public",)), start, stop),),
            stop + 1, stop + 1,
        )
        with self.assertRaisesRegex(ValueError, "comment"):
            rewrite_imports(source, header, header.specs(), ())

    def test_unknown_removal_is_rejected(self) -> None:
        source = b"module\nimport Mathlib\ndef x := 0\n"
        with self.assertRaisesRegex(ValueError, "absent"):
            rewrite_imports(
                source, self.header(source, b"import Mathlib"),
                (ImportSpec("Unknown", ()),), (),
            )

    def test_indented_import_can_be_replaced_without_overlapping_edits(self) -> None:
        source = b"module\n  public import Mathlib\n\ndef x := 0\n"
        header = self.header(source, b"public import Mathlib")
        changed = rewrite_imports(source, header, header.specs(),
                                  (ImportSpec("Mathlib.Data.Nat.Basic", ("public",)),))
        self.assertEqual(changed,
                         b"module\npublic import Mathlib.Data.Nat.Basic\n\ndef x := 0\n")

    def test_crlf_and_declaration_bytes_are_preserved(self) -> None:
        source = "-- α\r\nmodule\r\nimport Mathlib\r\n\r\ndef x := 0\r\n".encode()
        header = self.header(source, b"import Mathlib")
        changed = rewrite_imports(source, header, header.specs(),
                                  (ImportSpec("Mathlib.Data.Nat.Basic"),))
        self.assertEqual(changed,
                         "-- α\r\nmodule\r\nimport Mathlib.Data.Nat.Basic\r\n\r\ndef x := 0\r\n".encode())

    def test_native_header_rejects_normalized_byte_count(self) -> None:
        source = b"module\r\nimport Mathlib\r\ndef x := 0\r\n"
        row = {"status": "parsed", "source_utf8_bytes": len(source) - 3,
               "is_module": True, "imports": [], "insertion_byte": 8,
               "body_boundary_byte": 24}
        with self.assertRaisesRegex(ValueError, "byte"):
            decode_header(row, source)

    def test_external_and_parent_paths_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "Example.lean").write_text("module\n")
            self.assertEqual(source_path(root, "Example.lean"), root / "Example.lean")
            for name in ("../Other.lean", "/outside/Example.lean", "Example.txt"):
                with self.subTest(name=name), self.assertRaises(ValueError):
                    source_path(root, name)


class LegacyExportTests(unittest.TestCase):
    def test_owned_dependency_analysis_retains_transitive_exports(self) -> None:
        source = b"import Fixture.ExportOnly\nimport Fixture.Owned\n\ndef own : Nat := 0\n"
        spans = []
        for name in ("Fixture.ExportOnly", "Fixture.Owned"):
            directive = ("import " + name).encode()
            start = source.index(directive)
            spans.append(ImportSpan(ImportSpec(name), start, start + len(directive)))
        boundary = source.index(b"\n\n") + 2
        header = Header(False, tuple(spans), boundary, boundary)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            helpers = root / "helpers"
            helpers.mkdir()
            (helpers / "legacy.lean").write_text("External Lean backend is mocked\n")
            tools = Tools(root, root / "output", root / "lake", root / "lean", helpers, {}, 5,
                          time_binary=root / "time")

            def backend(argv: list[str], directory: Path) -> dict[str, object]:
                self.assertEqual(argv[-1], "Fixture.Provider")
                directory.parent.mkdir(parents=True)
                Path(str(directory) + ".stdout").write_text(json.dumps({
                    "module": "Fixture.Provider", "required_modules": ["Fixture.Owned"],
                }))
                Path(str(directory) + ".stderr").write_text("")
                command = {"argv": argv, "cwd": str(root), "exit_code": 0,
                           "timed_out": False, "remaining_group_killed": False,
                           "stdout": str(directory) + ".stdout", "stderr": str(directory) + ".stderr"}
                Path(str(directory) + ".json").write_text(json.dumps(command))
                return command

            with patch.object(Tools, "run", side_effect=backend) as run:
                proposal = legacy_proposal(tools, "Fixture.Provider", header, source, root / "analysis")
            run.assert_called_once()
            self.assertEqual(rewrite_imports(source, header, proposal.remove, proposal.add), source)
            self.assertEqual(json.loads((root / "analysis/legacy.stdout").read_text())["required_modules"],
                             ["Fixture.Owned"])

    def test_supplied_legacy_removal_cannot_be_verified_without_consumers(self) -> None:
        source = b"import Fixture.ExportOnly\n\ndef own : Nat := 0\n"
        start = 0
        end = source.index(b"\n")
        native = {"status": "parsed", "source_utf8_bytes": len(source), "is_module": False,
                  "insertion_byte": end + 1, "body_boundary_byte": end + 1,
                  "imports": [{"module": "Fixture.ExportOnly", "modifiers": [],
                               "source": {"span": {"start_byte": start, "end_byte": end}}}]}
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            (root / "Provider.lean").write_bytes(source)
            setup = root / ".lake/build/ir/Provider.setup.json"
            setup.parent.mkdir(parents=True)
            setup.write_text(json.dumps({"name": "Provider", "isModule": False, "imports": None,
                                         "importArts": {"Fixture.ExportOnly": {}, "Init": {}}}))
            tools = Tools(root, root / "output", root / "lake", root / "lean", root / "helpers", {}, 5,
                          time_binary=root / "time")
            row = {"path": "Provider.lean", "module": "Provider",
                   "source_sha256": hashlib.sha256(source).hexdigest()}
            proposal = Proposal((ImportSpec("Fixture.ExportOnly"),), (ImportSpec("Init"),))
            owned = {"module": "Provider", "declaration_count": 1, "loaded_module_count": 1,
                     "declarations": [{"name": "own", "level_params": [], "kind": "definition",
                                       "type": "Nat", "value": "Nat.zero", "is_unsafe": False,
                                       "is_partial": False, "is_exported": True,
                                       "is_private_name": False, "axioms": []}]}
            with patch("optimize_imports.artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
                    patch("optimize_imports.compile_arm", return_value={}) as compile_, \
                    patch("optimize_imports.snapshot_arm", return_value=owned) as snapshot:
                result = optimize_one(tools, row, native, proposal, {"exit_code": 0, "timed_out": False, "remaining_group_killed": False})
            self.assertEqual(result["status"], "blocked")
            self.assertIn("consumer validation", result["error"])
            compile_.assert_not_called()
            snapshot.assert_not_called()
            self.assertEqual((root / "Provider.lean").read_bytes(), source)


class SnapshotTests(unittest.TestCase):
    @staticmethod
    def snapshot(value: str = "Nat.zero") -> dict[str, object]:
        return {
            "module": "Example",
            "loaded_modules": ["Init", "Mathlib"],
            "declarations": [{
                "name": "Example.x", "level_params": [], "kind": "defn",
                "type": "Nat", "value": value, "is_unsafe": False,
                "axioms": ["propext", "Classical.choice"],
            }],
        }

    def test_loaded_module_reduction_and_axiom_order_are_allowed(self) -> None:
        before, after = self.snapshot(), self.snapshot()
        after["loaded_modules"] = ["Init"]
        after["declarations"][0]["axioms"].reverse()
        self.assertEqual(compare_snapshots(before, after), [])

    def test_same_type_with_different_definition_is_rejected(self) -> None:
        findings = compare_snapshots(self.snapshot(), self.snapshot("Nat.succ Nat.zero"))
        self.assertTrue(findings)
        self.assertIn("Example.x", findings[0])

    def test_missing_declaration_and_changed_axioms_are_rejected(self) -> None:
        before, after = self.snapshot(), self.snapshot()
        after["declarations"] = []
        self.assertTrue(compare_snapshots(before, after))
        after = self.snapshot()
        after["declarations"][0]["axioms"].append("sorryAx")
        self.assertTrue(compare_snapshots(before, after))


class RunnerFailureTests(unittest.TestCase):
    def test_child_failure_is_recorded_as_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            result = run_command(["/bin/sh", "-c", "printf partial; exit 37"],
                                 root, root / "command", {}, 5)
            self.assertEqual(result["exit_code"], 37)
            self.assertEqual((root / "command.stdout").read_text(), "partial")
            self.assertTrue((root / "command.json").is_file())

    def test_legacy_candidate_requires_manual_restoration(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / "Example.lean"
            original = b"module\nimport Mathlib\ndef x := 0\n"
            candidate = b"module\nimport Init\ndef x := 0\n"
            backup = root / "original.lean"
            backup.write_bytes(original)
            source.write_bytes(candidate)
            transaction = root / "transaction.json"
            transaction.write_text(json.dumps({
                "path": "Example.lean", "backup": str(backup),
                "source_sha256": hashlib.sha256(original).hexdigest(),
                "candidate_sha256": hashlib.sha256(candidate).hexdigest(),
            }))
            with self.assertRaisesRegex(ValueError, "Legacy candidate remains"):
                recover_source_edit(root, transaction)
            self.assertEqual(source.read_bytes(), candidate)
            self.assertEqual(backup.read_bytes(), original)
            self.assertTrue(transaction.exists())
            source.write_bytes(backup.read_bytes())
            recover_source_edit(root, transaction)
            self.assertEqual(source.read_bytes(), original)
            self.assertFalse(transaction.exists())


if __name__ == "__main__":
    unittest.main()
