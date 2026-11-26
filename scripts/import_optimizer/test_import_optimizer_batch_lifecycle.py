#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Root-package inventory custody across batches and resume; Lake and Lean are mocked."""

from __future__ import annotations

import contextlib
import io
import json
import os
import shutil
import sys
import tempfile
import time
import unittest
from collections.abc import Callable, Iterator
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_recovery as recovery

NAMES = ("A", "B", "C")


def lifecycle_inputs(root: Path) -> list[str]:
    """Three independent targets whose local dependencies share one namespace.

    Each target `X` imports `Lib.Base` and depends on `Lib.Sub.X`, which its
    batch's Lake preparation builds into the inventoried `Lib` namespace.
    """
    arguments = recovery.main_inputs(root, NAMES) + ["--batch-size", "1"]
    base = root / ".lake/build/lib/lean/Lib/Base.olean"
    base.parent.mkdir(parents=True)
    base.write_bytes(b"Lib.Base artifact fixture\n")
    manifest = root / "manifest.jsonl"
    rows = [json.loads(line) for line in manifest.read_text().splitlines()]
    for row in rows:
        row["direct_local_dependencies"] = ["Lib.Base", "Lib.Sub." + row["module"]]
        setup = root / ".lake/build/ir" / (row["module"] + ".setup.json")
        metadata = optimizer.read_json(setup)
        metadata["importArts"] = {"Lib.Base": [[str(base)], []], "Init": [[], []]}
        optimizer.write_json(setup, metadata)
    manifest.write_text("".join(json.dumps(row) + "\n" for row in rows))
    # The compiler standard library is LEAN_SYSROOT/lib/lean; the mocked Lake
    # environment reports the project root as LEAN_SYSROOT.
    library = root / "lib/lean/Init/Prelude.olean"
    library.parent.mkdir(parents=True)
    library.write_bytes(b"Init.Prelude artifact fixture\n")
    return arguments


@contextlib.contextmanager
def mocked_lake(root: Path, during_build: Callable[[str], None] | None = None,
                skip_growth: frozenset[str] = frozenset(),
                rewrite_existing: bool = True) -> Iterator[list[list[str]]]:
    builds: list[list[str]] = []
    namespace = root / ".lake/build/lib/lean/Lib/Sub"

    def external(argv: list[str], label: Path,
                 environment: dict[str, str] | None = None) -> dict[str, object]:
        if "build" not in argv or "--no-build" in argv:
            raise AssertionError(f"Unexpected external command: {argv}")
        targets = [word[1:] for word in argv if word.startswith("+")]
        builds.append(targets)
        # Lake builds each target's local dependency into the root build tree.
        namespace.mkdir(exist_ok=True)
        for target in targets:
            artifact = namespace / (target + ".olean")
            # Real Lake leaves an up-to-date target's artifacts alone.
            if target not in skip_growth and (rewrite_existing or not artifact.exists()):
                artifact.write_bytes(f"Lib.Sub.{target} artifact fixture\n".encode())
            if during_build is not None:
                during_build(target)
        label.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
        stdout.write_text("External Lake build fixture\n")
        stderr.write_text("")
        return {"argv": argv, "cwd": str(root), "exit_code": 0, "timed_out": False,
                "remaining_group_killed": False, "stdout": str(stdout), "stderr": str(stderr)}

    with patch.object(optimizer.signal, "signal"), \
            patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
            patch.object(optimizer, "run_command", side_effect=recovery.environment_stub), \
            patch.object(optimizer.Tools, "run", side_effect=external), \
            patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifact_mock": True}]), \
            patch.object(optimizer, "analyze_batch", side_effect=recovery.mock_no_change_proposals), \
            patch.object(optimizer, "compile_arm", side_effect=AssertionError("Unexpected Lean compile")), \
            contextlib.redirect_stdout(io.StringIO()):
        yield builds


def replace_same_bytes(path: Path) -> None:
    copy = path.with_name(path.name + ".copy")
    copy.write_bytes(path.read_bytes())
    os.replace(copy, path)


def rewrite_and_restore(path: Path) -> None:
    original = path.read_bytes()
    with path.open("r+b") as stream:
        stream.write(b"X" * len(original))
    time.sleep(0.01)
    with path.open("r+b") as stream:
        stream.write(original)


def chmod_and_restore(path: Path) -> None:
    mode = path.stat().st_mode & 0o7777
    path.chmod(0o600 if mode != 0o600 else 0o644)
    time.sleep(0.01)
    path.chmod(mode)


def fresh(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(b"not requested\n")


def journal(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "output/results.jsonl").read_text().splitlines()]


def manifest_paths(row: dict[str, object]) -> list[str]:
    proposal = optimizer.read_json(Path(row["proposal_receipt"]["path"]))
    compiled = proposal["analysis"]["inputs"]["compiled_inputs"][row["path"]]
    return [entry["path"] for entry in optimizer.read_json(Path(compiled["input_manifest"]["path"]))["files"]]


def completed_run(root: Path) -> list[str]:
    arguments = lifecycle_inputs(root)
    with mocked_lake(root) as builds, patch.object(sys, "argv", arguments):
        assert optimizer.main() == 0
    assert builds == [["A"], ["B"], ["C"]], builds
    return arguments


class BatchLifecycleTests(unittest.TestCase):
    def test_later_batches_accept_lake_growth_in_an_inventoried_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            completed_run(root)
            rows = journal(root)
            self.assertEqual([(row["path"], row["status"]) for row in rows],
                             [("A.lean", "no_change"), ("B.lean", "no_change"), ("C.lean", "no_change")])
            # Each batch pinned a fresh inventory that includes the growth.
            namespace = root / ".lake/build/lib/lean/Lib"
            for row, seen in zip(rows, (("A",), ("A", "B"), ("A", "B", "C"))):
                paths = manifest_paths(row)
                self.assertEqual([path for path in paths if path.startswith(str(namespace / "Sub"))],
                                 [str(namespace / "Sub" / (name + ".olean")) for name in seen])
                self.assertIn(str(namespace / "Base.olean"), paths)
                self.assertIn(str(root / "lib/lean/Init/Prelude.olean"), paths)
            # Each preparation recorded exactly its additions to the existing namespace.
            growth = optimizer.read_lake_growth(root / "output")
            self.assertEqual(sorted(growth), [str(namespace / "Sub" / (name + ".olean")) for name in NAMES])

    def test_outside_change_between_batches_blocks_every_later_batch(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = lifecycle_inputs(root)
            journal_path = root / "output/results.jsonl"
            injected = root / ".lake/build/lib/lean/Lib/Sub/Injected.olean"
            validate = optimizer.validate_inventory_sources

            def inject_after_first_journal(*args: object, **kwargs: object) -> None:
                if (not injected.exists() and journal_path.exists() and
                        len(journal_path.read_text().splitlines()) == 1):
                    injected.write_bytes(b"Not written by Lake\n")
                return validate(*args, **kwargs)

            with mocked_lake(root) as builds, patch.object(sys, "argv", arguments), \
                    patch.object(optimizer, "validate_inventory_sources", side_effect=inject_after_first_journal):
                self.assertEqual(optimizer.main(), 1)
            self.assertTrue(injected.exists())
            self.assertEqual(builds, [["A"]])
            rows = journal(root)
            self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "blocked"])
            self.assertEqual(rows[1]["error"], "Compiler standard-library inventory changed: "
                             f"{root / '.lake/build/lib/lean/Lib/Sub'}")
            self.assertEqual(rows[2]["error"], "An earlier Lake preparation was rejected: " + rows[1]["error"])

    def test_lake_preparation_may_only_add_new_requested_modules(self) -> None:
        build = Path(".lake/build/lib/lean")
        cases = {
            "rewrite_pinned": (lambda root: (root / build / "Lib/Base.olean").write_bytes(b"rebuilt\n"),
                               "Pinned root-package artifact changed (ctime, mtime, size): {}",
                               build / "Lib/Base.olean"),
            "remove_pinned": (lambda root: (root / build / "Lib/Sub/A.olean").unlink(),
                              "Pinned root-package artifact was removed: {}", build / "Lib/Sub/A.olean"),
            "same_bytes_replace": (lambda root: replace_same_bytes(root / build / "Lib/Base.olean"),
                                   "Pinned root-package artifact changed (ino, ctime, mtime): {}",
                                   build / "Lib/Base.olean"),
            "in_place_restore": (lambda root: rewrite_and_restore(root / build / "Lib/Base.olean"),
                                 "Pinned root-package artifact changed (ctime, mtime): {}",
                                 build / "Lib/Base.olean"),
            "chmod_restore": (lambda root: chmod_and_restore(root / build / "Lib/Base.olean"),
                              "Pinned root-package artifact changed (ctime): {}", build / "Lib/Base.olean"),
            "unrequested_module": (lambda root: (root / build / "Lib/Sub/Injected.olean").write_bytes(b"x\n"),
                                   "Lake preparation added an artifact outside its requested modules: {}",
                                   build / "Lib/Sub/Injected.olean"),
            "new_part_of_existing_module": (
                lambda root: (root / build / "Lib/Base.olean.server").write_bytes(b"x\n"),
                "Lake preparation added an artifact for an existing module: {}", build / "Lib/Base.olean.server"),
            "compiler_library": (lambda root: (root / "lib/lean/Init/Extra.olean").write_bytes(b"new\n"),
                                 "Compiler standard-library inventory changed: {}", Path("lib/lean/Init")),
            "fresh_namespace": (lambda root: fresh(root / build / "Fresh/Unrequested.olean"),
                                "Lake preparation added an artifact outside its requested modules: {}",
                                build / "Fresh/Unrequested.olean"),
            "fresh_compiler_module": (lambda root: fresh(root / build / "Init/Prelude.olean"),
                                      "Lake preparation added an artifact outside its requested modules: {}",
                                      build / "Init/Prelude.olean"),
            "top_level_module": (lambda root: fresh(root / build / "Top.olean"),
                                 "Lake preparation added an artifact outside its requested modules: {}",
                                 build / "Top.olean"),
        }
        for name, (mutate, message, path) in cases.items():
            with self.subTest(mutation=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = lifecycle_inputs(root)

                def during_build(target: str) -> None:
                    if target == "B":
                        mutate(root)

                with mocked_lake(root, during_build) as builds, patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 1)
                self.assertEqual(builds, [["A"], ["B"]])
                rows = journal(root)
                self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "blocked"])
                self.assertEqual(rows[1]["error"], message.format(root / path))
                # The rejection is sticky; batch 3 never runs Lake.
                self.assertEqual(rows[2]["error"], "An earlier Lake preparation was rejected: " + rows[1]["error"])
                # Batch 1's additions are recorded; rejected additions never are.
                self.assertEqual(sorted(optimizer.read_lake_growth(root / "output")),
                                 [str(root / build / "Lib/Sub/A.olean")])


    def test_rejected_fresh_additions_stay_rejected(self) -> None:
        build = Path(".lake/build/lib/lean")
        for name, addition in (("namespace", build / "Fresh/Unrequested.olean"), ("top_level", build / "Top.olean"),
                               ("compiler_module", build / "Init/Prelude.olean")):
            with self.subTest(addition=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = lifecycle_inputs(root)

                def during_build(target: str) -> None:
                    if target == "B":
                        fresh(root / addition)

                # Batch 2 adds only the rejected artifact; no inventoried namespace grows.
                with mocked_lake(root, during_build, frozenset({"B"})) as builds, \
                        patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 1)
                self.assertEqual(builds, [["A"], ["B"]])
                rows = journal(root)
                self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "blocked"])
                self.assertEqual(rows[1]["error"], "Lake preparation added an artifact outside its requested "
                                 f"modules: {root / addition}")
                self.assertEqual(rows[2]["error"], "An earlier Lake preparation was rejected: " + rows[1]["error"])

    def test_in_place_change_between_preparations_blocks_before_lake(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = lifecycle_inputs(root)
            journal_path = root / "output/results.jsonl"
            base = root / ".lake/build/lib/lean/Lib/Base.olean"
            changed: list[bool] = []
            validate = optimizer.validate_inventory_sources

            def change_after_first_journal(*args: object, **kwargs: object) -> None:
                if not changed and journal_path.exists() and len(journal_path.read_text().splitlines()) == 1:
                    before = base.stat()
                    base.write_bytes(b"X" * before.st_size)
                    os.utime(base, ns=(before.st_atime_ns, before.st_mtime_ns))
                    changed.append(True)
                return validate(*args, **kwargs)

            with mocked_lake(root) as builds, patch.object(sys, "argv", arguments), \
                    patch.object(optimizer, "validate_inventory_sources", side_effect=change_after_first_journal):
                self.assertEqual(optimizer.main(), 1)
            self.assertEqual(builds, [["A"]])
            rows = journal(root)
            self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "blocked"])
            self.assertEqual(rows[1]["error"], f"Pinned root-package artifact changed (ctime): {base}")
            self.assertEqual(rows[2]["error"], "An earlier Lake preparation was rejected: " + rows[1]["error"])


class ResumeLifecycleTests(unittest.TestCase):
    def resume(self, root: Path, arguments: list[str]) -> tuple[int, list[list[str]]]:
        with mocked_lake(root) as builds, patch.object(sys, "argv", [*arguments, "--resume"]):
            return optimizer.main(), builds

    def test_resume_accepts_recorded_growth_byte_identically(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = completed_run(root)
            before = (root / "output/results.jsonl").read_bytes()
            self.assertEqual(self.resume(root, arguments), (0, []))
            self.assertEqual((root / "output/results.jsonl").read_bytes(), before)

    def test_resume_takes_custody_of_saved_pins_before_later_preparations(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = lifecycle_inputs(root)
            with mocked_lake(root) as builds, patch.object(sys, "argv", [*arguments, "--max-batches", "1"]):
                self.assertEqual(optimizer.main(), 0)
            self.assertEqual(builds, [["A"]])
            first = (root / "output/results.jsonl").read_bytes()
            base = root / ".lake/build/lib/lean/Lib/Base.olean"
            verify = optimizer.verify_saved_no_change

            def touch_after_validation(result: dict[str, object], tools: optimizer.Tools) -> None:
                verify(result, tools)
                # Same bytes and directory: only the custody taken at resume can see it.
                chmod_and_restore(base)

            with mocked_lake(root) as builds, patch.object(sys, "argv", [*arguments, "--resume"]), \
                    patch.object(optimizer, "verify_saved_no_change", side_effect=touch_after_validation):
                self.assertEqual(optimizer.main(), 1)
            self.assertEqual(builds, [])
            journal_bytes = (root / "output/results.jsonl").read_bytes()
            self.assertTrue(journal_bytes.startswith(first))
            rows = journal(root)
            self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "blocked"])
            self.assertEqual(rows[1]["error"], f"Pinned root-package artifact changed (ctime): {base}")

    def test_bounded_invocations_keep_earlier_rows_byte_identical(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = lifecycle_inputs(root)
            journal_path = root / "output/results.jsonl"
            previous = b""
            for invocation, expected in enumerate((["A"], ["B"], ["C"])):
                extra = ["--max-batches", "1"] + (["--resume"] if invocation else [])
                with mocked_lake(root) as builds, patch.object(sys, "argv", [*arguments, *extra]):
                    self.assertEqual(optimizer.main(), 0)
                self.assertEqual(builds, [expected])
                current = journal_path.read_bytes()
                self.assertTrue(current.startswith(previous))
                self.assertEqual(len(current.splitlines()), invocation + 1)
                previous = current
            self.assertEqual([row["status"] for row in journal(root)], ["no_change"] * 3)
            self.assertEqual(self.resume(root, arguments), (0, []))
            self.assertEqual(journal_path.read_bytes(), previous)
            custody = root / "output" / optimizer.LAKE_CUSTODY_DIRECTORY
            self.assertFalse((custody / "rejected.json").exists())
            self.assertEqual(optimizer.read_json(custody / "listing.json"), {"namespaces": ["Lib"], "files": []})

    def test_bounded_resume_keeps_a_rejection_from_an_earlier_invocation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = lifecycle_inputs(root)
            rejected = root / ".lake/build/lib/lean/Fresh/Unrequested.olean"

            def during_build(target: str) -> None:
                if target == "B":
                    fresh(rejected)

            runs = []
            for extra in (["--max-batches", "1"], ["--max-batches", "1", "--resume"], ["--resume"]):
                with mocked_lake(root, during_build, frozenset({"B"})) as builds, \
                        patch.object(sys, "argv", [*arguments, *extra]):
                    runs.append((optimizer.main(), list(builds)))
            self.assertEqual(runs, [(0, [["A"]]), (1, [["B"]]), (1, [])])
            self.assertTrue(rejected.exists())
            rows = journal(root)
            self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "blocked"])
            message = f"Lake preparation added an artifact outside its requested modules: {rejected}"
            self.assertEqual(rows[1]["error"], message)
            self.assertEqual(rows[2]["error"], "An earlier Lake preparation was rejected: " + message)
            record = optimizer.read_json(root / "output" / optimizer.LAKE_CUSTODY_DIRECTORY / "rejected.json")
            self.assertEqual(record["error"], message)

    def test_bounded_resume_rejects_a_root_entry_created_between_invocations(self) -> None:
        for entry in ("Init/Prelude.olean", "Extra.olean"):
            with self.subTest(entry=entry), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = lifecycle_inputs(root)
                with mocked_lake(root) as builds, patch.object(sys, "argv", [*arguments, "--max-batches", "1"]):
                    self.assertEqual(optimizer.main(), 0)
                self.assertEqual(builds, [["A"]])
                build = root / ".lake/build/lib/lean"
                fresh(build / entry)
                with mocked_lake(root) as builds, patch.object(sys, "argv", [*arguments, "--resume"]):
                    self.assertEqual(optimizer.main(), 1)
                self.assertEqual(builds, [])
                rows = journal(root)
                self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "blocked"])
                message = f"Root artifact root changed since the last Lake preparation: {build / entry.split('/')[0]}"
                self.assertEqual(rows[1]["error"], message)
                self.assertEqual(rows[2]["error"], "An earlier Lake preparation was rejected: " + message)

    def test_resume_without_recorded_growth_rejects_earlier_rows(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = completed_run(root)
            before = (root / "output/results.jsonl").read_bytes()
            shutil.rmtree(root / "output" / optimizer.LAKE_GROWTH_DIRECTORY)
            with self.assertRaisesRegex(ValueError, "Saved Shake proposal inputs changed|unrecorded artifact"):
                self.resume(root, arguments)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), before)

    def test_resume_rejects_outside_growth_and_changed_artifacts(self) -> None:
        build = Path(".lake/build/lib/lean")
        cases = {
            "outside_growth": (lambda root: (root / build / "Lib/Sub/Injected.olean").write_bytes(b"x\n"),
                               "unrecorded artifact"),
            "outside_namespace": (lambda root: (root / build / "Lib/Other.olean").write_bytes(b"x\n"),
                                  "unrecorded artifact"),
            "old_artifact_bytes": (lambda root: (root / build / "Lib/Base.olean").write_bytes(b"corrupt\n"),
                                   "Saved root-package artifact is missing or changed since it was pinned: "
                                   ".*/Lib/Base.olean"),
            "recorded_artifact_bytes": (lambda root: (root / build / "Lib/Sub/C.olean").write_bytes(b"corrupt\n"),
                                        "Saved root-package artifact is missing or changed since it was pinned: "
                                        ".*/Lib/Sub/C.olean"),
            "compiler_library": (lambda root: (root / "lib/lean/Init/Extra.olean").write_bytes(b"new\n"),
                                 "unrecorded artifact"),
        }
        for name, (mutate, message) in cases.items():
            with self.subTest(mutation=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                arguments = completed_run(root)
                before = (root / "output/results.jsonl").read_bytes()
                mutate(root)
                with self.assertRaisesRegex(ValueError, message):
                    self.resume(root, arguments)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), before)

    def test_resume_rejects_recorded_growth_that_provides_a_consumed_module(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = completed_run(root)
            before = (root / "output/results.jsonl").read_bytes()
            server = root / ".lake/build/lib/lean/Lib/Base.ir"
            server.write_bytes(b"A second part for the consumed Lib.Base\n")
            optimizer.write_json(root / "output" / optimizer.LAKE_GROWTH_DIRECTORY / "9.json",
                                 {"preparation": "forged", "added": [optimizer.file_pin(server)]})
            with self.assertRaisesRegex(ValueError, "provider for a consumed module"):
                self.resume(root, arguments)
            self.assertEqual((root / "output/results.jsonl").read_bytes(), before)


class LakePreparationCustodyTests(unittest.TestCase):
    def tools(self, root: Path) -> optimizer.Tools:
        return optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean", root,
                               {"LEAN_SYSROOT": str(root / "sysroot")}, 5, time_binary=root / "bin/time")

    def test_only_inventories_wholly_inside_the_build_root_are_renewed(self) -> None:
        for grown in ("root", "external", "compiler"):
            with self.subTest(grown=grown), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                build = root / ".lake/build/lib/lean"
                (build / "Lib").mkdir(parents=True)
                (build / "Lib/Base.olean").write_bytes(b"root artifact\n")
                external = root / "dependency/Ext"
                external.mkdir(parents=True)
                (external / "Dep.olean").write_bytes(b"dependency artifact\n")
                (build / "Ext").symlink_to(external, target_is_directory=True)
                library = root / "sysroot/lib/lean"
                (library / "Init").mkdir(parents=True)
                (library / "Init/Prelude.olean").write_bytes(b"compiler artifact\n")
                tools = self.tools(root)
                for path in (build / "Lib", build / "Ext", library):
                    optimizer.standard_library_paths(path, tools)
                target = {"root": build / "Lib/New.olean", "external": external / "New.olean",
                          "compiler": library / "Init/New.olean"}[grown]
                if grown == "root":
                    self.prepare(tools, lambda: fresh(target), {"Lib.New"})
                    # The root namespace was taken again with the addition; the others kept old custody.
                    self.assertEqual(tools.library_inventories[build / "Lib"][0],
                                     (str(build / "Lib/Base.olean"), str(target)))
                    self.assertIn(build / "Ext", tools.library_inventories)
                    self.assertEqual(list(optimizer.read_lake_growth(root / "output")), [str(target)])
                else:
                    with self.assertRaisesRegex(ValueError, "inventory changed"):
                        self.prepare(tools, lambda: fresh(target), {"Lib.New"})
                    self.assertEqual(optimizer.read_lake_growth(root / "output"), {})

    def test_addition_providing_a_compiler_module_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            build = root / ".lake/build/lib/lean"
            (build / "Init").mkdir(parents=True)
            (build / "Init/Local.olean").write_bytes(b"root artifact\n")
            library = root / "sysroot/lib/lean"
            (library / "Init").mkdir(parents=True)
            (library / "Init/Prelude.olean").write_bytes(b"compiler artifact\n")
            tools = self.tools(root)
            for path in (build / "Init", library):
                optimizer.standard_library_paths(path, tools)

            def shadow(argv: list[str], label: Path, environment: dict[str, str] | None = None
                       ) -> dict[str, object]:
                (build / "Init/Prelude.olean").write_bytes(b"shadows the compiler's module\n")
                return {"exit_code": 0}

            with patch.object(optimizer.Tools, "run", side_effect=shadow), \
                    self.assertRaisesRegex(ValueError, "artifact for an existing module"):
                optimizer.run_lake_preparation(tools, ["lake", "build"], root / "output/prepare",
                                               frozenset({"Init.Prelude"}))
            # The rejection is sticky, so the next preparation is refused too.
            with patch.object(optimizer.Tools, "run", side_effect=AssertionError("Lake ran")), \
                    self.assertRaisesRegex(ValueError, "An earlier Lake preparation was rejected: "):
                optimizer.run_lake_preparation(tools, ["lake", "build"], root / "output/prepare",
                                               frozenset({"Init.Prelude"}))

    def prepare(self, tools: optimizer.Tools, change: Callable[[], None], modules: set[str]) -> None:
        def run(argv: list[str], label: Path, environment: dict[str, str] | None = None
                ) -> dict[str, object]:
            change()
            return {"exit_code": 0}

        with patch.object(optimizer.Tools, "run", side_effect=run):
            optimizer.run_lake_preparation(tools, ["lake", "build"], tools.output / "prepare",
                                           frozenset(modules))

    def build_tree(self, root: Path) -> tuple[optimizer.Tools, Path]:
        build = root / ".lake/build/lib/lean"
        (build / "Lib").mkdir(parents=True)
        (build / "Lib/Base.olean").write_bytes(b"root artifact\n")
        (build / "Other").mkdir()
        (build / "Other/X.olean").write_bytes(b"uninventoried namespace\n")
        (build / "Top.olean").write_bytes(b"top-level module\n")
        library = root / "sysroot/lib/lean/Init"
        library.mkdir(parents=True)
        (library / "Prelude.olean").write_bytes(b"compiler artifact\n")
        tools = self.tools(root)
        optimizer.standard_library_paths(build / "Lib", tools)
        optimizer.standard_library_paths(library.parent, tools)
        return tools, build

    def test_additions_outside_cached_namespaces_are_checked(self) -> None:
        cases = {
            "new_namespace_unrequested": (lambda build: fresh(build / "Fresh/Other.olean"), {"Fresh.Wanted"},
                                          "outside its requested modules: {build}/Fresh/Other.olean"),
            "new_namespace_compiler_module": (lambda build: fresh(build / "Init/Prelude.olean"), {"Init.Prelude"},
                                              "artifact for an existing module: {build}/Init/Prelude.olean"),
            "uncached_namespace_unrequested": (lambda build: fresh(build / "Other/Y.olean"), {"Other.Z"},
                                               "outside its requested modules: {build}/Other/Y.olean"),
            "uncached_namespace_existing_module": (lambda build: fresh(build / "Other/X.ir"), {"Other.X"},
                                                   "artifact for an existing module: {build}/Other/X.ir"),
            "new_top_level_unrequested": (lambda build: fresh(build / "Extra.olean"), {"Top"},
                                          "outside its requested modules: {build}/Extra.olean"),
            "existing_top_level_part": (lambda build: fresh(build / "Top.ir"), {"Top"},
                                        "artifact for an existing module: {build}/Top.ir"),
            "removed_top_level": (lambda build: (build / "Top.olean").unlink(), set(),
                                  "removed a root-package artifact: {build}/Top.olean"),
            "removed_uncached": (lambda build: (build / "Other/X.olean").unlink(), set(),
                                 "removed a root-package artifact: {build}/Other/X.olean"),
        }
        for name, (change, modules, message) in cases.items():
            with self.subTest(case=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build = self.build_tree(root)
                with self.assertRaises(ValueError) as raised:
                    self.prepare(tools, lambda: change(build), modules)
                self.assertTrue(str(raised.exception).endswith(message.format(build=build)), raised.exception)
                self.assertEqual(optimizer.read_lake_growth(tools.output), {})

    def test_requested_new_namespace_and_top_level_module_are_recorded(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, build = self.build_tree(root)

            def build_requested() -> None:
                fresh(build / "Fresh/Wanted.olean")
                fresh(build / "Fresh/Wanted.ir")
                fresh(build / "Next.olean")
                fresh(build / "Other/Y.olean")

            self.prepare(tools, build_requested, {"Fresh.Wanted", "Next", "Other.Y"})
            self.assertEqual(sorted(optimizer.read_lake_growth(tools.output)), [
                str(build / "Fresh/Wanted.ir"), str(build / "Fresh/Wanted.olean"),
                str(build / "Next.olean"), str(build / "Other/Y.olean")])
            # The new namespace is now under custody: a later outside change is rejected.
            (build / "Fresh/Injected.olean").write_bytes(b"outside writer\n")
            with self.assertRaisesRegex(ValueError, "inventory changed"):
                self.prepare(tools, lambda: None, set())

    def test_resume_sees_a_consumed_provider_through_its_symlinked_search_root(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            real = root / "pkg-real/lib"
            (real / "Dep").mkdir(parents=True)
            (real / "Dep/X.olean").write_bytes(b"dependency provider\n")
            (root / ".lake/packages/dep").mkdir(parents=True)
            (root / ".lake/packages/dep/lib").symlink_to(real, target_is_directory=True)
            lexical = root / ".lake/packages/dep/lib/Dep/X.olean"
            build = root / ".lake/build/lib/lean"
            build.mkdir(parents=True)
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean", root,
                                    {"LEAN_SYSROOT": str(root / "sysroot"),
                                     "LEAN_PATH": str(root / ".lake/packages/dep/lib")},
                                    5, time_binary=root / "bin/time")
            # The saved row pins the provider under Lake's lexical spelling, as a real setup does.
            metadata = {"name": "T", "isModule": True, "importArts": {"Dep.X": [[str(lexical)], []]}}
            paths = optimizer.compilation_input_paths(metadata, root, None, tools)
            # The actual saved row holds Lake's spelling and the resolved namespace inventory.
            self.assertEqual([path for path in paths if path.endswith("X.olean")],
                             [str(lexical), str(real / "Dep/X.olean")])
            saved = optimizer.pin_input_paths(tools, paths)
            addition = build / "Dep/X.ir"
            fresh(addition)
            grown = tuple(sorted((*paths, str(addition))))
            token = optimizer._recorded_lake_growth.set({str(addition): optimizer.file_pin(addition)})
            try:
                with self.assertRaisesRegex(ValueError, "provider for a consumed module: " + str(addition)):
                    optimizer.verify_input_manifest(saved, grown, tools.output, tools)
                # Lake's spelling alone must still name the provider.
                with self.assertRaisesRegex(ValueError, "provider for a consumed module: " + str(addition)):
                    optimizer.verify_recorded_growth(tools, (str(lexical),), (str(lexical), str(addition)))
            finally:
                optimizer._recorded_lake_growth.reset(token)

    def test_change_before_the_build_is_rejected_without_running_lake(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            namespace = root / ".lake/build/lib/lean/Lib"
            namespace.mkdir(parents=True)
            (namespace / "Base.olean").write_bytes(b"root artifact\n")
            tools = self.tools(root)
            optimizer.standard_library_paths(namespace, tools)
            (namespace / "Injected.olean").write_bytes(b"outside writer\n")
            run = AssertionError("Lake ran after a custody failure")
            with patch.object(optimizer.Tools, "run", side_effect=run), \
                    self.assertRaisesRegex(ValueError, "inventory changed"):
                optimizer.run_lake_preparation(tools, ["lake", "build"], root / "output/prepare",
                                               frozenset({"Lib.Injected"}))
            self.assertIn(namespace, tools.library_inventories)

    def test_grown_saved_manifest_is_never_reused_for_the_current_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            namespace = root / ".lake/build/lib/lean/Lib"
            namespace.mkdir(parents=True)
            (namespace / "Base.olean").write_bytes(b"root artifact\n")
            tools = self.tools(root)
            saved_paths = (str(namespace / "Base.olean"),)
            saved = optimizer.pin_input_paths(tools, saved_paths)
            added = namespace / "New.olean"
            added.write_bytes(b"recorded addition\n")
            grown = tuple(sorted((*saved_paths, str(added))))
            token = optimizer._recorded_lake_growth.set({str(added): optimizer.file_pin(added)})
            try:
                files = optimizer.verify_input_manifest(saved, grown, tools.output, tools)
            finally:
                optimizer._recorded_lake_growth.reset(token)
            self.assertEqual([row["path"] for row in files], list(saved_paths))
            self.assertNotIn(grown, tools.input_manifests)
            current = optimizer.pin_input_paths(tools, grown)
            self.assertEqual([row["path"] for row in optimizer.read_json(Path(current["path"]))["files"]],
                             list(grown))
            # A saved input that left the current set is never growth, even with a record.
            with self.assertRaisesRegex(ValueError, "different setup path set"):
                token = optimizer._recorded_lake_growth.set({str(added): optimizer.file_pin(added)})
                try:
                    optimizer.verify_recorded_growth(tools, (*saved_paths, str(namespace / "Gone.olean")), grown)
                finally:
                    optimizer._recorded_lake_growth.reset(token)
            # Outside resume validation the same difference is rejected.
            with self.assertRaisesRegex(ValueError, "different setup path set"):
                optimizer.verify_input_manifest(saved, grown, tools.output, tools)

    def test_failed_attempt_trusts_nothing_it_took(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, build = self.build_tree(root)
            cached = dict(tools.library_inventories)
            with self.assertRaisesRegex(ValueError, "outside its requested modules"):
                self.prepare(tools, lambda: fresh(build / "Fresh/Other.olean"), {"Fresh.Wanted"})
            self.assertEqual(tools.library_inventories, cached)
            self.assertNotIn("after", tools.root_listing)
            with patch.object(optimizer.Tools, "run", side_effect=AssertionError("Lake ran")), \
                    self.assertRaisesRegex(ValueError, "An earlier Lake preparation was rejected: .*Fresh/Other"):
                optimizer.run_lake_preparation(tools, ["lake", "build"], tools.output / "prepare", frozenset())

    def test_new_top_level_entries_between_preparations_are_rejected(self) -> None:
        for name, entry in (("namespace", "Init/Prelude.olean"), ("module", "Extra.olean")):
            with self.subTest(entry=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build = self.build_tree(root)
                self.prepare(tools, lambda: None, set())
                fresh(build / entry)
                with patch.object(optimizer.Tools, "run", side_effect=AssertionError("Lake ran")), \
                        self.assertRaisesRegex(ValueError, "Root artifact root changed since the last Lake "
                                               f"preparation: {build / entry.split('/')[0]}"):
                    optimizer.run_lake_preparation(tools, ["lake", "build"], tools.output / "prepare", frozenset())

    def test_namespace_moved_behind_a_symlink_is_rejected(self) -> None:
        for platform in ("linux", "darwin"):
            with self.subTest(platform=platform), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build = self.build_tree(root)
                optimizer.pin_input_paths(tools, (str(build / "Lib/Base.olean"),))

                def move_behind_symlink() -> None:
                    os.rename(build / "Lib", root / "moved-Lib")
                    (build / "Lib").symlink_to(root / "moved-Lib", target_is_directory=True)

                if platform != sys.platform and platform == "linux":
                    continue
                expected = ("Compilation input path identity changed" if platform == "linux" else
                            f"Lake preparation moved or replaced a root namespace: {build / 'Lib'}")
                with patch.object(optimizer.sys, "platform", platform), \
                        self.assertRaisesRegex(ValueError, expected):
                    self.prepare(tools, move_behind_symlink, set())

    def symlinked_artifact_tree(self, root: Path, artifact: str, target: str) -> tuple[optimizer.Tools, Path]:
        """A root artifact that is a symlink to a file outside the build root, under `store/`."""
        build = root / ".lake/build/lib/lean"
        (build / "Lib").mkdir(parents=True)
        for version in ("v1", "v2"):
            (root / "store" / version).mkdir(parents=True)
            (root / "store" / version / "Base.olean").write_bytes(f"external {version} bytes\n".encode())
        (root / "store/current").symlink_to(root / "store/v1", target_is_directory=True)
        link = build / artifact
        link.symlink_to(root / target)
        return self.tools(root), link

    def test_changes_behind_a_symlinked_artifact_are_rejected(self) -> None:
        def write_through_the_link(root: Path) -> None:
            (root / "store/v1/Base.olean").write_bytes(b"rewritten through the symlink\n")

        def retarget_a_directory_on_its_path(root: Path) -> None:
            (root / "store/current").unlink()
            (root / "store/current").symlink_to(root / "store/v2", target_is_directory=True)

        cases = (("Lib/Base.olean", "store/v1/Base.olean", "Lib.Base", write_through_the_link),
                 ("Top.olean", "store/v1/Base.olean", "Top", write_through_the_link),
                 ("Lib/Base.olean", "store/current/Base.olean", "Lib.Base", retarget_a_directory_on_its_path))
        for artifact, target, module, change in cases:
            with self.subTest(artifact=artifact, change=change.__name__), \
                    tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, link = self.symlinked_artifact_tree(root, artifact, target)
                node = optimizer.path_component_identity(link, strict=True)
                before = link.read_bytes()
                with self.assertRaises(ValueError) as raised:
                    self.prepare(tools, lambda: change(root), {module})
                # The link itself is untouched; only the bytes it resolves to changed.
                self.assertEqual(optimizer.path_component_identity(link, strict=True), node)
                self.assertNotEqual(link.read_bytes(), before)
                self.assertEqual(str(raised.exception),
                                 f"Lake preparation rewrote an artifact outside its requested modules: {link}")
                self.assertEqual(optimizer.read_lake_growth(tools.output), {})
                self.assertEqual(optimizer.read_lake_growth(tools.output, "rewritten"), {})

    def test_an_untouched_symlinked_artifact_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, link = self.symlinked_artifact_tree(root, "Lib/Base.olean", "store/current/Base.olean")
            addition = link.parent / "New.olean"
            self.prepare(tools, lambda: fresh(addition), {"Lib.Base", "Lib.New"})
            self.assertEqual(list(optimizer.read_lake_growth(tools.output)), [str(addition)])
            self.assertEqual(optimizer.read_lake_growth(tools.output, "rewritten"), {})

    @unittest.skipUnless(sys.platform == "linux", "inotify watches the Lake window")
    def test_transient_namespace_changes_in_the_window_are_rejected(self) -> None:
        def move_and_restore(build: Path, root: Path) -> None:
            os.rename(build / "Lib", root / "moved-Lib")
            os.rename(root / "moved-Lib", build / "Lib")

        def symlink_and_restore(build: Path, root: Path) -> None:
            os.rename(build / "Lib", root / "moved-Lib")
            (build / "Lib").symlink_to(root / "moved-Lib", target_is_directory=True)
            (build / "Lib").unlink()
            os.rename(root / "moved-Lib", build / "Lib")

        def chmod_directory_and_restore(build: Path, root: Path) -> None:
            chmod_and_restore(build / "Lib")

        for change in (move_and_restore, symlink_and_restore, chmod_directory_and_restore):
            with self.subTest(change=change.__name__), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build = self.build_tree(root)
                before = optimizer.namespace_topology([build / "Lib"])
                with self.assertRaisesRegex(ValueError, "Compilation input path identity changed: "):
                    self.prepare(tools, lambda: change(build, root), set())
                # The endpoint alone would not show it: the namespace node and path are restored.
                self.assertEqual(optimizer.namespace_topology([build / "Lib"]), before)

    def test_per_row_fallback_preparation_uses_the_guard(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            recovery.main_inputs(root, ("A",))
            tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean", root, {}, 5,
                                    root / "bin/time")
            row = {"path": "A.lean", "module": "A", "source_sha256": recovery.digest(recovery.ORIGINAL)}
            refused = ValueError("Pinned root-package artifact changed (ino): fixture")
            with patch.object(optimizer, "run_lake_preparation", side_effect=refused) as guard, \
                    patch.object(optimizer.Tools, "run", side_effect=AssertionError("unguarded Lake")):
                result = optimizer.optimize_one(tools, row, recovery.native_header(root / "A.lean"),
                                                optimizer.Proposal())
            self.assertEqual((result["status"], result["error"]), ("blocked", str(refused)))
            guard.assert_called_once()
            self.assertEqual(guard.call_args.args[3], frozenset({"A"}))

    def test_custody_keeps_the_first_pin_after_a_rehash(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            namespace = root / ".lake/build/lib/lean/Lib"
            namespace.mkdir(parents=True)
            base = namespace / "Base.olean"
            base.write_bytes(b"root artifact\n")
            tools = self.tools(root)
            optimizer.pin_input_paths(tools, (str(base),))
            first = tools.root_custody[str(base)]
            base.write_bytes(b"changed bytes\n")
            # A later pin re-hashes the file and updates the cache, but not the custody.
            optimizer.record_root_custody(tools, [optimizer.file_pin(base, tools.file_cache)])
            self.assertEqual(tools.root_custody[str(base)], first)
            with patch.object(optimizer.Tools, "run", side_effect=AssertionError("Lake ran")), \
                    self.assertRaisesRegex(ValueError, "Pinned root-package artifact changed .*: " + str(base)):
                optimizer.run_lake_preparation(tools, ["lake", "build"], tools.output / "prepare", frozenset())

    def test_dependency_closure_follows_frozen_local_edges(self) -> None:
        inventory = [{"module": "A", "direct_local_dependencies": ["B"]},
                     {"module": "B", "direct_local_dependencies": ["C"]},
                     {"module": "C", "direct_local_dependencies": []},
                     {"module": "D", "direct_local_dependencies": ["A"]}]
        self.assertEqual(optimizer.local_dependency_closure(inventory, {"A"}), {"A", "B", "C"})


class SearchedProviderTests(unittest.TestCase):
    """Providers in searched roots no inventory has cached: dependencies, the compiler, aliases."""

    def setup_tree(self, root: Path, lean_path: list[str]) -> tuple[optimizer.Tools, Path, Path]:
        build = root / ".lake/build/lib/lean"
        (build / "Lib").mkdir(parents=True)
        (build / "Lib/Base.olean").write_bytes(b"root artifact\n")
        dependency = root / "dep/lib"
        (dependency / "Lib/Sub").mkdir(parents=True)
        (dependency / "Foo.olean").write_bytes(b"dependency provider of Foo\n")
        (dependency / "Lib/Sub/Dep.olean").write_bytes(b"dependency provider of Lib.Sub.Dep\n")
        (dependency / "Other.olean").write_bytes(b"unrelated dependency module\n")
        (dependency / "Part.olean.server").write_bytes(b"only one part of a dependency module\n")
        (root / "deplink").symlink_to(root / "dep", target_is_directory=True)
        library = root / "sysroot/lib/lean/Init"
        library.mkdir(parents=True)
        (library / "Prelude.olean").write_bytes(b"compiler provider\n")
        tools = optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean", root,
                                {"LEAN_SYSROOT": str(root / "sysroot"), "LEAN_PATH": os.pathsep.join(lean_path)},
                                5, time_binary=root / "bin/time")
        return tools, build, dependency

    def prepare(self, tools: optimizer.Tools, change: Callable[[], None], modules: set[str]) -> None:
        def run(argv: list[str], label: Path, environment: dict[str, str] | None = None) -> dict[str, object]:
            change()
            return {"exit_code": 0}

        with patch.object(optimizer.Tools, "run", side_effect=run):
            optimizer.run_lake_preparation(tools, ["lake", "build"], tools.output / "prepare", frozenset(modules))

    def test_cold_providers_in_every_searched_root_are_rejected(self) -> None:
        cases = {
            "dependency, absolute entry": (["{root}/.lake/build/lib/lean", "{root}/dep/lib"], "Foo.olean",
                                           "{root}/dep/lib/Foo.olean"),
            "dependency, relative entry": ([".lake/build/lib/lean", "dep/lib"], "Foo.olean",
                                           "{root}/dep/lib/Foo.olean"),
            "dependency, symlinked entry": (["{root}/.lake/build/lib/lean", "{root}/deplink/lib"], "Foo.olean",
                                            "{root}/deplink/lib/Foo.olean"),
            "dependency, nested module": (["{root}/.lake/build/lib/lean", "{root}/dep/lib"], "Lib/Sub/Dep.olean",
                                          "{root}/dep/lib/Lib/Sub/Dep.olean"),
            "dependency, other part": (["{root}/dep/lib"], "Foo.ir", "{root}/dep/lib/Foo.olean"),
            "dependency, non-olean provider": (["{root}/dep/lib"], "Part.olean", "{root}/dep/lib/Part.olean.server"),
            "compiler library": ([], "Init/Prelude.olean", "{root}/sysroot/lib/lean/Init/Prelude.olean"),
        }
        for name, (lean_path, addition, provider) in cases.items():
            with self.subTest(case=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build, _ = self.setup_tree(root, [entry.format(root=root) for entry in lean_path])
                self.assertEqual(tools.library_inventories, {})
                module = addition.rsplit(".", 1)[0].replace("/", ".")
                with self.assertRaises(ValueError) as raised:
                    self.prepare(tools, lambda: fresh(build / addition), {module})
                self.assertEqual(str(raised.exception), f"Lake preparation added a shadowing artifact: "
                                 f"{build / addition} (module {module} was already provided by "
                                 f"{provider.format(root=root)})")
                self.assertEqual(optimizer.read_lake_growth(tools.output), {})

    def test_a_rewrite_visible_under_another_searched_root_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            build = root / ".lake/build/lib/lean"
            tools, build, _ = self.setup_tree(root, [str(build), str(build / "Lib")])
            with self.assertRaises(ValueError) as raised:
                self.prepare(tools, lambda: (build / "Lib/Base.olean").write_bytes(b"rebuilt\n"), {"Lib.Base", "Base"})
            self.assertEqual(str(raised.exception),
                             f"Lake preparation rewrote an artifact visible as module Base: {build / 'Lib/Base.olean'}")
            self.assertEqual(optimizer.read_lake_growth(tools.output, "rewritten"), {})

    def test_warm_providers_keep_their_existing_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, build, dependency = self.setup_tree(root, [str(root / ".lake/build/lib/lean"),
                                                              str(root / "dep/lib")])
            optimizer.standard_library_paths(dependency, tools)
            with self.assertRaisesRegex(ValueError, "added an artifact for an existing module: "
                                        + str(build / "Foo.olean")):
                self.prepare(tools, lambda: fresh(build / "Foo.olean"), {"Foo"})

    def test_additions_visible_under_another_searched_root_are_rejected(self) -> None:
        cases = {
            "root nested in the build root": ("{root}/.lake/build/lib/lean/Lib", "Lib/New.olean", "Lib.New",
                                              "New", "{root}/.lake/build/lib/lean/Lib"),
            "root containing the build root": ("{root}/.lake/build/lib", "New.olean", "New", "lean.New",
                                               "{root}/.lake/build/lib"),
        }
        for name, (extra, addition, module, alias, alias_root) in cases.items():
            with self.subTest(case=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build, _ = self.setup_tree(root, [str(root / ".lake/build/lib/lean"), extra.format(root=root)])
                with self.assertRaises(ValueError) as raised:
                    self.prepare(tools, lambda: fresh(build / addition), {module, alias})
                self.assertEqual(str(raised.exception), f"Lake preparation added a shadowing artifact: "
                                 f"{build / addition} (visible as module {alias} under searched root "
                                 f"{alias_root.format(root=root)})")

    def test_searched_provider_changes_during_the_build_are_rejected(self) -> None:
        def missing_root_created(root: Path, dependency: Path) -> None:
            fresh(root / "ghost/lib/New.olean")

        def provider_created(root: Path, dependency: Path) -> None:
            fresh(dependency / "New.olean")

        def provider_replaced_same_bytes(root: Path, dependency: Path) -> None:
            replace_same_bytes(dependency / "Foo.olean")

        def provider_removed(root: Path, dependency: Path) -> None:
            (dependency / "Foo.olean").unlink()

        def provider_chmod_restored(root: Path, dependency: Path) -> None:
            chmod_and_restore(dependency / "Foo.olean")

        cases = ((missing_root_created, "{root}/ghost/lib/New.olean"),
                 (provider_created, "{root}/dep/lib/New.olean"),
                 (provider_replaced_same_bytes, "{root}/dep/lib/Foo.olean"),
                 (provider_removed, "{root}/dep/lib/Foo.olean"),
                 (provider_chmod_restored, "{root}/dep/lib/Foo.olean"))
        for change, changed in cases:
            with self.subTest(change=change.__name__), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build, dependency = self.setup_tree(
                    root, [str(root / ".lake/build/lib/lean"), str(root / "dep/lib"), str(root / "ghost/lib")])

                def lake() -> None:
                    change(root, dependency)
                    fresh(build / "New.olean")

                with patch.object(optimizer.sys, "platform", "darwin"), self.assertRaises(ValueError) as raised:
                    self.prepare(tools, lake, {"Foo", "New"})
                self.assertEqual(str(raised.exception), "Lake preparation changed a module artifact outside the "
                                 f"root package: {changed.format(root=root)}")

    def test_a_provider_rewritten_through_its_symlink_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, build, dependency = self.setup_tree(root, [str(root / ".lake/build/lib/lean"),
                                                              str(root / "dep/lib")])
            store = root / "store/Linked.olean"
            fresh(store)
            (dependency / "Linked.olean").symlink_to(store)

            def lake() -> None:
                store.write_bytes(b"rewritten through the provider's symlink\n")
                fresh(build / "New.olean")

            with self.assertRaises(ValueError) as raised:
                self.prepare(tools, lake, {"Linked", "New"})
            self.assertEqual(str(raised.exception), "Lake preparation changed a module artifact outside the "
                             f"root package: {dependency / 'Linked.olean'}")

    @unittest.skipUnless(sys.platform == "linux", "inotify watches the Lake window")
    def test_transient_searched_providers_during_the_build_are_rejected(self) -> None:
        def file_created_and_removed(dependency: Path) -> None:
            fresh(dependency / "New.olean")
            (dependency / "New.olean").unlink()

        def namespace_created_and_removed(dependency: Path) -> None:
            fresh(dependency / "Fresh/New.olean")
            shutil.rmtree(dependency / "Fresh")

        def provider_replaced_and_restored(dependency: Path) -> None:
            original = dependency / "Foo.olean"
            os.rename(original, dependency / "Foo.saved")
            fresh(original)
            os.replace(dependency / "Foo.saved", original)

        for change, modules in ((file_created_and_removed, {"New"}), (namespace_created_and_removed, {"Fresh.New"}),
                                (provider_replaced_and_restored, {"Foo", "New"})):
            with self.subTest(change=change.__name__), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build, dependency = self.setup_tree(root, [str(root / ".lake/build/lib/lean"),
                                                                  str(root / "dep/lib")])
                before = {path: optimizer.path_state(path) for path in (dependency / "Foo.olean",
                                                                        dependency / "New.olean")}
                addition = build / (sorted(module for module in modules if module != "Foo")[0].replace(".", "/")
                                    + ".olean")

                def lake() -> None:
                    change(dependency)
                    fresh(addition)

                with self.assertRaisesRegex(ValueError, "Compilation input path identity changed: "
                                            + str(dependency)):
                    self.prepare(tools, lake, modules)
                if change is not provider_replaced_and_restored:
                    # The endpoint states alone would not show it.
                    self.assertEqual({path: optimizer.path_state(path) for path in before}, before)

    def test_unrelated_activity_in_searched_roots_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            tools, build, dependency = self.setup_tree(root, [str(root / ".lake/build/lib/lean"),
                                                              str(root / "dep/lib")])

            def lake() -> None:
                (dependency / "Other.trace").write_text("unrelated sidecar\n")
                fresh(dependency / "Unrelated/Module.olean")
                fresh(build / "Lib/New.olean")

            self.prepare(tools, lake, {"Lib.New"})
            self.assertEqual(list(optimizer.read_lake_growth(tools.output)), [str(build / "Lib/New.olean")])

    def test_resume_rejects_recorded_growth_another_searched_root_provides(self) -> None:
        for provider in ("dep/lib/Lib/Sub/New.olean", "sysroot/lib/lean/Lib/Sub/New.olean"):
            with self.subTest(provider=provider), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                tools, build, _ = self.setup_tree(root, [str(root / ".lake/build/lib/lean"), str(root / "dep/lib")])
                saved_paths = (str(build / "Lib/Base.olean"),)
                saved = optimizer.pin_input_paths(tools, saved_paths)
                addition = build / "Lib/Sub/New.olean"
                fresh(addition)
                fresh(root / provider)
                grown = tuple(sorted((*saved_paths, str(addition))))
                token = optimizer._recorded_lake_growth.set({str(addition): optimizer.file_pin(addition)})
                try:
                    with self.assertRaises(ValueError) as raised:
                        optimizer.verify_input_manifest(saved, grown, tools.output, tools)
                finally:
                    optimizer._recorded_lake_growth.reset(token)
                self.assertEqual(str(raised.exception), f"Saved compilation inputs gained a shadowing artifact: "
                                 f"{addition} (module Lib.Sub.New is provided by {root / provider})")

    def test_first_preparation_through_main_sees_a_cold_compiler_provider(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            arguments = lifecycle_inputs(root)
            # The mocked environment names the project as the compiler's sysroot.
            provider = root / "lib/lean/Lib/Sub/A.olean"
            fresh(provider)
            with mocked_lake(root) as builds, patch.object(sys, "argv", arguments):
                self.assertEqual(optimizer.main(), 1)
            self.assertEqual(builds, [["A"]])
            rows = journal(root)
            self.assertEqual([row["status"] for row in rows], ["blocked", "blocked", "blocked"])
            addition = root / ".lake/build/lib/lean/Lib/Sub/A.olean"
            message = (f"Lake preparation added a shadowing artifact: {addition} "
                       f"(module Lib.Sub.A was already provided by {provider})")
            self.assertEqual(rows[0]["error"], message)
            for row in rows[1:]:
                self.assertEqual(row["error"], "An earlier Lake preparation was rejected: " + message)


class ResumeHarness(unittest.TestCase):
    """Three one-module batches through main() with a mocked Lake that leaves up-to-date targets alone."""

    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name).resolve()
        self.arguments = lifecycle_inputs(self.root)
        self.sub = self.root / ".lake/build/lib/lean/Lib/Sub"
        self.environment_captures = 0

    @contextlib.contextmanager
    def lake(self, failing: frozenset[str] = frozenset(), pin_before_failing: bool = False,
             interrupt_after_preparation: bool = False, during_capture: Callable[[], None] | None = None,
             during_build: Callable[[str], None] | None = None):
        actual_preparation = optimizer.run_lake_preparation

        def analyses(tools, rows, headers, directory):
            if {str(row["module"]) for row in rows} & failing:
                if pin_before_failing:
                    optimizer.analysis_inputs(tools, rows)
                raise ValueError("Mock analysis failure")
            return recovery.mock_no_change_proposals(tools, rows, headers, directory)

        def preparation(*args, **kwargs):
            result = actual_preparation(*args, **kwargs)
            if interrupt_after_preparation:
                raise KeyboardInterrupt("Received signal 15")
            return result

        def capture(argv, cwd, label, environment, timeout):
            self.environment_captures += 1
            if during_capture is not None:
                during_capture()
            return recovery.environment_stub(argv, cwd, label, environment, timeout)

        with mocked_lake(self.root, during_build, rewrite_existing=False) as builds, \
                patch.object(optimizer, "analyze_batch", side_effect=analyses), \
                patch.object(optimizer, "run_lake_preparation", side_effect=preparation), \
                patch.object(optimizer, "run_command", side_effect=capture):
            yield builds

    def invoke(self, *extra: str, **lake: object) -> tuple[int, list[list[str]]]:
        with self.lake(**lake) as builds, patch.object(sys, "argv", [*self.arguments, *extra]):
            return optimizer.main(), builds

    def refused(self, message: str, *extra: str) -> None:
        captures = self.environment_captures
        with self.lake() as builds, patch.object(sys, "argv", [*self.arguments, "--resume", *extra]), \
                self.assertRaisesRegex(ValueError, message):
            optimizer.main()
        self.assertEqual(builds, [])
        self.assertEqual(self.environment_captures, captures, "a Lake command ran before the refusal")

    def change(self, path: Path, mutation: str) -> None:
        if mutation == "bytes":
            path.write_bytes(path.read_bytes() + b"changed\n")
        else:
            path.unlink()


class SavedReceiptResumeTests(ResumeHarness):
    """Every saved root-package receipt holds on resume, whatever the journal says."""

    def test_interrupted_preparation_growth_is_verified_with_empty_or_missing_journal(self) -> None:
        for journal_state in ("empty", "missing"):
            for mutation in ("bytes", "missing"):
                with self.subTest(journal=journal_state, mutation=mutation):
                    self.setUp()
                    with self.assertRaises(KeyboardInterrupt):
                        self.invoke(interrupt_after_preparation=True)
                    journal_path = self.root / "output/results.jsonl"
                    self.assertEqual(journal_path.read_text(), "")
                    if journal_state == "missing":
                        journal_path.unlink()
                    self.assertEqual(list(optimizer.read_lake_growth(self.root / "output")), [str(self.sub / "A.olean")])
                    self.change(self.sub / "A.olean", mutation)
                    self.refused("Saved root-package artifact is missing or changed since it was pinned: "
                                 + str(self.sub / "A.olean"))

    def test_growth_of_blocked_rows_is_verified(self) -> None:
        for extra in ((), ("--retry-blocked",)):
            with self.subTest(extra=extra):
                self.setUp()
                self.assertEqual(self.invoke("--max-batches", "1", failing=frozenset({"A"})), (1, [["A"]]))
                self.assertEqual([row["status"] for row in journal(self.root)], ["blocked"])
                self.change(self.sub / "A.olean", "bytes")
                self.refused("missing or changed since it was pinned: " + str(self.sub / "A.olean"), *extra)

    def test_growth_no_successful_row_covers_is_verified(self) -> None:
        self.assertEqual(self.invoke("--max-batches", "2", failing=frozenset({"B"})), (1, [["A"], ["B"]]))
        self.assertEqual([row["status"] for row in journal(self.root)], ["no_change", "blocked"])
        self.change(self.sub / "B.olean", "bytes")
        self.refused("missing or changed since it was pinned: " + str(self.sub / "B.olean"))

    def test_artifacts_pinned_only_by_a_blocked_row_are_verified(self) -> None:
        other = self.root / ".lake/build/lib/lean/Other/X.olean"
        other.parent.mkdir(parents=True)
        other.write_bytes(b"pre-existing artifact only B imports\n")
        setup = self.root / ".lake/build/ir/B.setup.json"
        metadata = optimizer.read_json(setup)
        metadata["importArts"]["Other.X"] = [[str(other)], []]
        optimizer.write_json(setup, metadata)
        self.assertEqual(self.invoke("--max-batches", "2", failing=frozenset({"B"}), pin_before_failing=True),
                         (1, [["A"], ["B"]]))
        saved = optimizer.saved_root_receipts(self.root, self.root / "output",
                                              optimizer.read_lake_growth(self.root / "output"))
        self.assertIn(str(other), saved)
        self.change(other, "bytes")
        self.refused("missing or changed since it was pinned: " + str(other))

    def test_unchanged_saved_receipts_resume_normally(self) -> None:
        self.assertEqual(self.invoke("--max-batches", "2", failing=frozenset({"B"})), (1, [["A"], ["B"]]))
        before = (self.root / "output/results.jsonl").read_bytes()
        self.assertEqual(self.invoke("--resume"), (1, [["C"]]))
        rows = journal(self.root)
        self.assertTrue((self.root / "output/results.jsonl").read_bytes().startswith(before))
        self.assertEqual([row["status"] for row in rows], ["no_change", "blocked", "no_change"])
        self.assertEqual(self.invoke("--resume", "--retry-blocked"), (0, [["B"]]))
        self.assertEqual([row["status"] for row in journal(self.root)][-1], "no_change")

    def test_a_retried_target_whose_growth_lake_rewrites_is_rejected(self) -> None:
        self.assertEqual(self.invoke("--max-batches", "1", failing=frozenset({"A"})), (1, [["A"]]))
        def rewriting(target: str) -> None:
            # This Lake rewrites the retried target's recorded artifact.
            if target == "A":
                (self.sub / "A.olean").write_bytes(b"rebuilt differently\n")

        with self.lake(during_build=rewriting) as builds, \
                patch.object(sys, "argv", [*self.arguments, "--resume", "--retry-blocked"]):
            self.assertEqual(optimizer.main(), 1)
        self.assertEqual(builds, [["A"]])
        rows = journal(self.root)
        self.assertEqual(rows[1]["error"], f"Pinned root-package artifact changed (ctime, mtime, size): "
                         f"{self.sub / 'A.olean'}")

    def test_same_bytes_rewrite_between_invocations_is_accepted(self) -> None:
        # A resume compares bytes; identities are compared only within one process.
        self.assertEqual(self.invoke("--max-batches", "1", failing=frozenset({"A"})), (1, [["A"]]))
        replace_same_bytes(self.sub / "A.olean")
        self.assertEqual(self.invoke("--resume"), (1, [["B"], ["C"]]))

    def test_change_during_environment_capture_is_rejected_before_any_preparation(self) -> None:
        self.assertEqual(self.invoke("--max-batches", "1", failing=frozenset({"A"})), (1, [["A"]]))
        target = self.sub / "A.olean"
        with self.lake(during_capture=lambda: chmod_and_restore(target)) as builds, \
                patch.object(sys, "argv", [*self.arguments, "--resume"]), \
                self.assertRaisesRegex(ValueError, f"Pinned root-package artifact changed \\(ctime\\): {target}"):
            optimizer.main()
        self.assertEqual(builds, [])

    def test_accepted_growth_is_under_custody_in_the_same_process(self) -> None:
        journal_path = self.root / "output/results.jsonl"
        target = self.sub / "A.olean"
        validate = optimizer.validate_inventory_sources
        changed: list[bool] = []

        def change_after_first_row(*args: object, **kwargs: object) -> None:
            if not changed and journal_path.exists() and len(journal_path.read_text().splitlines()) == 1:
                before = target.stat()
                target.write_bytes(b"X" * before.st_size)
                os.utime(target, ns=(before.st_atime_ns, before.st_mtime_ns))
                changed.append(True)
            return validate(*args, **kwargs)

        with patch.object(optimizer, "validate_inventory_sources", side_effect=change_after_first_row):
            self.assertEqual(self.invoke(failing=frozenset({"A"})), (1, [["A"]]))
        rows = journal(self.root)
        self.assertEqual([row["status"] for row in rows], ["blocked", "blocked", "blocked"])
        self.assertEqual(rows[1]["error"], f"Pinned root-package artifact changed (ctime): {target}")

    def test_saved_receipt_records_must_be_well_formed(self) -> None:
        def outside_build_root(output: Path) -> None:
            record = output / optimizer.LAKE_GROWTH_DIRECTORY / "1.json"
            optimizer.write_json(record, {"added": [optimizer.file_pin(self.root / "A.lean")]})

        def relative_path(output: Path) -> None:
            record = output / optimizer.LAKE_GROWTH_DIRECTORY / "1.json"
            optimizer.write_json(record, {"added": [{"path": ".lake/build/lib/lean/Lib/Sub/A.olean",
                                                     "bytes": 1, "sha256": "0" * 64}]})

        def conflicting_receipts(output: Path) -> None:
            pin = optimizer.file_pin(self.sub / "A.olean")
            optimizer.write_json(output / "inputs" / ("a" * 64 + ".json"), {"files": [{**pin, "sha256": "1" * 64}]})

        def malformed_manifest(output: Path) -> None:
            (output / "inputs" / ("b" * 64 + ".json")).write_text("{not json")

        def malformed_growth(output: Path) -> None:
            optimizer.write_json(output / optimizer.LAKE_GROWTH_DIRECTORY / "1.json", {"added": {"path": "x"}})

        def missing_run_identity(output: Path) -> None:
            (output / "run.json").unlink()
            (output / "results.jsonl").unlink()

        cases = {outside_build_root: "outside the root artifact root",
                 relative_path: "outside the root artifact root",
                 conflicting_receipts: "Saved receipts disagree on a root-package artifact",
                 malformed_manifest: "Expecting property name",
                 malformed_growth: "Invalid recorded Lake growth",
                 missing_run_identity: "without their original run identity"}
        for damage, message in cases.items():
            with self.subTest(damage=damage.__name__):
                self.setUp()
                self.assertEqual(self.invoke("--max-batches", "1"), (0, [["A"]]))
                damage(self.root / "output")
                self.refused(message)

    def test_a_new_run_refuses_an_output_directory_with_saved_custody(self) -> None:
        for name in (optimizer.LAKE_GROWTH_DIRECTORY, optimizer.LAKE_CUSTODY_DIRECTORY, "inputs"):
            with self.subTest(directory=name):
                self.setUp()
                (self.root / "output" / name).mkdir(parents=True)
                with self.lake(), patch.object(sys, "argv", self.arguments), \
                        contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                    optimizer.main()
                self.assertEqual(raised.exception.code, 2)


class Abrupt(BaseException):
    """An abrupt stop that no optimizer handler catches, standing in for a killed process."""


class InterruptedPreparationTests(ResumeHarness):
    """A Lake preparation stopped after its child may have written artifacts keeps the output closed."""

    def pending(self) -> Path:
        return self.root / "output" / optimizer.LAKE_CUSTODY_DIRECTORY / optimizer.PENDING_PREPARATION

    def interrupted_after_lake_writes(self, target: str):
        def during_build(built: str) -> None:
            if built == target:
                raise KeyboardInterrupt("Received signal 15")
        return during_build

    def test_marker_is_saved_before_lake_runs(self) -> None:
        seen: list[dict[str, object]] = []

        def during_build(target: str) -> None:
            seen.append(optimizer.read_json(self.pending()))

        self.assertEqual(self.invoke("--max-batches", "1", during_build=during_build), (0, [["A"]]))
        self.assertEqual(seen[0]["modules"], ["A", "Lib.Base", "Lib.Sub.A"])
        self.assertTrue(str(seen[0]["preparation"]).endswith("/prepare"))
        self.assertFalse(os.path.lexists(self.pending()))

    def test_interruption_after_lake_writes_closes_the_output(self) -> None:
        for later in (False, True):
            with self.subTest(later=later):
                self.setUp()
                target = "A"
                if later:
                    self.assertEqual(self.invoke("--max-batches", "1"), (0, [["A"]]))
                    target = "B"
                with self.assertRaises(KeyboardInterrupt):
                    self.invoke(*(["--resume"] if later else []),
                                during_build=self.interrupted_after_lake_writes(target))
                self.assertTrue((self.sub / f"{target}.olean").exists())
                self.assertEqual(optimizer.read_json(self.pending())["modules"][-1], f"Lib.Sub.{target}")
                growth = optimizer.read_lake_growth(self.root / "output")
                self.assertNotIn(str(self.sub / f"{target}.olean"), growth)
                self.assertFalse((self.pending().parent / "rejected.json").exists())
                for extra in ((), ("--retry-blocked",)):
                    self.refused("A Lake preparation was interrupted before its custody records were saved", *extra)
                self.assertTrue(os.path.lexists(self.pending()))

    def test_a_later_preparation_in_the_same_process_is_refused(self) -> None:
        tools = optimizer.Tools(self.root, self.root / "output", self.root / "bin/lake", self.root / "bin/lean",
                                self.root, {"LEAN_SYSROOT": str(self.root)}, 5, time_binary=self.root / "bin/time")

        def interrupted(argv, label, environment=None):
            fresh(self.sub / "A.olean")
            raise KeyboardInterrupt("Received signal 15")

        with patch.object(optimizer.Tools, "run", side_effect=interrupted), self.assertRaises(KeyboardInterrupt):
            optimizer.run_lake_preparation(tools, ["lake", "build"], tools.output / "prepare",
                                           frozenset({"Lib.Sub.A"}))
        with patch.object(optimizer.Tools, "run", side_effect=AssertionError("Lake ran")), \
                self.assertRaisesRegex(ValueError, "interrupted before its custody records were saved"):
            optimizer.run_lake_preparation(tools, ["lake", "build"], tools.output / "prepare",
                                           frozenset({"Lib.Sub.B"}))

    def stop_at(self, point: str, before: bool = False):
        """Stop abruptly right after (or before) one record write of the preparation."""
        actual = optimizer.write_json
        unlink = Path.unlink
        state = {"stopped": False}

        def matches(path: Path) -> bool:
            return {"pending": path.name == optimizer.PENDING_PREPARATION, "listing": path.name == "listing.json",
                    "growth": path.parent.name == optimizer.LAKE_GROWTH_DIRECTORY,
                    "rejected": path.name == "rejected.json"}.get(point, False)

        def write_json(path, value):
            hit = not state["stopped"] and matches(Path(path))
            if hit and before:
                state["stopped"] = True
                raise Abrupt(point)
            actual(path, value)
            if hit:
                state["stopped"] = True
                raise Abrupt(point)

        def unlink_marker(path, *args, **kwargs):
            removal = point == "marker-removal" or (
                point == "marker-removal-after-rejection" and (path.parent / "rejected.json").exists())
            if removal and not state["stopped"] and path.name == optimizer.PENDING_PREPARATION:
                state["stopped"] = True
                raise Abrupt(point)
            return unlink(path, *args, **kwargs)

        return contextlib.ExitStack(), write_json, unlink_marker, state

    def run_stopped(self, point: str, before: bool = False, **lake: object) -> None:
        _, write_json, unlink_marker, state = self.stop_at(point, before)
        with patch.object(optimizer, "write_json", side_effect=write_json), \
                patch.object(Path, "unlink", autospec=True, side_effect=unlink_marker), \
                self.assertRaises(Abrupt):
            self.invoke(**lake)
        self.assertTrue(state["stopped"])

    def test_every_commit_boundary_before_marker_removal_stays_closed(self) -> None:
        for point in ("pending", "listing", "growth", "marker-removal"):
            with self.subTest(stopped_after=point):
                self.setUp()
                self.run_stopped(point)
                self.assertTrue(os.path.lexists(self.pending()))
                self.refused("interrupted before its custody records were saved")

    def test_stop_before_the_marker_exists_leaves_a_resumable_run(self) -> None:
        builds: list[list[str]] = []
        with self.lake() as observed:
            _, write_json, unlink_marker, state = self.stop_at("pending", before=True)
            with patch.object(optimizer, "write_json", side_effect=write_json), \
                    patch.object(sys, "argv", self.arguments), self.assertRaises(Abrupt):
                optimizer.main()
            builds = list(observed)
        self.assertEqual(builds, [])
        self.assertFalse(os.path.lexists(self.pending()))
        self.assertEqual(self.invoke("--resume"), (0, [["A"], ["B"], ["C"]]))
        self.assertFalse(os.path.lexists(self.pending()))

    def test_a_rejection_replaces_the_marker_and_stays_closed(self) -> None:
        def unrequested(target: str) -> None:
            if target == "B":
                fresh(self.root / ".lake/build/lib/lean/Fresh/Unrequested.olean")

        self.assertEqual(self.invoke(during_build=unrequested), (1, [["A"], ["B"]]))
        self.assertFalse(os.path.lexists(self.pending()))
        self.assertTrue((self.pending().parent / "rejected.json").exists())
        # The rejected growth in A's namespace already stops the resume at A's saved row.
        with self.lake() as builds, patch.object(sys, "argv", [*self.arguments, "--resume"]), \
                self.assertRaisesRegex(ValueError, "gained an unrecorded artifact: " + str(self.sub / "B.olean")):
            optimizer.main()
        self.assertEqual(builds, [])
        # Stopped between the rejection record and the marker's removal: both keep it closed.
        self.setUp()
        self.run_stopped("marker-removal-after-rejection", during_build=unrequested)
        self.assertTrue((self.pending().parent / "rejected.json").exists())
        self.assertTrue(os.path.lexists(self.pending()))
        self.refused("interrupted before its custody records were saved")

    def test_the_marker_survives_until_the_rejection_record_is_saved(self) -> None:
        def unrequested(target: str) -> None:
            if target == "B":
                fresh(self.root / ".lake/build/lib/lean/Fresh/Unrequested.olean")

        # Stopped before the rejection record is written.
        self.run_stopped("rejected", before=True, during_build=unrequested)
        self.assertFalse((self.pending().parent / "rejected.json").exists())
        self.assertTrue(os.path.lexists(self.pending()))
        self.refused("interrupted before its custody records were saved")
        # The rejection record cannot be written.
        self.setUp()
        actual = optimizer.write_json

        def failing(path, value):
            if Path(path).name == "rejected.json":
                raise OSError(28, "No space left on device")
            actual(path, value)

        with patch.object(optimizer, "write_json", side_effect=failing), self.assertRaises(OSError):
            self.invoke(during_build=unrequested)
        self.assertFalse((self.pending().parent / "rejected.json").exists())
        self.assertTrue(os.path.lexists(self.pending()))
        self.refused("interrupted before its custody records were saved")

    def test_a_failed_success_record_write_keeps_the_marker(self) -> None:
        for record in ("listing.json", optimizer.LAKE_GROWTH_DIRECTORY):
            with self.subTest(record=record):
                self.setUp()
                actual = optimizer.write_json

                def failing(path, value):
                    if record in (Path(path).name, Path(path).parent.name):
                        raise OSError(28, "No space left on device")
                    actual(path, value)

                with patch.object(optimizer, "write_json", side_effect=failing), self.assertRaises(OSError):
                    self.invoke()
                self.assertTrue(os.path.lexists(self.pending()))
                self.refused("interrupted before its custody records were saved")

    def test_any_marker_entry_is_refused(self) -> None:
        for form in ("malformed", "directory", "dangling-symlink"):
            with self.subTest(form=form):
                self.setUp()
                self.assertEqual(self.invoke("--max-batches", "1"), (0, [["A"]]))
                marker = self.pending()
                if form == "malformed":
                    marker.write_text("{not json")
                elif form == "directory":
                    marker.mkdir()
                else:
                    marker.symlink_to(self.root / "missing-target")
                self.refused("interrupted before its custody records were saved")

    def test_completed_and_bounded_runs_leave_no_marker(self) -> None:
        for step, expected in ((("--max-batches", "1"), [["A"]]), (("--max-batches", "1", "--resume"), [["B"]]),
                               (("--resume",), [["C"]]), (("--resume",), [])):
            self.assertEqual(self.invoke(*step), (0, expected))
            self.assertFalse(os.path.lexists(self.pending()))


class UnpinnedRewriteTests(ResumeHarness):
    """Existing root artifacts nothing has pinned yet, rewritten during a Lake preparation."""

    def setUp(self) -> None:
        super().setUp()
        self.base = self.root / ".lake/build/lib/lean/Lib/Base.olean"
        self.other = self.root / ".lake/build/lib/lean/Lib/Other.olean"
        self.other.write_bytes(b"Lib.Other artifact, in no closure\n")

    def rewrites(self) -> dict[str, dict[str, object]]:
        return optimizer.read_lake_growth(self.root / "output", "rewritten")

    def rebuild(self, path: Path, during: str = "A", same_bytes: bool = False):
        def during_build(target: str) -> None:
            if target == during:
                if same_bytes:
                    replace_same_bytes(path)
                else:
                    path.write_bytes(path.read_bytes() + b"rebuilt\n")
        return during_build

    def test_a_requested_rebuild_is_accepted_and_recorded(self) -> None:
        for same_bytes in (False, True):
            with self.subTest(same_bytes=same_bytes):
                self.setUp()
                before = self.base.read_bytes()
                self.assertEqual(self.invoke("--max-batches", "1", failing=frozenset({"A"}),
                                             during_build=self.rebuild(self.base, same_bytes=same_bytes)), (1, [["A"]]))
                self.assertEqual(self.base.read_bytes() == before, same_bytes)
                self.assertEqual(self.rewrites(), {str(self.base): optimizer.file_pin(self.base)})
                self.assertEqual(self.invoke("--resume"), (1, [["B"], ["C"]]))

    def test_a_recorded_rebuild_is_verified_on_resume(self) -> None:
        for extra in ((), ("--retry-blocked",)):
            with self.subTest(extra=extra):
                self.setUp()
                self.assertEqual(self.invoke("--max-batches", "1", failing=frozenset({"A"}),
                                             during_build=self.rebuild(self.base)), (1, [["A"]]))
                self.change(self.base, "bytes")
                self.refused("missing or changed since it was pinned: " + str(self.base), *extra)

    def test_a_rebuilt_stale_target_with_no_additions_is_recorded(self) -> None:
        stale = self.sub / "A.olean"
        stale.parent.mkdir(exist_ok=True)
        stale.write_bytes(b"Lib.Sub.A artifact from an older source\n")
        self.assertEqual(self.invoke("--max-batches", "1", failing=frozenset({"A"}),
                                     during_build=self.rebuild(stale)), (1, [["A"]]))
        self.assertEqual(optimizer.read_lake_growth(self.root / "output"), {})
        self.assertEqual(list(self.rewrites()), [str(stale)])
        self.change(stale, "bytes")
        self.refused("missing or changed since it was pinned: " + str(stale))

    def test_a_rebuild_before_an_interruption_is_verified_with_an_empty_journal(self) -> None:
        with self.assertRaises(KeyboardInterrupt):
            self.invoke(interrupt_after_preparation=True, during_build=self.rebuild(self.base))
        self.assertEqual((self.root / "output/results.jsonl").read_text(), "")
        self.assertIn(str(self.base), self.rewrites())
        self.change(self.base, "bytes")
        self.refused("missing or changed since it was pinned: " + str(self.base))

    def test_a_rebuild_is_under_custody_in_the_same_process(self) -> None:
        journal_path = self.root / "output/results.jsonl"
        validate = optimizer.validate_inventory_sources

        def change_after_first_row(*args: object, **kwargs: object) -> None:
            if journal_path.exists() and len(journal_path.read_text().splitlines()) == 1 and \
                    not self.base.read_bytes().endswith(b"tampered\n"):
                before = self.base.stat()
                self.base.write_bytes(b"X" * (before.st_size - 9) + b"tampered\n")
                os.utime(self.base, ns=(before.st_atime_ns, before.st_mtime_ns))
            return validate(*args, **kwargs)

        with patch.object(optimizer, "validate_inventory_sources", side_effect=change_after_first_row):
            self.assertEqual(self.invoke(failing=frozenset({"A"}), during_build=self.rebuild(self.base)),
                             (1, [["A"]]))
        rows = journal(self.root)
        self.assertEqual(rows[1]["error"], f"Pinned root-package artifact changed (ctime): {self.base}")

    def test_an_unrequested_rewrite_is_rejected(self) -> None:
        for same_bytes in (False, True):
            with self.subTest(same_bytes=same_bytes):
                self.setUp()
                self.assertEqual(self.invoke(during_build=self.rebuild(self.other, same_bytes=same_bytes)),
                                 (1, [["A"]]))
                rows = journal(self.root)
                self.assertEqual(rows[0]["error"],
                                 f"Lake preparation rewrote an artifact outside its requested modules: {self.other}")
                self.assertTrue(rows[1]["error"].startswith("An earlier Lake preparation was rejected"))
                self.assertEqual(self.rewrites(), {})
                self.assertFalse(os.path.lexists(self.root / "output/lake-custody/pending.json"))

    def test_top_level_root_module_artifacts(self) -> None:
        top = self.root / ".lake/build/lib/lean/Top.olean"
        top.write_bytes(b"Top artifact\n")
        manifest = self.root / "manifest.jsonl"
        rows = [json.loads(line) for line in manifest.read_text().splitlines()]
        for row in rows:
            if row["module"] == "A":
                row["direct_local_dependencies"].append("Top")
        manifest.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.assertEqual(self.invoke("--max-batches", "1", during_build=self.rebuild(top)), (0, [["A"]]))
        self.assertEqual(list(self.rewrites()), [str(top)])
        self.assertEqual(self.invoke("--resume", during_build=self.rebuild(top, during="B")), (1, [["B"]]))
        self.assertEqual(journal(self.root)[-2]["error"],
                         f"Pinned root-package artifact changed (ctime, mtime, size): {top}")

    def test_untouched_artifacts_record_no_rewrite(self) -> None:
        spare = self.root / ".lake/build/lib/lean/Spare/X.olean"
        spare.parent.mkdir()
        spare.write_bytes(b"Spare.X artifact, never imported\n")
        self.assertEqual(self.invoke(), (0, [["A"], ["B"], ["C"]]))
        self.assertEqual(self.rewrites(), {})
        # Never pinned and never rewritten: trusted like any input present before the run.
        spare.write_bytes(b"changed between invocations\n")
        self.assertEqual(self.invoke("--resume"), (0, []))


if __name__ == "__main__":
    unittest.main()
