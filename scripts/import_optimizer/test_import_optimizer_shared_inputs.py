#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Phase-scoped shared input reuse; external Lean and Lake are mocked at `run_command`."""

from __future__ import annotations

import contextlib
import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from collections import Counter
from collections.abc import Iterator
from pathlib import Path
from unittest.mock import patch

import optimize_imports as optimizer
import test_import_optimizer_recovery as recovery
from test_import_optimizer_cache import runtime_stubs
from test_import_optimizer_performance import library_fixture


REAL_RUN_COMMAND = optimizer.run_command
REAL_TOOLS_RUN = optimizer.Tools.run


DEPENDENCY_PARTS = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")


def shared_dependencies(root: Path, names: tuple[str, ...], count: int = 6,
                        partial: bool = False) -> list[Path]:
    """Give every setup the same strict-layout dependency closure.

    The closure lives under the project's canonical artifact root, so pinning
    it exercises optional-artifact discovery, strict root selection and the
    selected namespace inventory, the parts a real batch spends its time on.
    With `partial`, a flat dependency outside any inventoried namespace starts
    with only its `.olean`, so tests can add optional artifacts that only
    discovery can notice, and a strict external root selects its namespace
    through canonical path resolution.
    """
    library = root / ".lake/build/lib/lean/Dep"
    library.mkdir(parents=True, exist_ok=True)
    prefixes = [library / f"M{index}" for index in range(count)]
    for prefix in prefixes:
        for suffix in DEPENDENCY_PARTS:
            Path(str(prefix) + suffix).write_bytes(f"Mocked {prefix.name}{suffix} bytes\n".encode())
    flat = root / "flat/Flat"
    external = root / "ext/Ext"
    if partial:
        flat.parent.mkdir()
        Path(str(flat) + ".olean").write_bytes(b"Mocked flat dependency bytes\n")
        external.mkdir(parents=True)
        for name in ("X", "Y"):
            (external / (name + ".olean")).write_bytes(b"Mocked external dependency bytes\n")
    for name in names:
        setup = root / ".lake/build/ir" / (name + ".setup.json")
        metadata = optimizer.read_json(setup)
        for prefix in prefixes:
            metadata["importArts"][f"Dep.{prefix.name}"] = [[str(prefix) + ".olean"], []]
        if partial:
            metadata["importArts"]["Flat"] = [[str(flat) + ".olean"], []]
            metadata["importArts"]["Ext.X"] = [[str(external / "X.olean")], []]
        optimizer.write_json(setup, metadata)
    return prefixes


@contextlib.contextmanager
def native_boundaries(root: Path, names: tuple[str, ...]) -> Iterator[tuple[list[str], list[str]]]:
    """Run the real `Tools.run` boundary and real compile arms; only children are mocked."""
    arguments = recovery.main_inputs(root, names) + ["--batch-size", str(len(names))]
    library_fixture(root)
    shared_dependencies(root, names)
    boundaries: list[str] = []

    def native(argv: list[str], cwd: Path, label: Path,
               environment: dict[str, str], timeout: int) -> dict[str, object]:
        if "env" in argv:
            return recovery.environment_stub(argv, cwd, label, environment, timeout)
        boundaries.append(label.name)
        label.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
        output = ""
        if "shake" in argv:
            requested = [argv[index + 1] for index, word in enumerate(argv) if word == "--only"]
            output = "".join(f"{module}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                             for module in requested)
        elif argv[0] == str(root / "bin/time"):
            Path(argv[argv.index("-o") + 1]).write_text(json.dumps({
                "wall_seconds": 0, "user_seconds": 0, "system_seconds": 0, "max_rss_kib": 0}) + "\n")
        elif "build" not in argv and "--run" not in argv:
            raise AssertionError(f"Unexpected external command: {argv}")
        stdout.write_text(output)
        stderr.write_text("")
        result = {"argv": argv, "cwd": str(cwd), "exit_code": 0, "timed_out": False,
                  "elapsed_seconds": 0, "remaining_group_killed": False,
                  "stdout": str(stdout), "stderr": str(stderr)}
        optimizer.write_json(Path(str(label) + ".json"), result)
        return result

    def snapshots(tools: optimizer.Tools, rows: list[dict[str, object]],
                  artifacts: Path | dict[str, Path], arm: Path,
                  compilations: dict[str, dict[str, object]]) -> dict[str, dict[str, object]]:
        arm.mkdir(parents=True, exist_ok=True)
        command = tools.run([str(tools.lean), "-j2", "--run",
                             str(tools.helpers / "declarations_batch.lean"),
                             *(str(row["module"]) for row in rows)], arm / "snapshot")
        optimizer.require_success(command)
        result = {}
        for row in rows:
            relative = Path(str(row["path"]))
            compilation = compilations[str(relative)]
            recovery.bind_mock_snapshot_inputs(tools, compilation, relative)
            olean = Path(str(compilation["artifact_root"])) / relative.with_suffix(".olean")
            result[str(row["module"])] = recovery.SavedSnapshotRecoveryTests.snapshot(
                str(row["module"]), olean)
        return result

    with patch.dict(os.environ, {"LEAN_SYSROOT": str(root)}), \
            patch.object(optimizer.signal, "signal"), \
            patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
            patch.object(optimizer, "run_command", side_effect=native), \
            patch.object(optimizer, "artifact_receipt", return_value=[{"external_artifacts_mock": True}]), \
            patch.object(optimizer, "snapshot_batch", side_effect=snapshots), \
            contextlib.redirect_stdout(io.StringIO()):
        yield arguments, boundaries


class VerifiedBatchScalingTests(unittest.TestCase):
    def test_verified_batch_rebuilds_shared_inputs_linearly_across_native_boundaries(self) -> None:
        counts: dict[int, Counter[str]] = {}
        for size in (2, 4, 8):
            with self.subTest(files=size), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                names = tuple(chr(ord("A") + index) for index in range(size))
                calls: Counter[str] = Counter()
                discovery = optimizer.full_import_artifacts
                check = optimizer.check_shake_inputs
                revalidate = optimizer.revalidate_analysis_inputs
                in_bundle_check = [False]

                def discovered(metadata: dict[str, object], project: Path) -> dict[str, list[list[str]]]:
                    calls["full_import_artifacts"] += 1
                    calls["bundle_reconstructions"] += in_bundle_check[0]
                    return discovery(metadata, project)

                def checked(tools: optimizer.Tools, inputs: object) -> list[dict[str, object]]:
                    calls["bundle_checks"] += 1
                    in_bundle_check[0] = True
                    try:
                        return check(tools, inputs)
                    finally:
                        in_bundle_check[0] = False

                def revalidated(tools: optimizer.Tools) -> None:
                    calls["boundary_bundle_rechecks"] += len(tools.validated_analysis_inputs.get("phase") or ())
                    revalidate(tools)

                with native_boundaries(root, names) as (arguments, boundaries), \
                        patch.object(optimizer, "full_import_artifacts", side_effect=discovered), \
                        patch.object(optimizer, "check_shake_inputs", side_effect=checked), \
                        patch.object(optimizer, "revalidate_analysis_inputs", side_effect=revalidated), \
                        patch.object(sys, "argv", arguments):
                    self.assertEqual(optimizer.main(), 0)
                    rows = [json.loads(line) for line in
                            (root / "output/results.jsonl").read_text().splitlines()]
                    self.assertEqual([row["status"] for row in rows], ["verified"] * size)
                    self.assertTrue(all(row["removed_imports"] == ["import Mathlib"] for row in rows))
                    calls["native_boundaries"] = len(boundaries)
                counts[size] = calls
                print(json.dumps({"files": size, **calls}))
                # Each compile arm crosses a real `Tools.run` boundary, and the
                # first arm of every module rechecks the whole shared Shake
                # bundle before its child runs.
                self.assertGreaterEqual(calls["native_boundaries"], 2 * size)
                self.assertGreaterEqual(calls["boundary_bundle_rechecks"], size)
                self.assertGreaterEqual(calls["bundle_checks"], 2 * size)
        # Boundaries grow linearly, so whole-batch reconstruction per boundary
        # would grow quadratically. Reconstruction must stay linear instead.
        for size in (2, 4, 8):
            self.assertLessEqual(counts[size]["bundle_reconstructions"], 4 * size)
        self.assertLessEqual(counts[8]["bundle_reconstructions"], 2 * counts[4]["bundle_reconstructions"])



def phase_tools(root: Path) -> optimizer.Tools:
    return optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                           Path(optimizer.__file__).resolve().parent / "import_optimizer", {}, 5,
                           root / "bin/time", root / ".lake/lakefile-lean-j2.toml")


@contextlib.contextmanager
def saved_no_change(root: Path, partial: bool = False) -> Iterator[dict[str, object]]:
    """A populated A/B batch whose shared Shake bundle pins a dependency closure."""
    arguments = recovery.main_inputs(root, ("A", "B"))
    shared_dependencies(root, ("A", "B"), partial=partial)
    with runtime_stubs(root), patch.object(sys, "argv", arguments):
        assert optimizer.main() == 0
        result = json.loads((root / "output/results.jsonl").read_text().splitlines()[0])
        assert result["status"] == "no_change" and result["path"] == "A.lean"
        yield result


def mutations(root: Path) -> dict[str, object]:
    library = root / ".lake/build/lib/lean/Dep"
    flat = root / "flat/Flat"
    pinned = Path(str(library / "M0") + ".olean")

    def add_optional_ir() -> None:
        for suffix in (".ir.sig", ".ir"):
            Path(str(flat) + suffix).write_bytes(b"Added optional artifact\n")

    def add_optional_private_pair() -> None:
        for suffix in (".olean.server", ".olean.private"):
            Path(str(flat) + suffix).write_bytes(b"Added optional artifact\n")

    def remove_optional_private_pair() -> None:
        for suffix in (".olean.server", ".olean.private"):
            Path(str(flat) + suffix).unlink()

    def replace_pinned_bytes() -> None:
        pinned.write_bytes(pinned.read_bytes().upper())

    def replace_and_restore_bytes() -> None:
        dependency = root / "fixture-import-part"
        replacement = root / "fixture-import-part.replacement"
        replacement.write_bytes(dependency.read_bytes())
        replacement.replace(dependency)

    def add_namespace_file() -> None:
        (library / "Added.olean").write_bytes(b"Added namespace artifact\n")

    def add_namespace_directory() -> None:
        (library / "Added").mkdir()

    def replace_namespace_with_symlink() -> None:
        moved = root / "elsewhere/Dep"
        moved.parent.mkdir()
        shutil.copytree(library, moved)
        shutil.rmtree(library)
        library.symlink_to(moved, target_is_directory=True)

    def replace_flat_directory_with_symlink() -> None:
        moved = root / "elsewhere-flat"
        shutil.copytree(flat.parent, moved)
        shutil.rmtree(flat.parent)
        flat.parent.symlink_to(moved, target_is_directory=True)

    def retarget_external_root() -> None:
        # Same lexical artifact path, different canonical root and inventory.
        moved = root / "ext-moved"
        shutil.copytree(root / "ext", moved)
        (moved / "Ext/Z.olean").write_bytes(b"Only in the new canonical root\n")
        shutil.rmtree(root / "ext")
        (root / "ext").symlink_to(moved, target_is_directory=True)

    def remove_dependency_part() -> None:
        Path(str(library / "M1") + ".olean.private").unlink()

    def edit_sibling_setup() -> None:
        setup = root / ".lake/build/ir/B.setup.json"
        metadata = optimizer.read_json(setup)
        metadata["importArts"]["Dep.M0"] = [[str(pinned)], [str(library / "M0") + ".ir.sig"]]
        optimizer.write_json(setup, metadata)

    def edit_sibling_source() -> None:
        (root / "B.lean").write_bytes(recovery.ORIGINAL + b"-- edited before child\n")

    return {name.removesuffix("_"): value for name, value in locals().items()
            if callable(value) and not name.startswith("_")}


# Expected outcome of each mutation at the next native boundary; the
# original derivation-free validation must reach the same outcome.
BOUNDARY_OUTCOMES = {
    "add_optional_ir": "rejected", "add_optional_private_pair": "rejected",
    "replace_pinned_bytes": "rejected", "replace_and_restore_bytes": "child ran",
    "add_namespace_file": "rejected", "add_namespace_directory": "rejected",
    "replace_namespace_with_symlink": "rejected",
    "replace_flat_directory_with_symlink": "child ran",
    "retarget_external_root": "rejected", "remove_dependency_part": "rejected",
    "edit_sibling_setup": "rejected", "edit_sibling_source": "rejected",
}


class BoundaryMutationTests(unittest.TestCase):
    """Reused derivations still reject changes before the next native child."""

    def outcome(self, name: str, reuse: bool) -> str:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with saved_no_change(root, partial=True) as result:
                mutate = mutations(root)[name]
                tools = phase_tools(root)
                marker = root / "real-child-marker"
                argv = [sys.executable, "-B", "-c",
                        "from pathlib import Path; Path(" + repr(str(marker)) + ").write_text('ran')"]
                calls: Counter[str] = Counter()
                derive = optimizer.derive_compilation_input_paths

                def counted(*arguments: object) -> tuple[str, ...]:
                    calls["derived"] += 1
                    return derive(*arguments)

                with contextlib.ExitStack() as stack:
                    stack.enter_context(patch.object(optimizer.Tools, "run", REAL_TOOLS_RUN))
                    stack.enter_context(patch.object(optimizer, "run_command", REAL_RUN_COMMAND))
                    stack.enter_context(patch.object(optimizer, "derive_compilation_input_paths",
                                                     side_effect=counted))
                    if not reuse:
                        stack.enter_context(patch.object(optimizer, "active_prepared_inputs",
                                                         return_value=None))
                    try:
                        with optimizer.analysis_validation_phase(tools):
                            optimizer.verify_saved_no_change(result, tools)
                            first = calls["derived"]
                            optimizer.require_success(tools.run(argv, root / "output/first-child"))
                            optimizer.verify_saved_no_change(result, tools)
                            # The first boundary and the following check
                            # reused both members' stored derivations.
                            self.assertEqual(calls["derived"], first if reuse else 3 * first)
                            marker.unlink()
                            mutate()
                            optimizer.require_success(tools.run(argv, root / "output/second-child"))
                    except (ValueError, OSError):
                        self.assertFalse(marker.exists())
                        verdict = "rejected"
                    else:
                        self.assertEqual(marker.read_text(), "ran")
                        verdict = "child ran"
                self.assertEqual(tools.prepared_inputs, {})
                self.assertEqual(tools.validated_analysis_inputs, {})
                return verdict

    def test_mutation_after_reuse_has_the_original_boundary_outcome(self) -> None:
        # Removing the flat optional pair needs the pair first; the
        # derivation test below covers it, and `remove_dependency_part` here.
        self.assertEqual(set(BOUNDARY_OUTCOMES),
                         set(mutations(Path("/unused"))) - {"remove_optional_private_pair"})
        for name, expected in BOUNDARY_OUTCOMES.items():
            with self.subTest(mutation=name):
                self.assertEqual(self.outcome(name, reuse=True), expected)
                self.assertEqual(self.outcome(name, reuse=False), expected)


class DerivationScopeTests(unittest.TestCase):
    def test_no_reuse_outside_a_phase_or_outside_bundle_checks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with saved_no_change(root) as result:
                tools = phase_tools(root)
                calls = Counter()
                derive = optimizer.derive_compilation_input_paths

                def counted(*arguments: object) -> tuple[str, ...]:
                    calls["derived"] += 1
                    return derive(*arguments)

                metadata = optimizer.read_json(root / ".lake/build/ir/A.setup.json")
                with patch.object(optimizer, "derive_compilation_input_paths", side_effect=counted):
                    # Standalone validation never keeps derivations.
                    optimizer.verify_saved_no_change(result, tools)
                    optimizer.verify_saved_no_change(result, tools)
                    self.assertEqual(calls["derived"], 4)
                    self.assertEqual(tools.prepared_inputs, {})
                    with optimizer.analysis_validation_phase(tools):
                        prepared = tools.prepared_inputs["phase"]
                        # Callers other than the shared bundle check always derive.
                        before = calls["derived"]
                        for _ in range(2):
                            optimizer.compilation_input_paths(metadata, root, None, tools)
                        self.assertEqual(calls["derived"], before + 2)
                        self.assertEqual(prepared.derivations, {})
                        optimizer.verify_saved_no_change(result, tools)
                        self.assertEqual(len(prepared.derivations), 2)
                    self.assertEqual(tools.prepared_inputs, {})
                    # A later phase starts empty instead of trusting the earlier one.
                    before = calls["derived"]
                    with optimizer.analysis_validation_phase(tools):
                        self.assertEqual(tools.prepared_inputs["phase"].derivations, {})
                        optimizer.verify_saved_no_change(result, tools)
                    self.assertEqual(calls["derived"], before + 2)

    def test_each_boundary_rereads_facts_before_reuse(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with saved_no_change(root) as result:
                tools = phase_tools(root)
                reads: Counter[str] = Counter()
                read = optimizer.read_input_fact

                def counted(kind: str, path: Path) -> object:
                    reads[kind] += 1
                    return read(kind, path)

                child = [sys.executable, "-B", "-c", "pass"]
                with patch.object(optimizer, "run_command", REAL_RUN_COMMAND), \
                        patch.object(optimizer.Tools, "run", REAL_TOOLS_RUN), \
                        optimizer.analysis_validation_phase(tools):
                    optimizer.verify_saved_no_change(result, tools)
                    window = tools.prepared_inputs["phase"].window
                    with patch.object(optimizer, "read_input_fact", side_effect=counted):
                        totals = []
                        for index in range(3):
                            optimizer.require_success(tools.run(child, root / f"output/child-{index}"))
                            totals.append(sum(reads.values()))
                            self.assertEqual(window, {})
                            optimizer.verify_saved_no_change(result, tools)
                    # Every boundary and every following check re-read the
                    # same deduplicated facts; none were carried over.
                    self.assertGreater(totals[0], 0)
                    self.assertEqual(totals[1] - totals[0], totals[2] - totals[1])
                    self.assertGreaterEqual(totals[1] - totals[0], totals[0])

    def test_reused_paths_match_a_fresh_derivation_after_each_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with saved_no_change(root, partial=True):
                tools = phase_tools(root)
                metadata = optimizer.read_json(root / ".lake/build/ir/A.setup.json")
                steps = mutations(root)
                sequence = ["add_optional_ir", "add_optional_private_pair",
                            "replace_flat_directory_with_symlink", "remove_optional_private_pair",
                            "retarget_external_root", "replace_namespace_with_symlink"]
                results: list[object] = []
                with optimizer.analysis_validation_phase(tools):
                    prepared = tools.prepared_inputs["phase"]

                    def reused() -> object:
                        prepared.new_window()
                        try:
                            with optimizer.using_prepared_inputs(tools):
                                return optimizer.compilation_input_paths(metadata, root, None, tools)
                        except (ValueError, OSError) as error:
                            return type(error)

                    def fresh() -> object:
                        # The original derivation, over the same cached inventories.
                        try:
                            return optimizer.derive_compilation_input_paths(metadata, root, None, tools)
                        except (ValueError, OSError) as error:
                            return type(error)

                    results.append(reused())
                    self.assertEqual(results[-1], fresh())
                    for name in sequence:
                        with self.subTest(mutation=name):
                            steps[name]()
                            results.append(reused())
                            self.assertEqual(results[-1], fresh())
                            self.assertEqual(reused(), results[-1])
                flat, external = str(root / "flat/Flat"), str(root / "ext-moved/Ext") + "/"
                self.assertNotIn(flat + ".ir", results[0])
                self.assertIn(flat + ".ir", results[1])
                self.assertIn(flat + ".olean.private", results[2])
                self.assertEqual(results[3], results[2])
                self.assertNotIn(flat + ".olean.private", results[4])
                self.assertIn(str(root / "ext/Ext/Y.olean"), results[4])
                self.assertIn(external + "Z.olean", results[5])
                self.assertNotIn(str(root / "ext/Ext/Y.olean"), results[5])
                # A namespace replaced by a symlink resolves to a new inventory.
                self.assertIn(str(root / "elsewhere/Dep/M0.olean"), results[6])

    def test_recorded_facts_cover_every_filesystem_read(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with saved_no_change(root, partial=True):
                (root / ".lake/build/lib/lean/Dep/Nested").mkdir()
                (root / ".lake/build/lib/lean/Dep/Nested/X.olean").write_bytes(b"Nested artifact\n")
                link = root / "linked-dependency"
                link.symlink_to(root / ".lake/build/lib/lean/Dep/M0.olean")
                setup = root / ".lake/build/ir/A.setup.json"
                metadata = optimizer.read_json(setup)
                metadata["importArts"]["Dep.Linked"] = [[str(link)], []]
                tools = phase_tools(root)
                touched: set[str] = set()
                originals = {name: getattr(os, name) for name in ("stat", "lstat", "scandir", "readlink", "listdir")}

                def spy(name: str):
                    def call(path: object = ".", *arguments: object, **keywords: object) -> object:
                        touched.add(os.fsdecode(os.fspath(path)) if not isinstance(path, int) else "")
                        return originals[name](path, *arguments, **keywords)
                    return call

                with optimizer.analysis_validation_phase(tools):
                    prepared = tools.prepared_inputs["phase"]
                    # Warm the library inventories so the recorded run reads
                    # them only through their cached directory identities.
                    optimizer.derive_compilation_input_paths(metadata, root, None, tools)
                    with contextlib.ExitStack() as stack:
                        for name in originals:
                            stack.enter_context(patch.object(os, name, spy(name)))
                        stack.enter_context(patch("io.open", side_effect=AssertionError("unrecorded file read")))
                        with optimizer.using_prepared_inputs(tools):
                            paths = optimizer.compilation_input_paths(metadata, root, None, tools)
                    facts = next(iter(prepared.derivations.values()))[1]
                self.assertIn(str(link), paths)
                covered: set[str] = set()
                inventories = []
                for (kind, path), value in facts.items():
                    covered.add(path)
                    covered.update(str(parent) for parent in Path(path).parents)
                    if kind in ("resolve", "inventory_resolve") and isinstance(value, str):
                        covered.add(value)
                        covered.update(str(parent) for parent in Path(value).parents)
                    if kind == "inventory":
                        inventories.append(path)
                uncovered = sorted(path for path in touched if path not in covered and
                                   not any(Path(path).is_relative_to(library) for library in inventories))
                self.assertGreater(len(touched), 0)
                self.assertTrue(any(kind == "inventory" for kind, _ in facts))
                self.assertEqual(uncovered, [])


if __name__ == "__main__":
    unittest.main()
