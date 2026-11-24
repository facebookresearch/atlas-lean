#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Snapshot verification reuse on a grouped batch with a private-only import.

External Lean and Lake are mocked at `run_command`. Compilation, grouped
snapshot collection, private closure discovery, fallback inventories and saved
validation run the optimizer's own code.
"""

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
import test_import_optimizer_outputs as outputs
import test_import_optimizer_recovery as recovery


REAL_RUN_COMMAND = optimizer.run_command


DEPENDENCY_PARTS = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")
PRIVATE_MODULE = "Priv.Hidden"


def private_parts(root: Path) -> list[list[str]]:
    prefix = root / ".lake/build/lib/lean/Priv/Hidden"
    return [[str(prefix) + suffix for suffix in (".olean", ".olean.server", ".olean.private")],
            [str(prefix) + suffix for suffix in (".ir.sig", ".ir")]]


def module_names(size: int) -> tuple[str, ...]:
    return tuple(f"M{chr(ord('A') + index)}" for index in range(size))


@contextlib.contextmanager
def private_batch(root: Path, size: int, dependencies: int = 8,
                  on_command: object = None) -> Iterator[tuple[list[str], list[str]]]:
    """Yield main() arguments and the native command labels in call order.

    `on_command(kind, argv, cwd, label, environment, timeout)` runs before
    each mocked native child of kind `build`, `shake`, `compile`, `deps`,
    `private_closure`, `unpinned_snapshot` or `snapshot`.
    """
    names = module_names(size)
    arguments = recovery.main_inputs(root, names) + ["--batch-size", str(size)]
    canonical = root / ".lake/build/lib/lean"
    for module in names:
        outputs.physical_parts(canonical, Path(module + ".lean"))
    library = canonical / "Dep"
    library.mkdir(parents=True)
    prefixes = [library / f"D{index}" for index in range(dependencies)]
    for prefix in prefixes:
        for suffix in DEPENDENCY_PARTS:
            Path(str(prefix) + suffix).write_bytes(b"Mocked dependency bytes\n")
    for group in private_parts(root):
        for name in group:
            Path(name).parent.mkdir(parents=True, exist_ok=True)
            Path(name).write_bytes(b"Mocked private-only dependency bytes\n")
    # A namespace only the fallback inventory sees, and a dependency that
    # starts without its optional IR artifacts.
    (canonical / "Extra").mkdir()
    (canonical / "Extra/Only.olean").write_bytes(b"Mocked unrelated fallback artifact\n")
    partial = library / "Partial"
    Path(str(partial) + ".olean").write_bytes(b"Mocked partial dependency bytes\n")
    for module in names:
        setup = root / ".lake/build/ir" / (module + ".setup.json")
        metadata = optimizer.read_json(setup)
        for prefix in prefixes:
            metadata["importArts"][f"Dep.{prefix.name}"] = [[str(prefix) + ".olean"], []]
        metadata["importArts"]["Dep.Partial"] = [[str(partial) + ".olean"], []]
        optimizer.write_json(setup, metadata)
    labels: list[str] = []

    def external(argv: list[str], cwd: Path, label: Path,
                 environment: dict[str, str], timeout: int) -> dict[str, object]:
        label.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = Path(str(label) + ".stdout"), Path(str(label) + ".stderr")
        text, error, code = "", "", 0
        kind = ""
        if "env" in argv:
            text = json.dumps({"LAKE": str(root / "bin/lake"), "LEAN_PATH": str(canonical),
                               "LEAN_SYSROOT": str(root)})
        elif "build" in argv:
            kind = "build"
        elif "shake" in argv:
            kind = "shake"
            text = "".join(f"{module}.lean:\n  remove #[import Mathlib]\n  add #[import Init]\n"
                           for module in names)
        elif argv[0] == str(root / "bin/time"):
            kind = "compile"
        elif "--deps" in argv:
            kind = "deps"
        elif "--run" in argv:
            helper = Path(argv[argv.index("--run") + 1]).name
            value = optimizer.read_json(Path(argv[argv.index("--run") + 2]))
            if helper == "private_imports.lean":
                kind = "private_closure"
            elif PRIVATE_MODULE not in value["importArts"]:
                kind = "unpinned_snapshot"
            else:
                kind = "snapshot"
        else:
            raise AssertionError(f"Unexpected native command: {argv}")
        if kind:
            labels.append(kind)
            if callable(on_command):
                on_command(kind, argv, cwd, label, environment, timeout)
        if kind == "compile":
            source = Path(argv[argv.index("-R") + 2])
            outputs.physical_parts(Path(argv[argv.index("-i") + 1]).parent, Path(source.name))
            Path(argv[argv.index("-o") + 1]).write_text('{"wall_seconds":0}\n')
        elif kind == "deps":
            modules = [line.removeprefix("import all ") for line in Path(argv[-1]).read_text().splitlines()]
            text = "".join(str(Path(environment["LEAN_PATH"]) / (module + ".olean")) + "\n"
                           for module in modules)
        elif kind == "private_closure":
            rows = [{"module": module, "artifacts": artifacts}
                    for module, artifacts in value["importArts"].items()]
            rows.append({"module": PRIVATE_MODULE, "artifacts": private_parts(root)})
            text = json.dumps(rows) + "\n"
        elif kind == "unpinned_snapshot":
            error = json.dumps({"kind": "missing_private_import_artifacts", "module": PRIVATE_MODULE}) + "\n"
            code = 3
        elif kind == "snapshot":
            modules = argv[argv.index("--run") + 3:]
            records = []
            for module in modules:
                record = recovery.SavedSnapshotRecoveryTests.snapshot(
                    module, Path(value["importArts"][module][0][0]))
                record.update(batch_modules=modules, batch_module_count=len(modules),
                              loaded_modules_scope="whole_batch",
                              loaded_modules=["Init", PRIVATE_MODULE, *modules],
                              loaded_module_count=len(modules) + 2)
                records.append(record)
            text = "".join(json.dumps(record) + "\n" for record in records)
        stdout.write_text(text)
        stderr.write_text(error)
        command = {"argv": list(argv), "cwd": str(cwd), "exit_code": code, "timed_out": False,
                   "elapsed_seconds": 0, "remaining_group_killed": False,
                   "stdout": str(stdout), "stderr": str(stderr)}
        optimizer.write_json(Path(str(label) + ".json"), command)
        return command

    with patch.object(optimizer.signal, "signal"), \
            patch.object(optimizer.subprocess, "check_output", side_effect=recovery.time_version_stub), \
            patch.object(optimizer, "run_command", side_effect=external), \
            contextlib.redirect_stdout(io.StringIO()):
        yield arguments, labels


def run_main(arguments: list[str]) -> int:
    with patch.object(sys, "argv", arguments):
        return optimizer.main()


def fixture_tools(root: Path) -> optimizer.Tools:
    return optimizer.Tools(root, root / "output", root / "bin/lake", root / "bin/lean",
                           Path(optimizer.__file__).resolve().parent / "import_optimizer",
                           {"LEAN_PATH": str(root / ".lake/build/lib/lean"), "LEAN_SYSROOT": str(root)},
                           5, root / "bin/time")


def saved_results(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "output/results.jsonl").read_text().splitlines()]


def snapshot_setups(results: list[dict[str, object]]) -> list[dict[str, object]]:
    return [optimizer.read_json(Path(result[arm]["snapshot_setup"]["path"]))
            for result in results for arm in ("baseline", "candidate")]


class GroupedPrivateSnapshotScalingTests(unittest.TestCase):
    def test_fresh_snapshot_checks_reuse_derivations_linearly(self) -> None:
        counts: dict[int, Counter[str]] = {}
        for size in (2, 4, 8):
            with self.subTest(files=size), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                calls: Counter[str] = Counter()
                inside = [0]
                originals = {name: getattr(optimizer, name) for name in (
                    "derive_compilation_input_paths", "derive_private_fallback_artifact_paths",
                    "verify_snapshot_dependencies")}

                def counted(name: str):
                    def call(*arguments: object, **keywords: object) -> object:
                        calls[name] += 1
                        if inside[0]:
                            calls[name + "[in snapshot checks]"] += 1
                        return originals[name](*arguments, **keywords)
                    return call

                def verify(*arguments: object, **keywords: object) -> object:
                    calls["verify_snapshot_dependencies"] += 1
                    inside[0] += 1
                    try:
                        return originals["verify_snapshot_dependencies"](*arguments, **keywords)
                    finally:
                        inside[0] -= 1

                with private_batch(root, size) as (arguments, labels), contextlib.ExitStack() as stack:
                    for name in ("derive_compilation_input_paths", "derive_private_fallback_artifact_paths"):
                        stack.enter_context(patch.object(optimizer, name, side_effect=counted(name)))
                    stack.enter_context(patch.object(optimizer, "verify_snapshot_dependencies", side_effect=verify))
                    self.assertEqual(run_main(arguments), 0)
                    results = saved_results(root)
                    self.assertEqual([result["status"] for result in results], ["verified"] * size)
                    self.assertTrue(all(result["removed_imports"] == ["import Mathlib"] for result in results))
                    self.assertTrue(all("snapshot_group" in result[arm] for result in results
                                        for arm in ("baseline", "candidate")))
                    # The production path hit the private-import completion branch.
                    self.assertEqual(labels.count("unpinned_snapshot"), 2)
                    self.assertGreaterEqual(labels.count("private_closure"), 4)
                    self.assertTrue(all(value.get("snapshot_private_dependencies") is not None
                                        for value in snapshot_setups(results)))
                    calls["deps"] = labels.count("deps")
                counts[size] = calls
                print(json.dumps({"files": size, **calls}))
                # One fresh check follows every dependency probe and the snapshot.
                self.assertGreaterEqual(calls["verify_snapshot_dependencies"], 2 * (size + 1))
        for size in (2, 4, 8):
            self.assertLessEqual(counts[size]["derive_compilation_input_paths"], 24 * size)
            self.assertLessEqual(counts[size]["derive_compilation_input_paths[in snapshot checks]"], 4 * size)
            self.assertLessEqual(counts[size]["derive_private_fallback_artifact_paths"], 16 * size)
        self.assertLessEqual(counts[8]["derive_compilation_input_paths"],
                             2.2 * counts[4]["derive_compilation_input_paths"])


def snapshot_mutations(root: Path) -> dict[str, object]:
    canonical = root / ".lake/build/lib/lean"
    library = canonical / "Dep"
    pinned = Path(str(library / "D0") + ".olean")

    def add_root_namespace() -> None:
        (canonical / "Added").mkdir()
        (canonical / "Added/New.olean").write_bytes(b"Added namespace artifact\n")

    def remove_root_namespace() -> None:
        shutil.rmtree(canonical / "Extra")

    def add_optional_artifacts() -> None:
        for suffix in (".ir.sig", ".ir"):
            Path(str(library / "Partial") + suffix).write_bytes(b"Added optional artifact\n")

    def edit_sibling_setup() -> None:
        setup = root / ".lake/build/ir/MB.setup.json"
        metadata = optimizer.read_json(setup)
        metadata["edited"] = True
        optimizer.write_json(setup, metadata)

    def edit_sibling_source() -> None:
        (root / "MB.lean").write_bytes(recovery.ORIGINAL + b"-- edited between snapshot checks\n")

    def retarget_namespace_symlink() -> None:
        moved = root / "elsewhere/Dep"
        moved.parent.mkdir()
        shutil.copytree(library, moved)
        shutil.rmtree(library)
        library.symlink_to(moved, target_is_directory=True)

    def replace_and_restore_artifact() -> None:
        replacement = pinned.with_name(pinned.name + ".replacement")
        replacement.write_bytes(pinned.read_bytes())
        replacement.replace(pinned)

    return {name: value for name, value in locals().items()
            if callable(value) and not name.startswith("_")}


class SnapshotMutationTests(unittest.TestCase):
    """A change after a reused snapshot check is rejected before the next child."""

    def outcome(self, name: str, reuse: bool) -> dict[str, object]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            marker = root / "child-after-mutation"
            state: dict[str, object] = {"checks": 0, "mutated": False, "rejected": None}
            verify = optimizer.verify_snapshot_dependencies
            batch = optimizer.snapshot_batch
            derived: Counter[str] = Counter()
            derive = optimizer.derive_compilation_input_paths

            def counted(*arguments: object, **keywords: object) -> object:
                derived["after_first_check" if state["checks"] else "before"] += 1
                return derive(*arguments, **keywords)

            def checked(*arguments: object, **keywords: object) -> object:
                verify(*arguments, **keywords)
                state["checks"] = cast_int(state["checks"]) + 1
                # Mutate after the second fresh check of the first batch: the
                # first stored the derivations and the second reused them.
                if state["checks"] == 2 and not state["mutated"]:
                    snapshot_mutations(root)[name]()
                    state["mutated"] = True

            def collected(*arguments: object, **keywords: object) -> object:
                try:
                    return batch(*arguments, **keywords)
                except (ValueError, OSError) as error:
                    if state["mutated"] and state["rejected"] is None:
                        state["rejected"] = type(error).__name__
                        state["marker_at_rejection"] = marker.exists()
                    raise

            def child(kind: str, argv: list[str], cwd: Path, label: Path,
                      environment: dict[str, str], timeout: int) -> None:
                if state["mutated"] and state["rejected"] is None:
                    # The next native child after the change is a real process.
                    REAL_RUN_COMMAND([sys.executable, "-B", "-c",
                                      "from pathlib import Path; Path(" + repr(str(marker)) + ").write_text('ran')"],
                                     cwd, Path(str(label) + ".marker"), environment, timeout)

            with private_batch(root, 2, on_command=child) as (arguments, labels), contextlib.ExitStack() as stack:
                stack.enter_context(patch.object(optimizer, "verify_snapshot_dependencies", side_effect=checked))
                stack.enter_context(patch.object(optimizer, "snapshot_batch", side_effect=collected))
                stack.enter_context(patch.object(optimizer, "derive_compilation_input_paths", side_effect=counted))
                if not reuse:
                    stack.enter_context(patch.object(optimizer, "active_prepared_inputs", return_value=None))
                try:
                    run_main(arguments)
                except (ValueError, OSError):
                    pass
            self.assertTrue(state["mutated"], name)
            return {"rejected": state["rejected"], "child_before_rejection": state.get("marker_at_rejection"),
                    "derived_after_first_check": derived["after_first_check"]}

    def test_change_between_reused_checks_has_the_original_outcome(self) -> None:
        for name in snapshot_mutations(Path("/unused")):
            with self.subTest(mutation=name):
                reused, original = self.outcome(name, True), self.outcome(name, False)
                self.assertIsNotNone(reused["rejected"])
                self.assertEqual(reused["rejected"], original["rejected"])
                self.assertEqual(reused["child_before_rejection"], original["child_before_rejection"])
                self.assertEqual(reused["child_before_rejection"], name in CHECKED_AFTER_THE_NEXT_CHILD)


# Changes only the post-child snapshot check sees, as before: the next
# dependency probe runs, and the check after it rejects the batch.
CHECKED_AFTER_THE_NEXT_CHILD = {"add_root_namespace"}


def cast_int(value: object) -> int:
    assert isinstance(value, int)
    return value


class FallbackDerivationTests(unittest.TestCase):
    @contextlib.contextmanager
    def completed(self, size: int = 2) -> Iterator[tuple[Path, optimizer.Tools, dict[str, object]]]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with private_batch(root, size) as (arguments, _):
                self.assertEqual(run_main(arguments), 0)
                tools = fixture_tools(root)
                metadata = optimizer.read_json(root / ".lake/build/ir/MA.setup.json")
                yield root, tools, metadata

    def test_reused_fallback_inventory_matches_a_fresh_one_after_listing_changes(self) -> None:
        with self.completed() as (root, tools, metadata):
            canonical = root / ".lake/build/lib/lean"
            steps = [
                ("new namespace", lambda: (
                    (canonical / "Fresh").mkdir(), (canonical / "Fresh/A.olean").write_bytes(b"x\n"))),
                ("artifact in a cached namespace", lambda: (canonical / "Fresh/C.olean").write_bytes(b"x\n")),
                ("root-level module", lambda: (canonical / "Top.olean").write_bytes(b"x\n")),
                ("removed namespace", lambda: shutil.rmtree(canonical / "Extra")),
                ("namespace replaced by a symlink", lambda: (
                    shutil.copytree(canonical / "Fresh", root / "fresh-copy"),
                    (root / "fresh-copy/B.olean").write_bytes(b"x\n"),
                    shutil.rmtree(canonical / "Fresh"),
                    (canonical / "Fresh").symlink_to(root / "fresh-copy", target_is_directory=True))),
                ("namespace symlink into output", lambda: (
                    (root / "output/Leak").mkdir(),
                    (root / "output/Leak/X.olean").write_bytes(b"x\n"),
                    (canonical / "Leak").symlink_to(root / "output/Leak", target_is_directory=True))),
            ]
            results: list[object] = []
            with optimizer.analysis_validation_phase(tools):
                prepared = tools.prepared_inputs["phase"]

                def reused() -> object:
                    prepared.new_window()
                    try:
                        with optimizer.using_prepared_inputs(tools):
                            return optimizer.private_fallback_artifact_paths(tools, metadata)
                    except (ValueError, OSError) as error:
                        return type(error)

                def fresh() -> object:
                    try:
                        return optimizer.derive_private_fallback_artifact_paths(tools, metadata)
                    except (ValueError, OSError) as error:
                        return type(error)

                results.append(reused())
                self.assertEqual(results[-1], fresh())
                for label, step in steps:
                    with self.subTest(step=label):
                        step()
                        results.append(reused())
                        self.assertEqual(results[-1], fresh())
                        self.assertEqual(reused(), results[-1])
            self.assertIn(str(canonical / "Extra/Only.olean"), results[0])
            self.assertIn(str(canonical / "Fresh/A.olean"), results[1])
            # A cached namespace whose membership changed is rejected by its
            # directory identities, by both the reused and the fresh path.
            self.assertIs(results[2], ValueError)
            self.assertIs(results[3], ValueError)

    def test_recorded_fallback_facts_cover_every_filesystem_read(self) -> None:
        with self.completed() as (root, tools, metadata):
            canonical = root / ".lake/build/lib/lean"
            (canonical / "Empty").mkdir()
            (canonical / "Top.olean").write_bytes(b"x\n")
            (root / "linked-ns").mkdir()
            (root / "linked-ns/L.olean").write_bytes(b"x\n")
            (canonical / "Linked").symlink_to(root / "linked-ns", target_is_directory=True)
            touched: set[str] = set()
            originals = {name: getattr(os, name) for name in ("stat", "lstat", "scandir", "readlink", "listdir")}

            def spy(name: str):
                def call(path: object = ".", *arguments: object, **keywords: object) -> object:
                    touched.add(os.fsdecode(os.fspath(path)) if not isinstance(path, int) else "")
                    return originals[name](path, *arguments, **keywords)
                return call

            with optimizer.analysis_validation_phase(tools):
                prepared = tools.prepared_inputs["phase"]
                # Warm the inventory cache, so the recorded run reads each
                # inventory only through its directory identities.
                optimizer.derive_private_fallback_artifact_paths(tools, metadata)
                with contextlib.ExitStack() as stack:
                    for name in originals:
                        stack.enter_context(patch.object(os, name, spy(name)))
                    stack.enter_context(patch("io.open", side_effect=AssertionError("unrecorded file read")))
                    with optimizer.using_prepared_inputs(tools):
                        paths = optimizer.private_fallback_artifact_paths(tools, metadata)
                facts = next(value for key, value in prepared.derivations.items()
                             if key[0] == "private_fallback")[1]
            self.assertIn(str(canonical / "Top.olean"), paths)
            self.assertIn(str(canonical / "Linked/L.olean"), paths)
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
                               not any(Path(path).is_relative_to(inventory) for inventory in inventories))
            self.assertTrue(any(kind == "children" for kind, _ in facts))
            self.assertGreater(len(touched), 0)
            self.assertEqual(uncovered, [])

    def test_saved_rows_ignore_unrelated_fallback_changes_but_fresh_checks_do_not(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            with private_batch(root, 2) as (arguments, _):
                self.assertEqual(run_main(arguments), 0)
                journal = (root / "output/results.jsonl").read_bytes()
                tools = fixture_tools(root)
                result = saved_results(root)[0]
                setup_pin = result["baseline"]["snapshot_setup"]
                setup = Path(setup_pin["path"])
                identities = optimizer.snapshot_dependency_identities(setup, tools, setup_pin=setup_pin)
                artifact_root = Path(result["baseline"]["artifact_root"])
                optimizer.verify_snapshot_dependencies(tools, artifact_root, setup, identities)
                canonical = root / ".lake/build/lib/lean"
                (canonical / "Unrelated").mkdir()
                (canonical / "Unrelated/U.olean").write_bytes(b"Unrelated rebuilt artifact\n")
                # Fresh (exact) snapshot verification rejects the new fallback member...
                with optimizer.analysis_validation_phase(tools):
                    with self.assertRaises(ValueError):
                        optimizer.verify_snapshot_dependencies(tools, artifact_root, setup, identities)
                # ...while saved-row resume keeps exact=False isolation.
                self.assertEqual(run_main([*arguments, "--resume"]), 0)
                self.assertEqual((root / "output/results.jsonl").read_bytes(), journal)


if __name__ == "__main__":
    unittest.main()
