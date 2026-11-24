#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#
# This source code is licensed under the license found in the
# LICENSE file in the root directory of this source tree.

"""Run the optimizer and resume on a small real Lean project, without downloads."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

SCRIPTS = Path(__file__).resolve().parents[1]
SOURCE = """module

import Std.Data.HashMap
import Std.Data.TreeMap

@[expose] public def answer : Nat := 42
public theorem answer_eq : answer = 42 := rfl
"""


def run(argv: list[str], root: Path) -> None:
    try:
        subprocess.run(argv, cwd=root, check=True)
    except subprocess.CalledProcessError:
        journal = root / ".lake/import-results/results.jsonl"
        if journal.exists():
            for line in journal.read_text().splitlines():
                row = json.loads(line)
                print(json.dumps({key: row.get(key) for key in ("path", "status", "error")}),
                      file=sys.stderr)
        raise


def smoke_test(lake: Path, root: Path) -> None:
    lean = lake.with_name("lean")
    (root / "Smoke.lean").write_text(SOURCE)
    (root / "lean-toolchain").write_bytes((SCRIPTS.parent / "lean-toolchain").read_bytes())
    (root / "lakefile.toml").write_text(
        'name = "import_optimizer_smoke"\n'
        'defaultTargets = ["Smoke"]\n\n[[lean_lib]]\nname = "Smoke"\n'
    )
    (root / "lake-manifest.json").write_text(json.dumps({
        "version": "1.1.0", "packagesDir": ".lake/packages", "packages": [],
        "name": "import_optimizer_smoke", "lakeDir": ".lake",
    }) + "\n")
    run(["git", "init", "-q"], root)
    run(["git", "add", "Smoke.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json"], root)
    run(["git", "-c", "user.name=Optimizer Test", "-c", "user.email=test@example.invalid",
         "commit", "-qm", "Import optimizer smoke fixture"], root)
    manifest = root / ".lake/inventory.jsonl"
    run([sys.executable, str(SCRIPTS / "generate_import_inventory.py"),
         "--root", str(root), "--lean", str(lean), "--output", str(manifest)], root)
    output = root / ".lake/import-results"
    command = [sys.executable, str(SCRIPTS / "optimize_imports.py"),
               "--root", str(root), "--lake", str(lake), "--manifest", str(manifest),
               "--output", str(output), "--batch-size", "1"]
    run(command, root)
    summary = json.loads((output / "summary.json").read_text())
    assert summary["status_counts"] == {
        "verified": 1, "no_change": 0, "blocked": 0, "readonly": 0,
    }, summary
    assert summary["pending_count"] == 0, summary
    journal = (output / "results.jsonl").read_bytes()
    result, = [json.loads(line) for line in journal.splitlines()]
    assert result["module"] == "Smoke", result
    assert result["declaration_count"] == 2 and result["declaration_differences"] == [], result
    assert set(result["removed_imports"]) == {
        "import Std.Data.HashMap", "import Std.Data.TreeMap",
    }, result
    for arm in ("baseline", "candidate"):
        assert result[arm]["command"]["exit_code"] == 0, result[arm]
        assert len(result[arm]["artifacts"]) == 7, result[arm]
    assert (root / "Smoke.lean").read_text() == SOURCE
    patches = list(output.rglob("*.patch"))
    assert len(patches) == 1 and "-import Std.Data." in patches[0].read_text(), patches
    run([*command, "--resume"], root)
    assert (output / "results.jsonl").read_bytes() == journal
    assert (root / "Smoke.lean").read_text() == SOURCE
    print("PASS: real candidate verified; unused imports removed in saved patch; source unchanged; resume verified")


def legacy_smoke_test(lake: Path, import_graph: Path, root: Path) -> None:
    """Exercise the pinned ImportGraph API when its package has already been built."""
    manifest = json.loads((SCRIPTS.parent / "lake-manifest.json").read_text())
    expected = next(package["rev"] for package in manifest["packages"]
                    if package["name"] == "importGraph")
    actual = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=import_graph, text=True,
    ).strip()
    assert actual == expected, (actual, expected)
    source = root / "Legacy.lean"
    source.write_text("import Std.Data.HashMap\n\n"
                      "def legacySize (m : Std.HashMap Nat Nat) : Nat := m.size\n")
    lean = lake.with_name("lean")
    environment = dict(os.environ)
    environment.update(json.loads((root / ".lake/import-results/environment.stdout").read_text()))
    environment["LEAN_PATH"] = os.pathsep.join((
        str(root), str(import_graph / ".lake/build/lib/lean"),
    ))
    subprocess.run([str(lean), "-o", str(root / "Legacy.olean"), str(source)],
                   cwd=root, env=environment, check=True)
    output = subprocess.check_output([
        str(lean), "--run", str(SCRIPTS / "import_optimizer/legacy.lean"), "Legacy",
    ], cwd=root, env=environment, text=True)
    result = json.loads(output)
    assert result["module"] == "Legacy" and result["owned_declaration_count"] == 1, result
    assert result["suggestion_only"] is True and result["required_modules"], result
    print("PASS: pinned ImportGraph legacy helper analyzed a real compiled declaration")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", type=Path, default=shutil.which("lake"),
                        help="Lake executable for the repository's pinned toolchain")
    parser.add_argument("--import-graph", type=Path,
                        help="Also test legacy analysis using this prebuilt, pinned ImportGraph checkout")
    args = parser.parse_args()
    if args.lake is None:
        parser.error("Lake is required")
    with tempfile.TemporaryDirectory(prefix="import-optimizer-smoke-") as temporary:
        root = Path(temporary).resolve()
        smoke_test(args.lake.absolute(), root)
        if args.import_graph is not None:
            legacy_smoke_test(args.lake.absolute(), args.import_graph.resolve(), root)


if __name__ == "__main__":
    main()
