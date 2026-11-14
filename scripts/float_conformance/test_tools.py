#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Exercise executable-name dispatch and rejected tools in normal/-O Python."""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

from run import digest, execute, require, resolved_tool

KINDS = ("direct", "hardlink", "symlink", "missing", "nonexecutable")
CASE_NAMES = tuple(mode + "-" + role + "-" + kind
                   for mode in ("normal", "optimized")
                   for role in ("lean", "leanc", "cc") for kind in KINDS) + tuple(
    mode + "-real-" + kind for mode in ("normal", "optimized")
    for kind in ("direct", "hardlink", "symlink"))


def run_cases(out):
    out.mkdir(parents=True, exist_ok=False)
    fixture = out / "fixture"
    fixture.mkdir()
    dispatch = fixture / "dispatcher.py"
    dispatch.write_text("#!/usr/bin/env python3\nimport os,sys\n"
                        "name=os.path.basename(sys.argv[0])\nprint(name)\n"
                        "sys.exit(0 if name in ('lean','leanc','cc') else 73)\n")
    dispatch.chmod(0o755)
    tools = {}
    for role in ("lean", "leanc", "cc"):
        for kind in KINDS:
            directory = fixture / (role + "-" + kind)
            directory.mkdir()
            tool = directory / role
            if kind in ("direct", "nonexecutable"):
                shutil.copyfile(dispatch, tool)
                tool.chmod(0o755 if kind == "direct" else 0o644)
            elif kind == "hardlink":
                os.link(dispatch, tool)
            elif kind == "symlink":
                tool.symlink_to(dispatch)
            tools[role + "-" + kind] = (tool, "--version", 1 if kind in ("missing", "nonexecutable") else 0)
    launcher = shutil.which("lean")
    require(launcher is not None, "installed lean launcher required")
    prefix = execute(out, "discover_prefix", [launcher, "--print-prefix"]).strip()
    elan = shutil.which("elan")
    require(elan is not None, "installed elan required")
    copied_elan = fixture / "elan"
    shutil.copyfile(elan, copied_elan)
    copied_elan.chmod(0o755)
    require(digest(copied_elan) == digest(elan), "elan copy differs")
    tools["real-direct"] = (Path(prefix) / "bin/lean", "--print-prefix", 0)
    for kind in ("hardlink", "symlink"):
        directory = fixture / ("real-" + kind)
        directory.mkdir()
        tool = directory / "lean"
        if kind == "hardlink":
            os.link(copied_elan, tool)
            require(tool.stat().st_ino == copied_elan.stat().st_ino, "not a hard link")
        else:
            tool.symlink_to(Path(elan).absolute())
        tools["real-" + kind] = (tool, "--print-prefix", 0)
    outcomes = []
    for case_name in CASE_NAMES:
        mode, key = case_name.split("-", 1)
        tool, option, expected = tools[key]
        case = out / case_name
        argv = [sys.executable, "-B"] + (["-O"] if mode == "optimized" else []) + [
            str(Path(__file__).resolve()), "--invoke", str(tool), "--option=" + option,
            "--out", str(case)]
        rec = dict(case=case_name, argv=argv, expected_exit=expected, start_unix=time.time())
        with (out / "cases.jsonl").open("a") as log:
            log.write(json.dumps(rec) + "\n")
            log.flush()
            os.fsync(log.fileno())
        process = subprocess.run(argv, capture_output=True, timeout=30)
        (case / "stdout").write_bytes(process.stdout)
        (case / "stderr").write_bytes(process.stderr)
        rec.update(exit_code=process.returncode, elapsed_seconds=time.time()-rec["start_unix"])
        (case / "receipt.json").write_text(json.dumps(rec, indent=2) + "\n")
        if expected:
            require(b"tool check failed:" in process.stderr, "negative missed tool check")
        outcomes.append(rec)
    failures = [r["case"] for r in outcomes if r["exit_code"] != r["expected_exit"]]
    summary = dict(cases=len(outcomes), negative_cases=12, failures=failures, results=outcomes)
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    require(not failures, "tool dispatch failures: " + ", ".join(failures))
    print("36 tool dispatch cases passed, including 12 rejected tools")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--invoke", type=Path)
    parser.add_argument("--option", default="--version")
    args = parser.parse_args()
    try:
        if args.invoke:
            args.out.mkdir(parents=True, exist_ok=False)
            selected = resolved_tool(args.invoke)
            result = execute(args.out, "tool", [selected, args.option])
            require(Path(selected).name == args.invoke.name, "invoked basename changed")
            require(digest(selected) == digest(args.invoke), "selected tool bytes changed")
            (args.out / "selected.json").write_text(json.dumps(dict(
                invoked=str(args.invoke), selected=selected,
                canonical=str(args.invoke.resolve()), sha256=digest(selected), output=result), indent=2) + "\n")
        else:
            run_cases(args.out.resolve())
    except (OSError, ValueError) as error:
        parser.exit(1, f"tool check failed: {error}\n")


if __name__ == "__main__":
    main()
