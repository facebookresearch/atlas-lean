#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Bind CI to a commit, check tool provenance, and select diagnostic evidence."""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

from run import SOURCE, digest, execute, require, verify_provenance
from test_tools import CASE_NAMES as TOOL_CASE_NAMES
from native_paths import COMMANDS as NATIVE_COMMANDS
from test_native_paths import CASE_NAMES as NATIVE_CASE_NAMES

SOURCES = ("Model.lean", "README.md", "compare.py", "corpus.py", "fixtures.json",
           "oracle.c", "run.py", "test_compare.py", "evidence.py", "test_tools.py",
           "native_paths.py", "native_trace.gdb", "test_native_paths.py")
DRIVER_COMMANDS = ("lean_prefix", "actual_lean_prefix", "lean_version", "leanc_version",
                   "cc_version", "build_oracle", "emit_model", "link_model",
                   "oracle_libraries", "model_libraries", "lean_libraries",
                   "leanc_libraries", "cc_libraries", "smoke_model", "smoke_oracle",
                   "full_model", "full_oracle")
CASES = ("positive", "wrong_signed_zero", "changed_finite", "wrong_nan_class",
         "nan_payload_allowed") + tuple(
    stream + "_" + kind for stream in ("inputs", "model", "oracle")
    for kind in ("missing", "duplicate", "malformed", "out_of_range", "empty"))


def package(root, out):
    """An exact filename allowlist also retains partially completed failed runs."""
    out.mkdir(parents=True, exist_ok=False)
    selected = {}

    def copy(src, name, required=False):
        if not src.exists():
            require(not required, f"missing required evidence: {src}")
            return
        require(src.is_file() and not src.is_symlink(), f"not a regular file: {src}")
        target = out / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, target)
        selected[name] = digest(target)

    def receipts(base, commands):
        copy(root / base / "commands.jsonl", base + "/commands.jsonl")
        for name in commands:
            for suffix in (".stdout", ".stderr", ".result.json"):
                rel = base + "/" + name + suffix
                copy(root / rel, rel)

    copy(root / "head.json", "head.json", required=True)
    for name in SOURCES:
        copy(SOURCE / name, "source/" + name, required=True)
    copy(SOURCE.parents[1] / ".github/workflows/float-conformance.yml",
         "source/float-conformance.yml", required=True)
    receipts(".", ("git_head", "tool_dispatch", "driver", "controls_normal",
                   "controls_optimized", "provenance", "native_controls"))
    receipts("run", DRIVER_COMMANDS)
    receipts("run/native-paths", NATIVE_COMMANDS)
    for name in ("trace.gdb", "result.json"):
        copy(root / "run/native-paths" / name, "run/native-paths/" + name)
    for name in ("result.json", "runtime-hashes.json", "tool-provenance.json",
                 "Model.c", "model", "oracle", "oracle.d"):
        copy(root / "run" / name, "run/" + name)
    for size in ("smoke", "full"):
        for name in ("inputs.bin", "inputs.txt", "inputs.jsonl", "corpus.json",
                     "rows.jsonl", "mismatches.jsonl", "summary.json"):
            rel = "run/" + size + "/" + name
            copy(root / rel, rel)
    for mode in ("normal", "optimized"):
        base = "controls-" + mode
        for name in ("commands.jsonl", "summary.json"):
            copy(root / base / name, base + "/" + name)
        for case in CASES:
            for name in ("inputs.txt", "model.txt", "oracle.txt", "stdout", "stderr",
                         "receipt.json", "result/rows.jsonl", "result/mismatches.jsonl",
                         "result/summary.json"):
                rel = base + "/" + case + "/" + name
                copy(root / rel, rel)
    receipts("tool-dispatch", ("discover_prefix",))
    for name in ("cases.jsonl", "summary.json", "fixture/dispatcher.py"):
        copy(root / "tool-dispatch" / name, "tool-dispatch/" + name)
    for case in TOOL_CASE_NAMES:
        base = "tool-dispatch/" + case
        receipts(base, ("tool",))
        for name in ("stdout", "stderr", "receipt.json", "selected.json"):
            copy(root / base / name, base + "/" + name)
    for name in ("commands.jsonl", "summary.json"):
        copy(root / "provenance" / name, "provenance/" + name)
    for mode in ("normal", "optimized"):
        for case in ("positive", "omitted", "wrong"):
            base = "provenance/" + mode + "-" + case
            for name in ("pins.json", "stdout", "stderr", "receipt.json"):
                copy(root / base / name, base + "/" + name)
    receipts("native-controls", ("build_mismatched_oracle",))
    for name in ("summary.json", "gmp/original.h", "gmp/gmp.h", "gmp/oracle",
                 "gmp/oracle.d", "gmp/metadata.json"):
        copy(root / "native-controls" / name, "native-controls/" + name)
    for case in NATIVE_CASE_NAMES:
        base = "native-controls/" + case
        receipts(base, ("check",))
        receipts(base + "/paths", NATIVE_COMMANDS)
        for name in ("paths/trace.gdb", "paths/result.json", "failed-tracer",
                     "oracle-command.json", "oracle.stdout", "oracle.stderr", "oracle.result.json"):
            copy(root / base / name, base + "/" + name)
    record = dict(files=len(selected), bytes=sum((out / n).stat().st_size for n in selected),
                  full_result_present="run/result.json" in selected,
                  selection="explicit filenames; no tmp/cache/environment/private data",
                  sha256=selected)
    (out / "selection.json").write_text(json.dumps(record, indent=2) + "\n")
    (out / "SHA256SUMS").write_text("".join(
        value + "  " + name + "\n" for name, value in sorted(selected.items())))
    require(record["files"] >= 11 and record["bytes"] > 0, "empty evidence package")
    return record


def test_provenance(dataset, out):
    out.mkdir(parents=True, exist_ok=False)
    pins = json.loads((dataset / "runtime-hashes.json").read_text())
    binding = json.loads((dataset / "tool-provenance.json").read_text())
    compiler = binding["lean"]
    require(compiler != binding["lean_launcher"], "test requires default elan launcher")
    require(pins.get(compiler) == digest(compiler), "actual compiler not pinned")
    outcomes = []
    for optimized in (False, True):
        for name, expected in (("positive", 0), ("omitted", 1), ("wrong", 1)):
            case = out / (("optimized-" if optimized else "normal-") + name)
            case.mkdir()
            mutant = dict(pins)
            if name == "omitted":
                del mutant[compiler]
            if name == "wrong":
                mutant[compiler] = "0" * 64
            (case / "pins.json").write_text(json.dumps(mutant, indent=2) + "\n")
            argv = [sys.executable, "-B"] + (["-O"] if optimized else []) + [
                str(Path(__file__).resolve()), "verify", "--dataset", str(dataset),
                "--pins", str(case / "pins.json")]
            receipt = dict(argv=argv, expected_exit=expected, start_unix=time.time())
            with (out / "commands.jsonl").open("a") as log:
                log.write(json.dumps(receipt) + "\n")
                log.flush()
                os.fsync(log.fileno())
            result = subprocess.run(argv, capture_output=True, timeout=30)
            (case / "stdout").write_bytes(result.stdout)
            (case / "stderr").write_bytes(result.stderr)
            receipt.update(exit_code=result.returncode, elapsed_seconds=time.time()-receipt["start_unix"])
            (case / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            require(result.returncode == expected, f"{case.name}: incorrect exit")
            if expected:
                require(b"missing or wrong actual compiler hash" in result.stderr,
                        "negative control missed provenance gate")
            outcomes.append(receipt)
    (out / "summary.json").write_text(json.dumps(dict(cases=6, results=outcomes), indent=2) + "\n")
    print("6 provenance cases passed; omitted/wrong compiler hashes fail in both modes")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("head", "ci", "package", "verify", "test"))
    parser.add_argument("--out", type=Path)
    parser.add_argument("--root", type=Path)
    parser.add_argument("--dataset", type=Path)
    parser.add_argument("--pins", type=Path)
    parser.add_argument("--expected")
    args = parser.parse_args()
    try:
        if args.mode == "head":
            require(args.out is not None and args.expected is not None, "head requires out/expected")
            args.out.mkdir(parents=True, exist_ok=False)
            os.environ.update(GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="file",
                              GIT_OPTIONAL_LOCKS="0", GIT_NO_REPLACE_OBJECTS="1")
            actual = execute(args.out, "git_head", ["git", "rev-parse", "HEAD"]).strip()
            record = dict(expected=args.expected, actual=actual, matches=actual == args.expected,
                          run_id=os.environ.get("GITHUB_RUN_ID"),
                          run_attempt=os.environ.get("GITHUB_RUN_ATTEMPT"))
            (args.out / "head.json").write_text(json.dumps(record, indent=2) + "\n")
            require(re.fullmatch(r"[0-9a-f]{40}", args.expected) and actual == args.expected,
                    "checked-out HEAD does not match requested commit")
        elif args.mode == "ci":
            require(args.out is not None, "ci requires out")
            head = json.loads((args.out / "head.json").read_text())
            require(head["matches"], "HEAD was not verified")
            execute(args.out, "tool_dispatch", [sys.executable, "-B", SOURCE / "test_tools.py",
                                               "--out", args.out / "tool-dispatch"])
            execute(args.out, "driver", [sys.executable, "-B", SOURCE / "run.py",
                                        "--out", args.out / "run"])
            for mode in ("normal", "optimized"):
                execute(args.out, "controls_" + mode,
                        [sys.executable, "-B"] + (["-O"] if mode == "optimized" else [])
                        + [SOURCE / "test_compare.py", "--dataset", args.out / "run",
                           "--out", args.out / ("controls-" + mode)])
            execute(args.out, "provenance", [sys.executable, "-B", SOURCE / "evidence.py",
                                            "test", "--dataset", args.out / "run",
                                            "--out", args.out / "provenance"])
            execute(args.out, "native_controls", [sys.executable, "-B", SOURCE / "test_native_paths.py",
                                                  "--dataset", args.out / "run",
                                                  "--out", args.out / "native-controls"])
        elif args.mode == "package":
            require(args.root is not None and args.out is not None, "package requires root/out")
            result = package(args.root, args.out)
            print(json.dumps({k: v for k, v in result.items() if k != "sha256"}))
        elif args.mode == "test":
            require(args.dataset is not None and args.out is not None, "test requires dataset/out")
            test_provenance(args.dataset, args.out)
        else:
            require(args.dataset is not None, "verify requires dataset")
            pins = json.loads(args.pins.read_text()) if args.pins else None
            verify_provenance(args.dataset, pins)
            print("compiler provenance verified")
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"evidence failed: {error}\n")


if __name__ == "__main__":
    main()
