#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Real-process native-evidence and GMP metadata controls; never rebuild Lean."""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

from run import SOURCE, digest, execute, require
from native_paths import COMMANDS

KINDS = ("positive", "absent", "malformed", "missing_instruction", "wrong_caller",
         "failed_receipt", "missing_breakpoint", "missing_tracer", "tracer_failure",
         "gmp_matching", "gmp_mismatch")
CASE_NAMES = tuple(mode + "-" + kind for mode in ("normal", "optimized") for kind in KINDS)


def invoke(out, name, argv, expected):
    rec = dict(name=name, argv=[str(a) for a in argv], expected_exit=expected, start_unix=time.time())
    with (out / "commands.jsonl").open("a") as log:
        log.write(json.dumps(rec) + "\n")
        log.flush()
        os.fsync(log.fileno())
    process = subprocess.run(rec["argv"], capture_output=True, timeout=180)
    (out / (name + ".stdout")).write_bytes(process.stdout)
    (out / (name + ".stderr")).write_bytes(process.stderr)
    rec.update(exit_code=process.returncode, elapsed_seconds=time.time()-rec["start_unix"])
    (out / (name + ".result.json")).write_text(json.dumps(rec, indent=2) + "\n")
    require(process.returncode == expected, f"{name}: expected exit {expected}, got {process.returncode}")
    return rec, process


def run_tests(dataset, paths, out):
    out.mkdir(parents=True, exist_ok=False)
    # Find the real included GMP header, not a guessed architecture path.
    dependencies = (dataset / "oracle.d").read_text().replace("\\\n", " ").split(":", 1)[1].split()
    candidates = [Path(p) for p in dependencies if Path(p).is_file()
                  and re.search(r"#define\s+__GNU_MP_VERSION_PATCHLEVEL\s+\d+", Path(p).read_text())]
    require(len(candidates) == 1, "cannot identify the included GMP version header")
    header = candidates[0].read_text()
    altered, count = re.subn(r"(#define\s+__GNU_MP_VERSION_PATCHLEVEL\s+)(\d+)",
                            lambda m: m[1] + str(int(m[2]) + 91), header)
    require(count == 1, "GMP mutation must change exactly one macro")
    private = out / "gmp"
    private.mkdir()
    (private / "original.h").write_text(header)
    (private / "gmp.h").write_text(altered)
    build = json.loads((dataset / "build_oracle.result.json").read_text())["argv"]
    build = [build[0], "-I" + str(private)] + build[1:]
    build[build.index("-o") + 1] = str(private / "oracle")
    build[build.index("-MF") + 1] = str(private / "oracle.d")
    execute(out, "build_mismatched_oracle", build)
    require(str(private / "gmp.h") in (private / "oracle.d").read_text(), "mutated header was not used")
    versions = [int(re.search(r"#define\s+" + name + r"\s+(\d+)", altered)[1])
                for name in ("__GNU_MP_VERSION", "__GNU_MP_VERSION_MINOR", "__GNU_MP_VERSION_PATCHLEVEL")]
    matching = json.loads((dataset / "smoke_oracle.stderr").read_text())
    require(matching["gmp_header"] == matching["gmp_runtime"], "matching oracle version not recorded")
    metadata = dict(original_header=str(candidates[0]), original_sha256=digest(candidates[0]),
                    changed_header=".".join(map(str, versions)), runtime=matching["gmp_runtime"],
                    changed_sha256=digest(private / "gmp.h"), changed_lines=1)
    (private / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    outcomes = []
    for case_name in CASE_NAMES:
        mode, kind = case_name.split("-", 1)
        case = out / case_name
        case.mkdir()
        command = [sys.executable, "-B"] + (["-O"] if mode == "optimized" else [])
        expected = 0 if kind in ("positive", "gmp_matching") else 1
        if kind.startswith("gmp_"):
            oracle = dataset / "oracle" if kind == "gmp_matching" else private / "oracle"
            command += [str(Path(__file__).resolve()), "--oracle", str(oracle),
                        "--dataset", str(dataset), "--out", str(case)]
        else:
            target = case / "paths"
            collect = kind in ("missing_breakpoint", "missing_tracer", "tracer_failure")
            if not collect:
                target.mkdir()
                for name in COMMANDS:
                    for suffix in (".stdout", ".stderr", ".result.json"):
                        shutil.copyfile(paths / (name + suffix), target / (name + suffix))
                if kind in ("absent", "malformed", "wrong_caller"):
                    file = target / "trace_oracle.stdout"
                    text = file.read_text()
                    if kind == "absent":
                        text = "\n".join(s for s in text.splitlines() if not s.startswith("FLOAT_TRACE "))
                    elif kind == "malformed":
                        text = re.sub(r"(?m)^FLOAT_TRACE .*", "FLOAT_TRACE {broken", text)
                    else:
                        row = next(s for s in text.splitlines() if s.startswith("FLOAT_TRACE "))
                        data = json.loads(row[len("FLOAT_TRACE "):])
                        data["callers"]["mpfr_add"] = {"unrelated_caller": 1}
                        text = text.replace(row, "FLOAT_TRACE " + json.dumps(data))
                    file.write_text(text)
                if kind == "missing_instruction":
                    file = target / "disasm_hw_add.stdout"
                    file.write_text(re.sub(r"\bv?addsd\b", "nop", file.read_text()))
                if kind == "failed_receipt":
                    file = target / "trace_oracle.result.json"
                    data = json.loads(file.read_text()); data["exit_code"] = 17
                    file.write_text(json.dumps(data) + "\n")
            command += [str(SOURCE / "native_paths.py"), "collect" if collect else "verify",
                        "--dataset", str(dataset), "--out", str(target)]
            if kind == "missing_breakpoint":
                command.append("--missing-breakpoint")
            if kind == "missing_tracer":
                command += ["--gdb", str(case / "no-such-gdb")]
            if kind == "tracer_failure":
                fake = case / "failed-tracer"
                fake.write_text("#!/bin/sh\nexit 17\n"); fake.chmod(0o755)
                command += ["--gdb", str(fake)]
        rec, process = invoke(case, "check", command, expected)
        if expected:
            marker = b"GMP header/runtime version mismatch" if kind == "gmp_mismatch" else b"native paths failed:"
            require(marker in process.stderr, "negative missed intended guard")
        if kind == "gmp_mismatch":
            require(("header=" + metadata["changed_header"]).encode() in process.stderr
                    and ("runtime=" + metadata["runtime"]).encode() in process.stderr,
                    "mismatch versions not reported")
        outcomes.append(rec)
    (out / "summary.json").write_text(json.dumps(dict(cases=len(outcomes), negative_cases=18,
                                                       results=outcomes), indent=2) + "\n")
    print("22 native evidence/GMP cases passed, including 18 real failure exits")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", required=True, type=Path)
    parser.add_argument("--paths", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--oracle", type=Path)
    args = parser.parse_args()
    try:
        if args.oracle:
            # Preserve the native exit while recording its own complete receipt.
            argv = [str(args.oracle), str(args.dataset / "smoke/inputs.txt")]
            rec = dict(argv=argv, start_unix=time.time())
            (args.out / "oracle-command.json").write_text(json.dumps(rec, indent=2) + "\n")
            p = subprocess.run(argv, capture_output=True, timeout=30)
            (args.out / "oracle.stdout").write_bytes(p.stdout)
            (args.out / "oracle.stderr").write_bytes(p.stderr)
            rec.update(exit_code=p.returncode, elapsed_seconds=time.time()-rec["start_unix"])
            (args.out / "oracle.result.json").write_text(json.dumps(rec, indent=2) + "\n")
            sys.stdout.buffer.write(p.stdout); sys.stderr.buffer.write(p.stderr)
            raise SystemExit(p.returncode)
        run_tests(args.dataset, args.paths or args.dataset / "native-paths", args.out)
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"native controls failed: {error}\n")


if __name__ == "__main__":
    main()
