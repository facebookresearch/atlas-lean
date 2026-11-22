#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Real-process controls on a populated corpus, including python -O regressions."""
import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    source = args.dataset
    originals = dict(inputs=(source / "full/inputs.txt").read_text(),
                     model=(source / "full_model.stdout").read_text(),
                     oracle=(source / "full_oracle.stdout").read_text())
    count = len(originals["inputs"].splitlines())
    check(count >= 8192, "controls require the full populated corpus")
    cases = [("positive", None, None, 0, 0)]
    model = [list(map(int, line.split("|")))
             for line in originals["model"].splitlines()]
    zero = next(i for i, row in enumerate(model)
                if row[1:3] == [0x8000000000000000, 0x3FF0000000000000])
    nan = next(i for i, row in enumerate(model)
               if row[1:3] == [0, 0x7FF8000000000042])
    check(model[zero][4] == 0x8000000000000000, "missing signed-zero anchor")
    check(model[0][3] == 0x3FF0000000000000, "missing even-tie anchor")
    check(model[nan][3] == 0x7FF8000000000000, "missing NaN anchor")
    for name, index, column, value, expected in (
        ("wrong_signed_zero", zero, 4, 0, 1),
        ("changed_finite", 0, 3, 0x3FF0000000000001, 1),
        ("wrong_nan_class", nan, 3, 0x7FF0000000000000, 1),
        ("nan_payload_allowed", nan, 3, 0xFFF8000000001234, 0),
    ):
        rows = [row[:] for row in model]
        rows[index][column] = value
        data = "".join("|".join(map(str, row)) + "\n" for row in rows)
        cases.append((name, "model", data, expected, expected))
    for stream, original in originals.items():
        lines = original.splitlines(keepends=True)
        separator = " " if stream == "inputs" else "|"
        invalid = lines[0].strip().split(separator)
        invalid[1] = str(2**64)
        variants = {
            "missing": "".join(lines[:-1]),
            "duplicate": "".join(lines + [lines[0]]),
            "malformed": "not a record\n" + "".join(lines[1:]),
            "out_of_range": separator.join(invalid) + "\n"
                            + "".join(lines[1:]),
            "empty": "",
        }
        for kind, data in variants.items():
            cases.append((stream + "_" + kind, stream, data, 1, None))
    outcomes = []
    for name, stream, data, expected, mismatches in cases:
        case = args.out / name
        case.mkdir()
        files = {}
        for key, original in originals.items():
            files[key] = case / (key + ".txt")
            files[key].write_text(data if key == stream else original)
        command = [sys.executable, "-B"]
        if sys.flags.optimize:
            command.append("-O")
        command += [str(Path(__file__).with_name("compare.py")),
                    "--expected-pairs", str(count), "--out", str(case / "result")]
        for key, path in files.items():
            command += ["--" + key, str(path)]
        record = dict(case=name, argv=command, expected_exit=expected,
                      start_unix=time.time(), pairs=count)
        with (args.out / "commands.jsonl").open("a") as log:
            log.write(json.dumps(record) + "\n")
            log.flush()
            os.fsync(log.fileno())
        result = subprocess.run(command, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=30)
        (case / "stdout").write_bytes(result.stdout)
        (case / "stderr").write_bytes(result.stderr)
        record.update(exit_code=result.returncode,
                      elapsed_seconds=time.time() - record["start_unix"])
        (case / "receipt.json").write_text(json.dumps(record, indent=2) + "\n")
        check(result.returncode == expected, f"{name}: wrong process exit")
        if expected:
            check(b"comparison failed:" in result.stderr,
                  f"{name}: did not reach comparator error path")
        if mismatches is not None:
            summary = json.loads((case / "result/summary.json").read_text())
            check(summary["operations"] == 2 * count,
                  f"{name}: comparison was not populated")
            check(summary["mismatches"] == mismatches,
                  f"{name}: wrong mismatch count")
        outcomes.append(record)
    summary = dict(cases=len(outcomes), positive_cases=2, negative_cases=18,
                   pairs_per_positive=count, optimized=sys.flags.optimize,
                   results=outcomes)
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "results"}))


if __name__ == "__main__":
    main()
