#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Fail-closed binary64 result comparison; all checks survive python -O."""
import argparse
import json
import re
from pathlib import Path

LIMIT = 16384
U64 = 2**64


def require(condition, message):
    if not condition:
        raise ValueError(message)


def records(path, columns, separator, count):
    rows = []
    with Path(path).open(encoding="ascii") as source:
        for line in source:
            require(len(rows) < count, f"{path}: extra or duplicate row")
            require(len(line) <= 512, f"{path}: oversized row")
            fields = line.rstrip("\n").split(separator)
            require(len(fields) == columns, f"{path}: malformed row")
            require(all(re.fullmatch(r"[0-9]+", x) for x in fields),
                    f"{path}: invalid unsigned integer")
            row = tuple(int(x) for x in fields)
            require(all(x < U64 for x in row), f"{path}: out of range")
            require(row[0] == len(rows), f"{path}: wrong/duplicate index")
            rows.append(row)
    require(len(rows) == count, f"{path}: missing or empty records")
    return rows


def is_nan(bits):
    return bits & 0x7FF0000000000000 == 0x7FF0000000000000 and bool(
        bits & 0xFFFFFFFFFFFFF)


def same(left, right):
    return left == right or (is_nan(left) and is_nan(right))


def output_class(bits):
    exponent = (bits >> 52) & 2047
    fraction = bits & 0xFFFFFFFFFFFFF
    if exponent == 2047:
        return "nan" if fraction else "infinity"
    if exponent:
        return "normal"
    if fraction:
        return "subnormal"
    return "negative_zero" if bits >> 63 else "positive_zero"


def compare(inputs, model, oracle, count, out):
    require(1 <= count <= LIMIT, "invalid expected pair count")
    expected = records(inputs, 3, " ", count)
    require(len({r[1:] for r in expected}) == count, "duplicate input pair")
    models = records(model, 5, "|", count)
    oracles = records(oracle, 7, "|", count)
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    mismatches = 0
    classes = {op: {} for op in ("add", "mul")}
    with (out / "rows.jsonl").open("w") as joined, (
        out / "mismatches.jsonl"
    ).open("w") as bad:
        for inp, md, oc in zip(expected, models, oracles):
            require(md[:3] == inp and oc[:3] == inp,
                    f"operand identity mismatch at index {inp[0]}")
            for offset, op in enumerate(("add", "mul")):
                m, p, h = md[3 + offset], oc[3 + offset], oc[5 + offset]
                match = same(m, p) and same(m, h) and same(p, h)
                row = dict(index=inp[0], op=op, a=f"{inp[1]:016x}",
                           b=f"{inp[2]:016x}", model=f"{m:016x}",
                           mpfr=f"{p:016x}", hardware=f"{h:016x}",
                           match=match)
                encoded = json.dumps(row, sort_keys=True) + "\n"
                joined.write(encoded)
                name = output_class(m)
                classes[op][name] = classes[op].get(name, 0) + 1
                if not match:
                    bad.write(encoded)
                    mismatches += 1
    summary = dict(pairs=count, operations=2 * count,
                   pairwise_comparisons=6 * count, mismatches=mismatches,
                   output_classes=classes, nan_policy="class only")
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    require(mismatches == 0, f"{mismatches} mismatching operations")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("inputs", "model", "oracle", "out"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--expected-pairs", required=True, type=int)
    args = parser.parse_args()
    try:
        result = compare(args.inputs, args.model, args.oracle,
                         args.expected_pairs, args.out)
    except (OSError, UnicodeError, ValueError) as error:
        parser.exit(1, f"comparison failed: {error}\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
