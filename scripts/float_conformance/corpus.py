# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Deterministic distinct binary64 pairs, with explicit fixture provenance."""
import hashlib
import json
import struct
from collections import Counter
from pathlib import Path


def generate(count, out):
    if count != 1 and not 8192 <= count <= 16384:
        raise ValueError("use 1 for smoke, or 8192..16384 distinct pairs")
    rows, seen, duplicates = [], set(), Counter()

    def add(a, b, group, label):
        if (a, b) in seen:
            duplicates[group] += 1
            return
        seen.add((a, b))
        rows.append(dict(index=len(rows), a=a, b=b, group=group, label=label))

    # First pair is the halfway tie 1 + 2^-53, even significand rounds down.
    add(0x3FF0000000000000, 0x3CA0000000000000, "tie", "even_down")
    if count > 1:
        fixtures = json.loads(Path(__file__).with_name("fixtures.json")
                              .read_text())
        for row in fixtures:
            add(int(row["a"], 16), int(row["b"], 16), "F1", row["label"])
        edges = [0, 0x8000000000000000, 1, 0x8000000000000001,
                 0x000FFFFFFFFFFFFF, 0x800FFFFFFFFFFFFF,
                 0x0010000000000000, 0x8010000000000000,
                 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF,
                 0x7FF0000000000000, 0xFFF0000000000000,
                 0x7FF8000000000042, 0xFFF0000000000001,
                 0x3FF0000000000000, 0xBFF0000000000000]
        for i, a in enumerate(edges):
            for j, b in enumerate(edges):
                add(a, b, "edge_grid", f"{i}_{j}")
        for sign in (0, 1 << 63):
            for parity in (0, 1):
                add(0x3FF0000000000000 + parity + sign,
                    0x3CA0000000000000 + sign, "tie", "add_parity_sign")
                add(0x3FF8000000000000 + sign,
                    0x3FF0000000000001 + 2 * parity, "tie", "mul_parity")
            for offset in (-1, 0, 1):
                add(1 + sign, 0x3FE0000000000000 + offset,
                    "boundary", "underflow_neighbor")
                add(0x7FEFFFFFFFFFFFFF + sign,
                    0x7C90000000000000 + offset + sign,
                    "boundary", "overflow_neighbor")
            add(3 + sign, 0x3FE0000000000000, "boundary", "underflow_up")
        state = 0xF22580254761
        mask = (1 << 64) - 1

        def word():
            nonlocal state
            state = (state + 0x9E3779B97F4A7C15) & mask
            z = state
            z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & mask
            z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & mask
            return z ^ (z >> 31)

        for i in range(4096):
            add(word(), word(), "random", str(i))
        while len(rows) < count:
            a = word()
            exponent = max(0, min(2046, ((a >> 52) & 2047)
                                  + word() % 5 - 2))
            b = (word() & 0x800FFFFFFFFFFFFF) | (exponent << 52)
            add(a, b, "near_exponent", str(len(rows)))
    if len(rows) != count or len(seen) != count:
        raise ValueError("wrong distinct corpus size")
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    raw = b"".join(struct.pack(">QQ", r["a"], r["b"]) for r in rows)
    (out / "inputs.bin").write_bytes(raw)
    (out / "inputs.txt").write_text("".join(
        f"{r['index']} {r['a']} {r['b']}\n" for r in rows))
    (out / "inputs.jsonl").write_text("".join(json.dumps(
        dict(r, a=f"{r['a']:016x}", b=f"{r['b']:016x}"), sort_keys=True)
        + "\n" for r in rows))
    summary = dict(pairs=count, distinct_pairs=len(seen), emitted_duplicates=0,
                   suppressed_duplicates=dict(duplicates),
                   groups=dict(Counter(r["group"] for r in rows)),
                   seed="0xF22580254761", binary_encoding="big-endian QQ",
                   input_sha256=hashlib.sha256(raw).hexdigest())
    (out / "corpus.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary
