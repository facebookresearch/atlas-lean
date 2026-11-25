#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Collect and validate bounded native call-path evidence for the smoke pair."""
import argparse
import json
import re
from pathlib import Path

from compare import require

SYMBOLS = {
    "hw_add": ("oracle", "hw_add"),
    "hw_mul": ("oracle", "hw_mul"),
    "oracle_pair": ("oracle", "oracle_pair"),
    "model_add": ("model", "l_Float_Model_add"),
    "model_mul": ("model", "l_Float_Model_mul"),
    "unpacked_add": ("model", "l_Float_Model_UnpackedFloat_add"),
    "unpacked_mul": ("model", "l_Float_Model_UnpackedFloat_mul"),
    "normalize": ("model", "l_Float_Model_UnpackedFloat_normalize"),
    "round_wrapper": ("model", "l_Float_Model_UnpackedFloat_round"),
    "round": ("model", "l_Float_Model_UnpackedFloat_roundWithAccuracy"),
}
COMMANDS = tuple("disasm_" + name for name in SYMBOLS) + ("trace_model", "trace_oracle")


def validate(dataset, out):
    from run import digest
    evidence = {}
    for name in COMMANDS:
        receipt = json.loads((out / (name + ".result.json")).read_text())
        require(type(receipt["exit_code"]) is int and receipt["exit_code"] == 0,
                "native evidence command failed: " + name)
        role = SYMBOLS[name[len("disasm_"):]][0] if name.startswith("disasm_") else name[len("trace_"):]
        argv = receipt["argv"]
        invoked = argv[-1] if name.startswith("disasm_") else argv[argv.index("--args") + 1]
        require(invoked == str(dataset / role), "native evidence binary binding failed")
    for role in ("model", "oracle"):
        text = (out / ("trace_" + role + ".stdout")).read_text()
        errors = (out / ("trace_" + role + ".stderr")).read_text()
        require(not re.search(r"Python Exception|Traceback \(most recent call last\)|Error in sourced command file",
                              text + errors), "native tracer reported an error")
        records = [line[len("FLOAT_TRACE "):] for line in text.splitlines()
                   if line.startswith("FLOAT_TRACE ")]
        require(len(records) == 1, "missing or duplicated native trace record")
        record = json.loads(records[0])
        require(record["role"] == role and record["exits"] == [0]
                and type(record["exits"][0]) is int, "bad native trace exit")
        counts = record["counts"]
        require(all(type(n) is int and n > 0 for n in counts.values()), "unhit native breakpoint")
        if role == "oracle":
            require(counts["oracle_pair"] == counts["hw_add"] == counts["hw_mul"] == 1,
                    "native smoke call count")
            require(counts["mpfr_init2"] == 3, "MPFR initialization count")
            for symbol in ("mpfr_add", "mpfr_mul"):
                require(record["callers"][symbol].get("oracle_pair") == 1,
                        "MPFR call did not come directly from oracle_pair")
            record["mpfr_mul_non_direct_entries"] = counts["mpfr_mul"] - 1
        else:
            require(counts["l_Float_Model_ofBits"] == 4, "model input decoding count")
            for symbol in ("l_Float_Model_add", "l_Float_Model_mul",
                           "l_Float_Model_UnpackedFloat_add", "l_Float_Model_UnpackedFloat_mul"):
                require(counts[symbol] == 1, "model smoke call count")
            require(counts["l_Float_Model_UnpackedFloat_roundWithAccuracy"] > 0,
                    "integer rounding not reached")
        rows = [line for line in text.splitlines() if re.fullmatch(r"\d+(?:\|\d+)+", line)]
        expected = (dataset / ("smoke_" + role + ".stdout")).read_text().splitlines()
        require(len(rows) == 1 and rows == expected, "trace output differs from populated smoke")
        for symbol in counts:
            require(record["first_frames"].get(symbol), "missing observed call stack")
        evidence[role] = record
    assembly = {}
    for name, (_, symbol) in SYMBOLS.items():
        text = (out / ("disasm_" + name + ".stdout")).read_text()
        require(re.search(r"^[0-9a-f]+ <" + re.escape(symbol) + r">:", text, re.M),
                "missing disassembly symbol: " + symbol)
        require(re.search(r"^\s*[0-9a-f]+:\s+\S+", text, re.M), "empty native instructions")
        assembly[name] = text
    for name, opcode in (("hw_add", "addsd"), ("hw_mul", "mulsd")):
        require(re.search(r"^\s*[0-9a-f]+:\s+v?" + opcode + r"\b", assembly[name], re.M),
                "missing hardware instruction: " + opcode)
    def calls(text, symbol):
        return re.search(r"\b(?:callq?|jmpq?)\s+[^\n]*<" + re.escape(symbol) + r"(?:@plt)?>", text)
    for symbol in ("mpfr_add", "mpfr_mul"):
        require(calls(assembly["oracle_pair"], symbol), "missing direct MPFR instruction")
    for op in ("add", "mul"):
        require(calls(assembly["model_" + op], "l_Float_Model_UnpackedFloat_" + op),
                "model does not call unpacked arithmetic")
        require(re.search(r"\b(?:callq?|jmpq?)\s+[^\n]*<lean_(?:nat|int)_", assembly["unpacked_" + op]),
                "unpacked arithmetic lacks integer runtime path")
    for caller, callee in (("unpacked_add", "normalize"), ("normalize", "round"),
                           ("round_wrapper", "roundWithAccuracy"),
                           ("unpacked_mul", "roundWithAccuracy")):
        require(calls(assembly[caller], "l_Float_Model_UnpackedFloat_" + callee),
                "unpacked arithmetic lacks explicit rounding path: " + caller)
    for name in ("model_add", "model_mul", "unpacked_add", "unpacked_mul", "normalize", "round_wrapper", "round"):
        require(not re.search(r"^\s*[0-9a-f]+:\s+v?(?:add|sub|mul|div)s[sd]\b", assembly[name], re.M),
                "hardware float arithmetic in selected core model instructions")
    return dict(status="pass", trace_pairs=1,
                input_sha256=digest(dataset / "smoke/inputs.bin"),
                binaries={role: digest(dataset / role) for role in ("model", "oracle")},
                evidence=evidence, scope="one populated smoke pair; not a full-corpus trace")


def collect(dataset, out, gdb="gdb", missing=False):
    from run import SOURCE, digest, execute, resolved_tool
    out.mkdir(parents=True, exist_ok=False)
    (out / "trace.gdb").write_bytes((SOURCE / "native_trace.gdb").read_bytes())
    for name, (role, symbol) in SYMBOLS.items():
        execute(out, "disasm_" + name,
                ["objdump", "-d", "--no-show-raw-insn", "--disassemble=" + symbol, dataset / role])
    for role in ("model", "oracle"):
        execute(out, "trace_" + role, [gdb, "-q", "-nx", "-batch",
                "-iex", "set auto-load off", "-iex", "set debuginfod enabled off",
                "-ex", "set $trace_oracle=" + str(int(role == "oracle")),
                "-ex", "set $trace_missing=" + str(int(missing)),
                "-x", out / "trace.gdb", "--args", dataset / role, dataset / "smoke/inputs.txt"])
    result = validate(dataset, out)
    result["tools"] = {tool: dict(path=resolved_tool(tool), sha256=digest(resolved_tool(tool)))
                       for tool in (gdb, "objdump")}
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("collect", "verify"))
    parser.add_argument("--dataset", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--gdb", default="gdb")
    parser.add_argument("--missing-breakpoint", action="store_true")
    args = parser.parse_args()
    try:
        result = (collect(args.dataset, args.out, args.gdb, args.missing_breakpoint)
                  if args.mode == "collect" else validate(args.dataset, args.out))
        print(json.dumps(result, sort_keys=True))
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"native paths failed: {error}\n")


if __name__ == "__main__":
    main()
