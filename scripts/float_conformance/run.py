#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
# Licensed under the LICENSE file in the root directory of this source tree.
"""Build and compare Lean core, MPFR and hardware without Lake or downloads."""
import argparse
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path

from compare import compare, require
from corpus import generate

SOURCE = Path(__file__).resolve().parent


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1048576), b""):
            h.update(block)
    return h.hexdigest()


def resolved_tool(name):
    # Preserve argv[0]: symlink names can select a multiplexed tool's behavior.
    # Opening this path for hashing still reads the target's actual bytes.
    path = Path(shutil.which(str(name)) or name).absolute()
    require(path.is_file() and os.access(path, os.X_OK), f"not executable: {path}")
    return str(path)


def verify_provenance(out, pins=None):
    if pins is None:
        pins = json.loads((out / "runtime-hashes.json").read_text())
    binding = json.loads((out / "tool-provenance.json").read_text())
    for command, role in (("emit_model", "lean"), ("link_model", "leanc"),
                          ("build_oracle", "cc")):
        receipt = json.loads((out / (command + ".result.json")).read_text())
        executable = binding[role]
        require(receipt["exit_code"] == 0 and receipt["argv"][0] == executable,
                f"{role}: compiler/command binding failed")
        require(pins.get(executable) == digest(executable),
                f"{role}: missing or wrong actual compiler hash")
    require(pins.get(str(out / "Model.c")) == digest(out / "Model.c"),
            "missing or wrong emitted model C hash")


def execute(out, name, argv):
    record = dict(name=name, argv=[str(x) for x in argv],
                  start_unix=time.time(), timeout_seconds=180)
    with (out / "commands.jsonl").open("a") as log:
        log.write(json.dumps(record) + "\n")
        log.flush()
        os.fsync(log.fileno())
    with (out / (name + ".stdout")).open("wb") as stdout, (
        out / (name + ".stderr")
    ).open("wb") as stderr:
        try:
            result = subprocess.run(record["argv"], stdout=stdout,
                                    stderr=stderr, timeout=180)
            record["exit_code"] = result.returncode
        except subprocess.TimeoutExpired:
            record["exit_code"] = 124
        except OSError as error:
            stderr.write((str(error) + "\n").encode())
            record["exit_code"] = 127
    record["elapsed_seconds"] = time.time() - record["start_unix"]
    (out / (name + ".result.json")).write_text(
        json.dumps(record, indent=2) + "\n")
    require(record["exit_code"] == 0,
            f"{name} exited {record['exit_code']}; see {out}")
    return (out / (name + ".stdout")).read_text()


def build(args, out):
    require(platform.system() == "Linux" and platform.machine() == "x86_64",
            "initial support is x86_64 Linux only")
    require(shutil.disk_usage(out).free >= 10 * 1024**3,
            "need at least 10 GiB free before building")
    with (out / "write-probe").open("wb") as stream:
        stream.write(b"float-conformance\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
    for name in ("tmp", "cache"):
        (out / name).mkdir()
    os.environ.update(TMPDIR=str(out / "tmp"),
                      XDG_CACHE_HOME=str(out / "cache"),
                      PYTHONDONTWRITEBYTECODE="1", OMP_NUM_THREADS="1")
    launcher = resolved_tool(args.lean)
    prefix = Path(execute(out, "lean_prefix", [launcher, "--print-prefix"]).strip()).resolve()
    lean = resolved_tool(prefix / "bin/lean")
    actual_prefix = execute(out, "actual_lean_prefix", [lean, "--print-prefix"]).strip()
    require(Path(actual_prefix).resolve() == prefix, "selected Lean prefix changed")
    leanc = resolved_tool(args.leanc or prefix / "bin/leanc")
    compiler = shlex.split(os.environ.get("CC", "cc"))
    require(bool(compiler), "empty CC")
    compiler[0] = resolved_tool(compiler[0])
    binding = dict(lean_launcher=launcher, lean=lean, leanc=leanc,
                   cc=compiler[0], prefix=str(prefix))
    binding["canonical_targets"] = {
        role: str(Path(binding[role]).resolve(strict=True))
        for role in ("lean_launcher", "lean", "leanc", "cc")}
    (out / "tool-provenance.json").write_text(json.dumps(binding, indent=2) + "\n")
    execute(out, "lean_version", [lean, "--version"])
    execute(out, "leanc_version", [leanc, "--version"])
    execute(out, "cc_version", compiler + ["--version"])
    flags = []
    for name in ("CPPFLAGS", "CFLAGS", "LDFLAGS"):
        flags += shlex.split(os.environ.get(name, ""))
    # These follow user flags so the numerical-safety settings cannot be lost.
    flags += ["-O2", "-g", "-std=c11", "-fno-fast-math", "-frounding-math",
              "-ffp-contract=off", "-mfpmath=sse", "-msse2", "-fno-lto",
              "-Wall", "-Wextra", "-Werror", "-MD", "-MF", str(out / "oracle.d")]
    execute(out, "build_oracle", compiler + flags
            + [str(SOURCE / "oracle.c"), "-o", str(out / "oracle")]
            + ["-lmpfr", "-lgmp", "-lm"])
    execute(out, "emit_model", [lean, "-j1", "-c", str(out / "Model.c"),
                               str(SOURCE / "Model.lean")])
    execute(out, "link_model", [leanc, "-O0", "-g", "-o", str(out / "model"),
                               str(out / "Model.c")])
    pins = {str(p): digest(p) for p in SOURCE.iterdir() if p.is_file()}
    pins[str(out / "Model.c")] = digest(out / "Model.c")
    pins[launcher] = digest(launcher)
    pins[str(Path(launcher).resolve(strict=True))] = pins[launcher]
    deps = (out / "oracle.d").read_text().replace("\\\n", " ").split(":", 1)[1]
    for name in shlex.split(deps):
        path = Path(name).resolve()
        pins[str(path)] = digest(path)
    for name, executable in (("oracle", out / "oracle"),
                             ("model", out / "model"),
                             ("lean", Path(lean)),
                             ("leanc", Path(leanc)),
                             ("cc", Path(compiler[0]))):
        pins[str(executable)] = digest(executable)
        pins[str(executable.resolve(strict=True))] = pins[str(executable)]
        linked = execute(out, name + "_libraries", ["ldd", str(executable)])
        for library in re.findall(r"(?:=> )?(/\S+) \(", linked):
            library = str(Path(library).resolve(strict=True))
            pins[library] = digest(library)
    (out / "runtime-hashes.json").write_text(json.dumps(pins, indent=2) + "\n")
    verify_provenance(out)


def run_dataset(out, count, name):
    dataset = out / name
    corpus = generate(count, dataset)
    execute(out, name + "_model", [out / "model", dataset / "inputs.txt"])
    execute(out, name + "_oracle", [out / "oracle", dataset / "inputs.txt"])
    # Full parser/comparator is shared with the independently exercised CLI.
    summary = compare(dataset / "inputs.txt", out / (name + "_model.stdout"),
                      out / (name + "_oracle.stdout"), count, dataset)
    return dict(corpus=corpus, comparison=summary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--leanc")
    parser.add_argument("--pairs", type=int, default=8192)
    args = parser.parse_args()
    out = args.out.resolve()
    try:
        require(8192 <= args.pairs <= 16384, "full corpus must be 8192..16384")
        out.mkdir(parents=True, exist_ok=False)
        build(args, out)
        smoke = run_dataset(out, 1, "smoke")
        full = run_dataset(out, args.pairs, "full")
        report = dict(status="pass", smoke=smoke, full=full,
                      scope="binary64 add/mul, RNE; NaN class only",
                      claim="finite conformance evidence, not proof",
                      cpu_affinity=sorted(os.sched_getaffinity(0)),
                      python=sys.version, python_optimized=sys.flags.optimize)
        (out / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    except (OSError, ValueError) as error:
        parser.exit(1, f"conformance failed: {error}\n")
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
