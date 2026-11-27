#!/usr/bin/env python3
"""Run the three linter checks end to end on a probe module, with Lean.

.github/workflows/linters.yml runs this when a pull request changes the checks
or the toolchain pins. It needs a checkout with the Mathlib cache fetched. It
commits a probe module with known findings on top of HEAD, runs each check
against HEAD, then commits a second change that only documents an existing probe
declaration and runs the checks against the first commit. It then moves HEAD
back and deletes the probe, leaving the working tree as it was.

    python3 scripts/linters_self_test.py      # in GitHub Actions, or with --local

Exit 0 if every check reports what it should, 1 otherwise.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

from lean_changes import inert

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
PROBE = Path("MathlibExt/LintersSelfTestProbe.lean")
# The files that the self-test creates, and deletes again.
PROBES = (PROBE,)

LONG = "a + b = b + a ∧ a * b = b * a ∧ a + 0 = a ∧ b + 0 = b ∧ a * 1 = a ∧ b * 1 = b"
PROBE_TEXT = f"""\
import Mathlib.Tactic.Ring

/-! Probe module of scripts/linters_self_test.py, which deletes it again. -/

theorem lintersProbeLong (a b : Nat) : {LONG} := by
  refine ⟨Nat.add_comm a b, Nat.mul_comm a b, ?_, ?_, ?_, ?_⟩
  ·
    simp
  · simp
  · simp
  · simp

theorem lintersProbeSemicolon : True := by trivial ; done

def lintersProbeNoDoc (n : Nat) (m : Nat) : Nat := n + 1

def lintersProbeUnused (n : Nat) (m : Nat) : Nat := n + 1
"""
# Only documents an existing declaration, whose unused argument stays.
DOCUMENTED = PROBE_TEXT.replace("def lintersProbeUnused",
                                "/-- Adds one to `n`. -/\ndef lintersProbeUnused")

# Each check, and patterns its output must match after the first and the second commit.
EXPECTED = {
    "check_syntax_linters.py": ([r"linter\.style\.longLine", r"linter\.style\.cdot"],
                                [r"No Mathlib linter warning on the added lines"]),
    "check_text_linters.py": ([r"space before a semicolon"],
                              [r"No text-lint error on the added lines"]),
    # The second commit's docstring starts the range of `lintersProbeUnused`, whose unused
    # argument runLinter still reports there; the check keeps it out.
    "check_env_linters.py": ([r"docBlame: lintersProbeNoDoc", r"unusedArguments: lintersProbeNoDoc",
                              r"unusedArguments: lintersProbeUnused"],
                             [r" 0 on declarations the change adds, [1-9]\d* on declarations it "
                              r"keeps", r"No environment-linter finding on the added declarations"]),
}
# Exit codes after the first and the second commit.
EXIT_CODES = (1, 0)
GIT = ["git", "-c", "user.name=linters self-test", "-c", "user.email=self-test@invalid"]


def git(*args: str) -> str:
    return subprocess.run([*GIT, *args], cwd=ROOT, check=True, capture_output=True,
                          text=True).stdout.strip()


def reserve(paths: tuple[Path, ...]) -> bool:
    """Create each of `paths`, empty and new, so that the probes never write through a file or
    a link already there; `False`, creating none, if one is there."""
    created: list[Path] = []
    for path in paths:
        try:
            (ROOT / path).open("x").close()
        except FileExistsError:
            for done in created:
                (ROOT / done).unlink()
            return False
        created.append(path)
    return True


def commit(text: str, message: str) -> str:
    (ROOT / PROBE).write_text(text, encoding="utf-8")
    git("add", "--", str(PROBE))
    git("commit", "-q", "--no-verify", "-m", message, "--", str(PROBE))
    return git("rev-parse", "HEAD")


def child_env() -> dict[str, str]:
    """The checks' environment: as outside GitHub Actions, so that the probe's findings annotate
    nothing and never reach the job's summary."""
    env = {key: value for key, value in os.environ.items() if key != "GITHUB_STEP_SUMMARY"}
    env["GITHUB_ACTIONS"] = "false"
    return env


def run_checks(base: str, round_: int) -> bool:
    ok = True
    for script, expected in EXPECTED.items():
        result = subprocess.run([sys.executable, str(SCRIPTS / script), "--base", base],
                                cwd=ROOT, capture_output=True, text=True, env=child_env())
        output = result.stdout + result.stderr
        want_code = EXIT_CODES[round_]
        missing = [pattern for pattern in expected[round_] if not re.search(pattern, output)]
        if result.returncode != want_code or missing:
            ok = False
            print(inert(f"FAIL {script} (round {round_ + 1}): exit {result.returncode}, wanted "
                        f"{want_code}; missing {missing}\n{output}"))
        else:
            print(f"ok {script} (round {round_ + 1}): exit {result.returncode}")
    return ok


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--local", action="store_true",
                        help="run outside GitHub Actions (it commits and then moves HEAD back)")
    args = parser.parse_args()
    if os.environ.get("GITHUB_ACTIONS") != "true" and not args.local:
        parser.error("this commits to the checkout; pass --local to run it outside GitHub Actions")
    if git("diff", "--cached", "--name-only"):
        print("Changes are staged; not running.", file=sys.stderr)
        return 1
    start = git("rev-parse", "HEAD")
    if not reserve(PROBES):
        print(f"A file or link is at {' or '.join(map(str, PROBES))}; not running.",
              file=sys.stderr)
        return 1
    try:
        first = commit(PROBE_TEXT, "linters self-test: probe module")
        ok = run_checks(start, 0)
        commit(DOCUMENTED, "linters self-test: document an existing declaration")
        ok = run_checks(first, 1) and ok
    finally:
        git("reset", "-q", "--soft", start)
        git("rm", "-q", "--cached", "--ignore-unmatch", "--", *map(str, PROBES))
        for probe in PROBES:
            (ROOT / probe).unlink(missing_ok=True)
    print("The checks report what they should." if ok else "A check reported something else.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
