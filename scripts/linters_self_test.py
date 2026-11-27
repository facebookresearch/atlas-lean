#!/usr/bin/env python3
"""Run the linter checks end to end on a probe module, with Lean.

.github/workflows/linters.yml runs this when a pull request changes the checks
or the toolchain pins. It needs a checkout with the Mathlib cache fetched, and
for the unused-imports check a built agitate in $AGITATE_DIR (without one, that
check is skipped, and the script says so). It commits a probe module with known
findings on top of HEAD, builds it as CI does, runs each check against HEAD,
then commits a second change that only documents an existing probe declaration,
builds it and runs the checks against the first commit. It then moves HEAD back
and deletes the probe, leaving the working tree as it was.

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

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
PROBE = Path("MathlibExt/LintersSelfTestProbe.lean")

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

theorem lintersProbeSimpArg (a b : Nat) : a + b = b + a := by
  simp [Nat.add_comm, Nat.mul_comm]

theorem lintersProbeNew : True := trivial

@[deprecated lintersProbeNew (since := "2026-11-26")]
theorem lintersProbeOld : True := trivial

theorem lintersProbeUsesOld : True := lintersProbeOld
"""
# Only documents an existing declaration, whose unused argument stays.
DOCUMENTED = PROBE_TEXT.replace("def lintersProbeUnused",
                                "/-- Adds one to `n`. -/\ndef lintersProbeUnused")

# Each check, and patterns its output must match after the first and the second commit.
EXPECTED = {
    "check_syntax_linters.py": ([r"linter\.style\.longLine", r"linter\.style\.cdot",
                                 r"linter\.unusedSimpArgs",
                                 r"linter\.deprecated: `lintersProbeOld` has been deprecated"],
                                [r"No linter or deprecation warning on the added lines"]),
    "check_text_linters.py": ([r"space before a semicolon"],
                              [r"No text-lint error on the added lines"]),
    # The second commit's docstring starts the range of `lintersProbeUnused`, whose unused
    # argument runLinter still reports there; the check keeps it out.
    "check_env_linters.py": ([r"docBlame: lintersProbeNoDoc", r"unusedArguments: lintersProbeNoDoc",
                              r"unusedArguments: lintersProbeUnused"],
                             [r" 0 on declarations the change adds, [1-9]\d* on declarations it "
                              r"keeps", r"No environment-linter finding on the added declarations"]),
    # Nothing records that the probe needs Mathlib.Tactic.Ring for Mathlib's linters.
    "check_unused_imports.py": ([r"unused import[^:]*: agitate finds `import Mathlib\.Tactic\.Ring` "
                                 r"unused here"],
                                [r"No changed Lean file of the production libraries adds an import"]),
}
# Exit codes after the first and the second commit.
EXIT_CODES = (1, 0)
GIT = ["git", "-c", "user.name=linters self-test", "-c", "user.email=self-test@invalid"]


def git(*args: str) -> str:
    return subprocess.run([*GIT, *args], cwd=ROOT, check=True, capture_output=True,
                          text=True).stdout.strip()


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
    # Build first, as CI does, so that the checks read the build's replayed log, not a fresh one.
    build = subprocess.run([sys.executable, str(SCRIPTS / "lean_changes.py"), "build",
                            "--base", base],
                           cwd=ROOT, capture_output=True, text=True, env=child_env())
    if build.returncode != 0:
        print(f"FAIL lean_changes.py build (round {round_ + 1}): exit {build.returncode}\n"
              f"{build.stdout}{build.stderr}")
        return False
    ok = True
    for script, expected in EXPECTED.items():
        if script == "check_unused_imports.py" and not os.environ.get("AGITATE_DIR"):
            print(f"skipped {script} (round {round_ + 1}): AGITATE_DIR names no agitate build")
            continue
        result = subprocess.run([sys.executable, str(SCRIPTS / script), "--base", base],
                                cwd=ROOT, capture_output=True, text=True, env=child_env())
        output = result.stdout + result.stderr
        want_code = EXIT_CODES[round_]
        missing = [pattern for pattern in expected[round_] if not re.search(pattern, output)]
        if result.returncode != want_code or missing:
            ok = False
            print(f"FAIL {script} (round {round_ + 1}): exit {result.returncode}, wanted "
                  f"{want_code}; missing {missing}\n{output}")
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
    if (ROOT / PROBE).exists() or git("diff", "--cached", "--name-only"):
        print(f"{PROBE} exists or changes are staged; not running.", file=sys.stderr)
        return 1
    start = git("rev-parse", "HEAD")
    try:
        first = commit(PROBE_TEXT, "linters self-test: probe module")
        ok = run_checks(start, 0)
        commit(DOCUMENTED, "linters self-test: document an existing declaration")
        ok = run_checks(first, 1) and ok
    finally:
        git("reset", "-q", "--soft", start)
        git("rm", "-q", "--cached", "--ignore-unmatch", "--", str(PROBE))
        (ROOT / PROBE).unlink(missing_ok=True)
    print("The checks report what they should." if ok else "A check reported something else.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
