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
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from lean_changes import inert

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
PROBE = Path("MathlibExt/LintersSelfTestProbe.lean")
# A `module` file whose undecorated theorem is private, under a name that PROBE declares publicly.
PRIVATE_PROBE = Path("MathlibExt/LintersSelfTestPrivateProbe.lean")
PRIVATE_PROBE_TEXT = """\
module

/-! Probe module of scripts/linters_self_test.py, which deletes it again. -/

theorem lintersProbeCollision : 7 = 7 := rfl
"""
PROBES = (PROBE, PRIVATE_PROBE)
# The exceptions file of scripts/lint_declarations.lean (and runLinter). The probe commit adds
# entries, and the self-test puts the file back as it was. An entry names one declaration, so
# each of the two `lintersProbeCollision`s keeps the finding listed for the other.
NOLINTS = Path("scripts/nolints.json")
PROBE_NOLINTS = [["rootNamespace", "lintersProbeListed"],
                 ["synTaut", "lintersProbeCollision"],
                 ["duplicateStatement",
                  "_private.MathlibExt.LintersSelfTestPrivateProbe.0.lintersProbeCollision"]]

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

theorem lintersProbeAddComm (a b : Nat) : a + b = b + a := Nat.add_comm a b

alias lintersProbeAddCommAlias := lintersProbeAddComm

theorem lintersProbeIff (a b : Nat) : a + 0 = b ↔ a = b := by simp

alias ⟨lintersProbeIffMp, _⟩ := lintersProbeIff

theorem lintersProbeMpCopy (a b : Nat) (h : a + 0 = b) : a = b := (lintersProbeIff a b).mp h

universe u v

/-- A named proposition: its proofs have one statement. -/
def LintersProbeClaim : Prop := ∀ p : Nat, p + 0 = p

theorem lintersProbeClaimA : LintersProbeClaim := fun _ => rfl

theorem lintersProbeClaimB : LintersProbeClaim := fun _ => rfl

theorem lintersProbePairUV {{A : Type u}} {{B : Type v}} (a : A) (b : B) : (a, b) = (a, b) := rfl

theorem lintersProbePairVU {{A : Type v}} {{B : Type u}} (a : A) (b : B) : (a, b) = (a, b) := rfl

/-- A class of propositions, whose instances are theorems. -/
class LintersProbeFact (p : Prop) : Prop where
  out : p

instance lintersProbeInst : LintersProbeFact (2 = 2) := ⟨rfl⟩

theorem lintersProbeFact : LintersProbeFact (2 = 2) := ⟨rfl⟩

@[nolint docBlameThm]
theorem lintersProbeNoDocOk : 3 = 3 := rfl

theorem lintersProbeListed : 4 = 4 := rfl

-- The universe of `=` comes before the arguments of `Prod` that tell `u` from `v`.
theorem lintersProbeProdUV : @Prod.{{u, v}} = @Prod.{{u, v}} := rfl

theorem lintersProbeProdVU : @Prod.{{v, u}} = @Prod.{{v, u}} := lintersProbeProdUV.{{v, u}}

universe w x y

/-- Five universes, so that no limit on their number hides a swap. -/
def LintersProbeFive (A : Type u) (B : Type v) (C : Type w) (D : Type x) (E : Type y) :
    Type (max u v w x y) :=
  A × B × C × D × E

theorem lintersProbeFiveUV :
    @LintersProbeFive.{{u, v, w, x, y}} = @LintersProbeFive.{{u, v, w, x, y}} := rfl

theorem lintersProbeFiveVU :
    @LintersProbeFive.{{v, u, w, x, y}} = @LintersProbeFive.{{v, u, w, x, y}} :=
  lintersProbeFiveUV.{{v, u, w, x, y}}

theorem lintersProbeCollision : 7 = 7 := rfl
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
                              r"unusedArguments: lintersProbeUnused",
                              r"docBlameThm: lintersProbeLong theorem missing documentation",
                              r"explicitVarsOfIff: lintersProbeIff should be made implicit",
                              r"duplicateStatement: lintersProbeAddComm has the same statement as "
                              r"`Nat\.add_comm`",
                              r"rootNamespace: lintersProbeNoDoc is in the root namespace",
                              # Two proofs of a named proposition, and two statements that differ
                              # only in which universe is which.
                              r"duplicateStatement: lintersProbeClaimA has the same statement as "
                              r"`lintersProbeClaimB`",
                              r"duplicateStatement: lintersProbePairUV has the same statement as "
                              r"`lintersProbePairVU`",
                              # A theorem that restates an instance is reported.
                              r"duplicateStatement: lintersProbeFact has the same statement as "
                              r"`lintersProbeInst`",
                              # `@[nolint docBlameThm]` and the exceptions file each drop exactly
                              # one finding.
                              r"rootNamespace: lintersProbeNoDocOk is in the root namespace",
                              r"docBlameThm: lintersProbeListed theorem missing documentation",
                              r"duplicateStatement: lintersProbeProdUV has the same statement as "
                              r"`lintersProbeProdVU`",
                              r"duplicateStatement: lintersProbeFiveUV has the same statement as "
                              r"`lintersProbeFiveVU`",
                              # The `mp` theorem of an `alias ⟨_, _⟩` is compared.
                              r"duplicateStatement: lintersProbeMpCopy has the same statement as "
                              r"`lintersProbeIffMp`",
                              r"LintersSelfTestPrivateProbe\.lean:\d+:\d+: synTaut: "
                              r"lintersProbeCollision ",
                              r"LintersSelfTestProbe\.lean:\d+:\d+: duplicateStatement: "
                              r"lintersProbeCollision has the same statement"],
                             [r" 0 on declarations the change adds, [1-9]\d* on declarations it "
                              r"keeps", r"No environment-linter finding on the added declarations"]),
}
# Patterns that the output must not match after the first and the second commit.
ABSENT = {
    # An alias restates its target on purpose: it is neither reported nor shown as a match.
    "check_env_linters.py": ([r"duplicateStatement: lintersProbeAddCommAlias ",
                              r"same statement as [^\n]*`lintersProbeAddCommAlias`",
                              r"duplicateStatement: lintersProbeInst ",
                              r"docBlameThm: lintersProbeNoDocOk ",
                              r"rootNamespace: lintersProbeListed ",
                              r"LintersSelfTestProbe\.lean:\d+:\d+: synTaut: "
                              r"lintersProbeCollision ",
                              r"LintersSelfTestPrivateProbe\.lean:\d+:\d+: duplicateStatement: "
                              r"lintersProbeCollision "], []),
}
# Exit codes after the first and the second commit.
EXIT_CODES = (1, 0)
GIT = ["git", "-c", "user.name=linters self-test", "-c", "user.email=self-test@invalid"]


def git(*args: str) -> str:
    return subprocess.run([*GIT, *args], cwd=ROOT, check=True, capture_output=True,
                          text=True).stdout.strip()


def commit(text: str, message: str, nolints: list | None = None) -> str:
    """Commit the probe module, and the private probe and `nolints` as the exceptions file if
    `nolints` is given."""
    (ROOT / PROBE).write_text(text, encoding="utf-8")
    paths = [str(PROBE)]
    if nolints is not None:
        (ROOT / PRIVATE_PROBE).write_text(PRIVATE_PROBE_TEXT, encoding="utf-8")
        paths.append(str(PRIVATE_PROBE))
        (ROOT / NOLINTS).write_text(json.dumps(nolints, indent=2) + "\n", encoding="utf-8")
        paths.append(str(NOLINTS))
    git("add", "--", *paths)
    git("commit", "-q", "--no-verify", "-m", message, "--", *paths)
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
        unexpected = [pattern for pattern in ABSENT.get(script, ([], []))[round_]
                      if re.search(pattern, output)]
        if result.returncode != want_code or missing or unexpected:
            ok = False
            print(inert(f"FAIL {script} (round {round_ + 1}): exit {result.returncode}, wanted "
                        f"{want_code}; missing {missing}; unexpected {unexpected}\n{output}"))
        else:
            print(f"ok {script} (round {round_ + 1}): exit {result.returncode}")
    return ok


# Exceptions files that the driver must accept (exit 0) or reject (exit 2), as Lean decodes names.
NOLINTS_CASES = [
    ('[["duplicateStatement", "«foo bar».baz"], '
     '["synTaut", "_private.MathlibExt.Foo.0.bar"]]', 0),
    ('[["duplicateStatement", "Foo..bar"]]', 2),
    ('["rootNamespace"]', 2),
    ('{"rootNamespace": "Foo.bar"}', 2),
]


def check_nolints_decoder() -> bool:
    """Whether the driver's `--check-nolints`, which the workflow runs on a change to the file,
    accepts and rejects what Lean's decoder does."""
    ok = True
    with tempfile.TemporaryDirectory() as tmp:
        for number, (text, want) in enumerate(NOLINTS_CASES):
            path = Path(tmp, f"nolints-{number}.json")
            path.write_text(text + "\n", encoding="utf-8")
            result = subprocess.run(["lake", "env", "lean", "--run",
                                     str(SCRIPTS / "lint_declarations.lean"), "--check-nolints",
                                     str(path)],
                                    cwd=ROOT, capture_output=True, text=True, env=child_env())
            if result.returncode != want:
                ok = False
                print(inert(f"FAIL lint_declarations.lean --check-nolints on {text}: exit "
                            f"{result.returncode}, wanted {want}\n{result.stdout}"
                            f"{result.stderr}"))
            else:
                print(f"ok lint_declarations.lean --check-nolints on {text}: exit {want}")
    return ok


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--local", action="store_true",
                        help="run outside GitHub Actions (it commits and then moves HEAD back)")
    args = parser.parse_args()
    if os.environ.get("GITHUB_ACTIONS") != "true" and not args.local:
        parser.error("this commits to the checkout; pass --local to run it outside GitHub Actions")
    if any((ROOT / probe).exists() for probe in PROBES) or \
            git("diff", "--cached", "--name-only") or \
            git("status", "--porcelain", "--", str(NOLINTS)):
        print(f"A probe module exists, changes are staged or {NOLINTS} has local changes; "
              "not running.", file=sys.stderr)
        return 1
    start = git("rev-parse", "HEAD")
    had_nolints = (ROOT / NOLINTS).exists()
    nolints = json.loads((ROOT / NOLINTS).read_text()) if had_nolints else []
    try:
        first = commit(PROBE_TEXT, "linters self-test: probe module", nolints + PROBE_NOLINTS)
        ok = run_checks(start, 0)
        commit(DOCUMENTED, "linters self-test: document an existing declaration")
        ok = run_checks(first, 1) and ok
        ok = check_nolints_decoder() and ok
    finally:
        git("reset", "-q", "--soft", start)
        git("rm", "-q", "--cached", "--ignore-unmatch", "--", *map(str, PROBES))
        for probe in PROBES:
            (ROOT / probe).unlink(missing_ok=True)
        if had_nolints:
            git("checkout", start, "--", str(NOLINTS))
        else:
            git("rm", "-q", "--cached", "--ignore-unmatch", "--", str(NOLINTS))
            (ROOT / NOLINTS).unlink(missing_ok=True)
    print("The checks report what they should." if ok else "A check reported something else.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
