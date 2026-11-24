#!/usr/bin/env python3
"""Keep .github/workflows/bump-cache.yml in step with ci.yml's build job.

bump-cache.yml warms ci.yml's build cache for a Lean/Mathlib bump: it builds a
bump's head and saves .lake/build where ci.yml's restore step finds it. That
only helps while the two agree on the cache path, the key prefix and what the
build runs. It is only safe while the workflow stays dispatch-only and
read-only, passes its inputs to scripts through the environment, and keeps its
partial builds out of ci.yml's key space. The build step itself runs here with
stand-ins for `lake`, `timeout` and `scripts/check.sh`, under `bash -e` as
GitHub runs it, to check the order of the commands and the status it reports.

Run with: python3 -m unittest discover -s scripts -p test_bump_cache_workflow.py
"""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
import textwrap
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WORKFLOWS = ROOT / ".github" / "workflows"
CI = WORKFLOWS / "ci.yml"
WARM = WORKFLOWS / "bump-cache.yml"

HASH = "${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}"
CI_PREFIX = "lake-build-${{ runner.os }}-" + HASH + "-"
HEAVY = re.compile(r"for module in \\\n((?:[ \t]+[A-Za-z0-9_.']+ \\\n)*[ \t]+[A-Za-z0-9_.']+); do")


def heavy_modules(text: str) -> list[list[str]]:
    """Each `for module in ...; do` list of memory-heavy modules, in order."""
    return [[line.strip().rstrip("\\").strip() for line in match.group(1).splitlines()]
            for match in HEAVY.finditer(text)]


def top_level_block(lines: list[str], key: str) -> list[str]:
    """The lines nested under the top-level `key:`, or [] when it is absent."""
    for index, line in enumerate(lines):
        if re.match(re.escape(key) + r":(\s.*)?$", line):
            body = []
            for nested in lines[index + 1:]:
                if nested.strip() and not nested.startswith((" ", "#")):
                    break
                body.append(nested)
            return body
    return []


def step(text: str, marker: str) -> str:
    """The text of the step whose first line contains `marker`, up to the next step."""
    start = text.index(marker)
    start = text.rindex("\n      - ", 0, start) + 1
    end = text.find("\n      - ", start + 1)
    return text[start:end if end != -1 else len(text)]


def job(text: str, name: str) -> str:
    """The text of the job `name`, up to the next job."""
    start = text.index(f"\n  {name}:\n") + 1
    following = re.search(r"(?m)^  [A-Za-z0-9_-]+:$", text[start + 1:])
    return text[start:start + 1 + following.start()] if following else text[start:]


def block_lines(text: str, key: str) -> list[str]:
    """The stripped lines of the block scalar `key: |` in `text`."""
    head, body = text.split(f"{key}: |\n", 1)
    indent = len(head.rsplit("\n", 1)[-1]) + 2
    lines = []
    for line in body.splitlines():
        if not line.startswith(" " * indent):
            break
        lines.append(line.strip())
    return lines


def run_blocks(lines: list[str]) -> list[str]:
    """The text of every `run:` script, inline or block."""
    scripts = []
    for index, line in enumerate(lines):
        match = re.match(r"(\s*)(?:- )?run:\s*(.*)$", line)
        if not match:
            continue
        indent, rest = len(match.group(1)), match.group(2)
        if rest not in ("|", ">", "|-", ">-"):
            scripts.append(rest)
            continue
        body = []
        for nested in lines[index + 1:]:
            if nested.strip() and len(nested) - len(nested.lstrip()) <= indent:
                break
            body.append(nested)
        scripts.append("\n".join(body))
    return scripts


class BumpCacheWorkflowTest(unittest.TestCase):
    def setUp(self) -> None:
        self.ci = CI.read_text(encoding="utf-8")
        self.warm = WARM.read_text(encoding="utf-8")
        self.warm_lines = self.warm.splitlines()

    def test_dispatch_only(self) -> None:
        on = top_level_block(self.warm_lines, "on")
        events = [m.group(1) for m in (re.match(r"  ([a-z_]+):", line) for line in on) if m]
        self.assertEqual(events, ["workflow_dispatch"],
                         "bump-cache.yml saves a cache main's builds restore: only a maintainer's dispatch may run it")

    def test_read_only_token(self) -> None:
        permissions = top_level_block(self.warm_lines, "permissions")
        granted = dict(re.findall(r"^  ([a-z-]+): (\S+)", "\n".join(permissions), re.M))
        self.assertEqual(granted, {"contents": "read", "pull-requests": "read"})
        self.assertIsNone(re.search(r"(?m)^[ \t]+permissions:", self.warm), "no job may widen the token")

    def test_inputs_reach_scripts_only_through_the_environment(self) -> None:
        for script in run_blocks(self.warm_lines):
            self.assertNotIn("${{", script, f"interpolated expression in a run script:\n{script}")

    def test_large_runner_builds_the_heavy_modules_with_the_rest(self) -> None:
        # ci.yml builds its memory-heavy modules one at a time on the 16 GB standard
        # runner; the warm-up's 64-core runner has the memory to build them with the rest.
        build, warm = job(self.ci, "build"), job(self.warm, "warm")
        self.assertEqual(len(heavy_modules(build)), 1, "ci.yml's build job moved its memory-heavy list; update this test")
        self.assertIn("    runs-on: ubuntu-24.04\n", build, "ci.yml's build job left the standard runner")
        self.assertIn("    runs-on: 64-core-ubuntu\n", warm)
        self.assertEqual(heavy_modules(self.warm), [], "a serial heavy step leaves the 64-core runner idle")
        self.assertNotIn("swapon", self.warm)

    def test_ci_restores_what_the_warm_up_saves(self) -> None:
        restore = step(self.ci, "name: Restore local build")
        self.assertIn("path: .lake/build", restore)
        fallback = block_lines(restore, "restore-keys")
        self.assertIn(CI_PREFIX, fallback, "ci.yml no longer falls back to lake-build-<os>-<pins>-; update bump-cache.yml")
        key = step(self.warm, "name: Name the cache entries")
        self.assertIn(f"NEW_PINS: {HASH}", key)
        self.assertIn("OS: ${{ runner.os }}", key)
        self.assertIn('prefix="lake-build-${OS}-${NEW_PINS}-"', key)
        self.assertIn('echo "complete=${prefix}${HEAD_SHA}"', key)
        checkpoints = re.search(r'checkpoints="([^"]+)"', key).group(1)
        self.assertFalse(checkpoints.startswith("lake-build-"), "checkpoints must stay out of ci.yml's key space")
        for marker in ("name: Restore an earlier build", "name: Save the build", "name: Confirm the save"):
            self.assertIn("path: .lake/build", step(self.warm, marker), marker)

    def test_only_a_checked_build_gets_cis_key(self) -> None:
        chosen = ("key: ${{ steps.build.outputs.status == 'ok' && steps.key.outputs.complete"
                  " || steps.key.outputs.checkpoint }}")
        self.assertIn(chosen, step(self.warm, "name: Save the build"))
        self.assertIn(chosen, step(self.warm, "name: Confirm the save"), "confirm the key that was saved")
        self.assertIn("lookup-only: true", step(self.warm, "name: Confirm the save"))
        restore = step(self.warm, "name: Restore an earlier build")
        self.assertIn("key: ${{ steps.key.outputs.complete }}", restore)
        self.assertEqual(block_lines(restore, "restore-keys"),
                         ["${{ steps.key.outputs.checkpoints }}", "${{ steps.key.outputs.prefix }}"])

    def test_same_build_command_as_ci(self) -> None:
        self.assertIn("run: scripts/check.sh build", step(self.ci, "name: Build extension libraries"))
        build = step(self.warm, "name: Build and check the head")
        self.assertIn("run_until_deadline scripts/check.sh build", build)

    def test_checks_before_checkout(self) -> None:
        order = [self.warm.index(m) for m in (
            "name: Check the pull request and its head", "uses: actions/checkout@",
            "name: Compare the head with main", "name: Run main's bump guard on the head",
            "name: Name the cache entries", "name: Build and check the head")]
        self.assertEqual(order, sorted(order))

    def test_runs_mains_guard_on_three_trees(self) -> None:
        guard = step(self.warm, "name: Run main's bump guard on the head")
        self.assertIn('git show "${MAIN_SHA}:scripts/bump/${file}" > "${guard}/main/scripts/bump/${file}"', guard)
        self.assertIn("for file in pinned_bump.py pinned_deps.json; do", guard)
        self.assertIn('trees=("base:${MAIN_SHA}" "merge-base:${merge_base}" "pr:${HEAD_SHA}")', guard)
        self.assertIn('diff --no-renames --name-only "$merge_base" "$HEAD_SHA"', guard)
        self.assertIn('cd "${guard}/main"\n', guard)
        self.assertIn('python3 scripts/bump/pinned_bump.py guard --base "${guard}/base" --merge-base "${guard}/merge-base"',
                      guard)
        # The same files as the Bump guard workflow reads.
        guard_workflow = (WORKFLOWS / "bump-guard.yml").read_text(encoding="utf-8")
        self.assertIn("for file in lean-toolchain lakefile.toml lake-manifest.json; do", guard_workflow)
        self.assertIn("for file in lean-toolchain lakefile.toml lake-manifest.json; do", guard)
        for kind in ("policy", "doc", "ledger"):
            self.assertIn(f"config_paths {kind})", guard_workflow)
        self.assertIn("for kind in policy doc ledger; do", guard)


class BuildStepTest(unittest.TestCase):
    """Run the workflow's build step with stand-ins, under `bash -e` as GitHub does."""

    def setUp(self) -> None:
        text = WARM.read_text(encoding="utf-8")
        body = step(text, "name: Build and check the head")
        self.script = textwrap.dedent(body.split("run: |\n", 1)[1])
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        (self.dir / "bin").mkdir()
        (self.dir / "scripts").mkdir()
        self.log = self.dir / "calls.log"
        stubs = {
            # timeout [options] DURATION COMMAND...: log, then fake a timeout or run COMMAND.
            "bin/timeout": 'echo "timeout $*" >> "$LOG"\n'
                           'while [[ "$1" == -* ]]; do shift; done; shift\n'
                           'if [ -n "${FAKE_RC:-}" ] && [[ "$*" == *"$FAKE_ON"* ]]; then exit "$FAKE_RC"; fi\n'
                           'exec "$@"\n',
            "bin/lake": 'echo "lake $*" >> "$LOG"\n[ "$*" != "build ${LAKE_FAILS:-none}" ]\n',
            "scripts/check.sh": 'echo "check.sh $*" >> "$LOG"\nexit "${CHECK_RC:-0}"\n',
        }
        for name, body in stubs.items():
            path = self.dir / name
            path.write_text("#!/usr/bin/env bash\n" + body)
            path.chmod(0o755)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def run_step(self, started_ago: int = 0, **env: str) -> tuple[str, list[str]]:
        output = self.dir / "github_output"
        output.write_text("")
        self.log.write_text("")
        environment = dict(os.environ, START=str(int(time.time()) - started_ago), GITHUB_OUTPUT=str(output),
                           LOG=str(self.log), PATH=f"{self.dir / 'bin'}:{os.environ['PATH']}", **env)
        proc = subprocess.run(["bash", "-e", "-c", self.script], cwd=self.dir, env=environment,
                              capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        status = re.findall(r"^status=(\w+)$", output.read_text(), re.M)
        self.assertEqual(len(status), 1, output.read_text())
        # timeout --signal=TERM --kill-after=5m <minutes>m COMMAND...
        calls = [line.split(" ", 4)[4] for line in self.log.read_text().splitlines() if line.startswith("timeout ")]
        return status[0], calls

    def test_success_runs_the_check(self) -> None:
        status, calls = self.run_step()
        self.assertEqual(status, "ok")
        self.assertEqual(calls, ["scripts/check.sh build"])
        self.assertTrue(all("--kill-after=5m" in line for line in self.log.read_text().splitlines()
                            if line.startswith("timeout ")))

    def test_failures_are_reported_not_fatal(self) -> None:
        status, calls = self.run_step(CHECK_RC="1")
        self.assertEqual((status, calls), ("failed", ["scripts/check.sh build"]))

    def test_timeouts(self) -> None:
        status, calls = self.run_step(FAKE_RC="124", FAKE_ON="check.sh")
        self.assertEqual((status, calls[-1]), ("timeout", "scripts/check.sh build"))
        # 137 well before the limit is a kill from elsewhere (memory), not the deadline.
        status, _ = self.run_step(FAKE_RC="137", FAKE_ON="check.sh")
        self.assertEqual(status, "failed")
        status, calls = self.run_step(started_ago=105 * 60)
        self.assertEqual((status, calls), ("timeout", []))

    def test_the_deadline_leaves_time_to_save(self) -> None:
        limit = re.search(r"(?m)^    timeout-minutes: (\d+)$", job(WARM.read_text(encoding="utf-8"), "warm"))
        deadline = re.search(r"deadline=\$\(\( START \+ (\d+) \* 60 \)\)", self.script)
        grace = re.search(r"--kill-after=(\d+)m", self.script)
        self.assertIsNotNone(limit)
        self.assertIsNotNone(deadline)
        self.assertIsNotNone(grace)
        # A command killed at the deadline may run for the grace period after it.
        self.assertGreaterEqual(int(limit.group(1)) - int(deadline.group(1)) - int(grace.group(1)), 15,
                                "leave at least 15 minutes to save the build")



class CompareStepTest(unittest.TestCase):
    """Run the workflow's check of the head against main on scratch repositories."""

    GUARD_CODE = (".github/workflows/bump-guard.yml", ".github/workflows/bump-pinned-release.yml",
                  "scripts/bump/pinned_bump.py")

    def setUp(self) -> None:
        text = WARM.read_text(encoding="utf-8")
        self.script = textwrap.dedent(step(text, "name: Compare the head with main").split("run: |\n", 1)[1])
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.work, self.temp = root / "work", root / "runner-temp"
        self.temp.mkdir()
        subprocess.run(["git", "init", "-q", "--bare", str(root / "origin.git")], check=True)
        self.git("init", "-q", "-b", "main", str(self.work), cwd=root)
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.com")
        self.write({"lean-toolchain": "leanprover/lean4:v4.35.0\n", "lake-manifest.json": "{}\n",
                    **{path: "guard\n" for path in self.GUARD_CODE}})
        self.git("remote", "add", "origin", f"file://{root / 'origin.git'}")
        self.git("push", "-q", "origin", "main")
        self.git("checkout", "-q", "-b", "bump")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def git(self, *args: str, cwd: Path | None = None) -> None:
        subprocess.run(["git", *args], cwd=cwd or self.work, check=True, capture_output=True)

    def write(self, files: dict[str, str]) -> None:
        for path, text in files.items():
            target = self.work / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "change")

    def run_step(self) -> subprocess.CompletedProcess:
        output = self.temp / "github_output"
        output.write_text("")
        proc = subprocess.run(["bash", "-e", "-c", self.script], cwd=self.work, capture_output=True, text=True,
                              env=dict(os.environ, RUNNER_TEMP=str(self.temp), GITHUB_OUTPUT=str(output)))
        self.main_output = output.read_text()
        return proc

    def test_new_pins_pass(self) -> None:
        self.write({"lean-toolchain": "leanprover/lean4:v4.36.0\n"})
        self.assertEqual(self.run_step().returncode, 0)
        main = subprocess.run(["git", "rev-parse", "main"], cwd=self.work, capture_output=True, text=True).stdout
        self.assertEqual(self.main_output, f"main={main.strip()}\n")

    def test_main_pins_fail(self) -> None:
        self.write({})
        proc = self.run_step()
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("not a bump", proc.stdout)

    def test_mode_only_change_fails(self) -> None:
        (self.work / "lean-toolchain").chmod(0o755)
        self.write({})
        proc = self.run_step()
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("must be a regular file", proc.stdout)



class GuardInputTest(unittest.TestCase):
    """The guard step's `put`: an optional file the tree lacks stays missing; anything else fails."""

    def setUp(self) -> None:
        text = WARM.read_text(encoding="utf-8")
        script = textwrap.dedent(step(text, "name: Run main's bump guard on the head").split("run: |\n", 1)[1])
        start = script.index("put() {")
        self.put = script[start:script.index("\n}\n", start) + 3]
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name) / "repo"
        self.guard = Path(self.tmp.name) / "guard"
        (self.guard / "pr").mkdir(parents=True)
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        (self.repo / "docs").mkdir()
        (self.repo / "docs" / "README.md").write_text("readme\n")
        os.symlink("README.md", self.repo / "docs" / "link.md")
        subprocess.run(["git", "add", "-A"], cwd=self.repo, check=True)
        subprocess.run(["git", "-c", "user.name=T", "-c", "user.email=t@example.com", "commit", "-q", "-m", "x"],
                       cwd=self.repo, check=True)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def call(self, file: str, required: str) -> subprocess.CompletedProcess:
        script = f'set -euo pipefail\nguard="{self.guard}"\n{self.put}\nput pr HEAD "{file}" {required}\n'
        return subprocess.run(["bash", "-e", "-c", script], cwd=self.repo, capture_output=True, text=True)

    def test_present_file_is_copied(self) -> None:
        self.assertEqual(self.call("docs/README.md", "true").returncode, 0)
        self.assertEqual((self.guard / "pr" / "docs" / "README.md").read_text(), "readme\n")

    def test_absent_optional_file_stays_missing(self) -> None:
        self.assertEqual(self.call("docs/missing.md", "false").returncode, 0)
        self.assertFalse((self.guard / "pr" / "docs" / "missing.md").exists())

    def test_absent_required_file_fails(self) -> None:
        proc = self.call("docs/missing.md", "true")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("is missing at HEAD", proc.stdout)

    def test_unusable_entries_fail(self) -> None:
        self.assertNotEqual(self.call("docs/link.md", "false").returncode, 0)
        self.assertNotEqual(self.call("../escape.md", "false").returncode, 0)
        if os.geteuid() == 0:
            self.skipTest("root can write to a read-only directory")
        (self.guard / "pr" / "docs").mkdir()
        (self.guard / "pr" / "docs").chmod(0o500)
        try:
            proc = self.call("docs/README.md", "false")
        finally:
            (self.guard / "pr" / "docs").chmod(0o700)
        self.assertNotEqual(proc.returncode, 0, "a present file that cannot be copied must stop the run")

if __name__ == "__main__":
    unittest.main()
