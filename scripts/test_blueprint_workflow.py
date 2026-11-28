#!/usr/bin/env python3
"""Security/correctness regressions for the upstream blueprint workflow."""

from __future__ import annotations

import ast
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import yaml

from scripts import next_task

ROOT = Path(__file__).resolve().parent.parent
# The card files, whose presence in the build's list and on disk the card job's own test checks
# (scripts/test_cards.py). On a PR, that job compares the move ledger with the base commit's, which main's runs cannot.
CARD_INPUTS = ("scripts/cards.py", "scripts/card_moves.py", "scripts/card-moves.jsonl", "scripts/test_cards.py")
# The folder of the move ledger's fragments, which the build lists before the first fragment lands.
FRAGMENTS = "scripts/card-moves.d/**"
WORKFLOW = ROOT / ".github" / "workflows" / "blueprint-pages.yml"
GRAPH_SYNC = ROOT / ".github" / "workflows" / "graph-sync.yml"
# The condition of every step and job that publishes: the repository opted in, and the `changes` job found a run of main
# itself, comparing the ref exactly (an expression's `==` ignores case).
PUBLISH = "vars.BLUEPRINT_PAGES == 'true' && needs.changes.outputs.main == 'true'"
# Where the build writes or fetches its outputs: a file committed there would be read with them.
OUTPUTS = (".lake/**", "build/**", "site-src/**", ".autoform-publication-backup-site-src/**", "site/**",
           "site-pages/**", "site-full/**", "mathlib-graph/**", "mathlib-pages-report.json", "v2-dependencies.jsonl",
           "v2-dependencies.jsonl.gz", "v2-modules.txt")


def build_paths(workflow):
    """The `changes` job's explicit path list, each path matching itself and everything beneath it (`dir/**` marks a
    directory); Git attributes and Autoform's output markers start the build too. Blank lines and lines starting with
    `#` are not entries."""
    decide = next(step for step in workflow["jobs"]["changes"]["steps"] if step.get("id") == "decide")
    lines = (line.strip() for line in decide["env"]["BUILD_PATHS"].splitlines())
    return [line for line in lines if line and not line.startswith("#")]


class BlueprintWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = WORKFLOW.read_text()
        # BaseLoader preserves "on" and expressions without evaluating them.
        cls.workflow = yaml.load(cls.text, Loader=yaml.BaseLoader)
        cls.job = cls.workflow["jobs"]["wiki"]
        cls.steps = cls.job["steps"]

    def step(self, name):
        return next(step for step in self.steps if step.get("name") == name)

    def test_a_pull_request_builds_only_when_it_changes_what_only_its_build_checks(self):
        events = self.workflow["on"]
        # Not a required check, so a merge-group run could not stop a merge; CI's
        # required build imports every v2 module together on each merge group.
        self.assertEqual(set(events), {"schedule", "pull_request", "workflow_dispatch"})
        # main is built once a day at 03:17 UTC (GitHub reads cron in UTC), not on every push.
        self.assertEqual(events["schedule"], [{"cron": "17 3 * * *"}])
        # No `paths` filter: GitHub matches one against the first 300 changed files only, so a PR with more changed
        # files outside the list would hide a listed file after them. The `changes` job reads the whole diff, and the
        # build's first jobs wait for its answer.
        for name, event in events.items():
            if isinstance(event, dict):
                self.assertNotIn("paths", event)
                self.assertNotIn("paths-ignore", event)
        self.assertFalse(events["pull_request"])
        jobs = self.workflow["jobs"]
        for name in ("wiki", "mathlib"):
            self.assertEqual(jobs[name]["needs"], "changes")
            self.assertEqual(jobs[name]["if"], "needs.changes.outputs.build == 'true'")
        # Every downstream build job waits for one of those two, directly or through another job, and none overrides a
        # skip: the card and Mathlib pages jobs have no condition, and the two deployment jobs only the publication one.
        later = {"mathlib-pages": ["changes", "wiki", "mathlib"], "cards": "wiki",
                 "deploy": ["changes", "wiki"], "promote": ["changes", "deploy", "mathlib-pages"]}
        self.assertEqual(set(jobs), {"changes", "scope", "tests", "wiki", "mathlib", *later})
        for name, needs in later.items():
            self.assertEqual(jobs[name]["needs"], needs)
        for name in ("mathlib-pages", "cards"):
            self.assertNotIn("if", jobs[name])
        for name in ("deploy", "promote"):
            self.assertEqual(jobs[name]["if"], PUBLISH)
        changes = jobs["changes"]
        self.assertNotIn("if", changes)
        self.assertNotIn("permissions", changes)
        self.assertEqual(changes["outputs"], {"build": "${{ steps.decide.outputs.build }}",
                                              "main": "${{ steps.decide.outputs.main }}"})
        checkout, decide = changes["steps"]
        self.assertEqual(checkout["if"], "github.event_name == 'pull_request'")
        # The event's own merge commit, whose first parent is the base it merges into: all of the PR's commits.
        self.assertEqual(checkout["with"],
                         {"persist-credentials": "false", "fetch-depth": "2", "sparse-checkout": ".github"})
        self.assertEqual(decide["id"], "decide")
        # Every event decides: a skipped decision would leave `build` unset and skip the daily build.
        self.assertNotIn("if", decide)
        # Isolated, so that no module of the checkout, in its working directory, can stand in for one it imports.
        self.assertIn('python3 -I - "$RUNNER_TEMP/changed-paths"', decide["run"])
        self.assertEqual(decide["env"]["EVENT"], "${{ github.event_name }}")
        self.assertNotIn("${{", decide["run"])
        paths = build_paths(self.workflow)
        self.assertEqual(len(paths), len(set(paths)))
        for path in paths:
            # An exact path, or a directory and all it holds: what the job's matcher reads.
            self.assertRegex(path, r"\A[^*?\[\]!\s]+(/\*\*)?\Z")
        self.assertCountEqual(paths, (
            # Every workflow, which the wiki job's tests read, and the Autoform pin it installs.
            ".github/workflows/**", ".github/autoform-ref",
            # The toolchain pins, the Python toolchain uv would read from the root, and the site configuration.
            "lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean", ".python-version",
            ".python-versions", "uv.toml", "pyproject.toml", ".venv/**", "scripts/__init__.py", "mkdocs.yml",
            "theme/**", "hooks/**",
            # Where the build writes or fetches its outputs.
            *OUTPUTS,
            # The scripts the jobs run or import, and the files they read beside the wiki.
            "scripts/generate_wiki.py", "scripts/sync_wiki.py", "scripts/import_mathgraph.py",
            "scripts/check_public_references.py", "scripts/extract_v2_lean_dependencies.py",
            "scripts/dump_v2_dependencies.lean", "scripts/list_v2_modules.sh", "scripts/extract_mathlib_graph.py",
            "scripts/dump_mathlib_dependencies.lean", "scripts/check_blueprint_site.py", "scripts/next_task.py",
            "scripts/build_mathlib_pages.py", "scripts/mathlib_link.py", "scripts/mathlib_pages.css",
            "scripts/pack_pages_site.py", "scripts/pages_packing.js", "scripts/pages_size.sh", "scripts/cards.py",
            "scripts/card_moves.py",
            # Their tests.
            "scripts/test_generate_wiki_navigation.py", "scripts/test_generate_wiki_docstrings.py",
            "scripts/test_sync_wiki.py", "scripts/test_graph_batch.py", "scripts/test_import_mathgraph.py",
            "scripts/test_extract_v2_lean_dependencies.py", "scripts/test_extract_mathlib_graph.py",
            "scripts/test_check_blueprint_site_navigation.py", "scripts/test_site_chrome.py",
            "scripts/test_blueprint_workflow.py", "scripts/test_blueprint_taxonomy.py",
            "scripts/test_build_mathlib_pages.py", "scripts/test_pack_pages_site.py", "scripts/test_cards.py",
            "scripts/test_card_pages.py",
            # The documents the build reads: the importer's tests compare the JSON schemas of the first with the
            # importer's, and the Mathlib layer job copies the second into its artifact.
            "docs/mathgraph-import.md", "docs/mathlib-layer.md",
            # The wiki, and what only a PR's build can check: the two ledgers, which its checks compare with the base
            # commit's, the wiki's moves and card retirements since the base, which the card check compares with the
            # move ledger, and its Mathlib source links, which it checks strictly.
            "scripts/mathgraph-map.jsonl", "scripts/card-moves.jsonl", FRAGMENTS, "blueprint/**",
        ))
        extract = next(step for step in jobs["mathlib"]["steps"] if step.get("name") == "Extract the Mathlib layer")
        self.assertIn("cp docs/mathlib-layer.md mathlib-graph/SCHEMA.md", extract["run"])
        # The reader of the list the job writes: changing it runs the tests that hold the two to one format.
        self.assertIn("scripts/next_task.py", paths)
        # Every test module the job runs is in the list, so changing a test runs it.
        tests = self.step("Test the wiki scripts")["run"]
        for module in re.findall(r"scripts\.(test_\w+)", tests):
            self.assertIn(f"scripts/{module}.py", paths)
        # So is every module of scripts/ the importer imports, whose tests run in this job (and, on a PR that skips the
        # build, in the test job).
        importer = (ROOT / "scripts" / "import_mathgraph.py").read_text()
        modules = re.findall(r"(?m)^    from \. import (\w+)", importer)
        self.assertIn("check_public_references", modules)
        for module in modules:
            self.assertIn(f"scripts/{module}.py", paths)
        # A path that no longer exists would silently stop building the site. The card job's own test checks its files;
        # the root has none of uv's Python toolchain files yet, and nothing is committed where the build writes.
        for path in paths:
            if path in CARD_INPUTS or path in ("lakefile.lean", ".python-version", ".python-versions", "uv.toml",
                                               "pyproject.toml", ".venv/**", "scripts/__init__.py", FRAGMENTS,
                                               *OUTPUTS):
                continue
            target = ROOT / path.removesuffix("/**")
            self.assertTrue(target.is_dir() if path.endswith("/**") else target.is_file(), path)

    def decide(self, event, base=None, commits=(), ref=None):
        """Run the `changes` job's decision for `event` on `ref` (by default a PR's merge ref, or main), on a
        repository whose HEAD, like a PR's merge commit, merges into a commit holding `base` a branch of `commits`
        (each a dict of path: text, or None to delete); the job's outputs, its step summary, and the paths the merge
        commit changes, as Git lists them."""
        script = self.workflow["jobs"]["changes"]["steps"][1]["run"]
        env_paths = self.workflow["jobs"]["changes"]["steps"][1]["env"]["BUILD_PATHS"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            # No global or system configuration (an excludes file, a signing key) reaches the fixture.
            env = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                   "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.com",
                   "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.com"}
            changed = []
            if event == "pull_request":
                def git(*args):
                    return subprocess.run(["git", "-C", str(root), *args], env=env, check=True,
                                          capture_output=True).stdout

                def commit(files, message):
                    for path, text in files.items():
                        target = root / path
                        if text is None:
                            target.unlink()
                            continue
                        target.parent.mkdir(parents=True, exist_ok=True)
                        target.write_text(text)
                    git("add", "--all", "--force")
                    git("commit", "--quiet", "--allow-empty", "-m", message)

                git("init", "--quiet", "--initial-branch=main")
                commit(base, "base")
                git("checkout", "--quiet", "-b", "topic")
                for index, files in enumerate(commits):
                    commit(files, f"topic {index}")
                git("checkout", "--quiet", "main")
                git("merge", "--quiet", "--no-ff", "-m", "merge", "topic")
                changed = git("diff-tree", "-r", "-z", "--no-commit-id", "--name-only", "HEAD^1", "HEAD", "--").decode()
                changed = [path for path in changed.split("\0") if path]
            output, summary = root / "output.txt", root / "summary.md"
            result = subprocess.run(
                ["bash", "-c", script], cwd=root, text=True, capture_output=True, check=False,
                env={**env, "EVENT": event, "BUILD_PATHS": env_paths, "RUNNER_TEMP": directory,
                     "GITHUB_REF": ref or ("refs/pull/1/merge" if event == "pull_request" else "refs/heads/main"),
                     "GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": str(summary)},
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            # Nothing a changed path names reaches the log, where it could issue a workflow command.
            self.assertEqual(result.stdout, "")
            outputs = dict(line.split("=", 1) for line in output.read_text().splitlines())
            self.assertEqual(set(outputs), {"build", "main"})
            return outputs, summary.read_text() if summary.exists() else "", changed

    def test_the_changes_job_builds_on_the_listed_paths_from_the_whole_diff(self):
        row = '{"subject": [{"type": "generic", "uri": "../roadmap/%s/README.md"}], "id": "af_%s"%s}\n'
        card = ', "extensions": {"org.atlas-wiki": {"card": {}}}'
        base = {"README.md": "x\n", "scripts/sync_wiki.py": "x\n", "scripts/card-moves.jsonl": "{}\n",
                "scripts/taxonomy.json": "{}\n", "blueprint/roadmap/a.md": "x\n", "MathlibExt/Old.lean": "x\n",
                "blueprint/roadmap/T/README.md": "x\n", "blueprint/javascripts/mathjax.js": "x\n",
                "blueprint/links/T.jsonl": row % ("T", "1" * 24, card),
                # A file named like the revision the job compares, which `--` keeps from being ambiguous.
                "HEAD": "x\n"}
        skipped = [
            {"scripts/taxonomy.json": "{\"x\": 1}\n"},
            {"scripts/wiki-sync.json": "{}\n"},
            {"docs/BLUEPRINT.md": "y\n", "docs/cards.md": "y\n", "README.md": "y\n"},
            {"MathlibExt/A.lean": "theorem a : True := trivial\n"},
            {"MathlibExt/Old.lean": None},
            {"HEAD": "y\n"},
            # A file whose name starts like a listed directory, or like a listed file, is another path.
            {"themes/a.css": "y\n", "scripts/sync_wiki.py.orig": "y\n", "hooks.py": "y\n", "blueprints/a.md": "y\n"},
            # The local install's pins: the workflow installs its own.
            {"scripts/requirements-blueprint.txt": "mkdocs\n"},
            # A JSON file Autoform does not take for a marker.
            {"MathlibExt/Probability/notes.json": "{}\n"},
            # A module at the root, the decision's working directory, named like one the decision imports (which an
            # interpreter that builds that module in would not load anyway).
            {"unicodedata.py": "raise SystemExit('the repository ran')\n"},
            # A file only named like Git attributes.
            {"docs/math.gitattributes": "*.md text eol=crlf\n"},
        ]
        built = [
            {"scripts/card-moves.jsonl": "{}\n{}\n"},
            {"scripts/card-moves.jsonl": "{}\n{}\n", "HEAD": "y\n"},
            # A new fragment of the move ledger, and a file of its folder that is no fragment, which the checks refuse.
            {"scripts/card-moves.d/20200101T000000Z-move.jsonl": "{}\n"},
            {"scripts/card-moves.d/notes.txt": "y\n"},
            {"scripts/mathgraph-map.jsonl": "{}\n"},
            {"scripts/sync_wiki.py": "y\n"},
            {"scripts/sync_wiki.py": None},
            # A rename: its old path is listed.
            {"scripts/sync_wiki.py": None, "scripts/sync_wiki2.py": "x\n"},
            {"theme/partials/nav.html": "y\n"},
            # A new workflow: the wiki job's tests read them all.
            {".github/workflows/other.yml": "on: push\n"},
            # The wiki's other files, each a page or an input of the site: its landing page, a new page beside the
            # roadmap, the files the sync makes from the taxonomy, and the MathJax inputs autoform render reads (a
            # macros file the vault did not have, and the old copy of the script). Every published page's Mathlib
            # source links are checked strictly.
            {"blueprint/README.md": "y\n"},
            {"blueprint/supplement.md": "y\n"},
            {"blueprint/coverage/README.md": "y\n"},
            {"blueprint/atlas.json": "{}\n"},
            {"blueprint/tex-macros.json": "{}\n"},
            {"blueprint/javascripts/mathjax.js": None},
            {"lean-toolchain": "leanprover/lean4:v0\n"},
            # A Lake configuration Lake would prefer to lakefile.toml.
            {"lakefile.lean": "import Lake\n"},
            # A Python toolchain file uv would read, which changes the Python the jobs run.
            {".python-version": "3.9\n"},
            {".python-versions": "3.9\n"},
            {"uv.toml": "required-version = \"==0.1\"\n"},
            {"pyproject.toml": "[tool.uv]\n"},
            {".venv/pyvenv.cfg": "home = /usr/bin\n"},
            {"scripts/__init__.py": "\n"},
            # A file Autoform takes for a marker of its output, which hides its directory from the Lean source index.
            {"MathlibExt/Probability/publication.json": "{}\n"},
            {"MathlibExt/Probability/manifest.json": "{}\n"},
            # Matched as Autoform matches them: case-folded.
            {"MathlibExt/Probability/MANIFEST.JSON": "{}\n"},
            {"MathlibExt/Probability/Publication.Json": "{}\n"},
            {"MathlibExt/Probability/manifeſt.JSON": "{}\n"},
            # A directory named like a marker, once folded, which can hide the marker beside it from Autoform.
            {"MathlibExt/Probability/MANIFEST.JSON/note.txt": "x\n"},
            # Git attributes, which can change how the checkout writes what the build reads: a ledger's line endings,
            # the Autoform pin's, a document the Mathlib layer copies, or a marker's encoding.
            {".gitattributes": "scripts/mathgraph-map.jsonl eol=crlf\n"},
            {"scripts/.gitattributes": "*.jsonl eol=crlf\n"},
            {".github/.gitattributes": "autoform-ref text eol=crlf\n"},
            {"docs/.gitattributes": "*.md text eol=crlf\n"},
            {"MathlibExt/.gitattributes": "manifest.json working-tree-encoding=UTF-16LE\n"},
            # A file committed where the build writes its outputs: a page there would meet the strict link check.
            {"site/notes.html": "<p>x</p>\n"},
            {"build/lean-dependencies.json": "{}\n"},
            # A file in the place of a listed directory, such as the output directory MkDocs must create, and a
            # directory in the place of a listed file, such as the report the Mathlib pages write.
            {"site": "x\n"},
            {"build": "x\n"},
            {"site-full": "x\n"},
            {"mathlib-pages-report.json/notes.txt": "x\n"},
            # The copy of site-src/ autoform render keeps while it writes, which it would restore over its output.
            {".autoform-publication-backup-site-src": "x\n"},
            {".autoform-publication-backup-site-src/notes.txt": "x\n"},
            # Pages edited or added: only a PR's build fails on a Mathlib source link that disagrees with its
            # declaration's title (docs/mathlib-pages.md).
            {"blueprint/roadmap/a.md": "y\n", "blueprint/roadmap/b.md": "y\n"},
            # A page removed or moved, with no annotation changed: the card job's strict check refuses a move with no
            # row in the move ledger, even of a page with no id that Git sees renamed
            # (scripts/test_cards.py, test_a_page_git_saw_renamed_needs_its_row_even_without_an_id).
            {"blueprint/roadmap/a.md": None},
            {"blueprint/roadmap/a.md": None, "blueprint/roadmap/moved/a.md": "x\n"},
            # A card that stops being one, its folder page and id left in place: the strict check refuses it with no
            # retirement row (docs/cards.md#move-ledger). Any annotation change builds, a new row's too.
            {"blueprint/links/T.jsonl": row % ("T", "1" * 24, "")},
            {"blueprint/links/T.jsonl": row % ("T", "1" * 24, card) + row % ("U", "2" * 24, "")},
            {"blueprint/links/U.jsonl": row % ("U", "2" * 24, "")},
        ]
        for head in skipped + built:
            with self.subTest(head=sorted(head)[:3]):
                outputs, summary, changed = self.decide("pull_request", base, [head])
                self.assertEqual(sorted(changed), sorted(head))
                self.assertEqual(outputs, {"build": "true" if head in built else "false", "main": "false"})
                self.assertTrue(summary)
                # Only the list's own entries are written, never a changed path (unless it is one of them).
                names = [pattern.removesuffix("/**") for pattern in build_paths(self.workflow)]
                for path in changed:
                    if path not in names:
                        self.assertNotIn(path, summary)
        # A path beneath a listed directory is named by the directory's entry alone.
        _, summary, _ = self.decide("pull_request", base, [{"blueprint/roadmap/private-name.md": "y\n"}])
        self.assertEqual(summary, "The PR changes `blueprint/**`: the site is built.\n")
        # Each reason is given once, a listed entry by its name, the others with no path.
        _, summary, _ = self.decide("pull_request", base,
                                    [{"docs/mathlib-layer.md": "y\n", "docs/.gitattributes": "* -text\n",
                                      "MathlibExt/x/manifest.json": "{}\n"}])
        self.assertEqual(summary.splitlines(), [
            "The PR changes `docs/mathlib-layer.md`: the site is built.",
            "The PR changes Git attributes: the site is built.",
            "The PR changes a file with the name of an Autoform output marker: the site is built."])
        # Past the first 300 changed paths, all a `paths` filter reads: the ledger sorts after the Lean files.
        lean = {f"MathlibExt/F{n:03}.lean": "y\n" for n in range(400)}
        outputs, _, changed = self.decide("pull_request", base, [{**lean, "scripts/card-moves.jsonl": "{}\n{}\n"}])
        self.assertEqual((len(changed), changed.index("scripts/card-moves.jsonl")), (401, 400))
        self.assertEqual(outputs["build"], "true")
        outputs, _, changed = self.decide("pull_request", base, [lean])
        self.assertEqual((len(changed), outputs["build"]), (400, "false"))
        fragment = "scripts/card-moves.d/20200101T000000Z-move.jsonl"
        outputs, _, changed = self.decide("pull_request", base, [{**lean, fragment: "{}\n"}])
        self.assertEqual((len(changed), changed.index(fragment), outputs["build"]), (401, 400, "true"))
        # A ledger changed by an earlier commit of the PR than its last: the merge commit holds them all.
        outputs, _, changed = self.decide("pull_request", base, [{"scripts/card-moves.jsonl": "{}\n{}\n"},
                                                                 {"MathlibExt/A.lean": "z\n"}])
        self.assertEqual((sorted(changed), outputs["build"]), (["MathlibExt/A.lean", "scripts/card-moves.jsonl"],
                                                               "true"))
        # Scheduled and manual runs always build, on any branch, and read no diff.
        for event in ("schedule", "workflow_dispatch"):
            for ref in ("refs/heads/main", "refs/heads/topic"):
                outputs, summary, changed = self.decide(event, ref=ref)
                self.assertEqual((outputs["build"], summary, changed), ("true", "", []))

    def test_a_pull_request_that_skips_the_build_still_runs_the_unit_tests(self):
        # Some of the build's unit tests read files the list leaves out, as scripts/test_blueprint_taxonomy.py and
        # scripts/test_build_mathlib_pages.py read scripts/taxonomy.json: a PR that skips the build runs them all on
        # their own, with the steps of the jobs that own them.
        jobs = self.workflow["jobs"]
        tests = jobs["tests"]
        self.assertEqual((tests["name"], tests["needs"], tests["if"]), (
            "test the site scripts", ["changes", "scope"],
            "${{ !cancelled() && needs.changes.outputs.build == 'false' && needs.scope.outputs.site_tests != 'false' }}"))
        self.assertNotIn("permissions", tests)
        # The wiki job's first three steps: its checkout, the Autoform pin and uv.
        self.assertEqual(tests["steps"][:3], jobs["wiki"]["steps"][:3])
        self.assertEqual([step.get("name") for step in tests["steps"][:3]],
                         ["Check out project", "Read the reviewed Autoform pin", "Install uv"])
        # Then every unit test step of the build's jobs, as written there.
        unit = [step for name in ("wiki", "mathlib", "mathlib-pages", "cards") for step in jobs[name]["steps"]
                if "python -m unittest" in step.get("run", "")]
        self.assertEqual(tests["steps"][3:], unit)
        self.assertEqual([step["name"] for step in unit], ["Test the wiki scripts", "Test the Mathlib pages script",
                                                           "Test the Pages packing script", "Test the card scripts"])

    def test_only_a_run_of_main_itself_may_publish(self):
        # The ref is compared exactly: GitHub's expressions would take `Main` for `main`.
        for event, ref, main in (("schedule", "refs/heads/main", "true"),
                                 ("workflow_dispatch", "refs/heads/main", "true"),
                                 ("workflow_dispatch", "refs/heads/Main", "false"),
                                 ("workflow_dispatch", "refs/heads/MAIN", "false"),
                                 ("workflow_dispatch", "refs/heads/main-2", "false"),
                                 ("workflow_dispatch", "refs/heads/topic/refs/heads/main", "false"),
                                 ("workflow_dispatch", "refs/tags/main", "false"),
                                 ("merge_group", "refs/heads/main", "false")):
            with self.subTest(event=event, ref=ref):
                self.assertEqual(self.decide(event, ref=ref)[0]["main"], main)
        # Never a PR, whatever its ref.
        for ref in ("refs/pull/1/merge", "refs/heads/main"):
            outputs, _, _ = self.decide("pull_request", {"README.md": "x\n"}, [{"README.md": "y\n"}], ref=ref)
            self.assertEqual(outputs["main"], "false")

    def test_reviewed_pin_is_a_full_sha(self):
        pin = (ROOT / ".github" / "autoform-ref").read_text().strip()
        self.assertRegex(pin, r"\A[0-9a-f]{40}\Z")
        self.assertIn("^[0-9a-f]{40}$", self.step(
            "Read the reviewed Autoform pin")["run"])
        self.assertNotIn("git ls-remote", self.text)
        self.assertNotIn("AUTOFORM_AUTOPIN", self.text)
        self.assertNotIn("pin", self.workflow["jobs"])

    def test_every_action_is_sha_pinned(self):
        for job in self.workflow["jobs"].values():
            for step in job["steps"]:
                if "uses" in step:
                    self.assertRegex(step["uses"], r"@[0-9a-f]{40}\Z")

    def test_untrusted_build_has_no_write_token_or_persistent_credentials(self):
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertNotIn("permissions", self.job)
        checkout = self.step("Check out project")
        self.assertEqual(checkout["with"]["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["with"]["sparse-checkout"])
        self.assertIn("!/Atlas/", checkout["with"]["sparse-checkout"])
        self.assertNotIn("secrets.", self.text)

    def test_current_build_and_dump_fail_closed(self):
        build = self.step("Build the current v2 libraries")
        self.assertEqual(build["run"],
                         "lake build MathlibExt CSLibExt PhyslibExt Domains WantedExt")
        dump = self.step("Dump declaration dependencies")
        self.assertNotIn("continue-on-error", build)
        self.assertNotIn("continue-on-error", dump)
        self.assertNotIn("if", dump)
        self.assertIn("set -euo pipefail", dump["run"])
        self.assertNotIn("set +e", self.text)
        self.assertNotIn("collisions", dump["run"])
        positions = {s.get("name"): i for i, s in enumerate(self.steps)}
        self.assertLess(positions[build["name"]], positions[dump["name"]])
        self.assertLess(positions[dump["name"]], positions[
            "Collapse dependencies onto the wiki articles"])

    def test_memory_heavy_production_targets_are_serialized(self):
        script = self.step("Build memory-heavy modules one at a time")["run"]
        commands = [row for row in script.splitlines() if row.startswith("lake build ")]
        self.assertEqual(commands, [
            "lake build MathlibExt.Combinatorics.Enumerative.Nontrivial1234_3412Classes",
            "lake build MathlibExt.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound",
        ])

    @staticmethod
    def dump_fixture(root):
        """A repository with the dump step's module-listing script."""
        (root / "scripts").mkdir()
        shutil.copy2(ROOT / "scripts/list_v2_modules.sh", root / "scripts")

    def test_dump_refuses_missing_compiled_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.dump_fixture(root)
            (root / ".lake/build/lib/lean").mkdir(parents=True)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "MathlibExt").mkdir()
            (root / "MathlibExt/Example.lean").write_text("-- fixture\n")
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            result = subprocess.run(
                ["bash", "-c", self.step("Dump declaration dependencies")["run"]],
                cwd=root, text=True, capture_output=True, check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Missing compiled module: MathlibExt/Example.lean",
                          result.stderr)
            self.assertFalse((root / "v2-dependencies.jsonl").exists())

    def test_dump_reads_non_ascii_paths_literally(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.dump_fixture(root)
            (root / ".lake/build/lib/lean/MathlibExt").mkdir(parents=True)
            (root / ".lake/build/lib/lean/MathlibExt/Étale.olean").write_text("")
            (root / "bin").mkdir()
            (root / "bin/lake").write_text("#!/usr/bin/env bash\necho '{}'\n")
            (root / "bin/lake").chmod(0o755)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "MathlibExt").mkdir()
            (root / "MathlibExt/Étale.lean").write_text("-- fixture\n")
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            result = subprocess.run(
                ["bash", "-c", self.step("Dump declaration dependencies")["run"]],
                cwd=root, text=True, capture_output=True, check=False,
                env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}"},
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((root / "v2-modules.txt").read_text(encoding="utf-8"),
                             "MathlibExt.Étale\n")

    def test_dump_refuses_a_partial_module_list(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.dump_fixture(root)
            (root / ".lake/build/lib/lean/MathlibExt").mkdir(parents=True)
            (root / ".lake/build/lib/lean/MathlibExt/Example.olean").write_text("")
            (root / "bin").mkdir()
            # `git ls-files` lists one module, then fails.
            (root / "bin/git").write_text(
                "#!/usr/bin/env bash\nprintf 'MathlibExt/Example.lean\\0'\nexit 74\n")
            (root / "bin/lake").write_text("#!/usr/bin/env bash\necho '{}'\n")
            for name in ("git", "lake"):
                (root / "bin" / name).chmod(0o755)
            result = subprocess.run(
                ["bash", "-c", self.step("Dump declaration dependencies")["run"]],
                cwd=root, text=True, capture_output=True, check=False,
                env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}"},
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((root / "v2-dependencies.jsonl").exists())
            self.assertFalse((root / "v2-dependencies.jsonl.gz").exists())

    def test_the_import_map_only_grows(self):
        # Right after the wiki tests: every line of scripts/mathgraph-map.jsonl is checked, and on a PR the base
        # commit's map, which the checkout of the merge commit lacks until it is fetched, must be its start, each line
        # appended since recording a page the PR adds.
        name = "Check that the import map only grows"
        names = [step.get("name") for step in self.steps]
        self.assertEqual(names.index(name), names.index("Test the wiki scripts") + 1)
        step = self.step(name)
        self.assertNotIn("continue-on-error", step)
        # The base commit arrives through the environment, never interpolated into the script.
        self.assertEqual(step["env"], {"BASE_SHA": "${{ github.event.pull_request.base.sha || '' }}"})
        self.assertNotIn("merge_group", step["env"]["BASE_SHA"])
        self.assertNotIn("${{", step["run"])
        # The importer imports Autoform: the step runs with the wiki tests' packages.
        def packages(script):
            return re.findall(r"--with (\S+)", script)

        self.assertEqual(packages(step["run"]), packages(self.step("Test the wiki scripts")["run"]))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "bin").mkdir()
            for tool in ("git", "uv"):
                (root / "bin" / tool).write_text(f'#!/usr/bin/env bash\nprintf \'%s\\n\' "{tool} $*" >> calls.txt\n')
                (root / "bin" / tool).chmod(0o755)
            for base in ("", "0123456789abcdef0123456789abcdef01234567"):
                with self.subTest(base=base):
                    (root / "calls.txt").write_text("")
                    result = subprocess.run(
                        ["bash", "-c", step["run"]], cwd=root, text=True, capture_output=True, check=False,
                        env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}", "BASE_SHA": base,
                             "AUTOFORM_SOURCE": "https://example.com/autoform.git", "AUTOFORM_REF": "0" * 40},
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    calls = (root / "calls.txt").read_text().splitlines()
                    command = "python scripts/import_mathgraph.py --check-map"
                    if base:
                        self.assertEqual(calls[0], f"git fetch --no-tags --depth=1 origin {base}")
                        self.assertTrue(calls[1].startswith("uv run --no-project"))
                        self.assertTrue(calls[1].endswith(f"{command} --base {base}"))
                    else:
                        self.assertEqual(len(calls), 1)
                        self.assertTrue(calls[0].endswith(command))

    def test_ci_builds_are_restored_and_only_the_mathlib_dump_is_saved_outside_pull_requests(self):
        # CI's keys and paths, so that both workflows read the entries CI saves from main (ci.yml): the build of the
        # commit a pull request is tested against, else main's newest, and the package builds, which only change with
        # the pins. They are restored after `lake exe cache get` clones the packages.
        names = [step.get("name") for step in self.steps]
        pins = "${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}"
        restore = self.step("Restore local build")
        self.assertIn("actions/cache/restore@", restore["uses"])
        self.assertEqual(restore["with"]["path"], ".lake/build")
        self.assertEqual(restore["with"]["key"], f"lake-build-{pins}-${{{{ steps.base.outputs.sha }}}}")
        self.assertEqual(restore["with"]["restore-keys"].strip(), f"lake-build-{pins}-")
        packages = self.step("Restore the package builds")
        self.assertIn("actions/cache/restore@", packages["uses"])
        self.assertEqual(packages["with"]["path"].splitlines(),
                         [".lake/packages/cslib/.lake/build", ".lake/packages/Physlib/.lake/build"])
        self.assertEqual(packages["with"]["key"], f"lake-deps-{pins}")
        self.assertNotIn("restore-keys", packages["with"])
        self.assertLess(names.index("Fetch Mathlib cache"), names.index("Restore the package builds"))
        self.assertLess(names.index("Find the base build"), names.index("Restore local build"))
        # A restore that fails part-way keeps what it extracted and reports no key: Lake must not trust it.
        removal = self.step("Remove a failed restore")
        self.assertEqual(removal["env"], {
            "PACKAGE_BUILDS": "${{ steps.package-builds.outputs.cache-matched-key }}",
            "LOCAL_BUILD": "${{ steps.build-cache.outputs.cache-matched-key }}",
        })
        self.assertEqual(packages["id"], "package-builds")
        self.assertEqual(restore["id"], "build-cache")
        self.assertEqual(names.index("Remove a failed restore"), names.index("Restore local build") + 1)
        self.assertLess(names.index("Restore the package builds"), names.index("Remove a failed restore"))
        self.assertLess(names.index("Remove a failed restore"), names.index("Build memory-heavy modules one at a time"))
        builds = (".lake/packages/cslib/.lake/build", ".lake/packages/Physlib/.lake/build", ".lake/build")
        for matched, kept in ((("", ""), ()), (("lake-deps-k", ""), builds[:2]), (("", "lake-build-k"), builds[2:]),
                              (("lake-deps-k", "lake-build-k"), builds)):
            with tempfile.TemporaryDirectory() as directory:
                for build in builds:
                    (Path(directory) / build / "lib").mkdir(parents=True)
                subprocess.run(["bash", "-c", removal["run"]], cwd=directory, check=True,
                               env={**os.environ, "PACKAGE_BUILDS": matched[0], "LOCAL_BUILD": matched[1]})
                self.assertEqual([b for b in builds if (Path(directory) / b / "lib").is_dir()], list(kept), matched)
        # A pull request's checkout is a merge commit whose first parent is the commit it is tested against; other
        # runs look for their own commit.
        with tempfile.TemporaryDirectory() as directory:
            def git(*args):
                return subprocess.run(["git", "-C", directory, "-c", "user.name=t", "-c", "user.email=t@t", *args],
                                      check=True, capture_output=True, text=True).stdout.strip()

            git("init", "-q")
            git("commit", "-q", "--allow-empty", "-m", "base")
            base = git("rev-parse", "HEAD")
            git("checkout", "-q", "-b", "topic")
            git("commit", "-q", "--allow-empty", "-m", "change")
            git("checkout", "-q", base)
            git("merge", "-q", "--no-ff", "-m", "merge", "topic")
            merge = git("rev-parse", "HEAD")
            # The checkout is a depth-one clone, where `HEAD^1` does not resolve.
            clone = Path(directory) / "clone"
            subprocess.run(["git", "clone", "-q", "--depth", "1", f"file://{directory}", str(clone)], check=True)
            for event, expected in (("pull_request", base), ("schedule", merge), ("workflow_dispatch", merge)):
                output = Path(directory) / f"{event}.out"
                subprocess.run(["bash", "-c", self.step("Find the base build")["run"]], cwd=clone, check=True,
                               env={**os.environ, "GITHUB_EVENT_NAME": event, "GITHUB_SHA": merge,
                                    "GITHUB_OUTPUT": str(output)})
                self.assertEqual(output.read_text(), f"sha={expected}\n", event)
        # The Mathlib dump and the graph built from it depend only on the pins and the scripts that make them. Runs
        # other than pull requests save them once per key; a restored graph skips the dump and the graph. No other
        # cache is saved here.
        mathlib = {step.get("name"): step for step in self.workflow["jobs"]["mathlib"]["steps"]}
        cached = mathlib["Restore the Mathlib graph"]
        self.assertIn("actions/cache/restore@", cached["uses"])
        self.assertEqual(cached["with"]["key"], "mathlib-graph-${{ runner.os }}-${{ hashFiles('lean-toolchain', "
                         "'lake-manifest.json', 'scripts/dump_mathlib_dependencies.lean', "
                         "'scripts/extract_mathlib_graph.py', 'scripts/extract_v2_lean_dependencies.py') }}")
        self.assertNotIn("restore-keys", cached["with"])
        self.assertEqual(cached["with"]["path"].splitlines(), [
            f"mathlib-graph/{name}" for name in ("mathlib-dump.jsonl.gz", "mathlib-dump-meta.json", "nodes.jsonl.gz",
                                                 "edges.jsonl.gz", "graph-meta.json")])
        order = list(mathlib)
        miss = "steps.mathlib-graph.outputs.cache-hit != 'true'"
        self.assertEqual([name for name, step in mathlib.items() if "if" in step and "cache-hit" in step["if"]],
                         ["Dump the Mathlib declarations", "Build the Mathlib graph", "Save the Mathlib graph"])
        for name in ("Dump the Mathlib declarations", "Build the Mathlib graph"):
            self.assertEqual(mathlib[name]["if"], miss, name)
            self.assertLess(order.index("Restore the Mathlib graph"), order.index(name), name)
        self.assertIn("extract_mathlib_graph.py graph", mathlib["Build the Mathlib graph"]["run"])
        save = mathlib["Save the Mathlib graph"]
        self.assertEqual(save["if"], f"{miss} && github.event_name != 'pull_request'")
        self.assertEqual(save["with"], {"path": cached["with"]["path"],
                                        "key": "${{ steps.mathlib-graph.outputs.cache-primary-key }}"})
        self.assertEqual(order.index("Save the Mathlib graph"), order.index("Build the Mathlib graph") + 1)
        self.assertEqual(order.index("Build the Mathlib graph"), order.index("Dump the Mathlib declarations") + 1)
        saves = [step for job in self.workflow["jobs"].values() for step in job["steps"]
                 if step.get("uses", "").startswith(("actions/cache@", "actions/cache/save@"))]
        self.assertEqual(saves, [save])

    def test_deployment_is_opt_in_and_never_runs_on_pr_or_merge_group(self):
        jobs = self.workflow["jobs"]
        deploy, promote = jobs["deploy"], jobs["promote"]
        self.assertEqual(deploy["needs"], ["changes", "wiki"])
        for job in (deploy, promote):
            self.assertEqual(job["permissions"], {
                "pages": "write", "id-token": "write", "deployments": "read", "contents": "read",
            })
            self.assertEqual(job["environment"]["name"], "github-pages")
        upload = next(step for step in jobs["mathlib-pages"]["steps"] if step.get("name") == "Upload the packed site")
        conditions = [deploy["if"], promote["if"], self.step("Upload Pages artifact")["if"], upload["if"]]
        for condition in conditions:
            # Opted in by the repository, and a scheduled or manual run of main, never a PR or a merge group: the
            # `changes` job decides (test_only_a_run_of_main_itself_may_publish). No clause requires a push.
            self.assertEqual(condition, PUBLISH)
        # Each job first reads the commit of the published site and fails, publishing nothing, unless the site is of
        # this run's commit or of an ancestor: a re-run never takes the site back, and a deployment job that succeeds
        # is one that published. It runs no repository code.
        for job in (deploy, promote):
            check, *publish = job["steps"]
            self.assertEqual(check["name"], "Check the commit of the published site")
            self.assertEqual(check["run"], deploy["steps"][0]["run"])
            self.assertEqual(check["env"], {"GH_TOKEN": "${{ github.token }}"})
            self.assertEqual([step["name"] for step in publish], ["Configure GitHub Pages", "Deploy"])
            for step in publish:
                self.assertIn("uses", step)
                self.assertNotIn("if", step)
                self.assertNotIn("continue-on-error", step)
            self.assertNotIn("continue-on-error", check)
            self.assertNotIn("run_attempt", job["if"])
        # GitHub Pages publishes at most 1 GB: the wiki job's site is packed for it, checked to give back every file
        # of the site, and measured as its upload packs it, before the upload.
        names = [step.get("name") for step in self.steps]
        pack, checked, upload = (self.step(name) for name in
                                 ("Pack the site for GitHub Pages", "Check the packed site", "Upload Pages artifact"))
        self.assertEqual(pack["run"], "python scripts/pack_pages_site.py pack site site-pages")
        self.assertIn("python scripts/pack_pages_site.py check site site-pages", checked["run"])
        self.assertIn("bash scripts/pages_size.sh site-pages 950000000", checked["run"])
        self.assertEqual(upload["with"]["path"], "site-pages")
        for step in (pack, checked):
            self.assertEqual(step["if"], upload["if"])
        self.assertEqual([names.index(name) for name in ("Keep the built site", "Pack the site for GitHub Pages",
                                                          "Check the packed site", "Upload Pages artifact")],
                         list(range(names.index("Keep the built site"), names.index("Keep the built site") + 4)))

    def test_a_site_is_published_only_over_one_of_the_same_or_an_earlier_commit(self):
        script = self.workflow["jobs"]["deploy"]["steps"][0]["run"]
        fake_gh = """#!/usr/bin/env python3
import json, os, sys
path = next(arg for arg in sys.argv[1:] if arg.startswith("repos/"))
state = json.loads(os.environ["FAKE"])
if state.get("fail"):
    sys.exit(1)
if "/statuses" in path:
    print(state["states"].get(path.split("/deployments/")[1].split("/")[0], ""))
elif "/deployments?" in path:
    print("\\n".join(state["deployments"]))
elif "/deployments/" in path:
    print(state["shas"][path.rsplit("/", 1)[1]])
elif "/compare/" in path:
    print(state["compare"])
"""
        live = {"shas": {"2": "b" * 40}}
        cases = [
            # Nothing was ever published, or only this job's own deployment is under way.
            ({"deployments": []}, 0),
            ({"deployments": ["4", "3"], "states": {"4": "in_progress", "3": "failure"}}, 0),
            ({"deployments": ["4", "3", "2"], "states": {"4": "in_progress", "3": "failure", "2": "success"},
              "compare": "ahead", **live}, 0),
            ({"deployments": ["2"], "states": {"2": "success"}, "compare": "identical", **live}, 0),
            ({"deployments": ["2"], "states": {"2": "success"}, "compare": "behind", **live}, 1),
            ({"deployments": ["2"], "states": {"2": "success"}, "compare": "diverged", **live}, 1),
            # Some deployment was live once and none is now: the published commit is unknown.
            ({"deployments": ["3", "2"], "states": {"3": "failure", "2": "inactive"}}, 1),
            ({"fail": True}, 1),
        ]
        with tempfile.TemporaryDirectory() as directory:
            bin_dir = Path(directory) / "bin"
            bin_dir.mkdir()
            (bin_dir / "gh").write_text(fake_gh)
            (bin_dir / "gh").chmod(0o755)
            for fake, expected in cases:
                env = {**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}", "FAKE": json.dumps(fake),
                       "GITHUB_REPOSITORY": "owner/repo", "GITHUB_SHA": "a" * 40}
                run = subprocess.run(["bash", "-c", script], env=env, capture_output=True, text=True)
                self.assertEqual(run.returncode, expected, (fake, run.stdout, run.stderr))
                if expected:
                    self.assertTrue("::error::" in run.stdout or fake.get("fail"), run.stdout)

    def test_the_pages_size_check_measures_the_archive_and_refuses_one_over_its_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory) / "site"
            site.mkdir()
            (site / "index.html").write_text("x" * 1000)
            (site / ".hidden").write_text("not uploaded")
            summary = Path(directory) / "summary.md"
            env = {**os.environ, "GITHUB_STEP_SUMMARY": str(summary)}
            script = ROOT / "scripts" / "pages_size.sh"
            fits = subprocess.run(["bash", str(script), str(site), "10240"], env=env, capture_output=True, text=True)
            over = subprocess.run(["bash", str(script), str(site), "1000"], env=env, capture_output=True, text=True)
            receipts = summary.read_text()
        self.assertEqual(fits.returncode, 0, fits.stderr)
        self.assertIn("2 files, 1012 bytes; Pages archive 10240 bytes; limit 10240 bytes", fits.stdout)
        self.assertEqual(over.returncode, 1)
        self.assertIn("::error::", over.stdout)
        self.assertEqual(len(receipts.splitlines()), 2)

    def test_the_mathlib_layer_cannot_hold_back_the_site(self):
        # The layer has its own job and check beside the wiki job, and deployment waits for the wiki job alone. Both
        # jobs wait only for the decision whether to build.
        jobs = self.workflow["jobs"]
        mathlib = jobs["mathlib"]
        self.assertEqual((mathlib["needs"], self.job["needs"]), ("changes", "changes"))
        self.assertEqual(mathlib["timeout-minutes"], self.job["timeout-minutes"])
        self.assertDeploysWhateverTheMathlibJobsDo()
        self.assertNotIn("permissions", mathlib)
        self.assertNotIn("continue-on-error", mathlib)
        checkout = next(step for step in mathlib["steps"] if step.get("name") == "Check out project")
        self.assertEqual(checkout["with"]["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["with"]["sparse-checkout"])
        self.assertIn("!/Atlas/", checkout["with"]["sparse-checkout"])
        # The layer's job sets up Lean, restores CI's builds, builds what they lack and makes the v2 extraction with
        # the wiki job's own steps, so that `bridge` checks the layer against the extraction the site uses. It
        # downloads nothing from the wiki job, which no longer runs the layer's dump.
        steps = {step.get("name"): step for step in mathlib["steps"]}
        order = list(steps)
        names = [step.get("name") for step in self.steps]
        shared = names[names.index("Free disk space for Lean caches"):names.index("Add the Lean-owned facts to the articles")]
        self.assertEqual(shared[-1], "Collapse dependencies onto the wiki articles")
        self.assertEqual(order[order.index(shared[0]):order.index(shared[0]) + len(shared)], shared)
        for name in shared:
            self.assertEqual(steps[name], self.step(name), name)
        self.assertFalse([step for step in mathlib["steps"] if "download-artifact" in step.get("uses", "")])
        self.assertFalse([step["name"] for step in self.steps if "extract_mathlib_graph.py" in step.get("run", "")])
        # Its dump of the v2 declarations with their Mathlib uses follows the extraction, runs one Lean process and
        # has a timeout, so a hang cannot hold the job until its own; a failure fails the layer's check. The upload
        # keeps it as before and cannot fail the job.
        dump, upload = "Dump the v2 declarations with their Mathlib uses", "Keep the v2 declarations with their Mathlib uses"
        self.assertEqual(order.index(dump), order.index(shared[-1]) + 1)
        self.assertEqual(order.index(upload), order.index(dump) + 1)
        self.assertLessEqual(int(steps[dump]["timeout-minutes"]), 30)
        self.assertIn("--jobs 1 --shards 1", steps[dump]["run"])
        self.assertIn("--modules v2-modules.txt", steps[dump]["run"])
        self.assertEqual(steps[upload]["continue-on-error"], "true")
        self.assertEqual(steps[upload]["with"]["name"], "v2-mathlib-dump")
        self.assertNotIn("mathlib-graph", self.step("Keep dependency diagnostics")["with"]["path"])
        extract = steps["Extract the Mathlib layer"]["run"]
        self.assertIn("set -euo pipefail", extract)
        self.assertIn("test -s mathlib-graph/v2-mathlib-dump.jsonl.gz", extract)
        self.assertIn("--check-v2 build/lean-dependencies.json", extract)
        self.assertIn("join --strict", extract)
        for command in ("dump", "graph", "bridge", "stats"):
            self.assertTrue(any(f"extract_mathlib_graph.py {command}" in step.get("run", "")
                                for step in mathlib["steps"]), command)
        # Only the uploads may fail without failing the layer's check.
        self.assertEqual([name for name, step in steps.items() if "continue-on-error" in step],
                         [upload, "Keep the Mathlib layer"])
        self.assertEqual(steps["Keep the Mathlib layer"]["with"]["name"], "mathlib-graph")
        self.assertEqual(steps["Keep the Mathlib layer"]["if"], "always()")

    def test_the_ready_tasks_are_published_with_the_site_and_kept_on_every_build(self):
        # What the tools own (docs/BLUEPRINT.md): Autoform's task list on the checkout after lean-facts, published
        # as tasks.json.
        name = "List the ready formalization tasks"
        step = self.step(name)
        script = step["run"]
        self.assertIn("set -euo pipefail", script)
        self.assertIn('uvx --from "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}" autoform work list blueprint --json', script)
        self.assertIn("cp build/tasks.json site-src/tasks.json", script)
        # The format it accepts is the one next_task.py reads.
        self.assertIn(f'.schema != "{next_task.SCHEMA}"', script)
        self.assertNotIn("continue-on-error", step)
        self.assertNotIn("if", step)
        names = [s.get("name") for s in self.steps]
        # After lean-facts and the render, which writes site-src/, and before MkDocs copies it into the site.
        for before in ("Add the Lean-owned facts to the articles", "Render the blueprint"):
            self.assertLess(names.index(before), names.index(name))
        self.assertLess(names.index(name), names.index("Build the Markdown site"))
        # Kept as the `tasks` artifact right after it is written, whatever the later steps do; a missing file fails.
        keep = self.step("Keep the task list")
        self.assertEqual(names.index("Keep the task list"), names.index(name) + 1)
        self.assertNotIn("if", keep)
        self.assertNotIn("continue-on-error", keep)
        self.assertEqual((keep["with"]["name"], keep["with"]["path"], keep["with"]["if-no-files-found"]),
                         ("tasks", "build/tasks.json", "error"))

    def test_the_nodes_to_expand_are_published_with_the_task_lists_commit(self):
        # CONTRIBUTING.md, Picking a task: graph-tasks.json, from the index the render wrote, after tasks.json and
        # before MkDocs copies site-src/ into the site. Only `next_task.py --graph` needs it, so it cannot fail the job.
        name = "List the nodes still to expand"
        step = self.step(name)
        names = [s.get("name") for s in self.steps]
        self.assertEqual(names.index(name), names.index("Keep the task list") + 1)
        self.assertLess(names.index(name), names.index("Build the Markdown site"))
        self.assertTrue(step["continue-on-error"])
        if shutil.which("jq") is None:
            self.skipTest("jq is not installed")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "build").mkdir()
            (root / "site-src" / "dependencies").mkdir(parents=True)
            (root / "build" / "tasks.json").write_text(json.dumps({"commit": "c" * 40, "commit_date": "2026-11-27"}))
            nodes = [{"id": "Algebra", "kind": "scope", "status": "not_ready", "route": "../roadmap/Algebra/"},
                     {"id": "Algebra/a", "kind": "node", "status": "not_ready", "title": "A",
                      "route": "../roadmap/Algebra/index.html#a"},
                     {"id": "Algebra/b", "kind": "node", "status": "can_state", "route": "../roadmap/Algebra/b.html"},
                     # A node to expand without a usable route is still listed, with no page.
                     {"id": "Algebra/c", "kind": "node", "status": "not_ready", "title": "C"},
                     {"id": "Algebra/d", "kind": "node", "status": "not_ready", "title": "D", "route": 7}]
            index = root / "site-src" / "dependencies" / "index.json"
            index.write_text(json.dumps({"schema": "autoform-dag-search/v1", "nodes": nodes}))
            script = step["run"]
            result = subprocess.run(["bash", "-c", script], cwd=root, text=True, capture_output=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            published = json.loads((root / "site-src" / "graph-tasks.json").read_text())
            self.assertEqual(published, {"schema": next_task.GRAPH_SCHEMA, "commit": "c" * 40,
                                         "commit_date": "2026-11-27", "nodes": [
                                             {"node_id": "Algebra/a", "title": "A",
                                              "page": "roadmap/Algebra/index.html#a"},
                                             {"node_id": "Algebra/c", "title": "C", "page": None},
                                             {"node_id": "Algebra/d", "title": "D", "page": None}]})
            # next_task.py reads what the step writes.
            with mock.patch.object(next_task, "request", lambda url: json.dumps(published).encode()):
                self.assertEqual([item["node_id"] for item in next_task.load_graph({"commit": "c" * 40,
                                                                                    "commit_date": "2026-11-27"})],
                                 ["Algebra/a", "Algebra/c", "Algebra/d"])
            # An index with no node to expand gives an empty list.
            index.write_text(json.dumps({"schema": "autoform-dag-search/v1", "nodes": [nodes[2]]}))
            result = subprocess.run(["bash", "-c", script], cwd=root, text=True, capture_output=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads((root / "site-src" / "graph-tasks.json").read_text())["nodes"], [])
            # Another format, a node without its kind or status, or a node to expand without an id, or one id twice,
            # leaves no file.
            for wrong in ({"nodes": nodes}, {"schema": "autoform-dag-search/v1", "nodes": "x"},
                          {"schema": "autoform-dag-search/v1", "nodes": [{"id": "Algebra/c", "kind": "node"}]},
                          {"schema": "autoform-dag-search/v1", "nodes": [nodes[1], nodes[1]]},
                          {"schema": "autoform-dag-search/v1", "nodes": [dict(nodes[1], id=" ")]}):
                (root / "site-src" / "graph-tasks.json").unlink(missing_ok=True)
                index.write_text(json.dumps(wrong))
                result = subprocess.run(["bash", "-c", script], cwd=root, text=True, capture_output=True, check=False)
                self.assertNotEqual(result.returncode, 0, wrong)
                self.assertFalse((root / "site-src" / "graph-tasks.json").exists(), wrong)

    def run_task_step(self, output: str, status: int = 0, files: dict[str, str] | None = None):
        """Run the task step in a fixture checkout of *files*, with an Autoform that writes *output* and exits with
        *status*."""
        if shutil.which("jq") is None:
            self.skipTest("jq is not installed")
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        for name, text in (files or {}).items():
            (root / name).write_text(text)
        subprocess.run(["git", "-C", str(root), "add", "--all"], check=True)
        subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q",
                        "--allow-empty", "-m", "fixture"], check=True)
        for folder in ("build", "site-src", "bin"):
            (root / folder).mkdir()
        (root / "output.json").write_text(output)
        (root / "bin" / "uvx").write_text(f'#!/bin/sh\necho "$@" > uvx-arguments\ncat output.json\nexit {status}\n')
        (root / "bin" / "uvx").chmod(0o755)
        environment = {**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}",
                       "AUTOFORM_SOURCE": "https://example.invalid/autoform.git", "AUTOFORM_REF": "a" * 40}
        result = subprocess.run(["bash", "-c", self.step("List the ready formalization tasks")["run"]], cwd=root,
                                env=environment, text=True, capture_output=True, check=False)
        git = lambda *args: subprocess.run(["git", "-C", str(root), *args], text=True, capture_output=True,
                                           check=True).stdout.strip()
        return root, result, git("rev-parse", "--verify", "HEAD"), git("log", "-1", "--format=%cI", "HEAD", "--")

    def test_tasks_json_is_autoforms_list_with_the_commit_and_the_pin(self):
        work = {"schema": next_task.SCHEMA, "open_statements": False, "source_revision": "f" * 64,
                "items": [{"article_id": "af_" + "0" * 24, "node_id": "Algebra/t", "phase": "proof", "ready": True,
                           "state": "can_prove", "lean_targets": [{"declaration": "Ext.t", "source_file": None}]}]}
        root, result, commit, date = self.run_task_step(json.dumps(work))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((root / "uvx-arguments").read_text().split(), [
            "--from", "git+https://example.invalid/autoform.git@" + "a" * 40,
            "autoform", "work", "list", "blueprint", "--json"])
        published = json.loads((root / "site-src" / "tasks.json").read_text())
        self.assertEqual(published, {**work, "commit": commit, "commit_date": date, "autoform_ref": "a" * 40})
        self.assertEqual((root / "build" / "tasks.json").read_text(), (root / "site-src" / "tasks.json").read_text())

    def test_a_file_named_head_leaves_the_task_list_whole(self):
        work = {"schema": next_task.SCHEMA, "open_statements": False, "source_revision": "f" * 64,
                "items": [{"article_id": "af_" + "0" * 24, "node_id": "Algebra/t", "phase": "proof", "ready": True,
                           "state": "can_prove", "lean_targets": [{"declaration": "Ext.t", "source_file": None}]}]}
        root, result, commit, date = self.run_task_step(json.dumps(work), files={"HEAD": "x\n"})
        self.assertEqual(result.returncode, 0, result.stderr)
        published = json.loads((root / "site-src" / "tasks.json").read_text())
        self.assertTrue(date)
        self.assertEqual((published["commit"], published["commit_date"]), (commit, date))
        next_task.load_tasks(str(root / "site-src" / "tasks.json"))

    def test_a_refused_or_unknown_task_list_fails_the_build(self):
        task = {"article_id": "af_" + "0" * 24, "node_id": "Algebra/t", "phase": "proof", "ready": True,
                "state": "can_prove", "lean_targets": [{"declaration": "Ext.t", "source_file": None}]}

        def listing(*items: dict) -> str:
            return json.dumps({"schema": next_task.SCHEMA, "items": list(items)})

        def picked(output: str) -> bool:
            # Whether next_task.py reads the list, as the step would publish it.
            with tempfile.TemporaryDirectory() as folder:
                path = Path(folder) / "tasks.json"
                path.write_text(output)
                try:
                    next_task.load_tasks(str(path))
                except next_task.Failure:
                    return False
                return True

        # A statement still to write may have no Lean declaration yet; a proof (below) may not.
        good = listing(task, {**task, "article_id": "af_" + "1" * 24, "node_id": "Algebra/u", "phase": "statement",
                              "state": "can_state", "lean_targets": []})
        root, result, _, _ = self.run_task_step(good)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(picked((root / "build" / "tasks.json").read_text()))
        broken = [{}, {**task, "node_id": None}, {**task, "node_id": " "}, {**task, "article_id": "af_" + "0" * 23},
                  {**task, "article_id": "af_" + "0" * 24 + "\n"}, {**task, "phase": None},
                  {**task, "ready": False, "state": "proved"}, {**task, "phase": "statement"},
                  {**task, "lean_targets": None}, {**task, "lean_targets": [{"declaration": 1}]},
                  {**task, "lean_targets": [{"declaration": ""}]}, {**task, "lean_targets": []}]
        # next_task.py refuses the tasks the step refuses (below).
        for bad in broken:
            self.assertFalse(picked(listing(bad)), bad)
        # A refusal, no output, two objects, another format, no items, an empty list (the checkout holds thousands
        # of ready tasks, so none means the list is wrong), a task without what next_task.py reads, and a node or an
        # article id twice.
        for output, status in (("", 2), ("", 0), (good + "\n" + good, 0),
                               (json.dumps({"schema": "autoform-work/v3", "items": [task]}), 0),
                               (json.dumps({"schema": next_task.SCHEMA}), 0), (listing(), 0),
                               *((listing(bad), 0) for bad in broken),
                               (listing(task, {**task, "node_id": "A/u"}), 0),
                               (listing(task, {**task, "article_id": "af_" + "1" * 24}), 0)):
            root, result, _, _ = self.run_task_step(output, status)
            self.assertNotEqual(result.returncode, 0, output)
            for path in ("build/tasks.json", "site-src/tasks.json"):
                self.assertFalse((root / path).exists(), (output, path))

    def test_the_cards_cannot_hold_back_the_site(self):
        # The card check has its own job after the wiki job; the wiki job and deployment never wait for it.
        jobs = self.workflow["jobs"]
        cards = jobs["cards"]
        self.assertEqual(cards["name"], "check the cards")
        self.assertEqual(cards["needs"], "wiki")
        self.assertEqual(jobs["deploy"]["needs"], ["changes", "wiki"])
        self.assertNotIn("permissions", cards)
        self.assertNotIn("continue-on-error", cards)
        # The card tests do not run in the wiki job. It checks the move ledger the site serves and derives the card
        # data its site shows in two steps, after lean-facts and before render, each of which can neither fail the
        # job nor hold it past its timeout.
        self.assertFalse(any("test_cards" in step.get("run", "") for step in self.steps))
        moves, derive = "Check the move ledger the site serves", "Derive the card data the site shows"
        self.assertEqual([step["name"] for step in self.steps if "cards.py" in step.get("run", "")], [moves, derive])
        wiki_names = [step.get("name") for step in self.steps]
        for name in (moves, derive):
            self.assertEqual(self.step(name)["continue-on-error"], "true")
            self.assertLessEqual(int(self.step(name)["timeout-minutes"]), 15)
            self.assertLess(wiki_names.index("Add the Lean-owned facts to the articles"), wiki_names.index(name))
            self.assertLess(wiki_names.index(name), wiki_names.index("Render the blueprint"))
        # The ledger check, independent of the strict card check, removes any earlier receipt before it runs.
        check_moves = self.step(moves)["run"]
        self.assertLess(check_moves.index("rm -f build/card-moves.json"),
                        check_moves.index("python scripts/cards.py moves build/card-moves.json"))
        self.assertIn('uv run --no-project --with "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}"', check_moves)
        checkout = next(step for step in cards["steps"] if step.get("name") == "Check out project")
        self.assertEqual(checkout["with"]["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["with"]["sparse-checkout"])
        steps = {step.get("name"): step for step in cards["steps"]}
        self.assertEqual(steps["Fetch the v2 extraction"]["with"]["name"], "blueprint-dependencies")
        names = list(steps)
        self.assertLess(names.index("Add the Lean-owned facts to the articles"),
                        names.index("Check the cards and derive their edges"))
        self.assertIn("python -m unittest scripts.test_cards", steps["Test the card scripts"]["run"])
        self.assertLess(names.index("Test the card scripts"), names.index("Check the cards and derive their edges"))
        check = steps["Check the cards and derive their edges"]["run"]
        self.assertIn("scripts/cards.py rollup build/cards.json", check)
        self.assertIn("--dependencies build/lean-dependencies.json", check)
        # The check renders card pages as the site does: with the site build's exact Markdown pins. So does the wiki
        # job's step that derives the card data its site shows.
        site = next(step["run"] for job in jobs.values() for step in job.get("steps", [])
                    if step.get("name") == "Build the Markdown site")
        for package in ("markdown", "pymdown-extensions"):
            pin = re.search(rf"--with ({re.escape(package)}==[^\s]+)", site).group(1)
            for run in (steps["Test the card scripts"]["run"], check, self.step(derive)["run"]):
                self.assertIn(f"--with {pin}", run)
        # The site's card data comes from the same inputs as the strict check: its command, without the moves since
        # the base commit, which only the card job checks.
        def command(script: str) -> list[str]:
            return [word for word in shlex.split(script[script.index("uv run"):].replace("\\\n", " "))
                    if word != "${base[@]}"]

        self.assertEqual(command(self.step(derive)["run"]), command(check))
        # The base commit's ledger, its frozen file and its fragments, against which the check holds the PR's (the
        # workflow runs in no merge group; ci.yml's `check the graph` does). A frozen file the base lacks stops the
        # step, never an empty ledger; an absent folder of fragments is none, a tree Git cannot read stops it.
        ledger = steps["Read the move ledger and annotations the base commit published"]
        self.assertIn("github.event.pull_request.base.sha", ledger["env"]["BASE"])
        self.assertNotIn("merge_group", ledger["env"]["BASE"])
        self.assertIn('git show "$BASE:scripts/card-moves.jsonl" > build/base/scripts/card-moves.jsonl',
                      ledger["run"])
        self.assertNotIn(": >", ledger["run"])
        self.assertIn('fragments="$(git ls-tree "$BASE" -- scripts/card-moves.d)"', ledger["run"])
        self.assertIn('git archive "$BASE" scripts/card-moves.d | tar -x -C build/base', ledger["run"])
        self.assertIn('echo "BASE_LEDGER=build/base/scripts"', ledger["run"])
        self.assertIn('git archive "$BASE" blueprint/links', ledger["run"])
        self.assertIn('echo "BASE_LINKS=build/base/blueprint/links"', ledger["run"])
        self.assertIn('diff --name-status -M "$BASE" HEAD -- blueprint/roadmap', ledger["run"])
        self.assertIn('echo "BASE_RENAMES=build/base-renames.tsv"', ledger["run"])
        self.assertIn('base=(--base-ledger "$BASE_LEDGER" --base-links "$BASE_LINKS" --renames "$BASE_RENAMES")', check)
        self.assertIn('"${base[@]}"', check)
        self.assertLess(names.index("Read the move ledger and annotations the base commit published"),
                        names.index("Check the cards and derive their edges"))
        # Only the upload may fail without failing the check.
        self.assertEqual([name for name, step in steps.items() if "continue-on-error" in step], ["Keep the card data"])
        self.assertEqual(steps["Keep the card data"]["with"]["name"], "cards")
        self.assertEqual(steps["Keep the card data"]["if"], "always()")

    def test_mathlib_credited_pages_get_their_edges_from_the_same_dump(self):
        # The credited Mathlib names are listed before the dump, which records their uses; the extraction writes the
        # registry beside the unchanged v2 extraction, and lean-facts reads it in both jobs that run it.
        names = [step.get("name") for step in self.steps]
        listing = "List the Mathlib declarations the wiki credits"
        self.assertIn("scripts/sync_wiki.py mathlib-names build/mathlib-names.txt", self.step(listing)["run"])
        self.assertLess(names.index(listing), names.index("Dump declaration dependencies"))
        dump = " ".join(self.step("Dump declaration dependencies")["run"].replace("\\\n", " ").split())
        self.assertIn("dump_v2_dependencies.lean v2-modules.txt build/mathlib-names.txt > v2-dependencies.jsonl", dump)
        self.assertIn("--registry build/mathlib-registry.json --names build/mathlib-names.txt",
                      self.step("Collapse dependencies onto the wiki articles")["run"])
        facts = "lean-facts build/lean-dependencies.json --registry build/mathlib-registry.json"
        self.assertIn(facts, self.step("Add the Lean-owned facts to the articles")["run"])
        self.assertIn("build/mathlib-registry.json", self.step("Keep dependency diagnostics")["with"]["path"])
        cards = {step.get("name"): step for step in self.workflow["jobs"]["cards"]["steps"]}
        self.assertIn(facts, cards["Add the Lean-owned facts to the articles"]["run"])
        self.assertIn("--registry build/mathlib-registry.json", cards["Check the cards and derive their edges"]["run"])
        # The card data the site shows comes from the same registry, so a Mathlib-credited main shows its edges.
        names = [step.get("name") for step in self.steps]
        derive = "Derive the card data the site shows"
        self.assertIn("--registry build/mathlib-registry.json", self.step(derive)["run"])
        self.assertLess(names.index("Collapse dependencies onto the wiki articles"), names.index(derive))

    def test_every_build_keeps_its_site_and_only_main_keeps_the_full_site(self):
        # The built site is a one-day artifact of every successful build, which the Mathlib pages job reads; only
        # main keeps the site with its Mathlib pages, and neither is a Pages upload.
        keep = self.step("Keep the built site")
        self.assertEqual(keep["if"], "success()")
        self.assertEqual((keep["with"]["name"], keep["with"]["retention-days"]), ("blueprint-site", "1"))
        steps = {step.get("name"): step for step in self.workflow["jobs"]["mathlib-pages"]["steps"]}
        full = steps["Keep the site with its Mathlib pages"]
        self.assertIn("actions/upload-artifact@", full["uses"])
        self.assertEqual((full["with"]["name"], full["with"]["path"]), ("blueprint-site-full", "site-full"))
        # A run of main, as the `changes` job decides, whether or not the site is published.
        self.assertEqual(full["if"], "needs.changes.outputs.main == 'true'")

    def test_a_site_that_does_not_keep_the_moved_addresses_is_neither_kept_nor_published(self):
        # The card pages hook keeps the move ledger's old addresses or only says why it cannot, and MkDocs builds the
        # site without them. The step after the site's checks fails the job instead, on every build, a pull request's
        # too, before the site is kept, packed or uploaded: no later step but the diagnostics runs, and neither do the
        # Mathlib pages or the deployment, which need the job.
        name = "Check that the site keeps the moved addresses"
        step = self.step(name)
        names = [s.get("name") for s in self.steps]
        self.assertEqual(names.index(name), names.index("Check routes, anchors, and article cards") + 1)
        self.assertEqual(names.index("Keep dependency diagnostics"), names.index(name) + 1)
        for later in ("Keep the built site", "Pack the site for GitHub Pages", "Check the packed site",
                      "Upload Pages artifact"):
            self.assertLess(names.index(name), names.index(later))
        for key in ("if", "continue-on-error"):
            self.assertNotIn(key, step)
        for later in self.steps[names.index(name) + 2:]:
            for function in ("always()", "failure()", "cancelled()"):
                self.assertNotIn(function, later.get("if", ""), later["name"])
        for job in ("mathlib-pages", "deploy"):
            self.assertIn("wiki", self.workflow["jobs"][job]["needs"])
            self.assertNotIn("always()", self.workflow["jobs"][job].get("if", ""))
        # It checks the hook's own table against the hook's own ledger, the frozen file, and its fragments: a table is
        # the hook's when it starts with the line the hook's moves_script writes first, which a file of that name from
        # the theme, also copied into the site, would not.
        hook = (ROOT / "hooks" / "card_pages.py").read_text()
        table, ledger = (re.search(rf'(?m)^{constant} = "([^"]+)"$', hook).group(1)
                         for constant in ("SCRIPT", "LEDGER"))
        script = step["run"]
        self.assertIn("set -euo pipefail", script)
        self.assertIn(f"table={table}\n", script)
        self.assertIn(f"[[ -f {ledger} ]]", script)
        self.assertNotIn("${{", script)
        header = re.search(r"(?m)^header='([^']*)'$", script).group(1)
        written = re.search(r'(?s)\ndef moves_script\(.*?\n    return \(\n        "(.*?)\\n"', hook)
        self.assertEqual(written.group(1), header)
        row = '{"page": "A/old", "to": "A/new", "article_id": "af_' + "0" * 24 + '"}\n'
        fragment = "scripts/card-moves.d/20261127T000000Z-move.jsonl"
        made = header + "\n   rewritten to where the address leads before the explorer starts. */\n"
        cases = [
            # A row and the hook's table: the site keeps the moved addresses.
            ({ledger: row, f"site/{table}": made}, 0),
            # A row, and no table, an empty one, one that is not the hook's, as the theme's would be, or one from the
            # site source, which the hook never replaces (it then keeps nothing).
            ({ledger: row}, 1),
            ({ledger: row, f"site/{table}": ""}, 1),
            ({ledger: row, f"theme/{table}": "var moves = {};\n", f"site/{table}": "var moves = {};\n"}, 1),
            ({ledger: row, f"site/{table}": made, f"site-src/{table}": made}, 1),
            # A row in a fragment only.
            ({ledger: "", fragment: row, f"site/{table}": made}, 0),
            ({ledger: "", fragment: row}, 1),
            # No row, blank lines aside: the hook writes no table.
            ({ledger: ""}, 0),
            ({ledger: "\n \t\n"}, 0),
            # No frozen file is no empty ledger: the hook keeps nothing.
            ({}, 1),
        ]
        with tempfile.TemporaryDirectory() as directory:
            for files, expected in cases:
                root = Path(tempfile.mkdtemp(dir=directory))
                for path, text in files.items():
                    (root / path).parent.mkdir(parents=True, exist_ok=True)
                    (root / path).write_text(text)
                run = subprocess.run(["bash", "-c", script], cwd=root, capture_output=True, text=True)
                self.assertEqual(run.returncode, expected, (files, run.stdout, run.stderr))
                self.assertEqual("::error title=Moved addresses not kept::" in run.stdout, bool(expected), run.stdout)

    def test_the_mathlib_pages_cannot_hold_back_the_site(self):
        # The pages have their own read-only job after the wiki and the Mathlib layer; deployment waits for the
        # wiki job alone, and the wiki job never runs the pages script.
        jobs = self.workflow["jobs"]
        pages = jobs["mathlib-pages"]
        self.assertEqual(pages["needs"], ["changes", "wiki", "mathlib"])
        self.assertDeploysWhateverTheMathlibJobsDo()
        for key in ("permissions", "continue-on-error", "if"):
            self.assertNotIn(key, pages)
        self.assertFalse(any("build_mathlib_pages" in step.get("run", "") for step in self.steps))
        steps = {step.get("name"): step for step in pages["steps"]}
        checkout = steps["Check out project"]["with"]
        self.assertEqual(checkout["persist-credentials"], "false")
        self.assertIn("!/v1/", checkout["sparse-checkout"])
        self.assertIn("!/Atlas/", checkout["sparse-checkout"])
        fetched = {(s["with"]["name"], s["with"]["path"]) for s in pages["steps"] if "download-artifact@" in s.get("uses", "")}
        self.assertEqual(fetched, {("blueprint-site", "site"), ("mathlib-graph", "mathlib-graph")})
        self.assertIn("python -m unittest scripts.test_build_mathlib_pages", steps["Test the Mathlib pages script"]["run"])
        self.assertIn("scripts/test_build_mathlib_pages.py", build_paths(self.workflow))
        build = steps["Build the Mathlib pages"]["run"]
        self.assertIn("build_mathlib_pages.py build", build)
        self.assertIn("github.event_name == 'pull_request' && '--strict-links' || ''", build)
        self.assertIn("build_mathlib_pages.py check site mathlib-graph site-full", steps["Check the site with its Mathlib pages"]["run"])
        for step in pages["steps"]:
            self.assertNotIn("continue-on-error", step)
            self.assertFalse(step.get("uses", "").startswith("actions/deploy-pages@"))
        # The full site, packed for GitHub Pages, goes up as a second Pages artifact, under the same conditions as the
        # wiki job's, after the check that it gives back every file of the full site and of its size. The full site is
        # kept as it is before it is packed.
        self.assertIn("python -m unittest scripts.test_pack_pages_site", steps["Test the Pages packing script"]["run"])
        self.assertIn("scripts/test_pack_pages_site.py", build_paths(self.workflow))
        for path in ("scripts/pack_pages_site.py", "scripts/pages_packing.js", "scripts/pages_size.sh"):
            self.assertIn(path, build_paths(self.workflow))
        self.assertEqual(steps["Pack the full site for GitHub Pages"]["run"],
                         "python scripts/pack_pages_site.py pack site-full site-pages")
        checked = steps["Check the packed site"]["run"]
        self.assertIn("python scripts/pack_pages_site.py check site-full site-pages", checked)
        self.assertIn("bash scripts/pages_size.sh site-pages 950000000", checked)
        upload = steps["Upload the packed site"]
        self.assertIn("actions/upload-pages-artifact@", upload["uses"])
        self.assertEqual((upload["with"]["name"], upload["with"]["path"]), ("github-pages-full", "site-pages"))
        self.assertEqual(upload["if"], self.step("Upload Pages artifact")["if"])
        names = [step["name"] for step in pages["steps"]]
        for earlier, later in (("Check the site with its Mathlib pages", "Keep the site with its Mathlib pages"),
                               ("Keep the site with its Mathlib pages", "Pack the full site for GitHub Pages"),
                               ("Pack the full site for GitHub Pages", "Check the packed site"),
                               ("Check the packed site", "Upload the packed site")):
            self.assertLess(names.index(earlier), names.index(later))
        for step in pages["steps"]:
            if "pack_pages_site" in step.get("run", "") and "unittest" not in step["run"]:
                self.assertNotIn("if", step)

    def assertDeploysWhateverTheMathlibJobsDo(self):
        # Deployment waits for the wiki job alone and publishes its site. Only after it, and only if the Mathlib pages
        # job succeeded, a second job publishes that job's packed full site in its place.
        jobs = self.workflow["jobs"]
        deploy, promote = jobs["deploy"], jobs["promote"]
        self.assertEqual(deploy["needs"], ["changes", "wiki"])
        self.assertNotIn("mathlib", deploy["if"])
        self.assertNotIn("with", next(step for step in deploy["steps"] if step["name"] == "Deploy"))
        self.assertNotIn("name", self.step("Upload Pages artifact").get("with", {}))
        self.assertEqual(promote["name"], "publish the full site")
        self.assertEqual(promote["needs"], ["changes", "deploy", "mathlib-pages"])
        for function in ("always()", "!cancelled()", "failure()"):
            self.assertNotIn(function, promote["if"])
        self.assertEqual(promote["if"], deploy["if"])
        steps = {step["name"]: step for step in promote["steps"]}
        self.assertEqual(steps["Deploy"]["with"], {"artifact_name": "github-pages-full"})
        self.assertNotIn("cancel-in-progress", str(self.workflow["concurrency"]["group"]))
        self.assertEqual(self.workflow["concurrency"]["cancel-in-progress"], "${{ github.ref != 'refs/heads/main' }}")


class GraphSyncWorkflowTests(unittest.TestCase):
    """The scoped declarations check (docs/BLUEPRINT.md, Maintaining articles) runs on every pull request and merge
    group, reads the Lean sources only, and reports without failing its job."""

    @classmethod
    def setUpClass(cls):
        cls.text = GRAPH_SYNC.read_text()
        cls.workflow = yaml.load(cls.text, Loader=yaml.BaseLoader)
        cls.job = cls.workflow["jobs"]["check"]
        cls.steps = {step.get("name"): step for step in cls.job["steps"]}

    def test_every_pull_request_and_merge_group_runs_it(self):
        # No filter skips a pull request, Lean-only ones included, and nothing skips the job: the merge queue could
        # require it one day (scripts/test_merge_queue_checks.py holds required checks to this).
        events = self.workflow["on"]
        self.assertEqual(set(events), {"pull_request", "merge_group", "workflow_dispatch"})
        self.assertEqual(events["pull_request"], "")
        self.assertEqual(events["merge_group"], {"types": ["checks_requested"]})
        for key in ("if", "needs", "strategy", "continue-on-error"):
            self.assertNotIn(key, self.job)
        self.assertIn("github.ref", self.workflow["concurrency"]["group"])
        # Its check's name is its own: another job of that name could stand in for it.
        names = [job.get("name", key) for path in sorted(GRAPH_SYNC.parent.glob("*.y*ml"))
                 for key, job in yaml.load(path.read_text(), Loader=yaml.BaseLoader)["jobs"].items()]
        self.assertEqual(names.count("graph sync"), 1)
        self.assertEqual(self.job["name"], "graph sync")

    def test_the_check_only_reports_and_keeps_its_report(self):
        step = self.steps["Check that the graph is in step with the Lean"]
        self.assertEqual(step["continue-on-error"], "true")
        self.assertIn('python scripts/sync_wiki.py declarations --base "$BASE" --check', step["run"])
        self.assertIn("--report build/graph-sync.json", step["run"])
        self.assertIn('exit "$status"', step["run"])
        keep = self.steps["Keep the report"]
        self.assertEqual((keep["if"], keep["continue-on-error"], keep["with"]["name"]), ("always()", "true", "graph-sync"))
        # No Lean is built or fetched: the check reads the sources as the declarations sync does.
        self.assertNotIn("lake", self.text)
        self.assertNotIn("elan", self.text)

    def test_it_reads_autoform_and_the_markdown_as_the_wiki_build_does(self):
        wiki = yaml.load(WORKFLOW.read_text(), Loader=yaml.BaseLoader)
        pins = {step["name"]: step for step in wiki["jobs"]["wiki"]["steps"]}
        self.assertEqual(self.steps["Read the reviewed Autoform pin"]["run"], pins["Read the reviewed Autoform pin"]["run"])
        self.assertEqual(self.steps["Install uv"]["with"], pins["Install uv"]["with"])
        self.assertEqual(self.workflow["env"]["AUTOFORM_SOURCE"], wiki["env"]["AUTOFORM_SOURCE"])
        check = self.steps["Check that the graph is in step with the Lean"]["run"]
        self.assertIn('--with "git+${AUTOFORM_SOURCE}@${AUTOFORM_REF}"', check)
        for pin in re.findall(r"--with ([\w.-]+==[^\s]+)", pins["Build the Markdown site"]["run"]):
            self.assertIn(f"--with {pin}", check)

    def test_it_holds_no_write_token_or_credentials(self):
        self.assertEqual(self.workflow["permissions"], {"contents": "read"})
        self.assertNotIn("permissions", self.job)
        self.assertEqual(self.steps["Check out project"]["with"]["persist-credentials"], "false")
        self.assertNotIn("secrets.", self.text)
        for step in self.job["steps"]:
            if "uses" in step:
                self.assertRegex(step["uses"], r"@[0-9a-f]{40}\Z")

    def run_check(self, status: int, report: str | None = None, extra: str = "", fix_fetch: str = "refs/heads/main",
                  changed: str | None = None, event: str = "pull_request", lean: bool = True):
        """Run the check's step with a uv that prints a verdict, writes *report* as the check's JSON report, if any,
        and exits with *status*, in a repository whose HEAD changes the files *changed* names, beside a README and,
        when *lean*, a Lean file, from the commit BASE names; with a git that fails when *changed* is None. Returns the
        result, the job summary and the arguments uv got."""
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        (root / "bin").mkdir()
        base = "b" * 40
        if changed is None:
            (root / "bin" / "git").write_text("#!/bin/sh\nexit 128\n")
            (root / "bin" / "git").chmod(0o755)
        else:
            git = lambda *args: subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@t",
                                                *args], check=True, capture_output=True, text=True).stdout.strip()
            git("init", "-q", "-b", "main")
            git("commit", "-q", "--allow-empty", "-m", "base")
            base = git("rev-parse", "HEAD")
            for path in [*(["MathlibExt/Algebra/Changed.lean"] if lean else []), "README.md", *changed.split()]:
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_text("changed\n")
            git("add", "-A")
            git("commit", "-q", "-m", "change")
        if report is not None:
            (root / "report.json").write_text(report)
        (root / "bin" / "uv").write_text(f'#!/bin/sh\necho "$@" > uv-arguments\necho "In step: no"\necho "error: a link" >&2\n'
                                        'printf "%s" "${UV_EXTRA:-}"\n'
                                        f'[ -f report.json ] && cp report.json build/graph-sync.json\nexit {status}\n')
        (root / "bin" / "uv").chmod(0o755)
        summary = root / "summary.md"
        result = subprocess.run(
            ["bash", "-c", self.steps["Check that the graph is in step with the Lean"]["run"]], cwd=root, text=True,
            capture_output=True, env={**os.environ, "PATH": f"{root / 'bin'}:{os.environ['PATH']}", "BASE": base,
                                      "AUTOFORM_SOURCE": "https://example.invalid/autoform.git", "AUTOFORM_REF": "a" * 40,
                                      "GITHUB_STEP_SUMMARY": str(summary), "UV_EXTRA": extra, "FIX_FETCH": fix_fetch,
                                      "EVENT": event})
        return result, summary.read_text(), (root / "uv-arguments").read_text().split()

    def test_the_check_output_can_neither_issue_a_command_nor_end_the_summary_block(self):
        # A file name holding a workflow command or a code fence, as the check prints it.
        result, summary, _ = self.run_check(0, extra="::error::forged\n```\n# Heading")
        lines = result.stdout.splitlines()
        start = next(number for number, line in enumerate(lines) if line.startswith("::stop-commands::"))
        token = lines[start].removeprefix("::stop-commands::")
        self.assertTrue(token.startswith("graph-sync-") and len(token) > len("graph-sync-") + 16, token)
        end = lines.index(f"::{token}::")
        self.assertTrue(start < lines.index("::error::forged") < end)
        self.assertTrue(all(line.startswith("    ") or not line.strip() or line.startswith(("###", "The check"))
                            for line in summary.splitlines()), summary)
        self.assertIn("    ```\n    # Heading", summary)
        # Lines a carriage return ends, and output with no last line end: every line of the summary stays indented,
        # and the log's resume marker stands on a line of its own.
        result, summary, _ = self.run_check(0, extra="one\r# two\r\n```three")
        self.assertTrue(summary.endswith("    one\n    # two\n    ```three\n"), summary)
        self.assertNotIn("\r", summary)
        self.assertTrue(any(line.startswith("::graph-sync-") for line in result.stdout.split("\n")), result.stdout)

    def test_the_verdict_goes_to_the_log_and_the_summary_with_the_branchs_command(self):
        if shutil.which("jq") is None:
            self.skipTest("jq is not installed")
        result, summary, arguments = self.run_check(1, '{"in_step": false}')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(arguments[arguments.index("python"):], ["python", "scripts/sync_wiki.py", "declarations", "--base",
                                                                "b" * 40, "--check", "--report", "build/graph-sync.json"])
        self.assertIn("In step: no\nerror: a link\n", result.stdout)
        self.assertIn("::warning title=Graph sync::", result.stdout)
        self.assertIn("    In step: no\n    error: a link\n", summary)
        self.assertIn('git fetch https://github.com/facebookresearch/atlas-lean.git refs/heads/main\n'
                      'python3 scripts/sync_wiki.py declarations --base "$(git merge-base FETCH_HEAD HEAD)"\n', summary)
        # A run dispatched with a base names it.
        result, summary, _ = self.run_check(1, '{"in_step": false}', fix_fetch="")
        self.assertIn(f"git fetch https://github.com/facebookresearch/atlas-lean.git {'b' * 40}\n"
                      f"python3 scripts/sync_wiki.py declarations --base {'b' * 40}\n", summary)
        result, summary, _ = self.run_check(0)
        self.assertEqual(result.returncode, 0)
        self.assertNotIn("::warning", result.stdout)
        self.assertNotIn("merge-base", summary)
        # A check that could not run, by its exit code or with no report that says the pull request is not in step,
        # as when Python fails, says so rather than that the pull request is not in step.
        for status, report in ((2, None), (1, None), (1, '{"in_step": true}'), (1, "not json")):
            result, summary, _ = self.run_check(status, report)
            self.assertEqual(result.returncode, status)
            self.assertIn("::warning title=Graph sync::The check could not run", result.stdout)
            self.assertIn(f"The check could not run (exit {status})", summary)
            self.assertNotIn("merge-base", summary)

    def test_a_lean_change_or_a_merge_group_is_held_only_to_the_errors(self):
        # A Lean pull request changes no graph file but links files, which it changes only for the declarations it
        # renames, moves or removes, and a merge group holds others' changes: their missing pages are the next
        # graph-sync batch's (docs/BLUEPRINT.md, Maintaining articles), so the check passes and asks for no sync.
        if shutil.which("jq") is None:
            self.skipTest("jq is not installed")
        pages = '{"in_step": false, "errors": [], "missing": ["Ext.fresh"], "changed": ["Ext.edited (Algebra/edited.md)"]}'
        for changed, event in (("", "pull_request"), ("blueprint/links/Algebra.jsonl", "pull_request"),
                               ("blueprint/roadmap/Algebra/fresh.md", "merge_group")):
            with self.subTest(changed=changed, event=event):
                result, summary, _ = self.run_check(1, pages, changed=changed, event=event)
                self.assertEqual(result.returncode, 0)
                self.assertNotIn("::warning", result.stdout)
                self.assertIn("the next graph-sync\nbatch writes its new declarations' pages", summary)
                self.assertNotIn("merge-base", summary)
                # The pages whose docstring changed are still listed, for the reviewer.
                self.assertIn("for the reviewer to check", summary)
                self.assertIn("\n    Ext.edited (Algebra/edited.md)\n", summary)
        # What the errors name is the change's to fix, by hand: the summary shows them alone, with no command that
        # would write the sync's output.
        errors = ('{"in_step": false, "errors": ["blueprint/links/Algebra.jsonl:3 links Ext.gone", "two\\n```"], '
                  '"changed": ["Ext.edited (Algebra/edited.md)"]}')
        for event in ("pull_request", "merge_group"):
            with self.subTest(event=event):
                result, summary, _ = self.run_check(1, errors, changed="", event=event)
                self.assertEqual(result.returncode, 1)
                self.assertIn("::warning title=Graph sync::This change's Lean leaves links or markers behind",
                              result.stdout)
                self.assertIn("\n    blueprint/links/Algebra.jsonl:3 links Ext.gone\n    two\n    ```\n", summary)
                self.assertIn("A Lean pull request runs no sync", summary)
                self.assertIn("\n    Ext.edited (Algebra/edited.md)\n", summary)
                self.assertNotIn("In step: no", summary)
                self.assertNotIn("error: a link", summary)
                self.assertNotIn("merge-base", summary)
        # A graph pull request, which changes other graph files (the links' defaults, a page count, or the move
        # ledger, its frozen file or a fragment) or links files with no Lean, or a change git cannot read, is held to
        # the sync.
        for changed, lean in (("blueprint/links/Algebra.jsonl scripts/taxonomy.json", True),
                              ("blueprint/links/_defaults.json", True), ("blueprint/roadmap/Algebra/fresh.md", True),
                              ("blueprint/links/Algebra.jsonl scripts/card-moves.jsonl", True),
                              ("blueprint/links/Algebra.jsonl scripts/card-moves.d/20261126T000000Z-retire.jsonl",
                               True),
                              ("blueprint/links/Algebra.jsonl", False), (None, True)):
            with self.subTest(changed=changed, lean=lean):
                result, summary, _ = self.run_check(1, pages, changed=changed, lean=lean)
                self.assertEqual(result.returncode, 1)
                self.assertIn("::warning title=Graph sync::The graph is not in step", result.stdout)
                self.assertIn('--base "$(git merge-base FETCH_HEAD HEAD)"', summary)
                self.assertIn("    In step: no\n", summary)
                self.assertNotIn("for the reviewer to check", summary)

    def test_the_graph_files_it_reads_are_the_syncs(self):
        # Whether a pull request is a graph pull request turns on the graph files it changes: the step names them as
        # sync_wiki.py does (graph_file), blueprint/ and its GRAPH_FILES and GRAPH_FOLDERS, so that a new place for the
        # graph's data, as the move ledger's fragments were, cannot be left out of the one and not the other.
        tree = ast.parse((ROOT / "scripts" / "sync_wiki.py").read_text())
        names = {target.id: ast.literal_eval(node.value) for node in tree.body if isinstance(node, ast.Assign)
                 for target in node.targets if isinstance(target, ast.Name)
                 and target.id in ("GRAPH_FILES", "GRAPH_FOLDERS")}
        self.assertEqual(set(names), {"GRAPH_FILES", "GRAPH_FOLDERS"})
        run = self.steps["Check that the graph is in step with the Lean"]["run"].replace("\\\n", " ")
        pathspec = re.search(r'changed="\$\(git diff --name-only --no-renames "\$BASE" HEAD -- ([^)]*)\)"', run)
        self.assertIsNotNone(pathspec, run)
        folders = [folder.rstrip("/") for folder in names["GRAPH_FOLDERS"]]
        self.assertEqual(sorted(pathspec.group(1).split()), sorted(["blueprint", *names["GRAPH_FILES"], *folders]))

    def find_base(self, event: str, env=lambda main, merge: {}):
        """Run the step that finds the base in a repository whose HEAD merges a branch into main, as a pull request's
        merge commit does, with the environment *env* gives for the main and merge commits; returns the result, what
        the step wrote to GITHUB_ENV, and those commits."""
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        git = lambda *args: subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@t", *args],
                                           check=True, capture_output=True, text=True).stdout.strip()
        git("init", "-q", "-b", "main")
        git("commit", "-q", "--allow-empty", "-m", "first")
        git("switch", "-q", "-c", "topic")
        git("commit", "-q", "--allow-empty", "-m", "topic")
        git("switch", "-q", "main")
        git("commit", "-q", "--allow-empty", "-m", "second")
        main = git("rev-parse", "HEAD")
        git("merge", "-q", "--no-ff", "-m", "merge", "topic")
        merge = git("rev-parse", "HEAD")
        output = root / "env"
        result = subprocess.run(["bash", "-c", self.steps["Find the base commit"]["run"]], cwd=root, text=True,
                                capture_output=True,
                                env={**os.environ, "EVENT": event, "GITHUB_ENV": str(output), **env(main, merge)})
        return result, output.read_text() if output.exists() else "", main, merge

    def test_a_pull_request_compares_with_its_base_and_a_merge_group_with_the_queues(self):
        env = self.steps["Find the base commit"]["env"]
        self.assertEqual(env["MERGE_GROUP_BASE"], "${{ github.event.merge_group.base_sha }}")
        self.assertEqual(env["DISPATCH_BASE"], "${{ inputs.base }}")
        self.assertEqual(env["PR_BASE_REF"], "${{ github.event.pull_request.base.ref }}")
        self.assertEqual(env["MERGE_GROUP_REF"], "${{ github.event.merge_group.base_ref }}")
        self.assertEqual(self.steps["Check out project"]["with"]["fetch-depth"], "2")
        result, written, main, merge = self.find_base("pull_request", lambda main, merge: {"PR_BASE_REF": "release/1.x"})
        self.assertEqual((result.returncode, written), (0, f"BASE={main}\nFIX_FETCH=refs/heads/release/1.x\n"),
                         result.stderr)
        # A branch name the fix command could not give plainly: it fetches the base commit instead.
        result, written, main, merge = self.find_base("pull_request", lambda main, merge: {"PR_BASE_REF": "a b;c"})
        self.assertEqual((result.returncode, written), (0, f"BASE={main}\nFIX_FETCH={main}\n"), result.stderr)
        # The queue's base, here the merge commit itself, which the checkout already has.
        result, written, main, merge = self.find_base("merge_group", lambda main, merge: {
            "MERGE_GROUP_BASE": merge, "MERGE_GROUP_REF": "refs/heads/main"})
        self.assertEqual((result.returncode, written), (0, f"BASE={merge}\nFIX_FETCH=refs/heads/main\n"),
                         result.stderr)
        # A run dispatched with a base fetches nothing to find one: the command names it.
        result, written, main, merge = self.find_base("workflow_dispatch", lambda main, merge: {"DISPATCH_BASE": main})
        self.assertEqual((result.returncode, written), (0, f"BASE={main}\nFIX_FETCH=\n"), result.stderr)
        # A run with no commit to compare with fails rather than checking against nothing.
        result, written, _, _ = self.find_base("workflow_dispatch", lambda main, merge: {"DISPATCH_BASE": "main"})
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(written, "")


class MoveLedgerGateTests(unittest.TestCase):
    """CI's required `check the graph` job checks the card move ledger's integrity as each pull request's merge commit
    and each merge group combines it (docs/cards.md#move-ledger), with `scripts/card_moves.py check` alone: against the
    commit it was made from, it fails only on a combined ledger whose rows break a rule among them, a changed frozen
    file, a changed, renamed or deleted published fragment, or new fragments that interact. What needs the rest of the
    tree, whether each move ends at a live page of its article and whether the moves since that commit have their rows,
    is the card script's, in jobs that gate no merge. The step runs here as written, on fixture repositories that hold
    no other script, with a `python3` that records its arguments."""

    CI = ROOT / ".github" / "workflows" / "ci.yml"
    G = "A"
    ROW = '{"subject": [{"type": "generic", "uri": "../roadmap/%s"}], "id": "af_%024x"}\n'

    @classmethod
    def setUpClass(cls):
        workflow = yaml.load(cls.CI.read_text(), Loader=yaml.BaseLoader)
        cls.job = workflow["jobs"]["graph"]
        cls.steps = {step.get("name"): step for step in cls.job["steps"]}
        cls.gate = cls.steps["Check the move ledger"]

    def test_the_gate_follows_the_autoform_check_and_needs_no_package(self):
        names = list(self.steps)
        self.assertEqual(names.index("Check the move ledger"),
                         names.index("Check the declarations and dependencies") + 1)
        checkout = self.job["steps"][0]
        self.assertEqual(checkout["with"]["fetch-depth"], "2")
        self.assertEqual(checkout["with"]["sparse-checkout"].split(), ["/*", "!/v1/", "!/Atlas/"])
        # Required: no condition and no tolerated failure.
        self.assertNotIn("if", self.gate)
        self.assertNotIn("continue-on-error", self.gate)
        # The standard library alone: no package, no Autoform, nothing written.
        self.assertIn('python3 scripts/card_moves.py check "${base[@]}"', self.gate["run"])
        for absent in ("uv ", "AUTOFORM", "cards.py", "RUNNER_TEMP"):
            self.assertNotIn(absent, self.gate["run"])
        self.assertEqual(self.gate["env"], {"EVENT": "${{ github.event_name }}",
                                            "GROUP_BASE": "${{ github.event.merge_group.base_sha || '' }}",
                                            "PYTHONDONTWRITEBYTECODE": "1"})

    def git(self, root: Path, *arguments: str) -> str:
        env = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1", "GIT_AUTHOR_NAME": "t",
               "GIT_AUTHOR_EMAIL": "t@example.com", "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.com"}
        return subprocess.run(["git", "-C", str(root), *arguments], check=True, capture_output=True, text=True,
                              env=env).stdout

    def repository(self) -> Path:
        """A repository with scripts/card_moves.py and no other script, a small wiki, a frozen ledger, a published
        fragment and Lean, on main."""
        root = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, root)
        (root / "scripts").mkdir()
        shutil.copyfile(ROOT / "scripts" / "card_moves.py", root / "scripts" / "card_moves.py")
        files = {"blueprint/roadmap/README.md": "# Roadmap\n\n- [A](A/README.md)\n",
                 "blueprint/roadmap/A/README.md": "# A\n",
                 "blueprint/links/_defaults.json": '{"object": {"type": "lean", "uri": "../.."}}\n',
                 "MathlibExt/Basic.lean": "theorem t : True := trivial\n",
                 "scripts/card-moves.jsonl": json.dumps({"page": "A/older", "to": "A/p", "article_id": f"af_{20:024x}"})
                 + "\n",
                 "scripts/card-moves.d/20260101T000000Z-q.jsonl": json.dumps(
                     {"page": "A/old", "to": "A/q", "article_id": f"af_{21:024x}"}) + "\n"}
        rows = ""
        for number, name in ((20, "p"), (21, "q"), (22, "r")):
            files[f"blueprint/roadmap/A/{name}.md"] = f"# {name}\n"
            rows += self.ROW % (f"A/{name}.md", number)
        files["blueprint/links/A.jsonl"] = self.ROW % ("A/README.md", 10) + rows
        for path, text in files.items():
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text(text)
        self.git(root, "init", "-q", "-b", "main")
        self.git(root, "add", "-A")
        self.git(root, "commit", "-q", "-m", "base")
        return root

    def change(self, root: Path, files: dict[str, str | None], message: str = "change") -> str:
        for path, text in files.items():
            if text is None:
                (root / path).unlink()
            else:
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_text(text)
        self.git(root, "add", "-A")
        self.git(root, "commit", "-q", "-m", message)
        return self.git(root, "rev-parse", "HEAD").strip()

    def pull_request(self, root: Path, files: dict[str, str | None]) -> None:
        """Main gains an unrelated commit; the pull request, from the base, changes ``files``; HEAD is GitHub's merge
        commit, main's tip its first parent."""
        base = self.git(root, "rev-parse", "HEAD").strip()
        self.change(root, {"README.md": "main moved on\n"}, "main")
        self.git(root, "checkout", "-q", "-b", "pr", base)
        self.change(root, files)
        self.git(root, "checkout", "-q", "main")
        self.git(root, "merge", "-q", "--no-ff", "--no-edit", "pr")

    def run_gate(self, root: Path, event: str, **env: str) -> tuple[int, str, list[str]]:
        """The step's script as CI runs it, the Lean unreadable throughout: its status, its errors, and the arguments
        `python3` got."""
        tools = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, tools)
        (tools / "python3").write_text("#!/bin/sh\nprintf '%s\\n' \"$@\" > \"$UV_ARGUMENTS\"\n"
                                       "exec \"$PYTHON\" \"$@\"\n")
        (tools / "python3").chmod(0o755)
        lean = root / "MathlibExt" / "Basic.lean"
        lean.chmod(0)
        try:
            result = subprocess.run(["bash", "-c", self.gate["run"]], cwd=root, capture_output=True, text=True, env={
                **os.environ, "PATH": f"{tools}{os.pathsep}{os.environ['PATH']}", "PYTHON": sys.executable,
                "UV_ARGUMENTS": str(tools / "arguments"), "RUNNER_TEMP": str(tools), "AUTOFORM_REF": "0" * 40,
                "EVENT": event, "GROUP_BASE": "", "BEFORE": "",
                "PYTHONDONTWRITEBYTECODE": self.gate["env"]["PYTHONDONTWRITEBYTECODE"], **env})
        finally:
            lean.chmod(0o644)
        arguments = (tools / "arguments").read_text().splitlines() if (tools / "arguments").exists() else []
        return result.returncode, result.stderr, arguments

    def assertUntouched(self, root: Path) -> None:
        self.assertEqual(self.git(root, "status", "--porcelain", "--ignored", "--untracked-files=all"), "")

    def test_a_pull_request_is_checked_against_its_merge_commit_s_first_parent(self):
        unrelated = {
            "Lean only": {"MathlibExt/Basic.lean": "theorem t : True := by trivial\n",
                          "MathlibExt/New.lean": "theorem u : True := trivial\n"},
            "a blueprint change touching no ledger endpoint": {
                "blueprint/roadmap/A/s.md": "# s\n", "blueprint/roadmap/A/r.md": "# r, edited\n",
                "blueprint/links/A.jsonl": None},
            "a move in a fragment of its own": {
                "blueprint/roadmap/A/r.md": None, "blueprint/roadmap/A/r2.md": "# r\n",
                "scripts/card-moves.d/20260102T000000Z-r.jsonl": json.dumps(
                    {"page": "A/r", "to": "A/r2", "article_id": f"af_{22:024x}"}) + "\n"},
            # The moves since the base are `check the cards`'s to hold to the ledger, not this step's.
            "a move with no row": {"blueprint/roadmap/A/r.md": None, "blueprint/roadmap/A/r2.md": "# r\n"},
            "a page deleted with no row": {"blueprint/roadmap/A/r.md": None},
            # Whether a move ends at a live page of its article needs the pages: the card script's, in the site build.
            "a move ending at no live page": {"scripts/card-moves.d/20260102T000000Z-r.jsonl": json.dumps(
                {"page": "A/r-old", "to": "A/nowhere", "article_id": f"af_{22:024x}"}) + "\n"},
        }
        for name, files in unrelated.items():
            with self.subTest(name):
                root = self.repository()
                links = (root / "blueprint/links/A.jsonl").read_text()
                if name.startswith("a blueprint"):
                    files = {**files, "blueprint/links/A.jsonl": links + self.ROW % ("A/s.md", 23)}
                if name.startswith("a move"):
                    files = {**files, "blueprint/links/A.jsonl": links.replace("A/r.md", "A/r2.md")}
                if name.startswith("a page deleted"):
                    files = {**files, "blueprint/links/A.jsonl": links.replace(self.ROW % ("A/r.md", 22), "")}
                self.pull_request(root, files)
                status, errors, arguments = self.run_gate(root, "pull_request")
                self.assertEqual((status, errors), (0, ""))
                self.assertEqual(arguments[-2:], ["--base", self.git(root, "rev-parse", "HEAD^1").strip()])
                self.assertUntouched(root)
        published = "scripts/card-moves.d/20260101T000000Z-q.jsonl"
        for name, files, message in (
            ("a published fragment edited", {published: '{"page":"A/old","to":"A/q","article_id":"af_%024x"}\n' % 21},
             f"{published}, a fragment of the base commit, changed"),
            ("a published fragment deleted", {published: None}, f"{published}, a fragment of the base commit, is gone"),
            ("a row appended to the frozen file", {"scripts/card-moves.jsonl": json.dumps(
                {"page": "A/older", "to": "A/p", "article_id": f"af_{20:024x}"}) + "\n" + json.dumps(
                {"page": "A/r-old", "to": "A/r", "article_id": f"af_{22:024x}"}) + "\n"},
             "card-moves.jsonl is not the base commit's; it is frozen"),
            ("an invalid combined ledger", {"scripts/card-moves.d/20260102T000000Z-r.jsonl": json.dumps(
                {"page": "A/older", "to": "A/r", "article_id": f"af_{22:024x}"}) + "\n"},
             "scripts/card-moves.d/20260102T000000Z-r.jsonl:1: A/older already moved"),
        ):
            with self.subTest(name):
                root = self.repository()
                self.pull_request(root, files)
                status, errors, _ = self.run_gate(root, "pull_request")
                self.assertEqual(status, 1)
                self.assertIn(message, errors)
                self.assertUntouched(root)
        # A checkout without the merge commit's two parents names no base: the gate stops, loudly, rather than check
        # the combined ledger alone. So does a checkout that is no merge commit at all.
        stop = "HEAD is no merge commit with both of its parents here: the pull request's base cannot be read"
        root = self.repository()
        self.pull_request(root, {"MathlibExt/New.lean": "theorem u : True := trivial\n"})
        shallow = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, shallow)
        self.git(shallow, "clone", "-q", "--depth=1", f"file://{root}", "checkout")
        status, errors, arguments = self.run_gate(shallow / "checkout", "pull_request")
        self.assertEqual((status, errors.strip(), arguments), (1, stop, []))
        root = self.repository()
        status, errors, arguments = self.run_gate(root, "pull_request")
        self.assertEqual((status, errors.strip(), arguments), (1, stop, []))

    def test_a_merge_group_is_checked_against_its_base_and_a_push_as_combined(self):
        root = self.repository()
        base = self.git(root, "rev-parse", "HEAD").strip()
        self.git(root, "checkout", "-q", "-b", "entry")
        self.change(root, {"blueprint/roadmap/A/r.md": None, "blueprint/roadmap/A/r2.md": "# r\n",
                           "blueprint/links/A.jsonl": (root / "blueprint/links/A.jsonl").read_text().replace(
                               "A/r.md", "A/r2.md"),
                           "scripts/card-moves.d/20260102T000000Z-r.jsonl": json.dumps(
                               {"page": "A/r", "to": "A/r2", "article_id": f"af_{22:024x}"}) + "\n"})
        self.git(root, "checkout", "-q", "main")
        self.git(root, "merge", "-q", "--no-ff", "--no-edit", "entry")
        status, errors, arguments = self.run_gate(root, "merge_group", GROUP_BASE=base)
        self.assertEqual((status, errors, arguments[-2:]), (0, "", ["--base", base]))
        # A group that names no base, or a base that cannot be fetched, stops the gate, loudly, before any check.
        self.assertEqual(self.run_gate(root, "merge_group"), (1, "The merge group names no base commit\n", []))
        status, errors, arguments = self.run_gate(root, "merge_group", GROUP_BASE="f" * 40)
        self.assertEqual((status, arguments), (1, []))
        self.assertTrue(errors.endswith(f"The merge group's base commit {'f' * 40} cannot be fetched\n"), errors)
        status, errors, arguments = self.run_gate(root, "workflow_dispatch")
        self.assertEqual((status, "--base" in arguments), (0, False))
        self.assertUntouched(root)

    def test_a_push_to_main_checks_the_combined_ledger_alone(self):
        # Two queue entries, each checked in its merge group against the one before it, land in one push: the second
        # fragment builds on the first, so against the commit the push replaced the two are new fragments that
        # interact. The push checks the combined ledger alone and passes; held to that commit, they would be refused.
        root = self.repository()
        before = self.git(root, "rev-parse", "HEAD").strip()
        links = (root / "blueprint/links/A.jsonl").read_text()
        self.change(root, {"blueprint/roadmap/A/r.md": None, "blueprint/roadmap/A/r2.md": "# r\n",
                           "blueprint/links/A.jsonl": links.replace("A/r.md", "A/r2.md"),
                           "scripts/card-moves.d/20260102T000000Z-first.jsonl": json.dumps(
                               {"page": "A/r", "to": "A/r2", "article_id": f"af_{22:024x}"}) + "\n"}, "first entry")
        first = self.git(root, "rev-parse", "HEAD").strip()
        self.change(root, {"blueprint/roadmap/A/r2.md": None, "blueprint/roadmap/A/r3.md": "# r\n",
                           "blueprint/links/A.jsonl": links.replace("A/r.md", "A/r3.md"),
                           "scripts/card-moves.d/20260103T000000Z-second.jsonl": json.dumps(
                               {"page": "A/r2", "to": "A/r3", "article_id": f"af_{22:024x}"}) + "\n"}, "second entry")
        # Each entry passed against the entry before it, as its merge group checked it.
        self.assertEqual(self.run_gate(root, "merge_group", GROUP_BASE=first)[:2], (0, ""))
        status, errors, arguments = self.run_gate(root, "push")
        self.assertEqual((status, errors, "--base" in arguments), (0, "", False))
        held = subprocess.run([sys.executable, "scripts/card_moves.py", "check", "--base", before], cwd=root,
                              capture_output=True, text=True, env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
        self.assertEqual(held.returncode, 1)
        self.assertIn("scripts/card-moves.d/20260102T000000Z-first.jsonl and "
                      "scripts/card-moves.d/20260103T000000Z-second.jsonl, both new, touch the address A/r2",
                      held.stderr)
        self.assertUntouched(root)


if __name__ == "__main__":
    unittest.main()
