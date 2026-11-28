"""Public-reference workflow routing and trusted-checkout regression tests."""

import contextlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github/workflows/public-references.yml"
REPOSITORY = "example/repository"
BASE, HEAD, SCANNER = "a" * 40, "b" * 40, "c" * 40
QUEUE_REF = "refs/heads/gh-readonly-queue/main/pr-1-example"


def step(name):
    source = WORKFLOW.read_text()
    marker = "      - name: " + name + "\n"
    start = source.index(marker) + len(marker)
    end = source.find("\n      - name: ", start)
    return source[start:] if end < 0 else source[start:end]


def python_step(name):
    block = step(name)
    start = block.index("          python3 - <<'PY'\n")
    source = block[start:].split("\n", 1)[1].split("          PY\n", 1)[0]
    source = textwrap.dedent(source)
    if "${{" in source:
        raise AssertionError("event expressions must not enter executable text")
    return compile(source, "workflow: " + name, "exec")


def event(kind="merge_group"):
    common = {"repository": {"full_name": REPOSITORY, "default_branch": "main"}}
    if kind == "merge_group":
        return {
            **common,
            "action": "checks_requested",
            "merge_group": {
                "base_sha": BASE,
                "head_sha": HEAD,
                "base_ref": "refs/heads/main",
                "head_ref": QUEUE_REF,
            },
        }
    return {
        **common,
        "action": "opened",
        "number": 1,
        "pull_request": {
            "number": 1,
            "base": {
                "sha": BASE,
                "ref": "main",
                "repo": {"full_name": REPOSITORY},
            },
            "head": {
                "sha": HEAD,
                "repo": {"clone_url": "https://example.invalid/untrusted"},
            },
        },
    }


class WorkflowShape(unittest.TestCase):
    def test_triggers_and_same_required_check(self):
        source = WORKFLOW.read_text()
        self.assertIn("  merge_group:\n    types: [checks_requested]", source)
        self.assertIn("  pull_request_target:\n", source)
        self.assertEqual(
            re.findall(r"^  ([a-z-]+):$", source.split("jobs:\n", 1)[1], re.M),
            ["public-references"],
        )
        self.assertIn(
            "if: steps.event.outputs.kind == 'pull_request_target'",
            step("Check complete public PR content"),
        )
        self.assertIn(
            "if: steps.event.outputs.kind == 'merge_group'",
            step("Check complete merge group"),
        )
        self.assertIn(
            '--expected-head "$PR_HEAD"',
            step("Check complete public PR content"),
        )
        self.assertIn(
            "github.event.merge_group.head_sha || github.event.pull_request.number",
            source,
        )
        self.assertIn("cancel-in-progress: false", source)

    def test_checkout_permissions_and_workflow_trust_are_explicit(self):
        source = WORKFLOW.read_text()
        checkout = step("Check out trusted base")
        self.assertIn(
            "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
            checkout,
        )
        self.assertIn("ref: ${{ steps.event.outputs.scanner_sha }}", checkout)
        self.assertIn("repository: ${{ github.repository }}", checkout)
        self.assertIn("fetch-depth: 0", checkout)
        self.assertIn("persist-credentials: false", checkout)
        self.assertEqual(source.count("uses:"), 1)
        self.assertNotIn("continue-on-error", source)
        self.assertNotIn(": write", source)
        self.assertIn("  contents: read\n  pull-requests: read", source)
        self.assertLess(
            source.index("- name: Validate event"),
            source.index("uses: actions/checkout@"),
        )
        self.assertIn("not this workflow definition", source)
        self.assertIn("separately protected ruleset source", source)
        self.assertNotIn("GH_TOKEN", step("Check complete merge group"))
        python_step("Validate event")
        python_step("Check complete merge group")


class EventValidation(unittest.TestCase):
    def validate(
        self,
        payload=None,
        kind="merge_group",
        env=None,
        api=None,
        network_error=False,
    ):
        payload = event(kind) if payload is None else payload
        with tempfile.TemporaryDirectory(
            prefix="public-workflow-event-"
        ) as directory:
            root = Path(directory)
            source, output = root / "event.json", root / "output"
            source.write_text(json.dumps(payload))
            output.write_text("")
            environment = {
                "GITHUB_EVENT_PATH": str(source),
                "GITHUB_OUTPUT": str(output),
                "GITHUB_EVENT_NAME": kind,
                "GITHUB_REPOSITORY": REPOSITORY,
                "GITHUB_SHA": HEAD if kind == "merge_group" else BASE,
                "GITHUB_REF": (
                    QUEUE_REF if kind == "merge_group" else "refs/heads/main"
                ),
                "GH_TOKEN": "unused-test-token",
            }
            environment.update(env or {})
            response = io.BytesIO(
                json.dumps({"sha": SCANNER} if api is None else api).encode()
            )
            failure = None
            error = OSError("unavailable") if network_error else None
            with patch.dict(os.environ, environment, clear=True), patch(
                "urllib.request.urlopen",
                return_value=response,
                side_effect=error,
            ) as opener:
                try:
                    exec(python_step("Validate event"), {})
                except SystemExit as error:
                    failure = error.code
                calls = list(opener.call_args_list)
            values = dict(
                line.split("=", 1) for line in output.read_text().splitlines()
            )
            return failure, values, calls

    def test_merge_group_is_pinned_to_default_branch_scanner(self):
        failure, values, calls = self.validate()
        self.assertIsNone(failure)
        self.assertEqual(
            values,
            {
                "kind": "merge_group",
                "base_sha": BASE,
                "head_sha": HEAD,
                "head_ref": QUEUE_REF,
                "pr_number": "",
                "scanner_sha": SCANNER,
            },
        )
        request = calls[0].args[0]
        self.assertEqual(
            request.full_url,
            "https://api.github.com/repos/example/repository/commits/main",
        )
        self.assertEqual(
            request.get_header("Authorization"), "Bearer unused-test-token"
        )
        self.assertEqual(calls[0].kwargs, {"timeout": 45})

    def test_pr_target_and_fork_metadata_use_existing_pr_route(self):
        payload = event("pull_request_target")
        payload["pull_request"]["base"]["ref"] = "release"
        failure, values, calls = self.validate(
            payload, "pull_request_target", {"GITHUB_REF": "refs/heads/release"}
        )
        self.assertIsNone(failure)
        self.assertEqual(values["kind"], "pull_request_target")
        self.assertEqual(values["pr_number"], "1")
        self.assertEqual(values["head_sha"], HEAD)
        self.assertEqual(values["scanner_sha"], SCANNER)
        self.assertTrue(calls[0].args[0].full_url.endswith("/commits/main"))

    def test_pr_into_another_branch_may_run_on_the_default_ref(self):
        payload = event("pull_request_target")
        payload["pull_request"]["base"]["ref"] = "roadmap-domain-imports"
        for run_ref in ("refs/heads/main", "refs/heads/roadmap-domain-imports"):
            with self.subTest(run_ref=run_ref):
                failure, values, calls = self.validate(
                    payload, "pull_request_target", {"GITHUB_REF": run_ref}
                )
                self.assertIsNone(failure)
                self.assertEqual(
                    values,
                    {
                        "kind": "pull_request_target",
                        "base_sha": BASE,
                        "head_sha": HEAD,
                        "head_ref": "",
                        "pr_number": "1",
                        "scanner_sha": SCANNER,
                    },
                )
                self.assertEqual(len(calls), 1)
                self.assertTrue(calls[0].args[0].full_url.endswith("/commits/main"))

    def test_non_main_default_and_distinct_runtime_sha(self):
        payload = event("pull_request_target")
        payload["repository"]["default_branch"] = "trunk"
        payload["pull_request"]["base"]["ref"] = "roadmap-domain-imports"
        # The run's own SHA (the default branch tip) need not be the PR base;
        # the outputs keep the PR's base and head, and the scanner is trunk.
        failure, values, calls = self.validate(
            payload,
            "pull_request_target",
            {"GITHUB_REF": "refs/heads/trunk", "GITHUB_SHA": "e" * 40},
        )
        self.assertIsNone(failure)
        self.assertEqual(
            (values["base_sha"], values["head_sha"], values["scanner_sha"]),
            (BASE, HEAD, SCANNER),
        )
        self.assertTrue(calls[0].args[0].full_url.endswith("/commits/trunk"))
        for run_ref in ("refs/heads/main", "refs/heads/release"):
            with self.subTest(run_ref=run_ref):
                self.assertEqual(
                    self.validate(
                        payload, "pull_request_target", {"GITHUB_REF": run_ref}
                    )[1:],
                    ({}, []),
                )

    def test_run_ref_must_be_the_base_or_trusted_default_branch(self):
        def stacked():
            payload = event("pull_request_target")
            payload["pull_request"]["base"]["ref"] = "roadmap-domain-imports"
            return payload

        for run_ref in (
            "refs/heads/other",
            "refs/heads/roadmap-applied-statements",
            "refs/heads/main\n",
            "refs/heads/main ",
            "main",
            "refs/tags/main",
            "refs/heads/roadmap-domain-imports/x",
            "",
        ):
            with self.subTest(run_ref=run_ref):
                self.assertEqual(
                    self.validate(
                        stacked(), "pull_request_target", {"GITHUB_REF": run_ref}
                    )[1:],
                    ({}, []),
                )
        # The default branch comes only from the event's repository object.
        for where in ("base", "head"):
            payload = stacked()
            payload["pull_request"][where]["repo"]["default_branch"] = "release"
            with self.subTest(pr_default=where):
                self.assertEqual(
                    self.validate(
                        payload,
                        "pull_request_target",
                        {"GITHUB_REF": "refs/heads/release"},
                    )[1:],
                    ({}, []),
                )
        bad = {
            "repository mismatch": lambda p: p["repository"].update(
                full_name="other/repository"
            ),
            "base repository mismatch": lambda p: p["pull_request"]["base"][
                "repo"
            ].update(full_name="other/repository"),
            "number mismatch": lambda p: p.update(number=2),
            "head sha": lambda p: p["pull_request"]["head"].update(sha="x" * 40),
            "base ref with newline": lambda p: p["pull_request"]["base"].update(
                ref="roadmap-domain-imports\nscanner_sha=" + HEAD
            ),
            "default branch with newline": lambda p: p["repository"].update(
                default_branch="main\nscanner_sha=" + HEAD
            ),
            "default branch missing": lambda p: p["repository"].pop(
                "default_branch"
            ),
            "base ref missing": lambda p: p["pull_request"]["base"].pop("ref"),
        }
        for name, change in bad.items():
            payload = stacked()
            change(payload)
            with self.subTest(case=name):
                self.assertEqual(
                    self.validate(
                        payload,
                        "pull_request_target",
                        {"GITHUB_REF": "refs/heads/main"},
                    )[1:],
                    ({}, []),
                )
        # Both refs are validated even when the run ref matches the other one.
        for field, value, run_ref in (
            ("base", "bad..ref", "refs/heads/main"),
            ("default", "bad..ref", "refs/heads/roadmap-domain-imports"),
        ):
            payload = stacked()
            if field == "base":
                payload["pull_request"]["base"]["ref"] = value
            else:
                payload["repository"]["default_branch"] = value
            with self.subTest(other_malformed=field):
                self.assertEqual(
                    self.validate(
                        payload, "pull_request_target", {"GITHUB_REF": run_ref}
                    )[1:],
                    ({}, []),
                )
        # A run ref equal to a malformed base or default ref is still invalid.
        for field, value in (
            ("base", "bad..ref"),
            ("base", "roadmap\nscanner_sha=" + HEAD),
            ("default", "bad..ref"),
            ("default", "main\nscanner_sha=" + HEAD),
        ):
            payload = stacked()
            if field == "base":
                payload["pull_request"]["base"]["ref"] = value
            else:
                payload["repository"]["default_branch"] = value
            with self.subTest(malformed=field, value=value):
                self.assertEqual(
                    self.validate(
                        payload,
                        "pull_request_target",
                        {"GITHUB_REF": "refs/heads/" + value},
                    )[1:],
                    ({}, []),
                )
        for env in (
            {"GITHUB_REPOSITORY": "other/repository"},
            {"GITHUB_SHA": "not-a-sha"},
        ):
            with self.subTest(env=env):
                self.assertEqual(
                    self.validate(
                        stacked(),
                        "pull_request_target",
                        {"GITHUB_REF": "refs/heads/main", **env},
                    )[1:],
                    ({}, []),
                )

    def test_pr_payload_base_may_differ_from_event_sha(self):
        # The PR scanner fetches its own API snapshot; this unused payload
        # field need not equal the event SHA. Live event staleness is not assumed.
        for action in ("edited", "ready_for_review", "reopened"):
            payload = event("pull_request_target")
            payload["action"] = action
            payload["pull_request"]["base"]["sha"] = "d" * 40
            failure, values, calls = self.validate(
                payload, "pull_request_target"
            )
            self.assertIsNone(failure)
            self.assertEqual(values["base_sha"], "d" * 40)
            self.assertEqual(values["head_sha"], HEAD)
            self.assertEqual(values["scanner_sha"], SCANNER)
            self.assertEqual(values["pr_number"], "1")
            self.assertTrue(calls[0].args[0].full_url.endswith("/commits/main"))

    def test_invalid_group_fields_fail_before_network_or_outputs(self):
        changes = [
            ("base_sha", "HEAD"),
            ("head_sha", "x" * 40),
            ("head_sha", "$(touch unwanted)"),
            ("head_sha", "b" * 40 + "\n"),
            ("head_sha", BASE),
            ("base_sha", None),
            ("head_ref", "refs/heads/main"),
            ("head_ref", "refs/heads/gh-readonly-queue/main\noutput=bad"),
            ("base_ref", "main"),
        ]
        for field, value in changes:
            with self.subTest(field=field, value=value):
                payload = event()
                payload["merge_group"][field] = value
                failure, values, calls = self.validate(payload)
                self.assertIsNotNone(failure)
                self.assertEqual((values, calls), ({}, []))
        for field in ("base_sha", "head_sha", "base_ref", "head_ref"):
            payload = event()
            del payload["merge_group"][field]
            self.assertEqual(self.validate(payload)[1:], ({}, []))

    def test_wrong_action_repository_context_and_event_fail_closed(self):
        for action in ("destroyed", "", None):
            payload = event()
            payload["action"] = action
            self.assertEqual(self.validate(payload)[1:], ({}, []))
        payload = event()
        payload["repository"]["full_name"] = "other/repository"
        self.assertEqual(self.validate(payload)[1:], ({}, []))
        for env in (
            {"GITHUB_SHA": SCANNER},
            {"GITHUB_REF": "refs/heads/main"},
            {"GITHUB_REPOSITORY": "--bad"},
        ):
            self.assertEqual(self.validate(env=env)[1:], ({}, []))
        self.assertEqual(self.validate(event(), kind="push")[1:], ({}, []))

    def test_invalid_pr_number_head_and_base_are_rejected(self):
        for number in (True, 0, -1, "1", "1;exit 0"):
            payload = event("pull_request_target")
            payload["pull_request"]["number"] = number
            self.assertEqual(
                self.validate(payload, "pull_request_target")[1:], ({}, [])
            )
        for field in ("base", "head"):
            payload = event("pull_request_target")
            payload["pull_request"][field]["sha"] = "not-a-sha"
            self.assertEqual(
                self.validate(payload, "pull_request_target")[1:], ({}, [])
            )
        payload = event("pull_request_target")
        payload["pull_request"]["base"]["repo"][
            "full_name"
        ] = "other/repository"
        self.assertEqual(
            self.validate(payload, "pull_request_target")[1:], ({}, [])
        )
        for env in (
            {"GITHUB_REF": "refs/heads/other"},
            {"GITHUB_SHA": "not-a-sha"},
            {"GITHUB_REPOSITORY": "other/repository"},
        ):
            self.assertEqual(
                self.validate(kind="pull_request_target", env=env)[1:], ({}, [])
            )

    def test_bad_scanner_response_fails_without_checkout_output(self):
        for response in ({}, {"sha": "main"}, {"sha": HEAD + "\n"}):
            failure, values, calls = self.validate(api=response)
            self.assertIsNotNone(failure)
            self.assertEqual(values, {})
            self.assertEqual(len(calls), 1)
        failure, values, calls = self.validate(network_error=True)
        self.assertIsNotNone(failure)
        self.assertEqual(values, {})
        self.assertEqual(len(calls), 1)


class MergeGroupRun(unittest.TestCase):
    def run_group(self, env=None, fault=None, scanner_status=0):
        environment = {
            "BASE_SHA": BASE,
            "HEAD_SHA": HEAD,
            "HEAD_REF": QUEUE_REF,
            "SCANNER_SHA": SCANNER,
            "GITHUB_SHA": HEAD,
            "GITHUB_REF": QUEUE_REF,
            "GITHUB_REPOSITORY": REPOSITORY,
        }
        environment.update(env or {})
        calls, scans = [], []
        head_reads = 0

        def run(args, **kwargs):
            nonlocal head_reads
            calls.append(args)
            if args[0] != "git":
                scans.append(args)
                return subprocess.CompletedProcess(args, scanner_status)
            self.assertEqual(
                args[:3], ["git", "-c", "core.hooksPath=/dev/null"]
            )
            command = args[3:]
            text = ""
            if command == ["remote", "get-url", "origin"]:
                text = "https://github.com/" + REPOSITORY
                if fault == "origin":
                    text = "https://example.invalid/other"
            elif command == ["rev-parse", "HEAD"]:
                head_reads += 1
                text = (
                    HEAD
                    if fault == "checkout"
                    or (fault == "checkout_changed" and head_reads > 1)
                    else SCANNER
                )
            elif command == ["rev-parse", "--is-shallow-repository"]:
                text = "true" if fault == "shallow" else "false"
            elif command == ["rev-parse", "FETCH_HEAD"]:
                text = SCANNER if fault == "moved_before" else HEAD
            elif command[:1] == ["cat-file"]:
                text = "blob" if fault == "type" else "commit"
            elif command[:1] == ["ls-remote"]:
                text = (
                    (SCANNER if fault == "moved_after" else HEAD)
                    + "\t"
                    + QUEUE_REF
                )
                sibling = SCANNER + "\trefs/heads/archive/" + QUEUE_REF
                if fault == "suffix_before":
                    text = sibling + "\n" + text
                elif fault == "suffix_after":
                    text += "\n" + sibling
                elif fault == "missing_ref":
                    text = sibling
                elif fault == "empty_ref":
                    text = ""
                elif fault == "duplicate_ref":
                    text += "\n" + text
                elif fault == "bad_row":
                    text = HEAD + " " + QUEUE_REF
                elif fault == "bad_sha":
                    text = "not-a-sha\t" + QUEUE_REF
                elif fault == "bad_ref":
                    text = HEAD + "\trefs/heads/bad ref"
                elif fault == "bad_sibling":
                    text += "\nnot-a-sha\trefs/heads/archive/" + QUEUE_REF
            if (
                (fault == "fetch" and command[:1] == ["fetch"])
                or (fault == "ancestry" and command[:1] == ["merge-base"])
                or (fault == "missing" and command[:1] == ["cat-file"])
                or (
                    fault == "bad_ref"
                    and command[:1] == ["check-ref-format"]
                    and command[-1] != QUEUE_REF
                )
            ):
                raise subprocess.CalledProcessError(1, args)
            return subprocess.CompletedProcess(args, 0, stdout=text.encode())

        with patch.dict(os.environ, environment, clear=True), patch(
            "subprocess.run", side_effect=run
        ):
            with self.assertRaises(SystemExit) as stopped:
                exec(python_step("Check complete merge group"), {})
        return stopped.exception.code, calls, scans

    def test_existing_range_cli_and_no_proposed_checkout(self):
        status, calls, scans = self.run_group()
        self.assertEqual(status, 0)
        self.assertEqual(
            scans,
            [
                [
                    sys.executable,
                    "scripts/check_public_references.py",
                    "--base",
                    BASE,
                    "--head",
                    HEAD,
                ]
            ],
        )
        self.assertIn(
            [
                "git",
                "-c",
                "core.hooksPath=/dev/null",
                "fetch",
                "--no-tags",
                "origin",
                BASE,
            ],
            calls,
        )
        self.assertIn(
            [
                "git",
                "-c",
                "core.hooksPath=/dev/null",
                "fetch",
                "--no-tags",
                "origin",
                QUEUE_REF,
            ],
            calls,
        )
        self.assertFalse(
            any("checkout" in call or "switch" in call for call in calls)
        )

    def test_malformed_hashes_never_reach_git(self):
        for field in ("BASE_SHA", "HEAD_SHA", "SCANNER_SHA"):
            status, calls, scans = self.run_group({field: "a;touch unwanted"})
            self.assertNotEqual(status, 0)
            self.assertEqual((calls, scans), ([], []))

    def test_pre_scan_failures_do_not_run_scanner(self):
        for fault in (
            "origin",
            "checkout",
            "shallow",
            "fetch",
            "moved_before",
            "type",
            "missing",
            "ancestry",
        ):
            with self.subTest(fault=fault):
                status, _, scans = self.run_group(fault=fault)
                self.assertNotEqual(status, 0)
                self.assertEqual(scans, [])

    def test_changed_ref_or_checkout_cannot_report_success(self):
        for fault in ("moved_after", "checkout_changed"):
            status, _, scans = self.run_group(fault=fault)
            self.assertNotEqual(status, 0)
            self.assertEqual(len(scans), 1)

    def test_valid_suffix_refs_are_ignored_in_either_order(self):
        for fault in ("suffix_before", "suffix_after"):
            status, _, scans = self.run_group(fault=fault)
            self.assertEqual(status, 0)
            self.assertEqual(len(scans), 1)

    def test_missing_duplicate_and_malformed_remote_rows_fail_closed(self):
        for fault in (
            "missing_ref",
            "empty_ref",
            "duplicate_ref",
            "bad_row",
            "bad_sha",
            "bad_ref",
            "bad_sibling",
        ):
            with self.subTest(fault=fault):
                status, _, scans = self.run_group(fault=fault)
                self.assertNotEqual(status, 0)
                self.assertEqual(len(scans), 1)

    def test_scanner_failure_and_incomplete_status_propagate(self):
        for status in (1, 2):
            self.assertEqual(self.run_group(scanner_status=status)[0], status)


class RealCombinedRange(unittest.TestCase):
    def exercise(self, private=False, advance_scanner=False, suffix_ref=False):
        with tempfile.TemporaryDirectory(
            prefix="public-workflow-git-"
        ) as directory:
            root = Path(directory)
            source, work = root / "source", root / "work"
            source.mkdir()
            environment = {
                **os.environ,
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": os.devnull,
                "GIT_TERMINAL_PROMPT": "0",
                "GIT_NO_LAZY_FETCH": "1",
                "PYTHONDONTWRITEBYTECODE": "1",
            }
            for key in (
                "GIT_AUTHOR_NAME",
                "GIT_AUTHOR_EMAIL",
                "GIT_COMMITTER_NAME",
                "GIT_COMMITTER_EMAIL",
            ):
                environment.pop(key, None)
            actual_run = subprocess.run

            def git(where, *args):
                return (
                    actual_run(
                        ["git", "-C", str(where), *args],
                        env=environment,
                        check=True,
                        capture_output=True,
                    )
                    .stdout.decode()
                    .strip()
                )

            def commit(message):
                git(source, "add", "--all")
                git(
                    source,
                    "-c",
                    "core.hooksPath=/dev/null",
                    "commit",
                    "-q",
                    "--allow-empty",
                    "-m",
                    message,
                )
                return git(source, "rev-parse", "HEAD")

            git(source, "init", "-q", "-b", "main")
            git(source, "config", "user.name", "Example Author")
            git(source, "config", "user.email", "author@example.com")
            git(source, "config", "commit.gpgsign", "false")
            (source / "scripts").mkdir()
            scanner_text = (
                ROOT / "scripts/check_public_references.py"
            ).read_text()
            (source / "scripts/check_public_references.py").write_text(
                scanner_text
            )
            base = commit("Trusted base")
            git(source, "checkout", "-q", "-b", "first")
            (source / "temporary.md").write_text(
                ("D" + "123456789") if private else "Public notes"
            )
            commit("First grouped change")
            (source / "temporary.md").unlink()
            first = commit("Remove intermediate file")
            git(source, "checkout", "-q", "-b", "second", base)
            (source / "other.md").write_text("Another grouped change")
            (source / "scripts/check_public_references.py").write_text(
                "from pathlib import Path\nPath('UNTRUSTED_EXECUTED').write_text('bad')\n"
            )
            second = commit("Second grouped change")
            tree = git(source, "rev-parse", "HEAD^{tree}")
            head = (
                actual_run(
                    [
                        "git",
                        "-C",
                        str(source),
                        "-c",
                        "commit.gpgsign=false",
                        "commit-tree",
                        tree,
                        "-p",
                        first,
                        "-p",
                        second,
                    ],
                    input=b"Combined queue range\n",
                    env=environment,
                    check=True,
                    capture_output=True,
                )
                .stdout.decode()
                .strip()
            )
            git(source, "update-ref", QUEUE_REF, head)
            if suffix_ref:
                sibling = "refs/heads/archive/" + QUEUE_REF
                git(source, "update-ref", sibling, base)
                advertised = git(source, "ls-remote", str(source), QUEUE_REF)
                self.assertEqual(len(advertised.splitlines()), 2)
                self.assertIn(head + "\t" + QUEUE_REF, advertised.splitlines())
                self.assertIn(base + "\t" + sibling, advertised.splitlines())
                self.assertNotEqual(advertised, head + "\t" + QUEUE_REF)
            git(source, "checkout", "-q", "main")
            scanner = base
            if advance_scanner:
                (source / "later.md").write_text("Later trusted default branch")
                scanner = commit("Advance trusted default branch")
            git(
                root,
                "clone",
                "-q",
                "--no-hardlinks",
                "--no-checkout",
                str(source),
                str(work),
            )
            git(work, "checkout", "-q", "--detach", scanner)
            git(
                work,
                "remote",
                "set-url",
                "origin",
                "https://github.com/" + REPOSITORY,
            )
            environment.update(
                {
                    "BASE_SHA": base,
                    "HEAD_SHA": head,
                    "HEAD_REF": QUEUE_REF,
                    "SCANNER_SHA": scanner,
                    "GITHUB_SHA": head,
                    "GITHUB_REF": QUEUE_REF,
                    "GITHUB_REPOSITORY": REPOSITORY,
                }
            )
            scan_results = []

            def run(args, **kwargs):
                args = list(args)
                if (
                    args[0] == "git"
                    and "origin" in args
                    and any(action in args for action in ("fetch", "ls-remote"))
                ):
                    # Only transport is substituted. Validation sees the fixed
                    # configured GitHub origin; fetch/range/object reads are real.
                    args[args.index("origin")] = str(source)
                kwargs.update(cwd=work, env=environment)
                if args[0] != "git":
                    kwargs["capture_output"] = True
                result = actual_run(args, **kwargs)
                if args[0] != "git":
                    scan_results.append(result)
                return result

            with patch.dict(os.environ, environment, clear=True), patch(
                "subprocess.run", side_effect=run
            ):
                with self.assertRaises(SystemExit) as stopped:
                    exec(python_step("Check complete merge group"), {})
            self.assertEqual(stopped.exception.code, 1 if private else 0)
            self.assertEqual(len(scan_results), 1)
            report = json.loads(scan_results[0].stdout)
            self.assertEqual(report["commits"], 4)
            self.assertEqual(bool(report["findings"]), private)
            self.assertFalse((work / "UNTRUSTED_EXECUTED").exists())
            self.assertEqual(
                (work / "scripts/check_public_references.py").read_text(),
                scanner_text,
            )
            self.assertEqual(git(work, "rev-parse", "HEAD"), scanner)

    def test_clean_combined_range_uses_trusted_scanner(self):
        self.exercise()

    def test_removed_intermediate_private_content_still_fails(self):
        self.exercise(private=True)

    def test_scanner_revision_can_advance_independently_of_group_base(self):
        self.exercise(advance_scanner=True)

    def test_sibling_suffix_ref_does_not_invalidate_exact_queue_ref(self):
        self.exercise(suffix_ref=True)


if __name__ == "__main__":
    unittest.main()
