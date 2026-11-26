#!/usr/bin/env python3
"""Regression tests for .github/workflows/codex.yml ready_for_review deduplication."""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "codex.yml"
HEAD_SHA = "a" * 40
OTHER_SHA = "b" * 40


def extract_step(source: str, name: str) -> str:
    marker = f"      - name: {name}\n"
    start = source.index(marker)
    next_step = source.find("\n      - name: ", start + len(marker))
    next_job = source.find("\n  report-failure:\n", start + len(marker))
    candidates = [pos for pos in (next_step, next_job) if pos >= 0]
    end = min(candidates) if candidates else len(source)
    return source[start:end]


def extract_github_script(step_block: str) -> str:
    marker = "          script: |\n"
    start = step_block.index(marker) + len(marker)
    raw_lines = step_block[start:].splitlines()
    script_lines = []
    for line in raw_lines:
        if line.strip() and not line.startswith("            "):
            break
        script_lines.append(line[12:] if line.startswith("            ") else "")
    script = "\n".join(script_lines) + "\n"
    if "${{" in script:
        raise AssertionError("GitHub Actions expressions must not appear inside script text")
    return script


NODE_HARNESS = textwrap.dedent(
    """\
    const fs = require("node:fs");
    const https = require("node:https");

    const spec = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
    const scriptBody = fs.readFileSync(process.argv[3], "utf8");

    const outputs = {};
    const infos = [];
    const warnings = [];
    const apiCalls = [];

    const core = {
      setOutput(k, v) { outputs[k] = String(v); },
      info(msg) { infos.push(String(msg)); },
      warning(msg) { warnings.push(String(msg)); },
    };

    const context = {
      repo: { owner: "example", repo: "atlas" },
      payload: spec.payload,
    };

    async function runWithOptionalTlsServer(fn) {
      if (!spec.tlsLogServer) {
        return await fn(null);
      }
      const server = https.createServer(
        { key: spec.tlsLogServer.key, cert: spec.tlsLogServer.cert },
        (req, res) => {
          apiCalls.push({ kind: "tls_log_fetch", headers: req.headers });
          res.writeHead(spec.tlsLogServer.status || 200, { "content-type": "text/plain" });
          res.end(spec.tlsLogServer.body || "");
        }
      );
      await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
      const port = server.address().port;
      try {
        return await fn(`https://127.0.0.1:${port}/job.log`);
      } finally {
        server.close();
      }
    }

    (async () => {
      await runWithOptionalTlsServer(async (tlsUrl) => {
        const github = {
          rest: {
            pulls: { listReviews: "pulls.listReviews" },
            issues: {
              listEvents: "issues.listEvents",
              listComments: "issues.listComments",
            },
            actions: {
              async listWorkflowRuns(params) {
                apiCalls.push({ endpoint: "listWorkflowRuns", params });
                if (spec.throwOn === "listWorkflowRuns") {
                  throw new Error("simulated API outage");
                }
                const seq = (spec.runsSequenceByStatus || {})[params.status];
                let byStatus;
                if (Array.isArray(seq) && seq.length > 0) {
                  byStatus = seq.length > 1 ? seq.shift() : seq[0];
                } else {
                  byStatus = (spec.runsByStatus || {})[params.status] || [];
                }
                const page = params.page || 1;
                const slice = byStatus.slice((page - 1) * 100, page * 100);
                return { data: { workflow_runs: slice } };
              },
              async listJobsForWorkflowRun(params) {
                apiCalls.push({ endpoint: "listJobsForWorkflowRun", params });
                const jobs = (spec.jobsByRun || {})[String(params.run_id)] || [];
                return { data: { jobs } };
              },
            },
          },
          async paginate(endpoint, params) {
            apiCalls.push({ endpoint, params });
            if (spec.throwOn === endpoint) {
              throw new Error(`simulated error on ${endpoint}`);
            }
            if (endpoint === "pulls.listReviews") return spec.reviews || [];
            if (endpoint === "issues.listEvents") return spec.events || [];
            if (endpoint === "issues.listComments") return spec.comments || [];
            throw new Error(`unexpected paginate endpoint: ${endpoint}`);
          },
          async request(route, params) {
            apiCalls.push({ endpoint: route, params });
            const entry = (spec.logsByJob || {})[String(params.job_id)];
            if (tlsUrl && entry === "__TLS_REDIRECT__") {
              const err = new Error("Found");
              err.status = 302;
              err.response = { headers: { location: tlsUrl } };
              throw err;
            }
            if (entry && typeof entry === "object" && entry.redirect) {
              const err = new Error("Found");
              err.status = 302;
              err.response = { headers: { location: entry.redirect } };
              throw err;
            }
            return { status: 200, data: entry ?? "" };
          },
        };

        process.env.TARGET_REF = spec.targetRef;
        const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
        const fn = new AsyncFunction("github", "context", "core", "require", scriptBody);
        await fn(github, context, core, require);
      });
      process.stdout.write(JSON.stringify({ outputs, infos, warnings, apiCalls }));
    })().catch((err) => {
      console.error(err);
      process.exit(1);
    });
    """
)


class CodexWorkflowStructureTests(unittest.TestCase):
    def setUp(self) -> None:
        self.source = WORKFLOW.read_text(encoding="utf-8")

    def test_preflight_understands_all_codex_workflow_jobs(self) -> None:
        import sys
        sys.path.insert(0, str(ROOT / "scripts" / "queue"))
        import preflight  # noqa: PLC0415

        names, understood = preflight._read_jobs(self.source)
        self.assertTrue(understood)
        self.assertEqual(
            names,
            ["codex", "report-failure", "codex-verdict", "cancel-rejected-build"],
        )

    def test_all_uses_are_pinned_to_full_commit_shas(self) -> None:
        uses_lines = re.findall(r"^\s*-?\s*uses:\s*(\S+)", self.source, re.M)
        self.assertGreaterEqual(len(uses_lines), 6)
        for ref in uses_lines:
            self.assertRegex(ref, r"^[^@]+@[0-9a-f]{40}$")

    def test_existing_verdict_step_ordering_and_downstream_guards(self) -> None:
        resolve_pos = self.source.index("      - name: Resolve target\n")
        existing_pos = self.source.index(
            "      - name: Check existing formal @codex verdict\n"
        )
        checkout_pos = self.source.index("      - name: Checkout request target\n")
        self.assertLess(resolve_pos, existing_pos)
        self.assertLess(existing_pos, checkout_pos)

        existing_block = extract_step(
            self.source, "Check existing formal @codex verdict"
        )
        self.assertIn("id: existing_verdict", existing_block)
        self.assertIn("steps.check_auth.outputs.authorized == 'true'", existing_block)
        self.assertIn("steps.check_auth.outputs.formal == 'true'", existing_block)
        self.assertIn("github.event.action == 'ready_for_review'", existing_block)
        extract_github_script(existing_block)

        self.assertIn(
            "verdict: ${{ steps.submit.outputs.verdict || steps.existing_verdict.outputs.verdict }}",
            self.source,
        )
        self.assertIn(
            "review_id: ${{ steps.submit.outputs.review_id || steps.existing_verdict.outputs.review_id }}",
            self.source,
        )

        guarded_steps = (
            "Checkout request target",
            "Load trusted review guide",
            "Guard fetched size",
            "Remove agent instructions from the review checkout",
            "Prepare isolated Codex runtime",
            "Start isolated credential broker",
            "Run Codex",
            "Stop isolated credential broker",
            "Submit Codex response",
            "Upload Codex output",
        )
        for step_name in guarded_steps:
            with self.subTest(step=step_name):
                block = extract_step(self.source, step_name)
                self.assertIn(
                    "steps.existing_verdict.outputs.skip != 'true'",
                    block,
                )


class ExistingVerdictExecutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        source = WORKFLOW.read_text(encoding="utf-8")
        cls.script = extract_github_script(
            extract_step(source, "Check existing formal @codex verdict")
        )

    def run_step(
        self, spec: dict, extra_env: dict[str, str] | None = None
    ) -> dict:
        with tempfile.TemporaryDirectory(prefix="atlas-codex-wf-") as tmp:
            root = Path(tmp)
            harness_path = root / "harness.js"
            spec_path = root / "spec.json"
            script_path = root / "step.js"
            harness_path.write_text(NODE_HARNESS, encoding="utf-8")
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            script_path.write_text(self.script, encoding="utf-8")
            env = dict(subprocess.os.environ)
            if extra_env:
                env.update(extra_env)
            proc = subprocess.run(
                ["node", str(harness_path), str(spec_path), str(script_path)],
                capture_output=True,
                text=True,
                timeout=20,
                env=env,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            return json.loads(proc.stdout)

    def base_approved_spec(self) -> dict:
        return {
            "targetRef": HEAD_SHA,
            "payload": {"pull_request": {"number": 42}},
            "reviews": [
                {
                    "id": 7001,
                    "user": {"login": "github-actions[bot]"},
                    "state": "APPROVED",
                    "commit_id": HEAD_SHA,
                    "submitted_at": "2026-11-24T05:35:25Z",
                    "body": "<!-- codex-comment-review -->\n\n## Codex review\n\nVerdict: approved",
                }
            ],
            "events": [
                {
                    "event": "base_ref_changed",
                    "created_at": "2026-11-24T04:00:00Z",
                }
            ],
            "comments": [
                {
                    "id": 900,
                    "body": "@codex Please review this draft against REVIEWING.md.",
                    "created_at": "2026-11-24T05:30:03Z",
                }
            ],
            "runsByStatus": {
                "success": [
                    {
                        "id": 501,
                        "path": ".github/workflows/codex.yml",
                        "event": "issue_comment",
                        "created_at": "2026-11-24T05:30:06Z",
                    }
                ]
            },
            "jobsByRun": {
                "501": [
                    {
                        "id": 801,
                        "name": "codex",
                        "conclusion": "success",
                        "completed_at": "2026-11-24T05:35:29Z",
                    },
                    {
                        "id": 802,
                        "name": "codex-verdict",
                        "conclusion": "success",
                    },
                ]
            },
            "logsByJob": {
                "802": (
                    "2026-11-24T05:35:35.3666774Z \x1b[36;1mecho \"Codex approved review 7001.\"\x1b[0m\n"
                    "2026-11-24T05:35:35.4149261Z Codex approved review 7001.\n"
                )
            },
        }

    def test_reuses_attested_approved_comment_verdict_on_exact_head(self) -> None:
        res = self.run_step(self.base_approved_spec())
        self.assertEqual(
            res["outputs"],
            {"skip": "true", "verdict": "approved", "review_id": "7001"},
        )

    def test_reuses_attested_changes_requested_comment_verdict(self) -> None:
        spec = self.base_approved_spec()
        spec["reviews"][0]["id"] = 7002
        spec["reviews"][0]["state"] = "CHANGES_REQUESTED"
        spec["reviews"][0]["body"] = (
            "<!-- codex-comment-review -->\n\n## Codex review\n\nVerdict: change requested"
        )
        spec["runsByStatus"] = {
            "failure": [
                {
                    "id": 502,
                    "path": ".github/workflows/codex.yml",
                    "event": "issue_comment",
                    "created_at": "2026-11-24T05:30:06Z",
                }
            ]
        }
        spec["jobsByRun"] = {
            "502": [
                {
                    "id": 811,
                    "name": "codex",
                    "conclusion": "success",
                    "completed_at": "2026-11-24T05:35:29Z",
                },
                {
                    "id": 812,
                    "name": "codex-verdict",
                    "conclusion": "failure",
                },
            ]
        }
        spec["logsByJob"] = {
            "812": "2026-11-24T05:35:35.4149261Z Codex verdict is 'change requested'; approval required.\n"
        }
        res = self.run_step(spec)
        self.assertEqual(
            res["outputs"],
            {"skip": "true", "verdict": "change requested", "review_id": "7002"},
        )

    def test_follows_https_302_log_redirect_without_authorization_header(self) -> None:
        with tempfile.TemporaryDirectory(prefix="atlas-tls-") as cert_dir:
            key_file = Path(cert_dir) / "key.pem"
            cert_file = Path(cert_dir) / "cert.pem"
            subprocess.run(
                [
                    "openssl",
                    "req",
                    "-x509",
                    "-newkey",
                    "rsa:2048",
                    "-nodes",
                    "-keyout",
                    str(key_file),
                    "-out",
                    str(cert_file),
                    "-days",
                    "1",
                    "-subj",
                    "/CN=127.0.0.1",
                    "-addext",
                    "subjectAltName=IP:127.0.0.1",
                ],
                check=True,
                capture_output=True,
            )
            spec = self.base_approved_spec()
            spec["logsByJob"]["802"] = "__TLS_REDIRECT__"
            spec["tlsLogServer"] = {
                "key": key_file.read_text(encoding="utf-8"),
                "cert": cert_file.read_text(encoding="utf-8"),
                "body": "2026-11-24T05:35:35.4149261Z Codex approved review 7001.\n",
            }
            res = self.run_step(
                spec, extra_env={"NODE_EXTRA_CA_CERTS": str(cert_file)}
            )
            self.assertEqual(
                res["outputs"],
                {"skip": "true", "verdict": "approved", "review_id": "7001"},
            )
            tls_fetches = [
                c for c in res["apiCalls"] if c.get("kind") == "tls_log_fetch"
            ]
            self.assertEqual(len(tls_fetches), 1)
            self.assertNotIn("authorization", tls_fetches[0]["headers"])

    def test_rejects_non_https_log_redirect_and_falls_back_to_review(self) -> None:
        spec = self.base_approved_spec()
        spec["logsByJob"]["802"] = {"redirect": "http://127.0.0.1:9/insecure.log"}
        res = self.run_step(spec)
        self.assertEqual(
            res["outputs"],
            {"skip": "false", "verdict": "", "review_id": ""},
        )
        self.assertTrue(
            any("Refusing non-HTTPS log redirect" in w for w in res["warnings"])
        )

    def test_does_not_skip_when_head_moved_since_comment_review(self) -> None:
        spec = self.base_approved_spec()
        spec["reviews"][0]["commit_id"] = OTHER_SHA
        res = self.run_step(spec)
        self.assertEqual(
            res["outputs"],
            {"skip": "false", "verdict": "", "review_id": ""},
        )

    def test_does_not_skip_when_base_retargeted_at_or_after_review(self) -> None:
        for retarget_time in (
            "2026-11-24T05:35:25Z",
            "2026-11-24T06:00:00Z",
            "not-a-timestamp",
        ):
            with self.subTest(retarget_time=retarget_time):
                spec = self.base_approved_spec()
                spec["events"] = [
                    {"event": "base_ref_changed", "created_at": retarget_time}
                ]
                res = self.run_step(spec)
                self.assertEqual(
                    res["outputs"],
                    {"skip": "false", "verdict": "", "review_id": ""},
                )

    def test_does_not_skip_for_dismissed_advisory_diffline_or_unattested_reviews(
        self,
    ) -> None:
        # 1. Dismissed after approval on same head
        spec_dismissed = self.base_approved_spec()
        spec_dismissed["reviews"].append(
            {
                "id": 7009,
                "user": {"login": "github-actions[bot]"},
                "state": "DISMISSED",
                "commit_id": HEAD_SHA,
                "submitted_at": "2026-11-24T05:40:00Z",
                "body": "<!-- codex-comment-review -->\nDismissed",
            }
        )
        self.assertEqual(self.run_step(spec_dismissed)["outputs"]["skip"], "false")

        # 2. Advisory comment review without formal marker
        spec_advisory = self.base_approved_spec()
        spec_advisory["reviews"][0]["body"] = (
            "<!-- codex-advisory-review -->\nInformal"
        )
        self.assertEqual(self.run_step(spec_advisory)["outputs"]["skip"], "false")

        # 3. Diff-line review comment (no conversation @codex issue_comment)
        spec_diffline = self.base_approved_spec()
        spec_diffline["comments"] = []
        self.assertEqual(self.run_step(spec_diffline)["outputs"]["skip"], "false")

        # 4. Unattested review id (log names a different review)
        spec_wrong_id = self.base_approved_spec()
        spec_wrong_id["logsByJob"]["802"] = (
            "2026-11-24T05:35:35.4149261Z Codex approved review 9999.\n"
        )
        self.assertEqual(self.run_step(spec_wrong_id)["outputs"]["skip"], "false")

        # 5. Beyond preflight's 8-run attestation budget
        spec_over_budget = self.base_approved_spec()
        newer_runs = [
            {
                "id": 600 + i,
                "path": ".github/workflows/codex.yml",
                "event": "issue_comment",
                "created_at": f"2026-11-24T05:35:{40 + i:02d}Z",
            }
            for i in range(8)
        ]
        spec_over_budget["runsByStatus"]["success"] = (
            newer_runs + spec_over_budget["runsByStatus"]["success"]
        )
        self.assertEqual(self.run_step(spec_over_budget)["outputs"]["skip"], "false")

    def test_api_failure_falls_back_cleanly_to_fresh_review(self) -> None:
        for endpoint in ("pulls.listReviews", "listWorkflowRuns"):
            with self.subTest(endpoint=endpoint):
                spec = self.base_approved_spec()
                spec["throwOn"] = endpoint
                res = self.run_step(spec)
                self.assertEqual(
                    res["outputs"],
                    {"skip": "false", "verdict": "", "review_id": ""},
                )
                self.assertEqual(len(res["warnings"]), 1)

    def test_waits_briefly_when_issue_comment_run_is_still_finishing_verdict_job(
        self,
    ) -> None:
        spec = self.base_approved_spec()
        completed_run = spec["runsByStatus"]["success"]
        spec["runsByStatus"] = {}
        spec["runsSequenceByStatus"] = {
            "success": [[], completed_run],
            "in_progress": [completed_run, []],
            "queued": [[], []],
        }
        res = self.run_step(spec, extra_env={"CODEX_ATTEST_POLL_MS": "5"})
        self.assertEqual(
            res["outputs"],
            {"skip": "true", "verdict": "approved", "review_id": "7001"},
        )

    def test_uses_latest_formal_verdict_when_multiple_reviews_exist_on_head(
        self,
    ) -> None:
        spec = self.base_approved_spec()
        spec["reviews"].insert(
            0,
            {
                "id": 6990,
                "user": {"login": "github-actions[bot]"},
                "state": "CHANGES_REQUESTED",
                "commit_id": HEAD_SHA,
                "submitted_at": "2026-11-24T05:20:00Z",
                "body": "<!-- codex-comment-review -->\nEarlier rejection",
            },
        )
        res = self.run_step(spec)
        self.assertEqual(
            res["outputs"],
            {"skip": "true", "verdict": "approved", "review_id": "7001"},
        )


if __name__ == "__main__":
    unittest.main()
