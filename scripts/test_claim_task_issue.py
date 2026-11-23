import json
import unittest

from scripts.claim_task_issue import change
from scripts.frontier_issues import BODY_END


MODULE = "blueprint/roadmap/A/F/M/README.md"
OTHER = "blueprint/roadmap/A/F/N/README.md"


def issue(field=True):
    key, label = ("field:A/F", "task:formalize") if field else ("node:A/topic", "task:dag-work")
    return {
        "state": "open", "assignees": [], "labels": [{"name": label}],
        "body": f"<!-- atlas-task: {key} -->\n<!-- atlas-node: A/F -->\n"
                f"<!-- atlas-module: {MODULE} -->\n<!-- atlas-module: {OTHER} -->\n{BODY_END}\n\nMaintainer note\n",
    }


def apply(live, patch):
    return dict(live, body=patch["body"], assignees=[{"login": login} for login in patch["assignees"]])


class Claim(unittest.TestCase):
    def test_modules_are_exclusive_but_a_field_can_have_two_claimants(self):
        live = issue()
        patch, reply = change(live, "alice", "claim", MODULE)
        self.assertEqual(reply, "Claimed.")
        live = apply(live, patch)
        self.assertEqual(change(live, "bob", "claim", MODULE), (None, "Already claimed by @alice."))
        patch, _ = change(live, "bob", "claim", OTHER)
        self.assertEqual(patch["assignees"], ["alice", "bob"])
        self.assertIn("Maintainer note", patch["body"])

    def test_dag_work_honors_existing_manual_assignment(self):
        live = dict(issue(False), assignees=[{"login": "alice"}])
        self.assertIsNone(change(live, "bob", "claim", None)[0])
        self.assertIsNone(change(live, "alice", "unclaim", None)[0])

    def test_invalid_module_and_unmanaged_issue_are_not_written(self):
        self.assertIsNone(change(issue(), "alice", "claim", "does-not-exist")[0])
        self.assertEqual(change(dict(issue(), labels=[]), "alice", "claim", MODULE), (None, ""))
        self.assertIsNone(change(dict(issue(), state="closed"), "alice", "claim", MODULE)[0])

    def test_release_removes_only_the_bot_recorded_claim(self):
        live = dict(issue(), assignees=[{"login": "carol"}])
        patch, _ = change(live, "alice", "claim", MODULE)
        live = apply(live, patch)
        self.assertIsNone(change(live, "bob", "unclaim", "@alice")[0])
        patch, message = change(live, "bob", "unclaim", "@alice", staff=True)
        self.assertEqual(message, "Released.")
        self.assertEqual(patch["assignees"], ["carol"])
        self.assertNotIn("atlas-claims", patch["body"])
        self.assertIn("Maintainer note", patch["body"])

    def test_ledger_failures_leave_assignment_alone(self):
        for bad in ("{x}", json.dumps({MODULE: 42})):
            live = issue()
            live["body"] += f"<!-- atlas-claims: {bad} -->\n"
            self.assertIsNone(change(live, "alice", "claim", MODULE)[0])
