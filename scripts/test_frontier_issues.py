"""Frontier issues follow the built graph: one per task that can start now, kept in step and closed when done."""

from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import frontier_issues as fi

REPO = "facebookresearch/atlas-lean"
HAS_AUTOFORM = importlib.util.find_spec("autoform_cli") is not None


def task(key="node:A/b", kind="formalize", phase="proof", **extra) -> dict:
    base = {
        "key": key, "kind": kind, "phase": phase, "node_id": key.split(":", 1)[1], "article_id": None,
        "title": "Result B", "page": "blueprint/roadmap/A/b.md", "subject": "A", "statement": "B holds.",
        "declarations": ["X.b"], "dependencies": [], "unlocks": 0,
    }
    base.update(extra)
    return base


def frontier(*tasks, finished=()) -> dict:
    return {"schema": fi.SCHEMA, "commit": "0" * 40, "source_revision": "r", "tasks": list(tasks), "finished": list(finished)}


def issue(number, item=None, state="open", state_reason=None, title=None, body=None, labels=None, marks=None) -> dict:
    if marks is not None:
        body = "".join(f"<!-- atlas-{name}: {value} -->\n" for name, value in marks) + "old\n"
    return {
        "number": number, "state": state, "state_reason": state_reason,
        "title": title if title is not None else fi.issue_title(item),
        "body": body if body is not None else fi.issue_body(item, REPO),
        "labels": [{"name": name} for name in (labels if labels is not None else fi.issue_labels(item))],
    }


class Rendering(unittest.TestCase):
    def test_titles_say_what_to_do(self) -> None:
        self.assertEqual(fi.issue_title(task()), "Prove: Result B")
        self.assertEqual(fi.issue_title(task(phase="statement")), "State in Lean: Result B")
        self.assertEqual(fi.issue_title(task(kind="dag-work", phase=None)), "Expand: Result B")
        self.assertLessEqual(len(fi.issue_title(task(title="x" * 500))), fi.TITLE_LIMIT)

    def test_the_body_carries_its_marks_links_and_criteria(self) -> None:
        dependencies = [{"title": f"D{n}", "page": f"blueprint/roadmap/A/d{n}.md"} for n in range(25)]
        body = fi.issue_body(task(dependencies=dependencies, unlocks=3), REPO)
        self.assertIn("<!-- atlas-task: node:A/b -->", body)
        self.assertIn("<!-- atlas-node: A/b -->", body)
        self.assertIn("> B holds.", body)
        self.assertIn(f"https://github.com/{REPO}/blob/main/blueprint/roadmap/A/b.md", body)
        self.assertIn("`X.b`", body)
        self.assertIn("and 5 more", body)
        self.assertIn("3 unfinished node(s)", body)
        self.assertIn("`theorem_wanted` is gone", body)
        self.assertIn("`unexpanded` marker is gone", fi.issue_body(task(kind="dag-work", phase=None), REPO))

    def test_a_module_issue_lists_its_ready_results(self) -> None:
        items = [{"title": f"R{n}", "page": f"blueprint/roadmap/A/r{n}.md", "phase": "proof" if n else "statement",
                  "declarations": [f"X.r{n}"], "unlocks": 0} for n in range(fi.ITEM_LIMIT + 3)]
        module = task("module:A", phase="module", title="Module A", items=items, declarations=[], statement="")
        self.assertEqual(fi.issue_title(module), "Formalize: Module A")
        body = fi.issue_body(module, REPO)
        self.assertIn(f"Ready now ({fi.ITEM_LIMIT + 3})", body)
        self.assertIn("- [ ] State [R0]", body)
        self.assertIn("- [ ] Prove [R1]", body)
        self.assertIn("(`X.r1`)", body)
        self.assertIn("and 3 more on the module page", body)
        self.assertIn("the issue closes when nothing in the module is ready", body)

    def test_labels_name_the_kind_the_graph_and_the_area(self) -> None:
        self.assertEqual(fi.issue_labels(task()), ["task:formalize", "math graph", "area:A"])
        self.assertEqual(fi.issue_labels(task(kind="dag-work", subject=None)), ["task:dag-work", "math graph"])


class Planning(unittest.TestCase):
    def plan(self, data, issues, labels=("task:formalize", "task:dag-work", "math graph", "area:A")):
        return fi.plan_sync(data, issues, set(labels), REPO)

    def test_a_new_task_gets_an_issue_and_missing_labels_are_created(self) -> None:
        plan = self.plan(frontier(task()), [], labels=())
        self.assertEqual([t["key"] for t in plan.create], ["node:A/b"])
        self.assertEqual(plan.labels, ["area:A", "math graph", "task:dag-work", "task:formalize"])

    def test_an_issue_in_step_is_left_alone(self) -> None:
        item = task()
        plan = self.plan(frontier(item), [issue(1, item, labels=fi.issue_labels(item) + ["help wanted"])])
        self.assertEqual((plan.unchanged, plan.writes()), (1, 0))

    def test_a_changed_task_updates_its_issue(self) -> None:
        old, new = task(statement="Old."), task(statement="New.")
        plan = self.plan(frontier(new), [issue(1, old)])
        self.assertEqual([(i["number"], t["statement"]) for i, t in plan.update], [(1, "New.")])

    def test_an_issue_is_found_by_its_node_when_the_task_key_changes(self) -> None:
        old = task()
        new = task(key="decl:X.b_renamed", declarations=["X.b_renamed"], node_id="A/b")
        plan = self.plan(frontier(new), [issue(1, old)])
        self.assertEqual(len(plan.update), 1)
        self.assertEqual(plan.create, [])

    def test_a_task_off_the_frontier_closes_its_issue(self) -> None:
        done, moved = task("node:A/done"), task("node:A/moved")
        plan = self.plan(frontier(finished=["node:A/done"]), [issue(1, done), issue(2, moved)])
        self.assertEqual([(i["number"], reason) for i, reason in plan.close], [(1, "completed"), (2, "not_planned")])

    def test_issues_without_marks_and_closed_issues_are_not_closed(self) -> None:
        plan = self.plan(frontier(), [issue(1, body="written by a person", title="t", labels=["task:formalize"]),
                                      issue(2, task(), state="closed", state_reason="completed")])
        self.assertEqual(plan.close, [])

    def test_a_task_back_on_the_frontier_reopens_its_issue_unless_declined(self) -> None:
        back, declined = task("node:A/back"), task("node:A/no")
        plan = self.plan(frontier(back, declined), [
            issue(1, back, state="closed", state_reason="completed"),
            issue(2, declined, state="closed", state_reason="not_planned"),
        ])
        self.assertEqual([i["number"] for i, _ in plan.reopen], [1])
        self.assertEqual((plan.declined, plan.create), (1, []))

    def test_a_task_blocked_for_a_while_gets_its_issue_back(self) -> None:
        item = task()
        open_issue = issue(1, item)
        plan = self.plan(frontier(), [open_issue])
        self.assertEqual([(i["number"], reason) for i, reason in plan.close], [(1, "not_planned")])
        github = FakeGitHub()
        fi.apply_plan(plan, github, REPO, max_writes=10)
        closed = dict(open_issue, state="closed", state_reason="not_planned",
                      body=github.calls[-1][5])
        self.assertIn(fi.OFF_FRONTIER, closed["body"])
        plan = self.plan(frontier(item), [closed])
        self.assertEqual(([i["number"] for i, _ in plan.reopen], plan.declined), ([1], 0))

    def test_managed_labels_follow_the_task_and_other_labels_stay(self) -> None:
        old = task(kind="dag-work", phase=None, subject="B")
        new = task(subject="A")
        stale = issue(1, old, labels=fi.issue_labels(old) + ["help wanted"])
        plan = self.plan(frontier(new), [stale])
        self.assertEqual(len(plan.update), 1)
        self.assertEqual(fi.merged_labels(stale, new), ["area:A", "help wanted", "math graph", "task:formalize"])

    def test_a_page_taking_over_an_old_path_does_not_take_another_articles_issue(self) -> None:
        moved = task(key="decl:X.moved", declarations=["X.moved"], node_id="A/moved", page="blueprint/roadmap/A/moved.md")
        newcomer = task(key="node:A/b", node_id="A/b", title="Another result")
        held = issue(1, dict(moved, node_id="A/b"))
        plan = self.plan(frontier(moved, newcomer), [held])
        self.assertEqual([(i["number"], t["key"]) for i, t in plan.update], [(1, moved["key"])])
        self.assertEqual([t["key"] for t in plan.create], ["node:A/b"])

    def test_an_issue_keyed_by_an_article_id_is_kept_when_ids_go_away(self) -> None:
        # Keys used to prefer article ids; an issue with such a key still matches its task by path.
        item = task(key="decl:X.b", node_id="A/b")
        held = issue(1, item, marks=[("task", "article:af_" + "2" * 24), ("node", "A/b")])
        plan = self.plan(frontier(item), [held])
        self.assertEqual(([i["number"] for i, _ in plan.update], plan.create, plan.close), ([1], [], []))

    def test_a_proved_result_with_a_new_name_closes_its_issue_as_completed(self) -> None:
        item = task(key="decl:X.b_wanted", node_id="A/b")
        plan = self.plan(frontier(finished=["decl:X.b", "node:A/b"]), [issue(1, item)])
        self.assertEqual([(i["number"], reason) for i, reason in plan.close], [(1, "completed")])

    def test_a_duplicate_issue_is_closed(self) -> None:
        item = task()
        plan = self.plan(frontier(item), [issue(1, item), issue(2, item)])
        self.assertEqual(plan.unchanged, 1)
        self.assertEqual([(i["number"], reason) for i, reason in plan.close], [(1, "not_planned")])

    def test_a_frontier_of_another_schema_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            self.plan({"schema": "other", "tasks": []}, [])


class FakeGitHub:
    def __init__(self, limit_after: int | None = None) -> None:
        self.calls: list[tuple] = []
        self.limit_after = limit_after

    def _record(self, *call) -> dict:
        if self.limit_after is not None and len(self.calls) >= self.limit_after:
            raise fi.RateLimited("limit")
        self.calls.append(call)
        return {}

    def create_label(self, name, color):
        return self._record("label", name, color)

    def create_issue(self, title, body, labels):
        return self._record("create", title, tuple(labels))

    def update_issue(self, number, **fields):
        return self._record("update", number, fields.get("state"), fields.get("state_reason"),
                            tuple(fields.get("labels", ())), fields.get("body"))


class Applying(unittest.TestCase):
    def plan(self) -> fi.Plan:
        changed, gone = task("node:A/changed", statement="New."), task("node:A/gone")
        stale = issue(1, task("node:A/changed", statement="Old."), labels=["task:formalize", "triage"])
        return fi.plan_sync(
            frontier(changed, task("node:A/new1"), task("node:A/new2")),
            [stale, issue(2, gone)], {"task:formalize", "math graph"}, REPO,
        )

    def test_closes_then_updates_then_creates_keeping_other_labels(self) -> None:
        github = FakeGitHub()
        self.assertEqual(fi.apply_plan(self.plan(), github, REPO, max_writes=100), 6)
        self.assertEqual([call[0] for call in github.calls], ["label", "label", "update", "update", "create", "create"])
        self.assertEqual([call[1] for call in github.calls[:2]], ["area:A", "task:dag-work"])
        self.assertEqual(github.calls[2][:4], ("update", 2, "closed", "not_planned"))
        self.assertEqual(github.calls[3][:3], ("update", 1, "open"))
        self.assertIn("triage", github.calls[3][4])
        self.assertEqual([call[1] for call in github.calls[4:]], ["Prove: Result B", "Prove: Result B"])

    def test_writes_stop_at_the_cap_and_at_a_rate_limit(self) -> None:
        github = FakeGitHub()
        self.assertEqual(fi.apply_plan(self.plan(), github, REPO, max_writes=3), 3)
        limited = FakeGitHub(limit_after=2)
        messages: list[str] = []
        self.assertEqual(fi.apply_plan(self.plan(), limited, REPO, max_writes=100, log=messages.append), 2)
        self.assertIn("the next run continues", messages[0])

    def test_the_summary_counts_every_action(self) -> None:
        summary = fi.summarize(self.plan(), frontier(task()), None, 400)
        self.assertIn("dry run: nothing was written", summary)
        self.assertIn("| open issues | 2 |", summary)
        self.assertIn("| close issues | 1 |", summary)


DAY = 86400.0
NOW = fi.parse_time("2026-11-20T00:00:00Z")


def assigned(login, when):
    return {"event": "assigned", "assignee": {"login": login}, "created_at": when}


def referenced(state):
    return {"event": "cross-referenced", "source": {"type": "issue", "issue": {"pull_request": {"url": "x"}, "state": state}}}


class LapsedClaims(unittest.TestCase):
    def held(self, *logins, state="open"):
        return dict(issue(1, task()), state=state, assignees=[{"login": login} for login in logins])

    def test_a_claim_lapses_after_seven_days_without_an_open_pr(self) -> None:
        timeline = [assigned("ada", "2026-11-10T00:00:00Z"), assigned("bob", "2026-11-18T00:00:00Z"), referenced("closed")]
        self.assertEqual(fi.stale_claims(self.held("ada", "bob"), timeline, NOW), ["ada"])

    def test_an_open_pr_keeps_every_claim(self) -> None:
        timeline = [assigned("ada", "2026-11-01T00:00:00Z"), referenced("open")]
        self.assertEqual(fi.stale_claims(self.held("ada"), timeline, NOW), [])

    def test_the_latest_assignment_counts_and_closed_issues_are_left_alone(self) -> None:
        timeline = [assigned("ada", "2026-11-01T00:00:00Z"), assigned("ada", "2026-11-19T00:00:00Z")]
        self.assertEqual(fi.stale_claims(self.held("ada"), timeline, NOW), [])
        self.assertEqual(fi.stale_claims(self.held("ada", state="closed"), [assigned("ada", "2026-11-01T00:00:00Z")], NOW), [])

    def test_releases_skip_issues_being_closed_and_issues_without_marks(self) -> None:
        plan = fi.Plan()
        kept, closing = dict(self.held("ada"), number=1), dict(self.held("ada"), number=2)
        unmarked = dict(self.held("ada"), number=3, body="by hand")
        plan.close.append((closing, "completed"))
        old = [assigned("ada", "2026-11-01T00:00:00Z")]
        fi.plan_releases(plan, [kept, closing, unmarked], lambda number: old, NOW)
        self.assertEqual([(i["number"], logins) for i, logins in plan.release], [(1, ["ada"])])
        read: list[int] = []
        fi.plan_releases(fi.Plan(), [dict(kept, number=n, updated_at=f"2026-11-0{n}") for n in (3, 1, 2)],
                         lambda number: read.append(number) or old, NOW, limit=2)
        self.assertEqual(read, [1, 2])

    def test_a_release_unassigns_and_says_why(self) -> None:
        class Recorder(FakeGitHub):
            def unassign(self, number, logins):
                return self._record("unassign", number, tuple(logins))

            def comment(self, number, body):
                return self._record("comment", number, body)

        plan = fi.Plan(release=[(self.held("ada"), ["ada"])])
        github = Recorder()
        self.assertEqual(fi.apply_plan(plan, github, REPO, max_writes=10), 2)
        self.assertEqual(github.calls[0], ("unassign", 1, ("ada",)))
        self.assertIn("Released the claim of @ada", github.calls[1][2])
        self.assertEqual(fi.apply_plan(plan, Recorder(), REPO, max_writes=1), 0)


class Command(unittest.TestCase):
    def test_sync_needs_a_token(self) -> None:
        with tempfile.TemporaryDirectory() as directory, patch.dict("os.environ", {}, clear=True):
            path = Path(directory) / "frontier.json"
            path.write_text(json.dumps(frontier()))
            self.assertEqual(fi.main(["sync", str(path), "--repo", REPO]), 2)


def comment_event(body="/claim", login="ada", association="CONTRIBUTOR", assignees=(), labels=("task:formalize",),
                  state="open", pull_request=False, user_type="User") -> dict:
    issue = {"number": 7, "state": state, "labels": [{"name": name} for name in labels],
             "assignees": [{"login": name} for name in assignees]}
    if pull_request:
        issue["pull_request"] = {"url": "x"}
    return {"action": "created", "issue": issue,
            "comment": {"id": 99, "body": body, "author_association": association, "user": {"login": login, "type": user_type}}}


class Claims(unittest.TestCase):
    def test_claim_assigns_a_free_task(self) -> None:
        self.assertEqual(fi.decide_claim(comment_event()), fi.ClaimDecision(add="ada", react=True))
        self.assertEqual(fi.decide_claim(comment_event("/claim\n\nI'll take it.")), fi.ClaimDecision(add="ada", react=True))

    def test_claim_of_a_held_task_says_who_holds_it(self) -> None:
        decision = fi.decide_claim(comment_event(assignees=["bob"]))
        self.assertIsNone(decision.add)
        self.assertIn("already claimed by @bob", decision.reply)
        self.assertIn("`/unclaim @bob`", decision.reply)
        self.assertEqual(fi.decide_claim(comment_event(assignees=["ada"])), fi.ClaimDecision(react=True))

    def test_claim_is_for_yourself_and_for_open_tasks(self) -> None:
        self.assertIn("@bob can claim it", fi.decide_claim(comment_event("/claim @bob")).reply)
        self.assertIn("closed", fi.decide_claim(comment_event(state="closed")).reply)

    def test_unclaim_releases_your_own_task_and_maintainers_free_others(self) -> None:
        self.assertEqual(fi.decide_claim(comment_event("/unclaim", assignees=["ada"])), fi.ClaimDecision(remove="ada", react=True))
        self.assertIn("only a maintainer", fi.decide_claim(comment_event("/unclaim @bob", assignees=["bob"])).reply)
        # Organization membership is not enough; the caller checks the repository role.
        self.assertIn("only a maintainer",
                      fi.decide_claim(comment_event("/unclaim @bob", association="MEMBER", assignees=["bob"])).reply)
        self.assertEqual(fi.decide_claim(comment_event("/unclaim @Bob", assignees=["bob"]), maintainer=True),
                         fi.ClaimDecision(remove="bob", react=True))
        self.assertIn("does not hold", fi.decide_claim(comment_event("/unclaim")).reply)

    def test_other_comments_and_issues_are_ignored(self) -> None:
        for event in (comment_event("please /claim"), comment_event("/claimed"), comment_event("/claim now please"),
                      comment_event(labels=("bug",)), comment_event(pull_request=True), comment_event(user_type="Bot")):
            self.assertIsNone(fi.decide_claim(event), event["comment"]["body"])

    def test_applying_a_claim_assigns_and_reacts_or_explains(self) -> None:
        class Recorder:
            repo = REPO

            def __init__(self, assigned):
                self.calls, self.assigned = [], assigned

            def request(self, method, path, payload=None):
                self.calls.append((method, path, payload))
                if path.endswith("/assignees") and method == "POST":
                    return {"assignees": [{"login": name} for name in self.assigned]}, {}
                return {}, {}

        event = comment_event()
        github = Recorder(["ada"])
        fi.apply_claim(fi.ClaimDecision(add="ada", react=True), event, github)
        self.assertEqual([call[:2] for call in github.calls], [
            ("POST", f"/repos/{REPO}/issues/7/assignees"), ("POST", f"/repos/{REPO}/issues/comments/99/reactions")])
        github = Recorder([])
        fi.apply_claim(fi.ClaimDecision(add="ada", react=True), event, github)
        self.assertEqual(github.calls[-1][1], f"/repos/{REPO}/issues/7/comments")
        self.assertIn("would not assign you", github.calls[-1][2]["body"])
        github = Recorder([])
        fi.apply_claim(fi.ClaimDecision(remove="ada", react=True), event, github)
        self.assertEqual(github.calls[0][:2], ("DELETE", f"/repos/{REPO}/issues/7/assignees"))

    def test_the_command_decides_on_the_current_issue_and_the_commenters_role(self) -> None:
        class Current:
            calls: list = []

            def __init__(self, repo, token, api, pause):
                self.repo = repo

            def request(self, method, path, payload=None):
                Current.calls.append((method, path))
                if path.endswith("/issues/7"):
                    # Since the event was captured, bob claimed the task.
                    return comment_event(assignees=["bob"])["issue"], {}
                if path.endswith("/collaborators/ada/permission"):
                    return {"permission": "read", "role_name": "triage"}, {}
                return {}, {}

        with tempfile.TemporaryDirectory() as directory, patch.dict("os.environ", {"GITHUB_TOKEN": "t"}), \
                patch.object(fi, "GitHub", Current):
            path = Path(directory) / "event.json"
            path.write_text(json.dumps(comment_event()))
            self.assertEqual(fi.main(["claim", "--event", str(path), "--repo", REPO]), 0)
            self.assertEqual(Current.calls[0], ("GET", f"/repos/{REPO}/issues/7"))
            self.assertEqual(Current.calls[-1], ("POST", f"/repos/{REPO}/issues/7/comments"))  # already claimed by bob
            Current.calls.clear()
            path.write_text(json.dumps(comment_event("/unclaim @bob", association="MEMBER")))
            fi.main(["claim", "--event", str(path), "--repo", REPO])
            self.assertIn(("GET", f"/repos/{REPO}/collaborators/ada/permission"), Current.calls)
            self.assertNotIn(("DELETE", f"/repos/{REPO}/issues/7/assignees"), Current.calls)

    def test_the_workflow_runs_from_the_default_branch_with_only_issue_writes(self) -> None:
        import yaml

        workflow = yaml.load((Path(fi.__file__).resolve().parent.parent / ".github/workflows/claim.yml").read_text(),
                             Loader=yaml.BaseLoader)
        self.assertEqual(list(workflow["on"]), ["issue_comment"])
        self.assertEqual(workflow["permissions"], {})
        job = workflow["jobs"]["claim"]
        self.assertEqual(job["permissions"], {"contents": "read", "issues": "write"})
        self.assertIn("github.event.issue.pull_request == null", job["if"])
        self.assertEqual(job["steps"][0]["with"]["persist-credentials"], "false")
        self.assertNotIn("comment.body", job["steps"][-1]["run"])
        for step in job["steps"]:
            if "uses" in step:
                self.assertRegex(step["uses"], r"@[0-9a-f]{40}\Z")


@unittest.skipUnless(HAS_AUTOFORM, "needs Autoform, as the wiki build installs it")
class Frontier(unittest.TestCase):
    """A built vault, as lean-facts leaves it: a proved definition, a stated theorem resting on it, a stated
    theorem whose proof rests on that one, a wanted definition, and a node marked unexpanded."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.blueprint = root / "blueprint"
        pages = {
            "README.md": "# ATLAS roadmap\n\n- [Topoi](T/README.md)\n",
            "T/README.md": "# Topoi\n\n- [Topos](topos.md)\n- [Slice](slice.md)\n- [Deep](deep.md)\n- [Jacobian](jacobian.md)\n- [Hodge](hodge.md)\n- [Second module](second/README.md)\n",
            "T/topos.md": "# Topos\n\nA topos.\n\n## Depends on\n\nThis node has no prerequisites.\n",
            "T/slice.md": "# Slice\n\nSlices are toposes.\n\n## Depends on\n\n- [Topos](topos.md)\n",
            "T/deep.md": "# Deep\n\nDeeper.\n\n## Depends on\n\nThis node has no prerequisites.\n\n## Proof depends on\n\n- [Slice](slice.md)\n",
            "T/jacobian.md": "# Jacobian\n\nThe Jacobian.\n\n## Depends on\n\nThis node has no prerequisites.\n",
            "T/hodge.md": "# Hodge\n\nTo expand.\n",
            "T/second/README.md": "# Second module\n\n- [Part 1](part-01/README.md)\n",
            "T/second/part-01/README.md": "# Part 1 of 1\n\n- [Far](far.md)\n",
            "T/second/part-01/far.md": "# Far\n\nFar away.\n\n## Depends on\n\nThis node has no prerequisites.\n",
        }
        for name, text in pages.items():
            path = self.blueprint / "roadmap" / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

        def row(page, declaration=None, **extra):
            entry = {"subject": [{"type": "generic", "uri": f"../roadmap/{page}"}]}
            if declaration:
                entry["object"] = [{"location": {"declaration": declaration}}]
            entry.update(extra)
            return entry

        rows = {
            "roadmap": [row("README.md")],
            "T": [
                row("T/README.md", extensions={"org.autoform": {"navigation": "module"}}),
                row("T/second/README.md", extensions={"org.autoform": {"navigation": "module"}}),
                row("T/second/part-01/README.md", extensions={"org.autoform": {"navigation": "transparent"}}),
                row("T/second/part-01/far.md", "X.far", kind="theorem", status="stated"),
                row("T/topos.md", "X.Topos", kind="def", status="formalized", id="af_" + "1" * 24),
                row("T/slice.md", "X.slice", kind="theorem", status="stated"),
                row("T/deep.md", "X.deep", kind="theorem", status="stated"),
                row("T/jacobian.md", "X.Jacobian", kind="def"),
                row("T/hodge.md", extensions={fi.OWN: {fi.UNEXPANDED: True}}),
            ],
        }
        (self.blueprint / "links").mkdir()
        (self.blueprint / "links" / "_defaults.json").write_text(json.dumps({"object": {"type": "lean", "uri": "../.."}}) + "\n")
        for name, entries in rows.items():
            (self.blueprint / "links" / f"{name}.jsonl").write_text("".join(json.dumps(e) + "\n" for e in entries))

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def test_the_frontier_holds_one_issue_per_module_and_per_node_to_expand(self) -> None:
        result = fi.build_frontier(self.blueprint, "abc")
        tasks = {t["key"]: t for t in result["tasks"]}
        self.assertEqual(set(tasks), {"module:T", "module:T/second", "node:T/hodge"})
        topoi = tasks["module:T"]
        self.assertEqual((topoi["kind"], topoi["phase"], topoi["title"]), ("formalize", "module", "Topoi"))
        self.assertEqual([(i["title"], i["phase"]) for i in topoi["items"]], [("Slice", "proof"), ("Jacobian", "statement")])
        self.assertEqual(topoi["items"][0]["declarations"], ["X.slice"])
        self.assertEqual((topoi["unlocks"], topoi["subject"], topoi["page"]), (1, "T", "blueprint/roadmap/T/README.md"))
        # A module split into parts is still one module.
        self.assertEqual([i["title"] for i in tasks["module:T/second"]["items"]], ["Far"])
        self.assertEqual((tasks["node:T/hodge"]["kind"], tasks["node:T/hodge"]["phase"]), ("dag-work", None))
        self.assertIn("decl:X.Topos", result["finished"])
        self.assertIn("node:T/topos", result["finished"])
        self.assertNotIn("module:T", result["finished"])  # Deep is unfinished, though not ready
        self.assertEqual(result["tasks"][0]["key"], "module:T")  # what it unblocks comes first

    def test_a_module_with_nothing_left_is_finished(self) -> None:
        links = self.blueprint / "links" / "T.jsonl"
        links.write_text(links.read_text().replace('"status": "stated"}', '"status": "formalized"}')
                         .replace('"X.far"}}], "kind": "theorem"', '"X.far"}}], "kind": "theorem"'))
        result = fi.build_frontier(self.blueprint, "abc")
        self.assertIn("module:T/second", result["finished"])
        self.assertNotIn("module:T/second", {t["key"] for t in result["tasks"]})

    def test_two_pages_for_one_declaration_are_one_task(self) -> None:
        page = self.blueprint / "roadmap" / "T" / "slice-again.md"
        page.write_text("# Slice again\n\nSlices are toposes.\n\n## Depends on\n\n- [Topos](topos.md)\n")
        readme = self.blueprint / "roadmap" / "T" / "README.md"
        readme.write_text(readme.read_text() + "- [Slice again](slice-again.md)\n")
        links = self.blueprint / "links" / "T.jsonl"
        row = {"subject": [{"type": "generic", "uri": "../roadmap/T/slice-again.md"}],
               "object": [{"location": {"declaration": "X.slice"}}], "kind": "theorem", "status": "stated"}
        links.write_text(links.read_text() + json.dumps(row) + "\n")
        topoi = next(t for t in fi.build_frontier(self.blueprint, "abc")["tasks"] if t["key"] == "module:T")
        self.assertEqual([i["declarations"] for i in topoi["items"]].count(["X.slice"]), 1)

    def test_the_command_writes_the_frontier(self) -> None:
        output = Path(self.tmp.name) / "build" / "frontier.json"
        self.assertEqual(fi.main(["frontier", str(self.blueprint), "--output", str(output), "--commit", "abc"]), 0)
        self.assertEqual(json.loads(output.read_text())["schema"], fi.SCHEMA)


if __name__ == "__main__":
    unittest.main()
