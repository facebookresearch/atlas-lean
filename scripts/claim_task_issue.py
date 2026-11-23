#!/usr/bin/env python3
"""Apply a bounded claim on a managed Atlas task, using issue assignments as the display."""

from __future__ import annotations

import argparse
import json
import os
import re
import urllib.error
from pathlib import Path

if __package__:
    from .frontier_issues import BODY_END, GitHub, KINDS, marks
else:
    from frontier_issues import BODY_END, GitHub, KINDS, marks

COMMAND = re.compile(r"/(claim|unclaim)(?:[ \t]+([^\s]+))?")
LOGIN = re.compile(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}")
MODULE = re.compile(r"<!-- atlas-module: ([^\s<>]+) -->", re.MULTILINE)
LEDGER = re.compile(r"<!-- atlas-claims: (\{[^\n]*\}) -->")
STAFF = {"admin", "maintain", "write"}
MAX_HOLDERS = 10


def change(issue: dict, login: str, command: str, arg: str | None, staff: bool = False) -> tuple[dict | None, str]:
    """Return one issue PATCH (body and assignees together) plus a response."""
    key, _ = marks(issue)
    body = issue.get("body") or ""
    generated, delimiter, tail = body.partition(BODY_END)
    kind = "formalize" if key and key.startswith("field:") else "dag-work"
    labels = {label["name"] for label in issue.get("labels", [])}
    if not (key and key.startswith(("field:", "node:")) and delimiter and KINDS[kind] in labels):
        return None, ""
    saved = LEDGER.search(tail)
    try:
        held = json.loads(saved.group(1)) if saved else {}
    except json.JSONDecodeError:
        return None, "The claim record is malformed; ask a maintainer to inspect it."
    # Ignore malformed or manually removed reservations rather than guessing.
    if not isinstance(held, dict) or any(not isinstance(k, str) or not isinstance(v, str) or not LOGIN.fullmatch(v)
                                         for k, v in held.items()):
        return None, "The claim record is malformed; ask a maintainer to inspect it."
    assignees = {user["login"].casefold(): user["login"] for user in issue.get("assignees", [])}
    login = login.casefold()
    if command == "claim":
        if issue.get("state") != "open":
            return None, "This task is closed."
        if kind == "formalize":
            if arg not in set(MODULE.findall(generated)):
                return None, "Use `/claim <module page path>` with a module path listed in this issue."
            slot = arg
        else:
            if arg is not None:
                return None, "Use `/claim` without an argument on an expansion issue."
            slot = "dag-work"
        if slot in held:
            return None, "You already hold this claim." if held[slot] == login else f"Already claimed by @{held[slot]}."
        if login in held.values():
            return None, "Release your existing claim on this issue before taking another module."
        if kind == "dag-work" and set(assignees) - {login}:
            return None, "Someone is already assigned to this expansion."
        if login in assignees:
            return None, "You already have a manual assignment; ask a maintainer before converting it to a claim."
        if len(assignees) >= MAX_HOLDERS:
            return None, "This issue already has ten assignees."
        held[slot] = login
        assignees[login] = login
        message = "Claimed."
    else:
        if arg and (not arg.startswith("@") or not LOGIN.fullmatch(arg[1:])):
            return None, "Use `/unclaim` or, if you maintain the repository, `/unclaim @login`."
        target = arg[1:].casefold() if arg else login
        if target != login and not staff:
            return None, "Only a repository maintainer can release someone else's claim."
        if target not in held.values():
            return None, "No bot-recorded claim to release."
        for slot in [slot for slot, owner in held.items() if owner == target]:
            del held[slot]
        assignees.pop(target, None)
        message = "Released."
    tail = LEDGER.sub("", tail).rstrip()
    record = f"\n\n<!-- atlas-claims: {json.dumps(held, sort_keys=True, separators=(',', ':'))} -->" if held else ""
    return {"body": generated + delimiter + tail + record + "\n", "assignees": list(assignees.values())}, message


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", required=True, type=Path)
    parser.add_argument("--repo", required=True)
    args = parser.parse_args()
    event = json.loads(args.event.read_text(encoding="utf-8"))
    comment, issue = event.get("comment") or {}, event.get("issue") or {}
    user = comment.get("user") or {}
    login = user.get("login", "")
    lines = (comment.get("body") or "").splitlines()
    match = COMMAND.fullmatch(lines[0].strip()) if lines else None
    if not (event.get("action") == "created" and issue and not issue.get("pull_request")
            and user.get("type") == "User" and LOGIN.fullmatch(login) and match):
        return 0
    github = GitHub(args.repo, os.environ["GITHUB_TOKEN"], os.environ.get("GITHUB_API_URL", "https://api.github.com"), pause=0)
    verb, arg = match.groups()
    number = issue["number"]
    live = github.read_issue(number)
    staff = False
    if verb == "unclaim" and arg and arg.startswith("@") and arg[1:].casefold() != login.casefold():
        try:
            permission, _ = github.request("GET", f"/repos/{args.repo}/collaborators/{login}/permission")
        except urllib.error.HTTPError as error:
            if error.code != 404:
                raise
        else:
            staff = permission.get("role_name") in STAFF or permission.get("permission") in STAFF
    patch, message = change(live, login, verb, arg, staff)
    if patch:
        updated = github.update_issue(number, **patch)
        if verb == "claim" and login.casefold() not in {user["login"].casefold() for user in updated["assignees"]}:
            # GitHub can silently omit a user it cannot assign. Restore the ledger in that case.
            github.update_issue(number, body=live["body"])
            message = "GitHub could not assign you; the claim was not recorded."
    if message:
        github.request("POST", f"/repos/{args.repo}/issues/{number}/comments", {"body": f"@{login} {message}"})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
