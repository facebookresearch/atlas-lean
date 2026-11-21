#!/usr/bin/env python3
"""Print the next ready formalization tasks of ATLAS that no pull request has taken.

    python3 scripts/next_task.py [-n N] [--json] [--tasks FILE_OR_URL] [--repo OWNER/NAME]

The site publishes tasks.json: the articles Autoform finds ready to state or to prove (docs/BLUEPRINT.md,
What the tools own), as `autoform work list --json` lists them on the last main build, with the commit they come
from. This script downloads it, or reads a local copy, and lists through the GitHub API the repository's open pull
requests, whatever their base, and those merged into main since that commit, whose work tasks.json may not show yet:
GitHub's times are to the second, so one merged in the commit's second counts too.
Such a pull request takes a task when its title, body or branch name holds, as a whole word:

- the task's article id (af_...), or one of its Lean declarations in full; or
- the end of such a declaration, its last components (`Faltings.genus`) or its last one alone (`fejer` for
  `MathlibExt.Analysis.FourierConvergenceWanted.Analysis.fejer`), when no other task's declaration ends the same
  way (two end with `JacobianChallenge.genus`, so that takes neither) and it is in the title, the branch name or code
  (a fenced block or a code span, as Markdown reads them, in a quote or a list too). A last
  component alone also has to hold an underscore or a digit, or come with another component of the declaration
  that at most five tasks' declarations share (`FourierConvergenceWanted`, say). Older pull requests name the
  declaration they prove that way; a common word alone, such as `c` or `add`, takes nothing.

In code a name counts as written, but for a dot after it (`Foo.bar.{u}`); in prose it also counts without a stop after
it and without the quotes or the emphasis around it. A prime is part of a name, and `_root_.` before one changes
nothing.

Of the free tasks it prints the next N: the statements still to write first, as they are what the results still
waiting are waiting for, then the proofs, each in tasks.json's order, which is by article path. --json prints them
for agents, with Autoform's fields.

The GitHub API needs no token, within its limit of 60 requests an hour from one address; when GH_TOKEN (or
GITHUB_TOKEN) is set, every request to it sends that token, and a redirect away from it drops the token. Only the
Python standard library is used.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

TASKS = "https://facebookresearch.github.io/atlas-lean/tasks.json"
REPOSITORY = "facebookresearch/atlas-lean"
API = "https://api.github.com"
# The branch tasks.json is built from, whose merged pull requests are read.
MAIN = "main"
# The `autoform work list --json` format tasks.json has; another one may mean other fields.
SCHEMA = "autoform-work/v2"
PER_PAGE = 100
# Open pull requests are read a page at a time, and closed ones newest first until they predate tasks.json's
# commit; at most this many pages of each.
OPEN_PAGES = 30
CLOSED_PAGES = 30
# A component of a declaration shared by at most this many tasks' declarations is specific enough to say which
# task a short name means (see taken).
RARE = 5
# An article id, and a run of the characters a Lean name is written with, dots, primes, "!" and "?" included.
ARTICLE_ID = re.compile(r"(?<![0-9A-Za-z])af_[0-9a-f]{24}(?![0-9A-Za-z])", re.IGNORECASE)
WORD = re.compile(r"[\w.'!?]+")
# Markdown code, as CommonMark reads it: a fence of three or more backticks or tildes, indented by at most three
# spaces, maybe in a quote (>) or after a list marker, opens a block, which a fence of the same character, at least as
# long and indented by at most three spaces, closes, as does the end of the quote that holds it; in a paragraph, a run
# of backticks that no backslash escapes opens a code span, which the next run of the same length closes. A line
# indented by four spaces or more opens no block: such code is read as prose, which takes fewer tasks.
QUOTE = re.compile(r" {0,3}> ?")
FENCE = re.compile(r" {0,3}(?:(?:[-*+]|\d{1,9}[.)]) {1,4})?(`{3,}|~{3,})")
SPAN = re.compile(r"(?<!`)(`+)(?!`)(.+?)(?<!`)\1(?!`)", re.DOTALL)


class Failure(Exception):
    """Why the script stops, for its reader."""


class SameOriginRedirects(urllib.request.HTTPRedirectHandler):
    """Follow a redirect, without the token when it leads away from the GitHub API."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        new = super().redirect_request(req, fp, code, msg, headers, newurl)
        if new is not None and urllib.parse.urlsplit(newurl)[:2] != urllib.parse.urlsplit(API)[:2]:
            new.remove_header("Authorization")
        return new


OPENER = urllib.request.build_opener(SameOriginRedirects)


def request(url: str, token: str | None = None) -> bytes:
    """The body *url* answers with, compressed on the way when the server can; only a request to the GitHub API
    sends *token*."""
    headers = {"User-Agent": "atlas-next-task", "Accept-Encoding": "gzip"}
    if url.startswith(API + "/"):
        headers.update({"Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"})
        if token:
            headers["Authorization"] = f"Bearer {token}"
    try:
        with OPENER.open(urllib.request.Request(url, headers=headers), timeout=60) as response:
            body = response.read()
            return gzip.decompress(body) if response.headers.get("Content-Encoding") == "gzip" else body
    except urllib.error.HTTPError as error:
        if error.code in (403, 429) and error.headers.get("X-RateLimit-Remaining") == "0":
            reset = error.headers.get("X-RateLimit-Reset", "")
            when = (datetime.fromtimestamp(int(reset), timezone.utc).strftime(" until %H:%M UTC")
                    if reset.isdigit() else "")
            raise Failure(f"GitHub's API limit is used up{when}; set GH_TOKEN to a GitHub token to read it with a "
                          "higher limit") from None
        raise Failure(f"{url}: HTTP {error.code} {error.reason}") from None
    except OSError as error:
        # URLError, a timeout or a dropped connection.
        raise Failure(f"{url}: {getattr(error, 'reason', None) or error}") from None


def load_tasks(source: str) -> dict:
    """tasks.json from a URL or a file, checked to be an `autoform work list --json` list."""
    try:
        data = request(source) if re.match(r"https?://", source) else Path(source).read_bytes()
        tasks = json.loads(data)
    except OSError as error:
        raise Failure(f"{source}: {error.strerror or error}") from None
    except ValueError:
        raise Failure(f"{source} is not JSON") from None
    if not isinstance(tasks, dict) or tasks.get("schema") != SCHEMA or not isinstance(tasks.get("items"), list):
        raise Failure(f"{source} is not a task list as `autoform work list --json` writes it ({SCHEMA})")
    items = tasks["items"]
    if not items:
        raise Failure(f"{source} lists no task")
    if not all(map(usable, items)):
        raise Failure(f"{source} holds a task without its node, article id, ready phase or Lean declarations")
    for key in ("node_id", "article_id"):
        if len({item[key] for item in items}) != len(items):
            raise Failure(f"{source} gives two tasks one {key}")
    commit = tasks.get("commit")
    if commit is not None and not isinstance(commit, str):
        raise Failure(f"{source}: its commit {commit!r} is not a commit name")
    date = tasks.get("commit_date")
    if date is not None:
        try:
            dated = isinstance(date, str) and moment(date).tzinfo is not None
        except ValueError:
            dated = False
        if not dated:
            raise Failure(f"{source}: its commit_date {date!r} is not a time with its offset")
    return tasks


def usable(item: object) -> bool:
    """Whether a task is one Autoform writes, with what this script reads: a node, an article id, a ready phase and
    the Lean declarations, which only a statement still to write may lack. The publication step checks the same."""
    return (isinstance(item, dict) and isinstance(item.get("node_id"), str) and item["node_id"].strip() != ""
            and isinstance(item.get("article_id"), str)
            and re.fullmatch(r"af_[0-9a-f]{24}", item["article_id"]) is not None
            and item.get("ready") is True
            and (item.get("phase"), item.get("state")) in (("statement", "can_state"), ("proof", "can_prove"))
            and isinstance(item.get("lean_targets"), list) and (item["lean_targets"] != [] or item["phase"] != "proof")
            and all(isinstance(target, dict) and isinstance(target.get("declaration"), str)
                    and target["declaration"].strip() != "" for target in item["lean_targets"]))


def moment(text: str) -> datetime:
    """A time as GitHub and Git write it, with its offset."""
    return datetime.fromisoformat(text.replace("Z", "+00:00"))


def pull_requests(repository: str, since: str | None, token: str | None) -> list[dict]:
    """The repository's open pull requests, whatever their base, and, when *since* is a time, those merged into MAIN
    after it."""
    def page(query: str, number: int) -> list[dict]:
        url = f"{API}/repos/{repository}/pulls?{query}&per_page={PER_PAGE}&page={number}"
        try:
            rows = json.loads(request(url, token))
        except ValueError:
            rows = None
        if not isinstance(rows, list):
            raise Failure(f"{url} did not list pull requests")
        return rows

    found: list[dict] = []
    for number in range(1, OPEN_PAGES + 1):
        rows = page("state=open", number)
        found += rows
        if len(rows) < PER_PAGE:
            break
    else:
        raise Failure(f"{repository} has more than {OPEN_PAGES * PER_PAGE} open pull requests, more than this script "
                      "reads")
    if since:
        cutoff = moment(since)
        for number in range(1, CLOSED_PAGES + 1):
            rows = page("state=closed&sort=updated&direction=desc", number)
            # The commit's second counts, as the commit and GitHub's merge times are both to the second.
            found += [row for row in rows if row.get("merged_at") and moment(row["merged_at"]) >= cutoff
                      and (row.get("base") or {}).get("ref") == MAIN]
            # A pull request merged at or after the cutoff was updated at or after it too.
            if len(rows) < PER_PAGE or moment(rows[-1]["updated_at"]) < cutoff:
                break
        else:
            raise Failure(f"more than {CLOSED_PAGES * PER_PAGE} pull requests were closed after {since}, when "
                          "tasks.json was computed, more than this script reads; use a newer tasks.json")
    return found


def words(text: str, code: bool = False) -> set[str]:
    """The whole words of *text* that could be Lean names. In code a word counts as written but for the dots after it
    (as in `Foo.bar.{u}`), as "?" and "!" can end a Lean name. In prose it also counts without a stop after it,
    without its quotes when it is quoted, and without the underscores around it when they mark emphasis (_name_). A
    prime always stays, as it is part of the name (`foo'` is not `foo`), and Lean's `_root_.` prefix names the same
    declaration as the name without it."""
    found = set()
    for word in WORD.findall(text):
        variants = {word.rstrip(".") if code else word}
        if not code:
            trimmed = word.rstrip(".?!")
            variants.add(trimmed)
            if len(trimmed) > 2 and trimmed[0] == trimmed[-1] == "'":
                variants.add(trimmed[1:-1])
            variants |= {variant.strip("_") for variant in variants
                         if len(variant) > 2 and variant[0] == variant[-1] == "_"}
        variants |= {variant.removeprefix("_root_.") for variant in variants}
        found |= variants
    return found


def markdown(text: str) -> tuple[list[str], str]:
    """A Markdown text's code, as CommonMark reads it (its fenced blocks, a block left open running to the end of its
    quote or of the text, and its code spans, also over several lines of a paragraph), and its prose, the rest."""
    code, prose, paragraph, block = [], [], [], []
    fence, depth_of_fence = None, 0

    def close_paragraph() -> None:
        # An escaped backtick is a backtick in the prose, so it opens no code span.
        joined = "\n".join(paragraph).replace("\\`", "\0")
        code.extend(match.group(2) for match in SPAN.finditer(joined))
        prose.append(SPAN.sub(" ", joined))
        paragraph.clear()

    for line in text.splitlines():
        depth = 0
        while quote := QUOTE.match(line):
            line, depth = line[quote.end():], depth + 1
        if fence is not None and depth < depth_of_fence:
            # The quote that held the block has ended, and the block with it.
            code.append("\n".join(block))
            fence = None
        if fence is None:
            opening = FENCE.match(line)
            # A backtick fence's info string holds no backtick.
            if opening and not (opening.group(1)[0] == "`" and "`" in line[opening.end():]):
                close_paragraph()
                fence, depth_of_fence, block = opening.group(1), depth, []
            elif not line.strip():
                close_paragraph()
            elif not paragraph and len(line) - len(line.lstrip(" ")) >= 4:
                # Indented code, read as prose, and never part of a code span.
                prose.append(line)
            else:
                paragraph.append(line)
        elif re.fullmatch(rf" {{0,3}}{re.escape(fence[0])}{{{len(fence)},}}[ \t]*", line):
            code.append("\n".join(block))
            fence = None
        else:
            block.append(line)
    close_paragraph()
    if fence is not None:
        code.append("\n".join(block))
    return code, "\n".join(prose)


def declarations(item: dict) -> list[str]:
    return [target["declaration"] for target in item.get("lean_targets", []) if target.get("declaration")]


def taken(items: list[dict], pulls: list[dict]) -> dict[str, list[int]]:
    """The pull requests that take each task (see the module docstring), by node id, for the tasks some pull request
    takes."""
    # How many tasks have a declaration that ends with each run of last components, or holds each component.
    ends: Counter[str] = Counter()
    shared: Counter[str] = Counter()
    for item in items:
        parts = [name.split(".") for name in declarations(item)]
        ends.update({".".join(names[k:]) for names in parts for k in range(len(names))})
        shared.update({part for names in parts for part in names[:-1]})
    by_word: dict[str, set[int]] = {}
    by_end: dict[str, set[int]] = {}
    parts_of: dict[int, set[str]] = {}
    for pull in pulls:
        title, body, branch = (part if isinstance(part, str) else ""
                               for part in (pull.get("title"), pull.get("body"), (pull.get("head") or {}).get("ref")))
        (title_code, title_prose), (body_code, body_prose) = markdown(title), markdown(body)
        code = {word for block in title_code + body_code for word in words(block, code=True)}
        ids = {match.group(0).lower() for match in ARTICLE_ID.finditer("\n".join((title, body, branch)))}
        every = words("\n".join((title_prose, body_prose, branch))) | code | ids
        for word in every:
            by_word.setdefault(word, set()).add(pull["number"])
        # The end of a declaration counts where code is meant: the title, the branch name and the code.
        for word in words(title_prose) | words(branch) | code:
            by_end.setdefault(word, set()).add(pull["number"])
        parts_of[pull["number"]] = {part for word in every for part in word.split(".")}
    found: dict[str, list[int]] = {}
    for item in items:
        numbers = set(by_word.get(item["article_id"].lower(), ()))
        for name in declarations(item):
            numbers |= by_word.get(name, set())
            parts = name.split(".")
            for k in range(1, len(parts)):
                end = ".".join(parts[k:])
                if ends[end] != 1:
                    continue
                for number in by_end.get(end, ()):
                    if (k < len(parts) - 1 or re.search(r"[_\d]", end)
                            or any(shared[part] <= RARE and part in parts_of[number] for part in parts[:-1])):
                        numbers.add(number)
        if numbers:
            found[item["node_id"]] = sorted(numbers)
    return found


def shown(value: object) -> str:
    """*value* as text that cannot steer a terminal: each character that is not printable, such as ESC, BEL or a line
    end, is written as its escape (`\\x1b`, `\\x07`, `\\n`)."""
    return "".join(c if c.isprintable() else c.encode("unicode_escape").decode("ascii") for c in str(value))


def ordered(items: list[dict]) -> list[dict]:
    """The statements still to write first, then the proofs, each in tasks.json's order."""
    return sorted(items, key=lambda item: item.get("phase") != "statement")


def positive(text: str) -> int:
    if not text.isdigit() or int(text) < 1:
        raise argparse.ArgumentTypeError("expected a positive whole number")
    return int(text)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("-n", "--count", type=positive, default=5, help="how many tasks to print (default 5)")
    parser.add_argument("--json", action="store_true", help="print JSON for agents")
    parser.add_argument("--tasks", default=TASKS, metavar="FILE_OR_URL", help=f"the task list (default {TASKS})")
    parser.add_argument("--repo", default=REPOSITORY, metavar="OWNER/NAME",
                        help=f"the repository whose pull requests take tasks (default {REPOSITORY})")
    args = parser.parse_args(argv)
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN") or None
    try:
        tasks = load_tasks(args.tasks)
        pulls = pull_requests(args.repo, tasks.get("commit_date"), token)
    except Failure as failure:
        print(f"error: {shown(failure)}", file=sys.stderr)
        return 1
    held = taken(tasks["items"], pulls)
    free = [item for item in ordered(tasks["items"]) if item["node_id"] not in held]
    chosen = free[:args.count]
    if args.json:
        print(json.dumps({
            "tasks": args.tasks, "commit": tasks.get("commit"), "commit_date": tasks.get("commit_date"),
            "autoform_ref": tasks.get("autoform_ref"), "ready": len(tasks["items"]), "taken": len(held),
            "free": len(free), "next": chosen,
            "taken_by": [{"node_id": node_id, "pull_requests": numbers} for node_id, numbers in held.items()],
        }, indent=2))  # ASCII only, so no character of the list reaches the terminal unescaped.
        return 0
    # The list comes from a download or a file: its fields are shown escaped.
    commit = shown((tasks.get("commit") or "")[:12]) or "an unrecorded commit"
    print(f"{len(tasks['items'])} ready tasks at {commit}; pull requests take {len(held)} of them, so {len(free)} "
          "are free.")
    if not tasks.get("commit_date"):
        print("This task list records no commit date, so pull requests merged since it was computed are not read.")
    for item in chosen:
        print(f"\n{shown(item['phase'])}: {shown(item.get('title'))}\n  article id   {shown(item['article_id'])}\n"
              f"  node         {shown(item['node_id'])}\n  Lean         {shown(', '.join(declarations(item)) or '-')}\n"
              f"  article      {shown(item.get('article_path'))}")
    if chosen:
        print("\nTo take one, open a draft pull request that names its article id (CONTRIBUTING.md, Picking a task).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
