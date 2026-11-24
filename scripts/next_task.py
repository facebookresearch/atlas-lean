#!/usr/bin/env python3
"""Print the next ready formalization tasks of ATLAS that no pull request has taken.

    python3 scripts/next_task.py [-n N] [--json] [--tasks FILE_OR_URL] [--priorities FILE_OR_URL] [--repo OWNER/NAME]

The site publishes tasks.json: the articles Autoform finds ready to state or to prove (docs/BLUEPRINT.md,
What the tools own), as `autoform work list --json` lists them on the last main build, with the commit they come
from. This script downloads it, or reads a local copy, and lists through the GitHub API the repository's open pull
requests, whatever their base, and those merged into main since that commit, whose work tasks.json may not show yet:
GitHub's times are to the second, so one merged in the commit's second counts too.
Such a pull request takes a task when its title, body or branch name holds, as a whole word:

- the task's article id (af_...), or one of its Lean declarations in full; or
- the end of such a declaration, its last components (`Faltings.genus`) or its last one alone (`fejer` for
  `MathlibExt.Analysis.FourierConvergenceWanted.Analysis.fejer`), when no other task's declaration ends the same
  way (two end with `JacobianChallenge.genus`, so that takes neither) and it is in the title, the branch name or code:
  a code span of the title, or a code block or span of the body as GitHub renders it. A last
  component alone also has to hold an underscore or a digit, or come with another component of the declaration
  that at most five tasks' declarations share (`FourierConvergenceWanted`, say). Older pull requests name the
  declaration they prove that way; a common word alone, such as `c` or `add`, takes nothing.

In code a name counts as written, but for a dot after it (`Foo.bar.{u}`); in prose it also counts without a stop after
it and without the quotes or the emphasis around it. A prime is part of a name, and `_root_.` before one changes
nothing. The pull requests are listed with their bodies as GitHub renders them, so that the code of a body is what
GitHub shows as code: an HTML comment, a link's title, or a block that GitHub shows as text, is none. An article id
or a full declaration counts wherever the body's Markdown holds it, though, and counts as written there.

Of the free tasks it prints the next N: the statements still to write first, as they are what the results still
waiting are waiting for, then the proofs. Among the statements, and among the proofs, the tasks of higher priority
come first, and those of equal priority in tasks.json's order. blueprint/priorities.json gives the priorities
(CONTRIBUTING.md, Picking a task): a weight for a subject or a field of the graph, named as the start of the node
ids under it (`NumberTheory/zeta-l-functions`), which counts for each task under it that no longer name covers, and
a default for the others. --priorities reads another such file, or a URL; without one, as when this script runs
outside the repository, all tasks have the same priority. --json prints the tasks for agents, with Autoform's
fields, and their priorities.

The GitHub API needs no token, within its limit of 60 requests an hour from one address; when GH_TOKEN (or
GITHUB_TOKEN) is set, every request to it sends that token, and a redirect away from it drops the token. Only the
Python standard library is used.
"""

from __future__ import annotations

import argparse
import gzip
import html.parser
import json
import math
import os
import re
import string
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
# The priorities of the graph's areas, in the checkout this script is in, and the format of that file.
PRIORITIES = Path(__file__).resolve().parent.parent / "blueprint" / "priorities.json"
PRIORITIES_SCHEMA = "atlas-task-priorities/v1"
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
# The API's media type for pull requests with their bodies as GitHub renders them (body_html), besides their Markdown.
RENDERED = "application/vnd.github.full+json"
# In a body as GitHub renders it, the elements that hold code, and those that run inside a line of text, whose text
# joins the text on either side of them; the text on either side of any other element, or of code, is not one word.
CODE = {"pre", "code"}
INLINE = {"a", "abbr", "b", "bdi", "bdo", "cite", "code", "del", "dfn", "em", "g-emoji", "i", "ins", "kbd", "mark",
          "math-renderer", "q", "s", "samp", "small", "span", "strong", "time", "tt", "u", "var"}
# In a title, as CommonMark reads it, a run of backticks that no backslash escapes opens a code span, which the next
# run of the same length closes; a backslash escapes punctuation, but not in a span.
TICKS = re.compile(r"`+")
ESCAPABLE = frozenset(string.punctuation)


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


def request(url: str, token: str | None = None, media: str = "application/vnd.github+json") -> bytes:
    """The body *url* answers with, compressed on the way when the server can; only a request to the GitHub API
    sends *token*, and asks for *media*."""
    headers = {"User-Agent": "atlas-next-task", "Accept-Encoding": "gzip"}
    if url.startswith(API + "/"):
        headers.update({"Accept": media, "X-GitHub-Api-Version": "2022-11-28"})
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


class Repeated(Exception):
    """A key that a JSON object gives twice."""


def unique(pairs: list[tuple[str, object]]) -> dict:
    """A JSON object, refused when it gives a key twice, whose first value JSON would otherwise silently drop."""
    found: dict = {}
    for key, value in pairs:
        if key in found:
            raise Repeated(key)
        found[key] = value
    return found


def not_json(constant: str) -> float:
    """Refuse NaN and the infinities, which are not JSON, though Python's reader takes them."""
    raise ValueError(f"{constant} is not JSON")


def weight(value: object) -> bool:
    """Whether *value* can be a priority: a positive number, neither infinite nor a boolean."""
    return isinstance(value, (int, float)) and not isinstance(value, bool) and 0 < value < math.inf


def load_priorities(source: str | os.PathLike) -> dict:
    """blueprint/priorities.json from a URL or a file, checked: its schema, an optional `about` text, the `default`
    priority and the `weights`, each a priority for a subject, a field or a page, named as a node id or as the start
    of one that ends before a slash. Each priority is a positive number."""
    source = os.fspath(source)
    try:
        data = request(source) if re.match(r"https?://", source) else Path(source).read_bytes()
        priorities = json.loads(data, object_pairs_hook=unique, parse_constant=not_json)
    except OSError as error:
        raise Failure(f"{source}: {error.strerror or error}") from None
    except Repeated as repeated:
        raise Failure(f"{source} gives {repeated.args[0]!r} twice") from None
    except ValueError:
        raise Failure(f"{source} is not JSON") from None
    if not isinstance(priorities, dict) or priorities.get("schema") != PRIORITIES_SCHEMA:
        raise Failure(f"{source} is not a list of priorities ({PRIORITIES_SCHEMA})")
    unknown = sorted(set(priorities) - {"schema", "about", "default", "weights"})
    if unknown:
        raise Failure(f"{source} has a key it should not: {unknown[0]!r}")
    if not isinstance(priorities.get("about", ""), str):
        raise Failure(f"{source}: its about is not a text")
    if not weight(priorities.get("default")):
        raise Failure(f"{source}: its default {priorities.get('default')!r} is not a positive number")
    weights = priorities.get("weights")
    if not isinstance(weights, dict):
        raise Failure(f"{source}: its weights are not an object")
    for key, value in weights.items():
        if any(part == "" or part.strip() != part for part in key.split("/")):
            raise Failure(f"{source}: {key!r} is not a node id or the start of one")
        if not weight(value):
            raise Failure(f"{source}: the weight of {key!r}, {value!r}, is not a positive number")
    return priorities


def priority(item: dict, priorities: dict | None) -> int | float:
    """A task's priority: the weight that *priorities* gives its node id, or else the longest start of it that ends
    before a slash and has one, or else their default; 1 when there are no priorities."""
    if priorities is None:
        return 1
    parts = str(item.get("node_id") or "").split("/")
    for end in range(len(parts), 0, -1):
        found = priorities["weights"].get("/".join(parts[:end]))
        if found is not None:
            return found
    return priorities["default"]


def moment(text: str) -> datetime:
    """A time as GitHub and Git write it, with its offset."""
    return datetime.fromisoformat(text.replace("Z", "+00:00"))


def pull_requests(repository: str, since: str | None, token: str | None) -> list[dict]:
    """The repository's open pull requests, whatever their base, and, when *since* is a time, those merged into MAIN
    after it."""
    def page(query: str, number: int) -> list[dict]:
        url = f"{API}/repos/{repository}/pulls?{query}&per_page={PER_PAGE}&page={number}"
        try:
            rows = json.loads(request(url, token, media=RENDERED))
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


def code_spans(title: str) -> tuple[list[str], str]:
    """A title's code spans, as CommonMark reads them (see TICKS), and its prose, the rest."""
    code, prose, start, at = [], [], 0, 0
    while at < len(title):
        if title[at] == "\\" and title[at + 1:at + 2] in ESCAPABLE:
            at += 2
        elif title[at] == "`":
            run = TICKS.match(title, at).group()
            closing = next((match for match in TICKS.finditer(title, at + len(run)) if match.group() == run), None)
            if closing is None:
                at += len(run)
            else:
                prose.append(title[start:at])
                code.append(title[at + len(run):closing.start()])
                start = at = closing.end()
        else:
            at += 1
    prose.append(title[start:])
    return code, " ".join(prose)


class Rendered(html.parser.HTMLParser):
    """A body as GitHub renders it: the text of each pre or code element, its code, and the rest of its text, its
    prose. An attribute, such as a link's title, is neither."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.code: list[list[str]] = []
        self.prose: list[str] = []
        self.depth = 0

    def handle_starttag(self, tag: str, attrs: list) -> None:
        self.boundary(tag)
        if tag in CODE:
            if not self.depth:
                self.prose.append(" ")
                self.code.append([])
            self.depth += 1

    def handle_endtag(self, tag: str) -> None:
        if tag in CODE and self.depth:
            self.depth -= 1
            if not self.depth:
                self.prose.append(" ")
        self.boundary(tag)

    def boundary(self, tag: str) -> None:
        if tag not in INLINE:
            self.handle_data("\n")

    def handle_data(self, data: str) -> None:
        (self.code[-1] if self.depth else self.prose).append(data)


def rendered(body_html: object) -> tuple[list[str], str]:
    """The code and the prose of a body that GitHub rendered as *body_html* (see Rendered): none if it rendered none."""
    if not isinstance(body_html, str):
        return [], ""
    reader = Rendered()
    reader.feed(body_html)
    reader.close()
    return ["".join(block) for block in reader.code], "".join(reader.prose)


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
        (title_code, title_prose), (body_code, body_prose) = code_spans(title), rendered(pull.get("body_html"))
        code = {word for block in title_code + body_code for word in words(block, code=True)}
        ids = {match.group(0).lower() for match in ARTICLE_ID.finditer("\n".join((title, body, branch)))}
        # An article id or a full declaration counts wherever the body's Markdown holds it, as written.
        every = words("\n".join((title_prose, body_prose, branch))) | words(body, code=True) | code | ids
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


def ordered(items: list[dict], priorities: dict | None = None) -> list[dict]:
    """The statements still to write first, then the proofs; among each, by priority, highest first, then in
    tasks.json's order."""
    return sorted(items, key=lambda item: (item.get("phase") != "statement", -priority(item, priorities)))


def positive(text: str) -> int:
    if not text.isdigit() or int(text) < 1:
        raise argparse.ArgumentTypeError("expected a positive whole number")
    return int(text)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("-n", "--count", type=positive, default=5, help="how many tasks to print (default 5)")
    parser.add_argument("--json", action="store_true", help="print JSON for agents")
    parser.add_argument("--tasks", default=TASKS, metavar="FILE_OR_URL", help=f"the task list (default {TASKS})")
    parser.add_argument("--priorities", metavar="FILE_OR_URL",
                        help="the priorities of the graph's areas (default blueprint/priorities.json in the checkout "
                             "this script is in, if there is one; without it all tasks have the same priority)")
    parser.add_argument("--repo", default=REPOSITORY, metavar="OWNER/NAME",
                        help=f"the repository whose pull requests take tasks (default {REPOSITORY})")
    args = parser.parse_args(argv)
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN") or None
    source = args.priorities if args.priorities is not None else str(PRIORITIES) if PRIORITIES.is_file() else None
    try:
        tasks = load_tasks(args.tasks)
        priorities = None if source is None else load_priorities(source)
        pulls = pull_requests(args.repo, tasks.get("commit_date"), token)
    except Failure as failure:
        print(f"error: {shown(failure)}", file=sys.stderr)
        return 1
    held = taken(tasks["items"], pulls)
    free = [item for item in ordered(tasks["items"], priorities) if item["node_id"] not in held]
    chosen = free[:args.count]
    if args.json:
        print(json.dumps({
            "tasks": args.tasks, "commit": tasks.get("commit"), "commit_date": tasks.get("commit_date"),
            "autoform_ref": tasks.get("autoform_ref"), "priorities": source, "ready": len(tasks["items"]),
            "taken": len(held), "free": len(free), "next": chosen,
            "priority": {item["node_id"]: priority(item, priorities) for item in chosen},
            "taken_by": [{"node_id": node_id, "pull_requests": numbers} for node_id, numbers in held.items()],
        }, indent=2))  # ASCII only, so no character of the list reaches the terminal unescaped.
        return 0
    # The list comes from a download or a file: its fields are shown escaped.
    commit = shown((tasks.get("commit") or "")[:12]) or "an unrecorded commit"
    print(f"{len(tasks['items'])} ready tasks at {commit}; pull requests take {len(held)} of them, so {len(free)} "
          "are free.")
    if not tasks.get("commit_date"):
        print("This task list records no commit date, so pull requests merged since it was computed are not read.")
    print(f"Priorities from {shown(source)}." if source is not None else
          "No priorities, so all tasks have the same priority.")
    for item in chosen:
        print(f"\n{shown(item['phase'])}: {shown(item.get('title'))}\n  article id   {shown(item['article_id'])}\n"
              f"  node         {shown(item['node_id'])}\n  Lean         {shown(', '.join(declarations(item)) or '-')}\n"
              f"  article      {shown(item.get('article_path'))}\n  priority     {shown(priority(item, priorities))}")
    if chosen:
        print("\nTo take one, open a draft pull request that names its article id (CONTRIBUTING.md, Picking a task).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
