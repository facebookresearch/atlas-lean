# Mathlib pages

The full site, which the workflow keeps as the `blueprint-site-full` artifact
for hosting outside GitHub Pages, has a page for every Mathlib module of the
graph's Mathlib layer ([`mathlib-layer.md`](mathlib-layer.md)), grouped by the
topics of `scripts/taxonomy.json`, and links the ATLAS statements to the
Mathlib declarations they use. `scripts/build_mathlib_pages.py` writes it from
the built site and the layer's `mathlib-graph` artifact of the same revision.
Like the layer, these pages are build outputs and are never committed: they
are about 1 GB of generated HTML. GitHub Pages, which publishes sites of up to
1 GB, gets the full site with its pages and the project map's data stored
gzipped ([BLUEPRINT.md](BLUEPRINT.md#the-github-pages-copy)).

## What a page shows

Each declaration of a module gets one block, in source order: its kind, its
name, a link to its source line at the pinned Mathlib revision, its signature,
its docstring, the declarations its statement uses and those its proof uses,
the declarations that use it, the ATLAS articles that use it (the layer's
bridge edges), and the ATLAS article that restates it, if one credits it with
`mathlib: true`. Uses are the layer's edges. As a display choice, used
instances are listed by name without links, after the other uses; instances
are nodes like any other and have their own blocks. The declarations and
articles that use a declaration are counted by whether they use it in their
statement or only in their proof, and up to 20 of each list are shown. A
declaration that a build has no page for is still named, and its name links to
its pinned source line.

Docstrings are rendered as Markdown with code blocks and the site's formulas,
without raw HTML, and keep only `http`, `https` and `mailto` links; a name in
code that is a declaration with a page links to it.

Pages, by site path:

| Path | Page |
|---|---|
| `mathlib/index.html` | the Mathlib pages' home: subjects with their counts |
| `mathlib/<Subject>/[<field>/[<subfield>/]]index.html` | a subject, field or subfield of the taxonomy |
| `mathlib/<Subject>/<field>/[<subfield>/]<topic>/index.html` | a topic with several modules |
| `mathlib/<Module>.html` | a module, named without its `Mathlib.` prefix (`mathlib/Topology.Basic.html`) |
| `mathlib/outside/index.html` | the modules that `mathlib_exclusions` keeps out of the taxonomy |
| `mathlib/<route>/index.html` | a notice where an index page moved away ([Moved index pages](#moved-index-pages)) |

A topic with one module has no page of its own: the module's page carries the
topic's title. A topic or folder that also has an ATLAS folder page links to
it. A declaration's anchor is its exact name (`#Finset.sum_comm`),
percent-encoded in links; every other `id` on these pages starts with `_`,
which no declaration's name does.

One page per module keeps a declaration's address independent of the taxonomy
and the number of files within hosting limits. Measured on the layer of
21 November 2026 (306,596 declarations): a page per declaration would need
306,596 files and about 3.4 GB of page chrome alone; a page per topic gives
4,105 pages and 1.45 GB of content, because every link carries a longer page
name; a page per module gives 7,970 module pages and 10,292 pages in all,
1.07 GB.

## Linking to a Mathlib declaration

A Mathlib declaration is identified by the pinned Mathlib revision and its
exact name: the `name` of a row of the layer's `nodes.jsonl.gz`. Data that
names one stores the name in a field named `mathlib` and the revision in
`mathlib_rev`; there is no other identifier, and no URL is stored.

Article prose links to a declaration's source line at the pinned revision, with
its exact name as the link's title:

```markdown
[double sums](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean#L120 "Finset.sum_comm")
```

`python scripts/mathlib_link.py GRAPH NAME...` prints such links from the
`mathlib-graph` artifact and refuses a name that is not a node. The address
works on every site, with or without Mathlib pages. Do not link with a custom
`mathlib:` scheme, which Autoform refuses to publish, or with the Mathlib
documentation's lookup address, which fails for declarations renamed upstream
since the pin.

## What the build changes in the ATLAS pages

- A link whose title is a declaration and whose address is written exactly as
  that declaration's source line at the pinned revision points to its Mathlib
  page. One that disagrees with its title is reported and left as written;
  `--strict-links`, as a pull request's build runs it, fails the build on it.
  A pull request builds the site when it changes the wiki, among others
  ([GitHub Actions and publication](BLUEPRINT.md#github-actions-and-publication)).
- The links that Autoform's Lean code blocks make to Mathlib's documentation
  point to the Mathlib page when they name a declaration that has one, and stay
  as written otherwise. Links to the documentation elsewhere are left alone.
- A statement box whose article credits a Mathlib declaration (status
  `mathlib`) links the credited name to its page; a credited name that is not a
  node is reported.
- A statement box lists the Mathlib declarations its Lean statement and proof
  use, up to 40 of each with their count, instances aside, in its dependency
  details.
- The home page links to the Mathlib pages, and the search index gets one entry
  per Mathlib page.

Everything about ATLAS that the build shows comes from the built site itself.
An article counts only where the site publishes it: its catalog entry
(`dependencies/index.json`) must lead to a page that has exactly one statement
box with the article's id whose heading carries the entry's anchor, or, for an
article that is its own page, to that page. Its title, address and Lean names
come from that entry; nothing is read from the blueprint sources, so an article
the site does not publish is never named, credited or counted.

`check` restores each changed ATLAS page from the built one, by removing what
the build added and putting back the links it changed, and requires the
original bytes. Every link of the Mathlib pages and every link the build added
or changed must lead to an existing file and anchor, and a link named after a
declaration to that declaration's anchor; every new search entry must name a
page.

## Moved index pages

Module pages and their anchors never move. Index pages do, when the taxonomy
changes: the root (route `""`), a scope's group page when the scope has a
module, at its scope path, and a topic's page when the topic has at least two
modules, at `<to>/<slugify(title)>`. A route is local to `mathlib/`, and
`mathlib/<route>/` and `mathlib/<route>/index.html` serve the same page or
notice; `outside` is never a route. The record in `scripts/mathlib-moves.d/`
says where some index pages went, and the full site keeps a notice at each
recorded route that no page holds. The record is small and reviewed, and its
completeness is advisory: a move without a row gets no notice.

### The record

Each change adds one fragment, `<YYYYMMDDTHHMMSSZ>-<slug>.jsonl`, named and
read as the card move ledger's fragments are
([cards.md](cards.md#move-ledger)): a published fragment is never edited,
renamed or deleted, and a new one is stamped no later than an hour past the
check's clock. Every entry the folder has on `main` stays as it is, by its
mode, type and Git object id, whatever it holds, and no path is used twice: a
new fragment is a path `main`'s first-parent chain never had, by any kind of
entry (a file, a folder, a link, a submodule), even one removed since, and an
entry that holds no fragment, empty or malformed, is never filled in. A check
of the working tree takes an entry as Git's index has it unless the working
tree changes it, so a submodule a clone leaves unchecked out is its commit,
not an empty folder. Each line is one row:

```json
{"index": "Topology/old-topic", "existed_at": "<40-hex commit of main>", "kind": "topic", "title": "Old topic", "modules": ["Mathlib.A", "Mathlib.B"], "to": "Topology/new-topic"}
```

- `index` is `""` or 1 to 4 components: the first matches `[A-Z][A-Za-z0-9]*`,
  the others `[a-z0-9]+(-[a-z0-9]+)*`.
- `existed_at` is a full commit of `main`'s first-parent chain, at or after the
  commit that added these pages, where the route existed; `kind` (`topic` or
  `group`), `title` (at most 200 characters) and `modules` (sorted) describe
  its owner in that commit's plan: the commit's own planner applied to its
  taxonomy and record and to the graph's modules, each taxonomy joined to them
  as the Mathlib layer joins its own.
- `to` is the route it went to, or a module (`Mathlib.M`) whose page stands for
  it; it must share a module with `modules`.

Authors write rows and reviewers check them. `python
scripts/build_mathlib_pages.py moves --base origin/main --graph mathlib-graph`
proposes a row for each index route of the base that the checkout lacks, with
a target traced by its modules; `--at <commit>` does so across one commit of
`main`; `--write <slug>` puts the rows in a new fragment, named as
`scripts/card_moves.py new-moves` names one; `--modules <list>` takes the
graph's modules from a list, one a line, instead of a `mathlib-graph`
artifact. Proposals are advice: rows are judged as below.

A recorded route is never a topic's again, not even the same topic's, whether
a topic or a group held it. A topic's folder is its natural slug unless a
folder of its scope, a recorded route or a topic before it in order has it;
then it takes the next of `-2`, `-3`, … that none of these and no other
topic's natural slug has, so no topic takes a route its owner keeps: a topic
that returns to its old place comes back at `-2`, or at `-3` when `-2` is
another topic's natural route. A group route is its scope's path: under the
row's title it becomes a page again, and a scope of another title keeps its
page there too, with a warning; a page is never overwritten. Of several rows
for one group route, the one whose `existed_at` comes latest on `main`'s
first-parent chain wins; two at one commit give a plain notice.

### Judging rows

A row is judged where it is introduced, against the reservations accepted
before it: on a pull request at its head, with the base's fragments; on `main`
at the first commit of the first-parent chain whose tree has anything at its
path, as that first entry was there, with the fragments of that commit's
parent. A fragment changed after its introduction is judged as introduced,
with a warning: its later content is never honoured, and a path whose first
entry is no fragment (a folder, a link, an empty or malformed file) introduced
no row, for good. Both a pull request's check and `main` read a path's
history this one way. A pull request's new rows must pass; on
`main` a failure is a warning, and the row is not honoured. Each row is judged
on its own, and the rows of one fragment against one plan, P0, the judging
commit's plan with the reservations accepted before the fragment:

1. `existed_at` is on `main`'s first-parent chain, before the judging commit.
2. The route is an index route of the plan of `existed_at`, and the row's
   kind, title and modules are its owner's there.
3. The route is no index route of P0 (an unchanged topic cannot be said to
   have moved, and two rows cannot justify one another).
4. The target is live in P0.
5. A target that shares no module with the row makes it a plain notice.

Only the rows that pass are reserved: a refused row reserves nothing and makes
no other row a duplicate.

Steps 2 to 5 recompute plans on the run's graph, which only stands for both
commits when their universe inputs are the run's: the `mathlib` entry of
`lake-manifest.json`, `lean-toolchain`, `scripts/dump_mathlib_dependencies.lean`,
`scripts/extract_mathlib_graph.py` and `scripts/extract_v2_lean_dependencies.py`.
The run's universe is that of the commit that produced the graph
(`stats.json`'s `atlas_commit`), once that commit is read and its manifest pins
the graph's `mathlib_rev`. A new row that cannot be recomputed is refused; a
row of `main` that cannot be, its commit or its judging commit having provably
other universe inputs, is honoured as stored, and after a pin change the
reservations follow the stored kind and title alone. What cannot be read
proves nothing, and is never taken for absent: a row whose judgement needs an
unreadable commit, tree, input or history, or a graph of unknown universe, is
unresolved, neither honoured nor refused, and so is every row judged after it,
since the reservations those rows are judged against are then unknown, unless
what refuses them does not depend on reservations. Two honoured rows
for one topic route make its notice plain on `main`, with a warning; on a pull
request the second is refused. On a pull request whose base and head share
universe inputs, the check also prints, as advice that never fails: the index
routes that vanish without a row, the routes whose owner changes, and topics
of one scope that share a folder name.

A pull request that changes the record alone does not build the site, so it
carries in its text the receipt of `python scripts/build_mathlib_pages.py
check-moves --base <base> --graph <graph>` for its exact head, which reviewers
check against the pull request and the CI artifact; the daily build judges its
rows again at their introducing commit whenever it can. `check-moves` judges
the head commit's tree alone, never the working tree. With `--graph`, a
`mathlib-graph` artifact as a directory or as the ZIP CI serves, it is a
verification of record only when the graph has nodes (in a ZIP, exactly one
regular `stats.json` and one regular `nodes.jsonl.gz`), its producer commit is
read and is the head or a commit of `main`'s first-parent chain, its Mathlib
pin is the one that commit's manifest pins, and its universe inputs are the
head's; when the base is a strict ancestor of the head, the head adds at least
one row, and the scripts run are the head's own. Its receipt names the full head
and base, each new fragment by blob, SHA-256 and row count, each new row with
what its route shows at the head, and the graph by its producer, its pin, the
SHA-256 of its `stats.json`, its `nodes.jsonl.gz` and its ZIP, and the count
and SHA-256 of its modules with a node, sorted, one a line. It judges
`main`'s rows as `main` does: one that fails is a warning, never an error of
the change. It exits 0 when every new row passes; 1 when a new row is
refused, the change has another error, or something established rules
certifying out, saying why; and 4, "not certified: …", when what it needs
cannot be established here: `main`'s record or a row of it, a reservation, a
witness, the base, which fragments are new, or the head's copy of a script or
input it runs on. That is neither a pass nor a refusal: run it again where the
whole history can be read. With `--modules`,
a list establishes no graph: the receipt says it is advisory and exits 3,
whatever its rows give.

In CI the graph is the run's own artifact: a pull request's check requires its
producer to be the checkout's HEAD. A shallow checkout, as CI's, fetches from
`origin` without a token what it lacks: a commit by its id, then `main`'s
history since 20 November 2026 without blobs, reading each blob it needs on
demand.

### Notices

From a route's honoured row, the build follows the targets through their own
honoured rows to a live page, an index page or a module page. The notice
redirects only when that page shares a module with what the route held:

- An automatic notice, "This page moved" ("This section moved" for a group),
  has a plain relative link to the page, a script that goes there with
  `location.replace`, keeping the address's fragment when the link has none, a
  refresh for readers without JavaScript, and the page as canonical.
- A plain notice, "This page was reorganised" (or "This section was
  reorganised"), has the link alone. A target sharing no module gives one; so
  do a chain that goes round, an ambiguous row, a target that cannot be
  verified and a chain with no live end, whose notice leads to the nearest live
  index enclosing the last route reached, with a warning.

A notice is never indexed and is out of the search index, the navigation and
the counts; it counts in the site's size and files. The GitHub Pages copy
stores it gzipped like any page, so there it redirects only with JavaScript,
once inflated. `build` writes the notices and lists under `moves` in its
report the honoured and refused rows with their reasons and what each route
shows in the built site, the head, the base and the graph; `check` judges
the record again and requires a notice, exactly as its row gives it, at each
honoured route no page holds and no other notice, each notice's link, refresh,
canonical and script naming one address. On a pull request, with
`GITHUB_EVENT_NAME` `pull_request`, its base read from `GITHUB_EVENT_PATH`,
`check` fails on a new row that does not pass, and, with exit status 4, on a
record it cannot establish; either fails the Mathlib pages job alone. The
record never fails `build`.

## Building

After the site and the layer are built:

```sh
python -m unittest scripts.test_build_mathlib_pages
python scripts/build_mathlib_pages.py build site mathlib-graph site-full
python scripts/build_mathlib_pages.py check site mathlib-graph site-full
```

`build` needs the site's MkDocs environment, since MkDocs renders each page's
chrome with the site's theme, and refuses a layer of another ATLAS revision
than the site's. The workflow's `build the Mathlib pages` job runs the tests,
builds and checks the full site, keeping `main`'s for three days as the
`blueprint-site-full` artifact, then packs and checks the GitHub Pages copy
([BLUEPRINT.md](BLUEPRINT.md#the-github-pages-copy)) and uploads it as a second
Pages artifact, `github-pages-full`, once `scripts/pages_size.sh` has measured
it as the upload packs it: at most 950 MB. Deployment publishes the wiki job's
site, packed the same way, as soon as it is built; then, if the Mathlib pages
job succeeded, the `publish the full site` job publishes the packed full site
in its place. The two come from the same run, and each publishes only over a
site of the run's commit or of one of its ancestors, failing otherwise, so a
later run's site is never replaced by an earlier one's. Runs of the workflow
from before that check have no such guard: do not re-run their deployment. A
failed, cancelled or timed-out Mathlib pages job leaves the wiki job's site
published.
