# Building and maintaining the dependency explorer

The explorer is a view of the maintained v2 libraries: `MathlibExt`,
`CSLibExt`, `PhyslibExt`, `Domains`, and `WantedExt`. The archived `v1/` package and the
standalone `Atlas/` developments are outside its scope.

What a PR may change in the graph, and how to expand a node, is in
[Graph rules](#graph-rules).

## Source ownership

- `blueprint/roadmap/`: committed mathematical articles and reading order.
- `blueprint/links/`: literature-links annotations associating articles with
  Lean declarations, stable article IDs, and navigation metadata.
- `scripts/taxonomy.json` and `blueprint/atlas.json`: subject organization.
- Card records in `blueprint/links/` and `scripts/card-moves.jsonl`: the cards readers navigate by,
  and the addresses moves retire ([cards.md](cards.md)).
- `scripts/mathgraph-map.jsonl`: the mathgraph results imported and the page
  each was written at ([mathgraph-import.md](mathgraph-import.md#the-map)).
- Lean sources: declaration kinds and statement/proof status.
- Compiled Lean: dependencies of declarations' types and values. The values of
  `def`, `abbrev` and `inductive` declarations, and of `instance` declarations
  of classes of data, which Lean compiles to definitions (bodies and
  constructors), contribute statement dependencies. Theorem proofs, including
  those of `instance` declarations of propositions, which Lean compiles to
  theorems, and `opaque` bodies (`partial def` included) contribute proof
  dependencies only: Lean cannot unfold them, so no statement that uses the
  constant can depend on them.
- AutoformBot: renderer and shared interactive graph viewer, installed at the
  reviewed full commit in `.github/autoform-ref`.

The HTML site, compiled dependency dump, `site-src/`, and `site/` are build
outputs, not committed sources. `blueprint/migrations/` remains the existing
migration ledger and is excluded from the published book.

The article corpus preserves the wiki's edited prose. It is not an
assertion that every article matches the latest Lean statement. Declaration
and docstring changes should be reviewed with the sync report below.

## Graph rules

These rules apply to any PR that changes the graph: `blueprint/roadmap/`,
`blueprint/links/`, `blueprint/atlas.json`, `blueprint/coverage/`,
`scripts/taxonomy.json`, `scripts/wiki-sync.json`, `scripts/card-moves.jsonl` or
`scripts/mathgraph-map.jsonl`. They add only what ATLAS
needs to AutoformBot's
[blueprint format](https://github.com/facebookresearch/autoform-bot/blob/b1fe52ba726bb675d9c974203fce427fe4927ff9/autoform_cli/reference/blueprint-format.md),
at the commit in `.github/autoform-ref`; where ATLAS needs something the
format lacks, open an AutoformBot issue rather than diverge.

The rules are normative: every graph PR is held against them, by its author
and by its reviewers ([REVIEWING.md](../REVIEWING.md#wiki-and-graph-prs)).
[Writing pages](#writing-pages),
[Nodes still to expand](#nodes-still-to-expand),
[Placing pages](#placing-pages) and [Cards](#cards) need a reader's judgment.
[What the tools own](#what-the-tools-own) is the mechanical layer, and
[Procedures](#procedures) gives the steps. How to open a graph PR is in
[CONTRIBUTING.md](../CONTRIBUTING.md#graph-prs).

### Writing pages

- **State what the declaration states.** Give every hypothesis and convention
  that changes the meaning (`x / 0 = 0`, truncated subtraction, a `[NeZero q]`
  argument, a list's default entry). A fix to a statement also goes into the
  Lean docstring on `main`, in the same PR or a linked issue, since the sync
  reports drift only one way. When the declaration is false, vacuous,
  unsatisfiable, mis-specified or private, the page states the source's
  mathematics and holds the declaration back, as
  [Maintaining articles](#maintaining-articles) describes.
- **Be unambiguous.** A planned page, one with no Lean link (a held page
  included), states its result precisely enough that a reader knows exactly
  which statement is meant, and cites the source it follows. It is reviewed
  against that source as a linked page is reviewed against its declaration.
- **Leave no gaps.** A planned page writes its own `## Depends on` and
  `## Proof depends on`: nothing else records its prerequisites, and they
  count toward its readiness. It links a
  declaration only once that declaration states what the page does and its
  Lean records the page's prerequisites (see
  [Expanding a node](#expanding-a-node)). Until then it stays unlinked, even
  if a declaration for it already exists; once linked it drops its own
  dependency sections.
- **Count what is not yet in Lean.** A planned page that states a result is a
  statement not yet in Lean, and Autoform counts it as one once it has a
  `kind`, which `lean-facts` gives it at build time: a held page takes that of
  the declaration it holds back, as a linked page would get it (a
  `theorem_wanted` is a theorem), except that a page stating a result held back
  as a definition (a `def` of a proposition, say) records `theorem` or `lemma`,
  which it takes instead; any other page that builds with no Lean link takes
  the kind its annotation records, as
  `"extensions": {"org.atlas-wiki": {"kind": "theorem"}}` (or `lemma`, `def`,
  `abbrev`, `instance`, `structure`, `class`, `inductive` or `opaque`). A held
  definition may so become a theorem, never a held theorem a definition:
  `lean-facts` refuses any other kind a held page records, and any value that
  is not a kind, such as a misspelt one. A page
  whose row still names a declaration of this project in a Lean link, as a
  reference, gets none, as Autoform would take that declaration for the
  page's own. Its readiness is Autoform's, from the prerequisites it lists:
  ready to state, planned, or not ready when marked `not_ready`; its topic does
  not read fully proved while it remains, and once ready it is a task. So such
  a page lists under `## Depends on` every page its statement uses, planned
  ones included. A page whose main statement defines an object, and which
  also proves results about it, records a definition kind and counts once; it
  links a declaration only once that declaration states the whole page (Leave
  no gaps), and its results count each only on pages of their own. A page
  whose main statement is a result records `theorem` or `lemma`, even if it
  first defines notation. An exposition records no kind, as
  Autoform's format gives it no declaration, and nothing counts it. A page
  whose result the Lean states under a declaration it does not link is
  relinked to it rather than given a kind.
- **One page per result.** Search the vault and pinned Mathlib before adding a
  page, and link an existing one instead of restating it. Pages for documented
  declarations come from `sync_wiki.py declarations`, then may be edited; a
  hand-written second page splits the node in two. When Lean states the same
  result more than once, the page credits one declaration and its row lists the
  others under `duplicates`, which get no page and whose uses count as uses of
  the page ([Maintaining articles](#maintaining-articles)).
- **Prose is timeless.** Don't describe the library's state ("the Lean proof",
  "not formalized yet"): it goes stale as the Lean changes, and the site shows
  status already.
- **`## Informally uses` records the source's proof, not readiness.** It lists
  only results the cited proof uses but the Lean need not; what the statement
  needs goes in the prose, and one the Lean also uses is redundant, not a
  finding. It links an existing page, never the page itself, closes no cycle,
  and never counts toward readiness.

### Nodes still to expand

- **Mark a node still to break down `not_ready`.** It is a planned article,
  not a folder page, whose annotation carries
  `"extensions": {"org.autoform": {"not_ready": true}}`. Its page says what
  the node covers, which sources it follows, and what a good expansion
  contains. Autoform never lists it as a task and counts it in its scope's
  status, so a folder still to expand does not look finished.
- **An expansion replaces the node** with pages beside it that together cover
  its mathematics at a sensible granularity, deletes the node's page and
  annotation (its `id` is never reused) and records its retirement in the move
  ledger, and repoints every link to it. A new
  page that is still high-level is a new marked node. Follow
  [Expanding a node](#expanding-a-node), which says when a new page may
  become a wanted statement.

### Placing pages

- **A page sits where `scripts/taxonomy.json` places it:** subject, field, an
  optional subfield, then topic folders. A subject with fields holds only
  field folders, regions only group subjects on the root page, and
  `not-yet-classified/` holds modules the taxonomy has not placed yet. The
  taxonomy is the one record of the hierarchy; the generator and the sync
  follow it. A topic folder, or a folder inside one, may be a card
  ([Cards](#cards)), which groups pages below the place the taxonomy gives
  their module.
- **Every page and subfolder is listed on its folder page** (`README.md`).
  The lists are the site's navigation and reading order: an unlisted
  statement appears only under "Other statements", and an unlisted planned
  page or subfolder does not appear in its chapter at all.
- **Each page has one annotation,** in `blueprint/links/<Subject>.jsonl`
  (`roadmap.jsonl` for the root page), naming at most one Lean declaration;
  otherwise Autoform's status for it is ambiguous. `autoform links set` does
  not write these per-subject files.
- **Moving a module or folder changes `scripts/taxonomy.json` in the same
  PR,** or the next sync and the next generated layout follow the old place.
  See [Moving a page](#moving-a-page). Moving pages into a card inside their
  topic is not a taxonomy change; it is recorded in `scripts/card-moves.jsonl`
  ([Cards](#cards)). A Lean pull request that moves a module's declarations to
  a new module leaves this to the next
  [graph-sync batch](#graph-sync-batches), which gives the new module their
  place when they keep their names.

### Library navigation

The roadmap root also has `Domains`, `CSLibExt`, and `PhyslibExt` entry points.
They link to the authored `## Library navigation` section at the end of
`blueprint/coverage/README.md`, whose links lead to canonical roadmap articles.
These are code-library navigation, not mathematical regions, extra result nodes,
or library-filtered progress totals. Mathematical subjects can contain results
from several code libraries; classify an implemented entry by its actual source
module, not its declaration namespace or subject. Label planned destinations
and related prerequisites separately from implemented entries.

The coverage table remains generated. `generate_wiki.generate()` preserves only
the authored library-navigation section when it generates coverage, including
when `sync_wiki.refresh_catalog()` refreshes the catalog. Keep the section's
three library headings at level three and any grouping below them. Use the exact
`## Library navigation` heading. Regeneration rejects additional level-two
sections and unparsed library-navigation headings before writing the catalog.
Do not edit generated counts or add another `Library navigation` section.

### Cards

- **A card is a folder whose folder page's annotation carries a card record**
  (`extensions["org.atlas-wiki"]["card"]`), as [cards.md](cards.md) gives it:
  a concept or a result, its main statement's `id`, a reviewed importance and
  level. Its folder page credits no declaration and writes no dependency
  section; its pages are its statements, 1 to 24, each listed once under
  `## Statements` with the main statement first, and an `## Idea` explains it
  to a learner. Readers navigate by concepts and named results, not by Lean
  declarations; keeping the card uncredited keeps Autoform's counts, readiness
  and tasks on the statements.
- **Links between cards go only under `## Background`** and are teaching
  links; elsewhere a card links another card's main statement. Every card
  edge is derived from the statements, with witnesses, which keeps the card
  map honest about what uses what.
- **A move that retires an address goes into `scripts/card-moves.jsonl`,**
  and a page gets an `id` before it moves; so does the retirement of a card or
  of a statement page, with what replaces it. `scripts/cards.py check` must
  pass.
- **A planned page may record its counterparts,** the Mathlib or ATLAS
  declarations that state its result or a close form, with how each compares
  ([cards.md](cards.md#counterparts)). Each is verified clause by clause against
  its declaration before it is written; it is data only, and gives no credit,
  makes no edge and never changes readiness.

### What the tools own

The tools write these, so they are never edited or committed by hand:

- `## Depends on` and `## Proof depends on` on a page linked to a declaration,
  of ATLAS or of Mathlib (an annotation with an `object`, or the module and
  name an earlier sync wrote): `sync_wiki.py lean-facts` writes them from the
  compiled Lean, those between ATLAS and Mathlib-credited pages from the
  Mathlib registry ([Mathlib-credited pages](#mathlib-credited-pages)).
- What `lean-facts` writes into rows at build time: `kind` and `status`; the
  Lean link of the declaration a row an earlier sync wrote with only a module
  and a name stands for; and, when a page's declaration is gone, the edits that
  unlink it: the link naming it, or a Mathlib link and the `mathlib` flag,
  removed, the row's other declarations of this project made references
  (`role: uses`), the module and name retired, and an empty `object` or
  `"mathlib": false` where a link or flag the folder defaults give must be
  masked.
- Build outputs, which are never committed: `lean-facts` output, `site-src/`,
  `site/`, the dependency dump.

`lean-facts` runs only on a clean checkout: it refuses when `blueprint/`
differs from HEAD (a file changed, staged, deleted or untracked there), its own
output of an earlier run included, so that every run derives its writes from the
authored rows and pages. Run the build's steps in a fresh, disposable checkout or
worktree, as the wiki job does, after saving or stashing your own work. Only in a
disposable checkout, and after reviewing any untracked files there, restore
`blueprint/` with `git restore --source=HEAD --staged --worktree -- blueprint` (or
`git checkout HEAD -- blueprint`), also after a run that failed part-way.
`declarations` and `ids`, which write committed rows, refuse rows that carry
`kind` or `status` (a check of those two fields, not of every edit lean-facts
makes), and the wiki tests fail on a committed row that carries them.
- `scripts/wiki-sync.json` and `blueprint/atlas.json`, which change only as
  [Maintaining articles](#maintaining-articles) describes.
- `scripts/mathgraph-map.jsonl`, to which `import_mathgraph.py` appends a line
  for each page it imports ([mathgraph-import.md](mathgraph-import.md#the-map)).

Each annotation has an `id` (`af_` and 24 hex digits) that is unique and never
changes; `autoform work` refuses an unfinished formalizable leaf without one,
so one such row stops the task list. `sync_wiki.py declarations` gives each row
it adds an `id`, and `sync_wiki.py ids` gives one to every row that has none,
such as a row written by hand; the wiki tests fail on a row without one.

CI's required `check the graph` job runs `autoform check blueprint` on the
committed graph, which fails on cycles, dangling dependency targets and missing
declarations. Nothing runs `autoform audit` in CI;
authors may run `autoform audit blueprint --lean-root .`, and reviewers still
check what it reports, such as overfull folders (`overfull-container`) and two
pages for one declaration (`duplicate-lean-target`). `autoform work` lists the
tasks once `lean-facts` has run. The wiki build writes that list, with the
commit and the Autoform pin, to `tasks.json`: the site publishes it after each
`main` build, at <https://facebookresearch.github.io/atlas-lean/tasks.json>, and
every build of the wiki keeps it as the `tasks` artifact. CONTRIBUTING.md says
how to [pick a task](../CONTRIBUTING.md#picking-a-task).

### Procedures

#### Moving a page

Move it with `autoform move`, which rewrites the links. In the same PR, change
`scripts/taxonomy.json` when the move changes where the taxonomy places the
module or folder, list the page on its new folder page, and, across subjects,
move its annotation to the new subject's links file, which `autoform move` does
not do. A move into a card inside the page's topic leaves the taxonomy as it is;
record it in `scripts/card-moves.jsonl` instead ([Cards](#cards)).

#### Expanding a node

1. Add the new pages beside the node and list them on the folder page. Move
   the node's prose and sources to the folder page or the new pages.
2. Delete the node's page and annotation, and append the retirement row to
   `scripts/card-moves.jsonl`, `{"statement": "<its id>", "page": "<its
   path>", "replaced_by": "<the id of the new page or folder page a reader
   should go to>"}` ([cards.md](cards.md#move-ledger)), so that its address
   keeps leading somewhere and its id is never reused. Repoint every link to
   it, under `## Depends on`, `## Proof depends on` or `## Informally uses`, to
   the new pages that link actually needs. `autoform check` fails on a link
   left under the first two but only warns under `## Informally uses`.
3. Give each new page the node's prerequisites it still needs; order among new
   planned pages goes in their own `## Depends on`.
4. Make a low-level page a `theorem_wanted` or `def_wanted` statement, with a
   docstring, in `WantedExt` only when each statement prerequisite appears in
   its Lean statement and each proof prerequisite is already proved: a wanted
   statement has no proof edges, and `lean-facts` replaces hand-written ones,
   so one made too early looks ready. Until then it stays a planned page with
   its own dependency sections. Put a wanted statement in a module whose pages
   that folder holds, or place a new module there in `scripts/taxonomy.json` in
   the same PR; its page then comes from the sync.

## Local environment and tests

Use Python 3.11–3.14 and the Lean toolchain in `lean-toolchain`.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r scripts/requirements-blueprint.txt \
  "git+https://github.com/facebookresearch/autoform-bot@$(cat .github/autoform-ref)"
python -m unittest \
  scripts.test_generate_wiki_navigation \
  scripts.test_generate_wiki_docstrings \
  scripts.test_sync_wiki \
  scripts.test_graph_batch \
  scripts.test_import_mathgraph \
  scripts.test_extract_v2_lean_dependencies \
  scripts.test_extract_mathlib_graph \
  scripts.test_check_blueprint_site_navigation \
  scripts.test_site_chrome \
  scripts.test_blueprint_workflow \
  scripts.test_blueprint_taxonomy \
  scripts.test_card_pages \
  scripts.test_cards
```

Render from a dedicated checkout that excludes `v1/` and `Atlas/`, as the
workflow does. Do not change an existing checkout's sparse settings while it
has uncommitted work. For a fresh clone:

```sh
git clone --filter=blob:none --sparse \
  https://github.com/facebookresearch/atlas-lean.git atlas-blueprint
cd atlas-blueprint
git sparse-checkout set --no-cone '/*' '!/v1/' '!/Atlas/'
```

Install the Python environment above in that checkout, then:

```sh
(
set -euo pipefail
lake exe cache get
lake build MathlibExt.Combinatorics.Enumerative.Nontrivial1234_3412Classes
lake build MathlibExt.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound
lake build MathlibExt CSLibExt PhyslibExt Domains WantedExt

scripts/list_v2_modules.sh v2-modules.txt
python scripts/sync_wiki.py mathlib-names build/mathlib-names.txt
lake env lean --run scripts/dump_v2_dependencies.lean v2-modules.txt \
  build/mathlib-names.txt > v2-dependencies.jsonl
python scripts/extract_v2_lean_dependencies.py \
  v2-dependencies.jsonl build/lean-dependencies.json \
  --registry build/mathlib-registry.json --names build/mathlib-names.txt
python scripts/sync_wiki.py lean-facts build/lean-dependencies.json \
  --registry build/mathlib-registry.json
autoform check blueprint --lean-root .
python scripts/cards.py moves build/card-moves.json
python scripts/cards.py rollup build/cards.json \
  --dependencies build/lean-dependencies.json \
  --registry build/mathlib-registry.json
autoform render blueprint --output site-src --lean-root . \
  --require-declarations --ileans .lake/build/lib/lean
mkdocs build --strict
python scripts/check_blueprint_site.py site-src site
)
```

These shell snippets use Bash; the second runs in a subshell that stops at the
first failing command without changing your shell's options. `lean-facts` updates the local articles and
annotations for rendering: run it in a disposable checkout, never commit those derived changes, and run it
again only on a clean one ([What the tools own](#what-the-tools-own)). Because the
rendered blueprint then differs from the commit, `autoform render` leaves out
each page's link to its Markdown source; restoring those links is tracked in
[#4993](https://github.com/facebookresearch/atlas-lean/issues/4993). Missing
compiled modules or import collisions fail the workflow rather than silently
publishing a partial graph. The ordinary repository CI remains the authority
for the libraries' build and trust-policy checks; it also imports the same modules
together (`scripts/check_declaration_collisions.sh`), so a pull request that adds a
colliding declaration fails there.

## The Mathlib layer

The graph's Mathlib layer has a node for each Mathlib declaration a
mathematician could cite, statement and proof edges between them with the
semantics above, bridge edges from the articles to the Mathlib nodes they use,
and each node's topic from the `Mathlib/...` keys of `scripts/taxonomy.json`.
[`mathlib-layer.md`](mathlib-layer.md) gives the node rules and the files. Like
the dependency dump, it is a build output: the workflow's `build the Mathlib
layer` job builds it beside `build the wiki`. It restores the same builds,
builds what they lack and makes the v2 extraction as `build the wiki` does,
then dumps the v2 declarations with their Mathlib uses, which it keeps as the
`v2-mathlib-dump` artifact. It uploads the layer as the `mathlib-graph`
artifact. The edges of the site's own Mathlib-credited pages come from the wiki
job's registry ([Mathlib-credited pages](#mathlib-credited-pages)), not from
this layer. A failure fails that job's check only; it never holds back the site
or its deployment, which do not read the layer. The dump of the Mathlib
declarations and the graph `graph` builds from it depend only on the pins and
the scripts that make them: runs other than PRs keep them in a
`mathlib-graph-*` cache, and a run that restores it skips them. `stats`
therefore takes the layer's ATLAS commit from the v2 dump. After the build and
the v2 extraction above:

```sh
python scripts/extract_mathlib_graph.py dump mathlib-graph/mathlib-dump.jsonl.gz
python scripts/extract_mathlib_graph.py dump --modules v2-modules.txt \
  --keep Mathlib,MathlibExt,CSLibExt,PhyslibExt,Domains,WantedExt \
  mathlib-graph/v2-mathlib-dump.jsonl.gz
python scripts/extract_mathlib_graph.py graph \
  mathlib-graph/mathlib-dump.jsonl.gz mathlib-graph
python scripts/extract_mathlib_graph.py bridge \
  mathlib-graph/v2-mathlib-dump.jsonl.gz mathlib-graph \
  --mathlib-dump mathlib-graph/mathlib-dump.jsonl.gz \
  --check-v2 build/lean-dependencies.json
python scripts/extract_mathlib_graph.py join --strict mathlib-graph
python scripts/extract_mathlib_graph.py stats mathlib-graph
```

`dump` runs `scripts/dump_mathlib_dependencies.lean` in shards that each
import every listed module (about 9 GB each, mostly shared `.olean` pages);
`--jobs` sets how many run at once. `bridge` fails unless its articles and their
ATLAS-to-ATLAS edges are those of `build/lean-dependencies.json`. Given
taxonomy-shaped files, such as
classification proposals, `join` reads their placements instead of those of
`scripts/taxonomy.json`; `--strict` fails on a placement target that is neither
a field of `scripts/taxonomy.json` nor one the given proposals add.

## Mathlib pages

The full site, kept as the `blueprint-site-full` artifact, adds one page per
Mathlib module of the layer, grouped by topic, and its statement boxes list the
Mathlib declarations their Lean statement and proof use. GitHub Pages
publishes it under its 1 GB limit with its pages and the project map's data
stored gzipped, for the browser to inflate
([The GitHub Pages copy](#the-github-pages-copy)).
[`mathlib-pages.md`](mathlib-pages.md) describes the
pages and how an article links to a Mathlib declaration: to its source line at
the pinned revision, with its exact name as the link's title, which
`python scripts/mathlib_link.py` prints. They are build outputs too, written
from the built site and the layer:

```sh
python -m unittest scripts.test_build_mathlib_pages
python scripts/build_mathlib_pages.py build site mathlib-graph site-full
python scripts/build_mathlib_pages.py check site mathlib-graph site-full
```

## Maintaining articles

A Lean pull request runs no sync: the next
[graph-sync batch](#graph-sync-batches) runs it over all the Lean merged since
the last batch, and so writes what each Lean pull request's own run would
([Lean pull requests and graph pull requests](../CONTRIBUTING.md#lean-pull-requests-and-graph-pull-requests)).
It makes only the edits the errors below ask for. A graph pull request that
changes the Lean, such as an expansion that adds wanted statements, runs the
sync scoped to its own changes, from the commit its branch starts at on the
branch it targets (here `main`, with `origin` this repository), and commits
what it writes:

```sh
python scripts/sync_wiki.py declarations --base "$(git merge-base origin/main HEAD)"
```

Its own declarations are those its Lean adds, documents, makes public or no
longer deprecates, compared with the Lean at the base; both are read with the
working tree's tools and taxonomy. Each of them that has no page gets one from
its docstring, laid out as below, and its annotation row goes among the rows of
its links file in path order, so that pull requests that add pages in different
places add lines in different places. A folder the run makes gets none of the
part folders `generate_wiki.py` would split it into, and where a part lists a
page or a folder the run adds, the run refreshes that part's copy on its
parent's page. In `scripts/wiki-sync.json` the run changes only the entries the
whole run below would change because of the pull request: the digests of its
own declarations and of those whose docstring it edits, and the entries of
those it removes. It lists the pages whose declaration's docstring the pull
request edits or removes, to check. It writes no page for any other
declaration, such as an older documented one of a module the changes touch, and
leaves `blueprint/atlas.json` and `blueprint/coverage/README.md` to the run
over the whole project.

A link the changes leave naming a declaration the Lean no longer has, and a
held marker they leave unusable, are errors, and the run then writes nothing:
relink the row to the declaration's successor and keep its article id, or, in
a graph pull request, remove the link and keep the page as a planned page
([Writing pages](#writing-pages)); a Lean pull request leaves a page whose own
declaration goes with no successor to a graph pull request
([Say how a pull request touches the graph](../CONTRIBUTING.md#say-how-a-pull-request-touches-the-graph)). So is a row the build refuses ([Mathlib-credited
pages](#mathlib-credited-pages)) that the changes add, as is a symbolic link
among the files the run reads (the wiki, the Lean libraries, the baseline and
the other graph files, the site configuration), since a read or write through
it could lead anywhere, a line of a links file that is no JSON object, and Lean
staged otherwise than the working tree has it; a refused row the base already
had stops a run that has something to write. A row of one of its declarations whose page is missing, or reached
through a link, is an error too, as is such a page, or a folder the pull
request adds on its way up to the roadmap's own page, that its folder page does
not list, or whose folder page or annotation row is missing. A second run
writes nothing.

With `--check`, the run writes nothing. It prints first whether the pull
request is in step, exiting 1 when it is not, with the command that brings it
in step, and whether the pull request's wiki changes are exactly what that
command writes on the base's wiki, file contents and executable bits: a fresh
article id on a new row counts as the same, and every row the base has must
keep its bytes. It reads the working tree; where the index holds a file
otherwise than the working tree, staged by hand, it asks for the two to agree
first, since a commit may take either. `--report FILE` also writes the findings
as JSON. The `graph
sync` check runs it on every pull request and merge group, and only reports for
now ([GitHub Actions and publication](#github-actions-and-publication)). Of a
Lean pull request, whose wiki changes are at most edits to links files, and of
a merge group, it asks only for what the errors above name: their missing
pages, digests and part lists are the next batch's. It still lists the pages
whose declaration's docstring changed, for the pull request's reviewer to
check.

After an upstream merge, a maintainer runs the sync over the whole project:

```sh
python scripts/sync_wiki.py declarations
```

Run this deliberately after Lean updates, review its additions, and commit
only the editorial/source changes. It creates pages for new documented
non-deprecated declarations, preserves existing article prose, and reports
removed declarations and changed docstrings. It never places a new page in a
card or below one: such a page goes to the card's parent folder and is listed
as unassigned, for an editor to place in a card, and no new page takes the name
of a folder or an address `scripts/card-moves.jsonl` records. It also refreshes
the source-derived area catalog and coverage metadata without replacing article
prose. A row the build refuses ([Mathlib-credited
pages](#mathlib-credited-pages)), such as a flagged row that also names a
declaration of this project, is reported as an error, and the run then writes
nothing: such a row neither keeps a declaration from its page nor places one.
It edits within a folder page only where every line of the page is simple: a
blank line, a heading, a single-line `- [title](page)` item with plain text
after it, or a line of plain text that opens no other block, with no item next to
text. On any other page, a new page's item goes at the end, after a blank line,
and is reported for an editor to place; a page with raw HTML or a code fence is
left as it is and the new page reported as an error. A part list
on a page that is not simple is left as it is and reported too. Every edit is
checked before it is written: Autoform's check of what the site may publish
must pass on the page, as `autoform render` would otherwise show it as typed,
with no link, and the text it publishes is rendered with the site's Markdown
extensions, read from `mkdocs.yml`, and read as a browser builds the page. An
edit that would lose a link, move a heading or its id, or not show the new link
where it belongs is left out and reported the same way, and a line of a part
list that the refresh replaces or removes is reported when it differs from the
part's own entries.

An annotation can hold its declaration back: its page states the mathematics
while the declaration is false, vacuous or otherwise does not say it, or the
declaration is private. The row then has no `object` and names the declaration
under `org.atlas-wiki`, as `"held": {"declaration": "<Lean name>", "reason":
"<false, vacuous, unsatisfiable, mis-specified, module-private or private by
design>", "issue": <number>}`, where `issue` is the issue, or a list of
issues, that tracks the Lean fix; a declaration private by design has none, and
its marker goes once the declaration is public. When a declaration has several
problems, `reason` names the one in its statement. `declarations` gives a held
declaration no page and lists it as held; `lean-facts` gives the held page the
declaration's kind, or the theorem kind a page stating a result held back as a
definition records, so it counts as a statement not yet in Lean
([Writing pages](#writing-pages)), private by design or not, unless
its marker is one `declarations` reports below, such as one naming a declaration
the Lean index does not resolve or that an earlier row holds back, whatever kind
the row records. In `declarations`, a marker that names no declaration, sits on a
linked row, names a declaration the Lean index does not resolve, or holds back
a declaration that another row links or holds is reported as an error, and the
run then writes nothing. The build's own steps (the extraction,
`lean-facts` and the cards) likewise refuse, before writing, a held row that
credits a declaration, of this project or of Mathlib, and a held declaration
that another row credits. Relink the page once every listed issue
is fixed and the declaration states what the page does: restore its `object`
and remove `held`.

When Lean states a page's result in several declarations, the page credits one
of them, and its row lists the others under `org.atlas-wiki`, as `"duplicates":
["<Lean name>", ...]`. A duplicate is no credit: the row still credits one
declaration. `declarations` gives a duplicate no page and lists it as a
duplicate. The extraction counts another page's use of a duplicate as a use of
the page's declaration, so that page depends on the page. To the declaration
itself, its duplicate is part of it. The page depends on what the duplicate
uses, as for an undocumented declaration, and never on itself. Where the
declaration names the duplicate itself, it also names what the duplicate names,
a Mathlib-credited declaration included. The row's own `object` credits a
declaration of this project, and the end that credits it names it itself: one
the links folder's defaults fill in counts for none, and so does one only a
reference names. An unlinked, planned, held or Mathlib-credited row lists none.
Each name is given once, and holds no control character, as no Lean name does.
It is not the row's own declaration, and no other row links it, holds it back or
lists it. `declarations` reports any
other list as an error and then writes nothing; a pull request's run stops only
on a list its changes break, as for a held marker. The extraction also writes
nothing when a page stands for a duplicate, when two private declarations share
the name of a duplicate or of the page's declaration, or when its dump lacks
either of them while the Lean sources still declare it, whatever became of the
other. A Lean change that deletes or renames a duplicate, or the page's
declaration, fails no build: the extraction warns, naming both, and a use of the
duplicate then counts for no page. `declarations` and `lean-facts` list such a
stale entry for an editor. A pull request's run stops on one its changes add or
change, such as a duplicate listed on a row whose declaration the Lean no longer
has. Drop the entry, or relink the page, keeping the row's article id.

`scripts/wiki-sync.json` is the
reviewed docstring-digest baseline. Removed declarations' articles are kept
as unlinked mathematical articles during rendering until an editor resolves
the report; no old Lean-source link is fabricated. Unlinking takes out the Lean
links that name the removed declaration, with its kind and status; the row's
other declarations of this project stay as references (role `uses`), so that
none of them takes the page's credit, and its other links stay. A module and name
an earlier sync wrote on the row go too, so that no later pass reads the page as
another declaration's.

Every page under `blueprint/roadmap/` needs a row in `blueprint/links/`;
`lean-facts` fails on a page without one. A folder page takes the navigation of
its sibling folders. A display formula `$$…$$` must be a Markdown block of its
own, with a blank line before and after it; inside a list item, indent it by
four spaces like the item's other paragraphs. Otherwise it renders as `$`,
inline math, `$`. The site check fails on such an unpaired delimiter, and on a
`$` attached to TeX-shaped text. Markdown drops the backslash of `\$`, so write
a literal dollar of that shape as `&#36;`, or inside inline code.

Changing AutoformBot requires a reviewed `.github/autoform-ref` update and
passing tests. The workflow has no automatic pin push, upstream-sync bot,
model-driven audit, or required personal token.

### Graph-sync batches

A graph-sync batch is one pull request that brings the wiki in step with all
the Lean merged into `main` since the last batch. For each documented
declaration merged without a page it adds the page and its annotation row and
lists the page on its folder page; it writes the docstring digests the scoped
sync writes; it places new modules in `scripts/taxonomy.json` and drops the
places of modules that are gone. One batch is open at a time, made on a fresh
`main` every one or two hours by whoever runs the batches. So `main`'s graph
trails its Lean by about one batch, plus the batch's review and queue time;
the site, built from `main` once a day, can trail `main` by up to a day more.

```sh
git fetch https://github.com/facebookresearch/atlas-lean.git main
git switch --detach FETCH_HEAD
python3 scripts/graph_batch.py make --body ../batch.md
```

`make` runs on a clean checkout, with Autoform installed as for the sync, and
reads the merged pull requests' descriptions and GitHub's rendering of them
with `gh`, logged in (`--bodies FILE` gives them as JSON instead; a description
given without its rendering places nothing). Write the description outside the
checkout, as above: a file left in it stops the next `make`. It starts from
the commit the last batch brought the graph up to, which that batch's commit
names in a `Graph-sync-through:` trailer (`python3 scripts/graph_batch.py
base` prints it). The last batch is the newest merged pull request whose head
is a batch; a commit within a merged branch never counts. The first batch
gives its base with `--base`; a later one may give an earlier commit, never a
later one, which would skip Lean. Then it:

1. places each module that neither its own placement nor its folder's covers:
   as a merged pull request's `Place:` line asks, for a module that pull
   request's merge changed; else, for a module new since the base, where the
   module whose declarations it took, by name, is placed, as a proof takes the
   place of the wanted statement it moves. It never places a module that
   already has a page outside the topic it would get, since the sync moves no
   page: placing that one is a graph pull request that moves its pages too. A
   module it cannot place goes to its subject's `not-yet-classified/` folder,
   as the sync puts any unplaced module; one in a folder that is no subject
   gets no pages, and placing it later is a graph pull request that also runs
   the sync over the whole project ([Maintaining articles](#maintaining-articles))
   to write them. For the same reason it never places a module older than the
   base in such a folder, whose older declarations the scoped sync would leave
   without pages;
2. drops the placement of each module that no longer exists, as a file or as a
   folder;
3. runs the scoped sync over every Lean change since the base, on `main`'s wiki
   and baseline: from a local commit that has `main`'s tree but the base's Lean;
4. commits all of it as one commit on top of `main`, with `Graph-sync-base:`
   and `Graph-sync-through:` trailers, and checks that commit as `verify` does.

When the sync stops, nothing is committed. If it stops on something `main`
already carries, such as a `held` marker that names a declaration a Lean pull
request renamed, fix that on `main` first, in a graph pull request: every batch
from here would stop the same way. If the check after the commit fails,
`git reset --hard HEAD^` takes the commit away.

A `Place:` line, one per module in a pull request's description, reads
`Place: <module> -> <field>` or `Place: <module> -> <field> | <topic>`: the
module as `scripts/taxonomy.json` keys it, a path without `.lean`, and a field
or subfield of the taxonomy, such as `Algebra/rings-and-fields`. A topic is one
line of at most 160 characters with none of ``<>[]{}|`@#\`` and no address
(`://`). Without one, the module takes its docstring's `# ` heading, or else
its name (its folder's, for a name such as `Basic`), as its topic's title,
unless it takes declarations from a module placed in the same field, whose
topic it then joins. A line counts only for a module that its pull request's
merge changed and that nothing places yet. `make` reads the lines after the
merge, as untrusted text: only those that GitHub's rendering of the
description shows as lines of plain text in a top-level paragraph, not in a
code block, a list, a quotation, a table or a `<details>`, and none of a
description edited after its pull request merged, which no review of the merge
saw. A line it leaves out gets a note.

A batch's description has `Graph: batch` and names no issue
([Graph PRs](../CONTRIBUTING.md#graph-prs)). `--body FILE` writes it: the
placements, each with where it comes from; the placements dropped; the new modules left unplaced,
and the changed ones that get no pages, in a folder with no subject; what
`make` left for an editor (lines it could not follow, modules it could not
place); the sync's own items for an editor, such as part-list lines its refresh
replaced; and the pages whose declaration's docstring changed while no pull
request recorded its digest. Push the commit to a branch of its own and open
the pull request with that description.

`python3 scripts/graph_batch.py verify <commit>`, run from an up-to-date
checkout of `main` (it refuses to run from the batch itself, whose checkout's
scripts and history are the pull request's), checks that the commit is a batch
and exactly what `make` writes:

- one commit, with `make`'s message, on its `Graph-sync-through:` commit, that
  changes only the taxonomy, pages and folder pages, links files and the
  baseline. Both of its commits are among the states `main` has had, on its
  first-parent history, as `verify` runs the sync of the first;
- a base no later than where the last batch before it ended;
- its taxonomy `main`'s with the placements `make` computes applied, byte for
  byte;
- its wiki in step, with changes that are exactly what the scoped sync writes,
  fresh article ids aside (the `--check` above).

From a newer `main`, it also checks that the batch still merges cleanly into
it, placing each module once, and that the scoped check finds nothing the
merge breaks, such as a second page for one declaration. Then it runs the sync
as `make` does and prints the description it recomputes (`--body FILE` writes
it too).

The batch's reviewer runs `verify` on the exact head, from `main`:

```sh
git fetch https://github.com/facebookresearch/atlas-lean.git main refs/pull/<number>/head
git switch --detach FETCH_HEAD
python3 scripts/graph_batch.py verify <head commit>
```

and reads what it prints, not the pull request's description, which whoever
opens the pull request can edit: the placements and where each comes from, the
placements dropped, the notes, the sync's items for an editor and the pages to
check. The pages are the sync's, made from docstrings that the Lean pull
requests' reviews covered. For each page under "Pages to check", the reviewer
compares the page with its declaration's new docstring, and opens a
page-problem issue for one that no longer matches: once the batch writes the
new digest, no sync reports that page again.

A batch is never updated. When `verify`, run from an up-to-date `main`, fails,
or when the merge queue removes the batch, close it and make the next one from
a fresh `main`: the next batch starts where the last merged one ended, so a
closed batch loses nothing. Never merge `main` into a batch: `verify` refuses
anything but one commit on the commit it names. If a merged batch is reverted,
make the next one with `--base` set to the reverted batch's base.

### Mathlib-credited pages

A page may state a Mathlib declaration instead of an ATLAS one when the wiki
needs a result or concept that only Mathlib proves: for a card, as a
prerequisite a planned page lists, or as an entry of a reviewed mathgraph
manifest ([mathgraph-import.md](mathgraph-import.md)). Its annotation, in its
subject's links file like every other ([Placing pages](#placing-pages)), names
Mathlib's repository in its Lean link and says so in Autoform's extension:

```json
{"subject": [{"type": "generic", "uri": "../roadmap/<folder>/<page>.md"}], "id": "af_...",
 "object": [{"type": "lean", "uri": "https://github.com/leanprover-community/mathlib4",
             "location": {"declaration": "<Mathlib name>", "module": "<Mathlib module>"}}],
 "extensions": {"org.autoform": {"mathlib": true}}}
```

Autoform shows it as in Mathlib, and it is never a task ([What the tools
own](#what-the-tools-own)). Its page states what the declaration states
([Writing pages](#writing-pages)) and commits no dependency section ([What the
tools own](#what-the-tools-own)). The `mathlib` flag is what credits Mathlib: a
Mathlib link on a row without it is a reference, which leaves the page's own
declaration its credit. The build reads every row as Autoform does, over the
links folder's defaults: a link with no `uri` is a Lean link to this project,
and a link with a `uri` but no `type` is no Lean link at all. The defaults never
set `kind` or `status`, which the build derives for each page from the Lean (or,
for a page with no Lean link, as [Writing pages](#writing-pages) says). A
page's own declaration is its Lean link to this project with role `states`, or
its only such link when none has a role, never the first by position. A link of
another type (PDF, HTML, LaTeX, generic) is a reference, whatever its role; so
is a Lean link to another repository, but one with role `states`, like a link of
a type Autoform does not know with that role, says the page is stated elsewhere,
and the page then credits none of this project's declarations. A flagged row
names exactly one Mathlib declaration, in a Lean link to Mathlib's repository,
and none of this project. A row's subject names its whole page: a
percent-encoded spelling is the same page, while a subject with a query, a
fragment or a location names only part of one, and Autoform leaves such a row
out. A page has one row, a row names a page that exists, a folder page's row
credits nothing and has no `kind` or `status`, and a declaration has one page;
otherwise the build stops before writing anything. A row an earlier sync wrote with only a module and a
name counts as the one declaration the Lean index gives it, and as none when the
index gives none or several. The extraction, `lean-facts` and `declarations`
decide so, and stop when it and another page stand for one declaration, or when
the row also holds that declaration back; `lean-facts` then gives the build's row
that declaration's Lean link, which Autoform and the cards read as any other.

The build lists such declarations (`sync_wiki.py mathlib-names`, whose output
may not lie inside `blueprint/`), imports their
modules in the dependency dump, and records which of them each article and each
of them reaches, through the constants no page credits, the project's and
Mathlib's alike, by the rules of the [Source ownership](#source-ownership)
list: a statement through what those constants state, a proof through
everything they use, their types included. An article depends on such a
declaration only where its statement or its proof names it itself (a
definition's body and an inductive type's constructors count as its
statement): one it reaches only through other constants gives the page no edge
to it. `extract_v2_lean_dependencies.py --registry` writes that registry beside
an unchanged `build/lean-dependencies.json`, with the digest of the credited
names, of the rows' `duplicates` lists, of the dump and of that extraction,
Mathlib's revision, and a format of its own. `lean-facts` and the cards take the
registry only beside the extraction it was written with, and only for their
checkout's credited names and `duplicates` lists: a `duplicates` edit can change
the bridges and leave the extraction as it was. Like that extraction, it holds
only for the dump and the checkout it was made from, which they cannot check
otherwise, so the wiki job makes all three in one run. Before
it writes either file, the extractor
refuses a dump that is not in the current format, was made at another Mathlib,
is not one whole stream (its header first, its footer last, rows between), has a
row unlike those the dump writes, or does not answer exactly the listed names.
`lean-facts --registry` checks that the registry is
well formed, in the current format, and was made from the checkout's credited
names and `duplicates` lists at its Mathlib, that
its found and missing names split those names, that each of its edges joins a
declaration a page credits to one it found and none is both kept and left out,
and that a module a row names is the declaration's, before it writes anything;
with or without the registry, it also stops when the extraction has no row for a
declaration a page credits and the Lean sources declare, which means it was made
for another state of the wiki. It then gives each page its declaration's kind
and its dependencies on the other pages, as for an ATLAS page. As there, they
are dependencies among the wiki's pages: a page with none has no prerequisite
among them. A credited name the build does not find in a Mathlib module, or
that is a declaration of the project, unlinks the page with a warning, as a
removed ATLAS declaration does: its Lean link, kind, status and `mathlib` flag
go, so the page no longer shows as in Mathlib, and its other links stay; it then
takes only a kind its row records ([Writing pages](#writing-pages)). A row
that names no module is looked for only in the modules the build imports. A
Mathlib bump that moves a credited declaration to another module stops
`lean-facts`, which names the new module, until the row names it: the bump
updates the row in the same change.

### Pages imported from mathgraph

`scripts/import_mathgraph.py` adds pages adapted from mathgraph, Jack McCarthy's
graph of textbook results, from a manifest reviewed row by row
([mathgraph-import.md](mathgraph-import.md)): planned pages, and pages credited
to a Mathlib declaration ([Mathlib-credited pages](#mathlib-credited-pages)).
The annotation of such a page records its origin under `org.atlas-wiki` as
`"seed": {"source": "mathgraph", "node": "<node id>", "revision": "<commit>"}`.
A planned page also lists there each prerequisite not yet linked by the import,
in `"pending": [{"key": "<mathgraph key>", "kind": "statement" | "proof",
"reason": "<reason>"}]`; a pending entry does not imply that no page states it.
Such a planned page is then a [node still to expand](#nodes-still-to-expand): it
carries `not_ready`, and its `## Expansion` section names the prerequisites a
good expansion links. A Mathlib-credited page has no pending entries, no
`not_ready` and no `## Expansion`. The importer never edits a page it imported
again. An editor who links a prerequisite under `## Depends on` or
`## Proof depends on` removes its entry in the same change, and `## Expansion`
and `not_ready` with the last one; no tool makes or checks that edit. After the
import a page is edited like any other; `scripts/mathgraph-map.jsonl` keeps the
digests of mathgraph's text, so that a later release can tell what a later
mathgraph revision changed.

## Page chrome

GitHub Pages publishes a site of at most 1 GB, so the theme's share of each
page is kept small. Readers with JavaScript browse with the explorer, which
hides Material's header, sidebars and footer; the theme's layout serves readers
without JavaScript and the explorer's fallback. `theme/partials/nav.html` lists
Home, the sections above the page, the page's siblings and its own entries;
each folder page lists its children too. In a folder of more than 50 entries, a
page's sidebar lists only the 50 entries around it, then a link to the folder
page, which lists them all, so that a page's sidebar stops growing with its
folder. `hooks/trim_pages.py` publishes the
renderer's notices for moved explorer URLs as bare redirects and collapses the
theme's indentation, `hooks/title_only_search.py` keeps one title record per
page in the search index, and `hooks/card_pages.py` shows each card on its
folder page, from card data of the commit being built, and keeps every address
the card move ledger retired leading to its page, with the ledger check's
receipt of that commit and with or without card data
([cards.md](cards.md#reading)), with `theme/stylesheets/atlas-cards.css`.

## GitHub Actions and publication

`Blueprint Pages` runs on `main` once a day at 03:17 UTC and on manual runs
(**Actions → Blueprint Pages → Run workflow**), and builds the site on each. It
starts on every PR too, but its first job, `decide whether to build`, lets the
build run only when the PR's merge commit changes, compared with its first
parent, what builds and checks the site: the scripts its jobs run and their
tests, `scripts/check_public_references.py`, which the importer imports, the
site configuration (`mkdocs.yml`, `theme/`, `hooks/`), the documents the build
reads (`docs/mathgraph-import.md`, whose JSON schemas a test of the importer
compares with the importer's, and `docs/mathlib-layer.md`, which the Mathlib
layer job copies into its artifact), the workflows, which its tests read,
`.github/autoform-ref`, the toolchain pins (`lean-toolchain`,
`lake-manifest.json`, `lakefile.toml`, or a `lakefile.lean`, which Lake would
prefer), or a Python toolchain file uv would read from the root
(`.python-version`, `.python-versions`, `uv.toml`, `pyproject.toml`, or an
environment in `.venv/`); a `.gitattributes` file anywhere counts too, since it
can change how the checkout writes what the build reads, and so does a file
committed where the build writes or fetches its outputs (`build/`, `site/`,
`mathlib-graph/` and the like), and so does a `publication.json` or
`manifest.json` anywhere, in any letter case, file or directory, which can make
Autoform leave its directory out of the Lean source index. It also lets it run
when the PR changes the wiki (`blueprint/`), whose pages, annotations and site
inputs it builds and checks, or one of the two ledgers its checks compare with
the PR's base commit, the import map `scripts/mathgraph-map.jsonl`
([The map](mathgraph-import.md#the-map)) and the card move ledger
`scripts/card-moves.jsonl` ([Move ledger](cards.md#move-ledger)). Only a PR's
build checks the wiki's moves and card retirements since that base against the
move ledger, and fails on a Mathlib source link that disagrees with its title:
`main`'s runs have no base commit and report such a link without failing
([mathlib-pages.md](mathlib-pages.md)). The job reads the PR's whole diff: a
`paths` filter would be matched against its first 300 changed files only, so a
PR with more changed files outside the list, Lean files say, could hide a listed
file after them. On any other PR, the build's jobs are skipped and
`test the site scripts` runs the build's unit tests alone, in a few minutes, so
that PRs that change only Lean library files, `scripts/taxonomy.json` or
`scripts/wiki-sync.json` do not wait about 50 minutes for the build, while the
tests that read such files still run: some check the committed taxonomy as the
wiki, the Mathlib layer's strict join and the Mathlib pages read it. A PR that
changes only Lean library files those tests do not read, provenance and
documentation skips them too: `scripts/ci_scope.py` lists the four Lean modules
and the document the tests read besides the graph's data and their own code.
`lean-facts` turns a renamed or deleted declaration into an unlinked page rather
than a failure, CI's `check the graph` checks the graph as committed,
`Graph sync` checks every PR's declarations, and `main`'s daily build checks the
whole wiki, its site and its cards as they stand, a failure there being fixed on
`main`.
With write access, build and check a branch before it merges with
`gh workflow run blueprint-pages.yml --ref <branch>`, or pick the branch under
**Run workflow**: the run builds the branch as a run of `main` does, without a
base commit, but skips what only publication needs (packing the wiki job's
site for GitHub Pages, keeping the full site, the Pages uploads and the
deployments, below). Merge groups do not run the workflow at all: it is not a
required check, so a merge-group run could not stop a merge, and CI's required
build already imports every v2 module together
(`scripts/check_declaration_collisions.sh`). Do not make `build the wiki` a
required status check: merge groups never report it, so a required check would
hold every merge group until the queue's timeout removed it. Its unique
`build the wiki` check must succeed before deployment. Tests, Lean compilation,
dependency extraction, rendering,
and strict site checks run in one read-only job from one checkout. The job
restores the builds CI saves from `main`, under CI's keys: the `lake-build-*`
build of the commit a PR is tested against, else `main`'s newest, and the
`lake-deps-*` package builds. It saves no cache of its own. The Mathlib
layer is built beside it, from the same builds, in a second read-only job,
`build the Mathlib layer`,
the Mathlib pages in a third, `build the Mathlib pages`, and the card scripts are
tested and the cards checked in a fourth, `check the cards`, from the wiki job's
dependency artifact ([cards.md](cards.md#checks-and-ci)); deployment waits for
none of them: it publishes the wiki job's site, packed for GitHub Pages like
the full site. Once it has, and if the Mathlib pages job succeeded, `publish
the full site` publishes that job's full site, packed for GitHub Pages ([The
GitHub Pages copy](#the-github-pages-copy)). Before either site is uploaded,
`scripts/pages_size.sh` measures it as the upload packs it and refuses an
archive over 950 MB, 5% below 10^9 bytes, since GitHub Pages publishes sites of
up to 1 GB. The wiki job checks the move ledger its site serves and derives the
card data its site shows itself, after `lean-facts` and before rendering, in two
steps that fail closed: a card error leaves the site without cards but with its
moved addresses, and fails `check the cards` only; an invalid ledger leaves it
without either ([cards.md](cards.md#reading)). The only write-capable jobs are the two Pages
deployment jobs; they run no Lean or Python package code. Each first reads the
commit of the site GitHub Pages serves, from its newest successful deployment,
and publishes only if it is the run's commit or one of its ancestors;
otherwise, or if that commit cannot be read, the job fails and publishes
nothing. A re-run, after "Re-run failed jobs" say, therefore never takes the
site back to an earlier commit. Runs from before this check have no such guard:
do not re-run their deployment.

`Graph sync` runs on every PR, Lean-only ones included, and on every merge
group. Its `graph sync` job checks out the PR merged into its base, installs
Autoform at `.github/autoform-ref` as the wiki job does, and runs the scoped
check of [Maintaining articles](#maintaining-articles) against the merge
commit's first parent, or the queue's base on a merge group. It reads the Lean
sources only, with no Lean build, and takes a few minutes. It only reports for
now: the check's step cannot fail the job, which is not a required check. The
verdict, the command that fixes it and whether the PR's wiki changes are only
the sync's go to the job summary and the `graph-sync` artifact. A PR that
changes Lean and no graph file but links files, and a merge group, are held only to the
check's errors: the links and markers their Lean leaves behind, which the
summary lists alone. With none, the job says that the next graph-sync batch
writes their pages, asks for no sync, and lists the pages whose declaration's
docstring changed, to check.

Publication is disabled until a repository maintainer:

1. Selects **GitHub Actions** as the Pages source.
2. Configures the `github-pages` environment to permit only `main` and any
   desired deployment approvals.
3. Sets repository Actions variable `BLUEPRINT_PAGES` to `true`.
4. Allows the SHA-pinned actions. `build the wiki` stays an optional check,
   for the reason above.

Only successful `main` builds publish. PRs, merge groups, and manual runs on
other branches never upload a Pages artifact or request deployment: the first
job compares the run's ref with `refs/heads/main` exactly, since an
expression's `==` ignores case and would take a branch `Main` for `main`. Every
successful build keeps the built site for a day as the `blueprint-site`
artifact, which `build the Mathlib pages` reads; `main`'s can be downloaded or
mirrored. Successful `main` builds also keep the site with its Mathlib pages
for three days as the `blueprint-site-full` artifact, unpacked, for hosting
elsewhere. No repository setting is changed merely by adding this workflow.

### The GitHub Pages copy

GitHub Pages publishes sites of up to 1 GB. It compresses the files it sends
but counts the files it stores, and it serves a stored `.gz` file as
`application/gzip`, without `Content-Encoding`, so the browser leaves it
compressed. Its copies of the wiki job's site and of the full site therefore
store each page under `mathlib/` and `roadmap/` gzipped, as `PAGE.gz`. At the
page's address, a small page with the same title loads
`javascripts/pages-packing.js` (`scripts/pages_packing.js`), which fetches the
stored page, inflates it with `DecompressionStream` and opens it in place of
the small page, at the same address and anchor. The explorer and the project
map fetch the pages they show: the script answers their fetch of a stored page
with the inflated page, so the other pages that run either, the home page,
`coverage/index.html` and the standalone map `dependencies/map/index.html`,
load it first in their head. The project map's data under
`dependencies/map/data/`, its parts, `search.json` and `relations.json`, is
stored gzipped too, as `FILE.gz` with nothing at its address: only the map
fetches it, and the script answers that fetch with the inflated file. The
map's `index.json` and every other file are published as built: the pages
that run the explorer preload the map's `index.json`; pages link to
`dependencies/index.json`, whose entries name the explorer's files under
`dependencies/scopes/` and `dependencies/chapters/`; and tools outside the
site read `tasks.json` and `publication.json`.

```sh
python scripts/pack_pages_site.py pack site-full site-pages
python scripts/pack_pages_site.py check site-full site-pages
```

`pack` writes the GitHub Pages copy. `check` requires every file of the site to
come back from it byte for byte, as its copy, by inflating its stored copy or by
removing the script tag `pack` added, each small page to be the one `pack`
writes, each stored data file to have no plain copy and no page to link to,
preload or load it, and the copy to have no other file. The wiki job packs and
checks its site before uploading it; the Mathlib pages job does the same with
the full site, on pull requests too. On the full site of 27 November 2026
(39,342 files, 3,044,837,982 bytes), the 20,215 pages under `mathlib/` and
`roadmap/` go from 2,449,502,501 bytes to 297,650,911 bytes with their small
pages, and the map's 258 data files from 356,448,636 bytes to 30,076,853 bytes:
a copy of 566,619,937 bytes in 59,558 files, whose Pages archive has 635,176,960
bytes, against 961,556,480 bytes with the pages alone stored gzipped. The wiki
job's site of that day (28,954 files, 1,705,855,924 bytes) packs into
423,294,011 bytes, a Pages archive of 472,862,720 bytes.

On GitHub Pages, these pages and the map need JavaScript and a browser with
`DecompressionStream`, which every major browser has had since 2023, to open.
Without them, and for search engines that do not run JavaScript, a page is the
small page, whose note says that it is stored compressed; the theme's layout
for readers without JavaScript (see [Page chrome](#page-chrome)) remains in the
full site, which stays the `blueprint-site-full` artifact.
