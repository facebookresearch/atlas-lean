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
`scripts/taxonomy.json` or `scripts/wiki-sync.json`. They add only what ATLAS
needs to AutoformBot's
[blueprint format](https://github.com/facebookresearch/autoform-bot/blob/6126f7fce521c0040796d0b67d952d36ee051f3f/autoform_cli/reference/blueprint-format.md),
at the commit in `.github/autoform-ref`; where ATLAS needs something the
format lacks, open an AutoformBot issue rather than diverge. Reviewers apply
the same rules ([REVIEWING.md](../REVIEWING.md#wiki-and-graph-prs)).

### Hierarchy

1. **A page sits where `scripts/taxonomy.json` places it:** subject, field, an
   optional subfield, then topic folders. A subject with fields holds only
   field folders, regions only group subjects on the root page, and
   `not-yet-classified/` holds modules the taxonomy has not placed yet. The
   taxonomy is the one record of the hierarchy; the generator and the sync
   follow it.
2. **Every page and subfolder is listed on its folder page** (`README.md`).
   The lists are the site's navigation and reading order: an unlisted
   statement appears only under "Other statements", and an unlisted planned
   page or subfolder does not appear in its chapter at all.
3. **Child limits:** `scripts/generate_wiki.py` splits a topic listing into
   parts above 20 entries, and `autoform audit` (`overfull-container`) reports
   a `navigation: module` page above 120 articles, the root page above 64, and
   any other article above 24 direct children. Past them a folder page stops
   being readable.
4. **Moving a module or folder changes `scripts/taxonomy.json` in the same
   PR,** or the next sync and the next generated layout follow the old place.
   See [Moving a page](#moving-a-page).

### Data and metadata

5. **Each page has one annotation,** in `blueprint/links/<Subject>.jsonl`
   (`roadmap.jsonl` for the root page), naming at most one Lean declaration,
   with an `id` (`af_` and 24 hex digits) that is unique and never changes.
   Otherwise Autoform's status for the page is ambiguous, and `autoform work`
   refuses an unfinished formalizable leaf without an `id`. `autoform links
   set` does not write these per-subject files. The sync gives each row it
   adds an `id`; a row without one is not a review finding until the one-off
   fill (#5524).
6. **Pages for documented declarations come from `sync_wiki.py
   declarations`,** then may be edited. A hand-written second page splits the
   node in two.
7. **A page states what its declaration states,** with every hypothesis and
   convention that changes the meaning (`x / 0 = 0`, truncated subtraction, a
   `[NeZero q]` argument, a list's default entry). A fix to a statement also
   goes into the Lean docstring on `main`, in the same PR or a linked issue,
   since the sync reports drift only one way. When the declaration is false,
   vacuous, unsatisfiable, mis-specified or private, the page states the
   source's mathematics and holds the declaration back, as [Maintaining
   articles](#maintaining-articles) describes.
8. **Build outputs are never committed:** `lean-facts` output, `site-src/`,
   `site/`, the dependency dump. `scripts/wiki-sync.json` and
   `blueprint/atlas.json` change only as
   [Maintaining articles](#maintaining-articles) describes.

### Edges

9. **A page linked to a declaration** (an annotation with an `object`, or the
   module and name an earlier sync wrote) **commits no `## Depends on` or
   `## Proof depends on`.** `sync_wiki.py lean-facts` writes them from the
   compiled Lean.
10. **A planned page, one with no Lean link (a held page included), may write
    its own `## Depends on` and `## Proof depends on`,** which count toward its
    readiness. It states its result precisely, cites its source, and is
    reviewed against that source. It is never a task. It links a declaration
    only once rules 7 and 13 allow, and then drops its own dependency sections.
11. **`## Informally uses` lists only results the cited proof uses** but the
    Lean need not; what the statement needs goes in the prose. One the Lean
    also uses is redundant, not a finding. It links an
    existing page, never the page itself, closes no cycle, and never counts
    toward readiness.

### Nodes without Lean

12. **A node still to break down is a planned article** (not a folder page)
    whose annotation carries
    `"extensions": {"org.autoform": {"not_ready": true}}`. Its page says what
    the node covers, which sources it follows, and what a good expansion
    contains. Autoform never lists it as a task and counts it in its scope's
    status, so a folder still to expand does not look finished.
13. **Expanding a node replaces it** with pages beside it that together cover
    its mathematics, deletes the node's page and annotation (its `id` is never
    reused), and repoints every link to it. A new page becomes a
    `theorem_wanted` or `def_wanted` statement only once its Lean statement
    records every prerequisite still blocking it; until then it stays a
    planned page, and one still high-level is a new marked node. See
    [Expanding a node](#expanding-a-node).

### Tasks and review

14. **Tasks are the articles `autoform work` finds ready** after `lean-facts`,
    as the wiki build runs it: ready to state (a `def_wanted`, or a definition
    in a module with `sorry`) once their statement prerequisites are stated,
    ready to prove (a `theorem_wanted`, or a theorem in a module with `sorry`)
    once their proof prerequisites are proved. Proved and Mathlib-backed
    articles never are. Committed annotations carry no `kind`, so on the
    committed tree it lists none.
15. **A graph PR keeps under 3,000 changed files and names its issue**
    (`Closes #…` or `Part of #…`), and an expansion changes no Lean outside
    `WantedExt`, so its reviewer need not review proofs.
16. **A code owner approves every graph PR** (`.github/CODEOWNERS`) **and
    Codex reviews it:** automatically for the repository's owners, members
    and collaborators and for forks on `codex.yml`'s trusted list; on any
    other fork PR a maintainer comments `@codex` for an advisory review. An
    expansion is judged for coverage and granularity, not only form.

### Procedures

#### Moving a page

Move it with `autoform move`, which rewrites the links. In the same PR, change
`scripts/taxonomy.json`, list the page on its new folder page, and, across
subjects, move its annotation to the new subject's links file, which
`autoform move` does not do.

#### Expanding a node

1. Add the new pages beside the node and list them on the folder page. Move
   the node's prose and sources to the folder page or the new pages.
2. Delete the node's page and annotation. Repoint every link to it, under
   `## Depends on`, `## Proof depends on` or `## Informally uses`, to the new
   pages that link actually needs. `autoform check` fails on a link left under
   the first two but only warns under `## Informally uses`.
3. Give each new page the node's prerequisites it still needs; order among new
   planned pages goes in their own `## Depends on`.
4. Make a low-level page a `theorem_wanted` or `def_wanted` statement, with a
   docstring, in `WantedExt` only when each statement prerequisite appears in
   its Lean statement and each proof prerequisite is already proved: a wanted
   statement has no proof edges, and `lean-facts` replaces hand-written ones,
   so one made too early looks ready. Put it in a module whose pages that
   folder holds, or place a new module there in `scripts/taxonomy.json` in the
   same PR; its
   page then comes from the sync (rule 6).

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
  scripts.test_extract_v2_lean_dependencies \
  scripts.test_extract_mathlib_graph \
  scripts.test_check_blueprint_site_navigation \
  scripts.test_site_chrome \
  scripts.test_blueprint_workflow \
  scripts.test_blueprint_taxonomy
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
lake exe cache get
lake build MathlibExt.Combinatorics.Enumerative.Nontrivial1234_3412Classes
lake build MathlibExt.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound
lake build MathlibExt CSLibExt PhyslibExt Domains WantedExt

git ls-files 'MathlibExt/*.lean' 'CSLibExt/*.lean' \
  'PhyslibExt/*.lean' 'Domains/*.lean' 'WantedExt/*.lean' |
while IFS= read -r source; do
  module="${source%.lean}"
  printf '%s\n' "${module//\//.}"
done > v2-modules.txt
lake env lean --run scripts/dump_v2_dependencies.lean v2-modules.txt \
  > v2-dependencies.jsonl
python scripts/extract_v2_lean_dependencies.py \
  v2-dependencies.jsonl build/lean-dependencies.json
python scripts/sync_wiki.py lean-facts build/lean-dependencies.json
autoform check blueprint --lean-root .
autoform render blueprint --output site-src --lean-root . \
  --require-declarations --ileans .lake/build/lib/lean
mkdocs build --strict
python scripts/check_blueprint_site.py site-src site
```

These shell snippets use Bash. `lean-facts` updates the local articles and
annotations for rendering; do not commit those derived changes. Because the
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
layer` job builds it once `build the wiki` has succeeded, from the v2
extraction and the dump of the v2 declarations with their Mathlib uses that
`build the wiki` makes last, after the site steps, and keeps as the
`v2-mathlib-dump` artifact. It uploads the layer as the `mathlib-graph`
artifact. A failure fails that job's check only; it never holds back the site
or its deployment, which do not read the layer. After the build and the v2
extraction above:

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
Mathlib declarations their Lean statement and proof use; the site GitHub Pages
publishes is unchanged. [`mathlib-pages.md`](mathlib-pages.md) describes the
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

```sh
python scripts/sync_wiki.py declarations
```

Run this deliberately after Lean updates, review its additions, and commit
only the editorial/source changes. It creates pages for new documented
non-deprecated declarations, preserves existing article prose, and reports
removed declarations and changed docstrings. It also refreshes the source-derived
area catalog and coverage metadata without replacing article prose.
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
declaration no page and lists it as held. A marker that names no declaration,
sits on a linked row, names a declaration the Lean index does not resolve, or
holds back a declaration that another row links or holds is reported as an
error, and the run then writes nothing. Relink the page once every listed issue
is fixed and the declaration states what the page does: restore its `object`
and remove `held`.

`scripts/wiki-sync.json` is the
reviewed docstring-digest baseline. Removed declarations' articles are kept
as unlinked mathematical articles during rendering until an editor resolves
the report; no old Lean-source link is fabricated.

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

## Page chrome

GitHub Pages publishes a site of at most 1 GB, so the theme's share of each
page is kept small. Readers with JavaScript browse with the explorer, which
hides Material's header, sidebars and footer; the theme's layout serves readers
without JavaScript and the explorer's fallback. `theme/partials/nav.html` lists
Home, the sections above the page, the page's siblings and its own entries;
each folder page lists its children too. `hooks/trim_pages.py` publishes the
renderer's notices for moved explorer URLs as bare redirects and collapses the
theme's indentation, and `hooks/title_only_search.py` keeps one title record
per page in the search index.

## GitHub Actions and publication

`Blueprint Pages` runs on `main` once a day at 03:17 UTC and on manual runs
(**Actions → Blueprint Pages → Run workflow**), and on
PRs that touch the wiki: `blueprint/`, the wiki scripts and
their tests, `scripts/taxonomy.json`, `scripts/wiki-sync.json`, the site
configuration (`mkdocs.yml`, `theme/`, `hooks/`), this document, the workflow,
`.github/autoform-ref`, or the toolchain pins (`lean-toolchain`,
`lake-manifest.json`, `lakefile.toml`). A Lean-only PR skips it, because
`lean-facts` turns a renamed or deleted declaration into an unlinked page rather
than a failure; `main` still builds the whole wiki once a day. Merge groups skip
it too: it is not a required check, so a merge-group run could not stop a merge,
and CI's required build already imports every v2 module together
(`scripts/check_declaration_collisions.sh`). Do not make
`build the wiki` a required status check: a workflow that `paths` skips never
reports on that PR, so a required check would block every PR it skips. Making
it requirable would need a first job that checks the changed paths and a
job-level `if` on the wiki job. Its unique `build the wiki` check must succeed
before deployment. Tests, Lean compilation, dependency extraction, rendering,
and strict site checks run in one read-only job from one checkout. The job
restores CI's `lake-build-*` cache and saves no cache of its own. The Mathlib
layer is built afterwards in a second read-only job, `build the Mathlib layer`,
and the Mathlib pages in a third, `build the Mathlib pages`; deployment waits
for neither. The only write-capable job is the separate Pages deployment job;
it runs no Lean or Python package code.

Publication is disabled until a repository maintainer:

1. Selects **GitHub Actions** as the Pages source.
2. Configures the `github-pages` environment to permit only `main` and any
   desired deployment approvals.
3. Sets repository Actions variable `BLUEPRINT_PAGES` to `true`.
4. Allows the SHA-pinned actions. `build the wiki` stays an optional check,
   for the reason above.

Only successful `main` builds publish. PRs, merge groups, and manual runs on
other branches never upload a Pages artifact or request deployment. Every
successful build keeps the built site for a day as the `blueprint-site`
artifact, which `build the Mathlib pages` reads; `main`'s can be downloaded or
mirrored. Successful `main` builds also keep the site with its Mathlib pages
for three days as the `blueprint-site-full` artifact, for hosting outside
GitHub Pages. No repository setting is changed merely by adding this workflow.
