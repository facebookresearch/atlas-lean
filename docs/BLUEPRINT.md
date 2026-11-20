# Building and maintaining the dependency explorer

The explorer is a view of the maintained v2 libraries: `MathlibExt`,
`CSLibExt`, `PhyslibExt`, and `WantedExt`. The archived `v1/` package and the
standalone `Atlas/` developments are outside its scope.

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
lake build MathlibExt CSLibExt PhyslibExt WantedExt

git ls-files 'MathlibExt/*.lean' 'CSLibExt/*.lean' \
  'PhyslibExt/*.lean' 'WantedExt/*.lean' |
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
for the libraries' build and trust-policy checks.

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
  --keep Mathlib,MathlibExt,CSLibExt,PhyslibExt,WantedExt \
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
(**Actions → Blueprint Pages → Run workflow**), on every merge group, and on
PRs that touch the wiki: `blueprint/`, the wiki scripts and
their tests, `scripts/taxonomy.json`, `scripts/wiki-sync.json`, the site
configuration (`mkdocs.yml`, `theme/`, `hooks/`), this document, the workflow,
`.github/autoform-ref`, or the toolchain pins (`lean-toolchain`,
`lake-manifest.json`, `lakefile.toml`). A Lean-only PR skips it, because
`lean-facts` turns a renamed or deleted declaration into an unlinked page rather
than a failure; merge groups and `main` still build the whole wiki. Do not make
`build the wiki` a required status check: a workflow that `paths` skips never
reports on that PR, so a required check would block every PR it skips. Making
it requirable would need a first job that checks the changed paths and a
job-level `if` on the wiki job. Its unique `build the wiki` check must succeed
before deployment. Tests, Lean compilation, dependency extraction, rendering,
and strict site checks run in one read-only job from one checkout. The job
restores CI's `lake-build-*` cache and saves no cache of its own. The Mathlib
layer is built afterwards in a second read-only job, `build the Mathlib layer`,
which deployment does not wait for. The only write-capable job is the separate
Pages deployment job; it runs no Lean or Python package code.

Publication is disabled until a repository maintainer:

1. Selects **GitHub Actions** as the Pages source.
2. Configures the `github-pages` environment to permit only `main` and any
   desired deployment approvals.
3. Sets repository Actions variable `BLUEPRINT_PAGES` to `true`.
4. Allows the SHA-pinned actions. `build the wiki` stays an optional check,
   for the reason above.

Only successful `main` builds publish. PRs, merge groups, and manual runs on
other branches never upload a Pages artifact or request deployment. Successful
`main` builds also keep the built site for a day as the `blueprint-site`
artifact, so it can be downloaded or mirrored while Pages is off. No
repository setting is changed merely by adding this workflow.
