# Building and maintaining the dependency explorer

The explorer is a view of the maintained v2 libraries: `MathlibExt`,
`CSLibExt`, `PhyslibExt`, and `WantedExt`. The archived `v1/` package and the
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
  `def`, `abbrev`, `instance` and `inductive` declarations (bodies and
  constructors) contribute statement dependencies. Theorem proofs and `opaque`
  bodies (`partial def` included) contribute proof dependencies only: Lean cannot
  unfold them, so no statement that uses the constant can depend on them.
- AutoformBot: renderer and shared interactive graph viewer, installed at the
  reviewed full commit in `.github/autoform-ref`.

The HTML site, compiled dependency dump, `site-src/`, and `site/` are build
outputs, not committed sources. `blueprint/migrations/` remains the existing
migration ledger and is excluded from the published book.

The article corpus preserves the wiki's edited prose. It is not an
assertion that every article matches the latest Lean statement. Declaration
and docstring changes should be reviewed with the sync report below.

## Graph rules

These are the rules for any PR that changes the graph: `blueprint/roadmap/`,
`blueprint/links/`, `blueprint/atlas.json`, `blueprint/coverage/`,
`scripts/taxonomy.json` or `scripts/wiki-sync.json`. Each rule gives its
reason. AutoformBot's [blueprint format](https://github.com/facebookresearch/autoform-bot/blob/6126f7fce521c0040796d0b67d952d36ee051f3f/autoform_cli/reference/blueprint-format.md),
at the commit in `.github/autoform-ref`, defines pages, links and status; these
rules add only what ATLAS needs on top of it. Where ATLAS needs something the
format lacks, open an AutoformBot issue rather than diverge. Reviewers apply
the same rules ([REVIEWING.md](../REVIEWING.md#wiki-and-graph-prs)).

### Hierarchy

1. **A page sits where `scripts/taxonomy.json` places its module or field:**
   subject, field, an optional subfield, then topic folders; regions only group
   subjects on the root page. A subject with fields holds only field folders;
   `not-yet-classified/` holds modules the taxonomy has not placed yet.
   *Reason:* the taxonomy is the one record of the hierarchy:
   `generate_wiki.py` lays out the folders from it, and `sync_wiki.py
   declarations` places a module with no pages yet where it says. A page placed
   elsewhere makes the vault and the taxonomy disagree.
2. **Every page and subfolder is listed on its folder page** (`README.md`).
   *Reason:* those lists are the site's navigation and reading order. Autoform
   takes a page's parent from its folder, so an unlisted statement still has
   one but appears only under "Other statements", and an unlisted planned page
   or subfolder does not appear in its chapter at all.
3. **Child limits follow the generator and Autoform's audit:**
   `scripts/generate_wiki.py` splits a topic listing into parts above 20
   entries, a `navigation: module` page may hold 120 articles, the root page
   (the subject index) 64, and `autoform audit` reports any other article
   with more than 24 direct children (`overfull-container`). *Reason:* past
   those sizes a folder page and its local graph stop being readable.
4. **Moving a module or folder is a taxonomy change, made in the same PR,**
   with `autoform move` to rewrite the links; then list the page on its new
   folder page and, across subjects, move its annotation to the new subject's
   links file (rules 2 and 5), which `autoform move` does not do. *Reason:* a
   move made only in the vault leaves the taxonomy describing the old place, so
   the next module the sync places, and the next generated layout, follow the
   old hierarchy.

### Data and metadata

5. **Each page has one annotation, in `blueprint/links/<Subject>.jsonl`**
   (`roadmap.jsonl` for the root page), and an annotation names at most one
   Lean declaration. An `id` (`af_` and 24 hex digits) is unique and never
   changes. `sync_wiki.py declarations` gives one to every annotation it adds;
   the annotations that have none yet get theirs in a one-off fill (#5524).
   `autoform links set` cannot do this, because it does not write these
   per-subject files. *Reason:* Autoform reads an article's facts from its
   annotation, and two annotations for one page, or one page for two
   declarations, make its status ambiguous; `autoform work` refuses an
   unfinished formalizable leaf without an `id`, so rule 14's tasks cannot be
   listed until every one has one. Until #5524 lands, a row without an `id`
   is not a review finding.
6. **Pages for documented declarations come from `sync_wiki.py
   declarations`,** then may be edited. Don't hand-write a second page for a
   declaration. *Reason:* the sync tracks docstring changes per declaration;
   a hand-written duplicate splits the node in two (`autoform audit`'s
   `duplicate-lean-target`).
7. **A page states what its declaration states,** with every hypothesis and
   convention that changes the meaning (`x / 0 = 0`, truncated subtraction, a
   `[NeZero q]` argument, a list's default entry). A fix to a statement also
   goes into the Lean docstring on `main`, in the same PR or in a linked issue.
   **Exception:** when the declaration is false, vacuous, unsatisfiable,
   mis-specified or private, the page states the source's mathematics, and its
   annotation holds the declaration back with a `held` marker instead of
   linking it, as [Maintaining articles](#maintaining-articles) describes: the
   reason and, unless it is private by design, the issue or issues tracking
   the Lean fix. *Reason:* readers trust the page, not the Lean,
   and the sync reports docstring drift only one way; a fix in a linked issue
   keeps the docstrings converging without making every wiki fix a Lean PR, and
   a held page should not be relinked to a declaration that is wrong.
8. **Build outputs are never committed:** `lean-facts` output, `site-src/`,
   `site/`, the dependency dump. `scripts/wiki-sync.json` and
   `blueprint/atlas.json` change only as [Maintaining articles](#maintaining-articles)
   describes. *Reason:* they are rebuilt from the Lean on every run.

### Edges

9. **A page tied to a Lean declaration never commits `## Depends on` or
   `## Proof depends on`;** `sync_wiki.py lean-facts` writes them from the
   compiled Lean at build time. *Reason:* Lean is the source of truth for
   those edges, and lean-facts rewrites the sections anyway.
10. **A page with no Lean declaration (a planned page) may write its own
    `## Depends on` and `## Proof depends on`.** They count toward its readiness,
    as Autoform's format says, and `lean-facts` leaves them alone on a page
    whose annotation has no Lean link (`object`), a held page included (a row
    an earlier sync wrote with only a module and a name counts as linked). Such
    a page has no `kind`, so it is not a task (rule 14). A planned page is
    held to the same standard as any article: it states its result precisely
    and cites the source it follows, and a reviewer checks the statement
    against that source. Once its Lean exists, its annotation links the
    declaration and the page drops its own dependency sections, following
    rules 7 and 9 from then on. *Reason:* nothing else
    records a planned node's prerequisites, and a planned page is the graph's
    record of mathematics not yet in Lean.
11. **`## Informally uses` lists only results the cited proof uses** but the
    Lean need not. What the statement needs (its definitions and ingredients)
    is described in the page's prose, not listed here. A result the Lean also
    uses may be listed; that is redundant, not a finding. It links an existing
    page, never the page itself, and closes no cycle. It never counts toward
    readiness. *Reason:* it records the source's argument without changing
    what is ready; reviews of the 21 wiki batches moved hundreds of statement
    ingredients out of this section.

### Nodes without Lean

12. **A node still to be broken down (DAG work) is a planned page whose
    annotation carries Autoform's** `"extensions": {"org.autoform": {"not_ready": true}}`.
    It is an article, not a folder page, and names no declaration. Its page
    says what the node covers, which sources it follows, and what a good
    expansion contains. *Reason:* Autoform defines `not_ready` as "needs more
    blueprint work before it can be attempted", never lists it as a task, and
    counts such leaves in their scope's status bar and item count, so a folder
    of nodes still to expand does not look finished on the site.
13. **Expanding a node replaces it** with new pages beside it in the same
    folder, listed on the folder page (rule 2). The expansion deletes the
    node's page and its annotation; its `id` is never reused. Its prose and
    sources move to the folder page or to the new pages, and every link to the
    node, in a `## Depends on`, `## Proof depends on` or `## Informally uses`,
    is repointed to the new pages that link actually needs. The new pages take
    over the node's own prerequisites: each carries the ones it still needs. A
    low-level new page is a `theorem_wanted` or `def_wanted` statement in
    `WantedExt` with a docstring, whose page then comes from the sync (rule 6),
    but only once the Lean records every prerequisite that still blocks it:
    each statement prerequisite appears in the declaration's statement, and
    each proof prerequisite is already proved, since a wanted statement has no
    proof and so no proof edges. Until then it stays a planned page that
    records them in its own sections (rule 10). The sync puts a page beside its
    module's other pages, so put the statements in a module whose pages that
    folder holds, or place a new module there in `scripts/taxonomy.json` in the
    same PR (rules 1 and 4). A new page that is still high-level is a new
    marked node. Order among the new planned pages goes in their own
    `## Depends on` (rule 10). *Reason:* a leaf becomes a formalization task
    only once it names a declaration, and a wanted statement is that
    declaration. A wanted statement's edges come only from its Lean statement,
    and `lean-facts` replaces the hand-written ones, so a wanted statement made
    too early would look ready while a prerequisite is still planned or
    unproved. A link to the removed node left under `## Depends on` or
    `## Proof depends on` fails `autoform check` ("dependency target does not
    exist"), but one left under `## Informally uses` only warns, so a passing
    check does not show that every link was repointed. `autoform move` cannot
    turn a page into a folder page, so replacing the node keeps the expansion
    to steps the tools support.

### Tasks and review

14. **Formalization tasks are the articles Autoform finds ready:** ready to
    state (a `def_wanted`, or a definition in a module with `sorry`) or ready
    to prove (a `theorem_wanted`, or a theorem in a module with `sorry`), once
    its prerequisites are as far along as Autoform requires: statement
    prerequisites stated, proof prerequisites proved. Proved and Mathlib-backed
    articles are never tasks. Autoform finds them on the checkout after
    `sync_wiki.py lean-facts`, as the wiki build runs it: committed annotations
    carry no `kind`, so `autoform work list` on the committed tree lists no
    task, with or without ids. *Reason:* one readiness rule, Autoform's, for
    the site, `autoform work list` and the task list.
15. **A graph PR keeps under 3,000 changed files, names the issue it
    works on (`Closes #…`, or `Part of #…` when it does part of it), and an
    expansion changes no Lean outside `WantedExt`.** *Reason:*
    GitHub shows at most 3,000 files in one diff, and a reviewer judging an
    expansion should not also have to review proofs.
16. **Every graph PR needs an approval from a code owner**
    (`.github/CODEOWNERS`) as well as Codex's review. Codex reviews a PR
    automatically when its author is an owner, member or collaborator of the
    repository or its fork's owner is on `codex.yml`'s trusted list; on any
    other fork PR, a maintainer comments `@codex` for an advisory review. An expansion is judged
    for mathematical coverage and granularity, not only form. *Reason:* agents
    can produce graph changes faster than people can check them, and a poor
    expansion spreads into every task below it.

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
  scripts.test_check_blueprint_site_navigation \
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
model-driven audit, schedule, or required personal token.

## GitHub Actions and publication

`Blueprint Pages` runs on every merge group, on pushes and manual runs of
`main`, and on PRs that touch the wiki: `blueprint/`, the wiki scripts and
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
restores CI's `lake-build-*` cache and saves no cache of its own. The only
write-capable job is the separate Pages deployment job; it runs no Lean or
Python package code.

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
