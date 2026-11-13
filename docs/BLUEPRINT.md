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
- Compiled Lean: dependencies of declarations' types and values. Definitions'
  bodies and inductive constructors contribute statement dependencies;
  theorem values contribute proof dependencies.
- AutoformBot: renderer and shared interactive graph viewer, installed at the
  reviewed full commit in `.github/autoform-ref`.

The HTML site, compiled dependency dump, `site-src/`, and `site/` are build
outputs, not committed sources. `blueprint/migrations/` remains the existing
migration ledger and is excluded from the published book.

The imported article corpus preserves the fork's edited prose. It is not an
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
annotations for rendering; do not commit those derived changes. Missing
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
`scripts/wiki-sync.json` is the
reviewed docstring-digest baseline. Removed declarations' articles are kept
as unlinked mathematical articles during rendering until an editor resolves
the report; no old Lean-source link is fabricated.

Changing AutoformBot requires a reviewed `.github/autoform-ref` update and
passing tests. There is no automatic pin push, upstream-sync bot, model-driven
audit, schedule, or required personal token in this contribution.

## GitHub Actions and publication

`Blueprint Pages` runs on all PRs and merge groups, and on pushes/manual runs
of `main`. Its unique `build the wiki` check must succeed before deployment.
Tests, Lean compilation, dependency extraction, rendering, and strict site
checks run in one read-only job from one checkout. The only write-capable job
is the separate Pages deployment job; it runs no Lean or Python package code.

Publication is disabled until a repository maintainer:

1. Selects **GitHub Actions** as the Pages source.
2. Configures the `github-pages` environment to permit only `main` and any
   desired deployment approvals.
3. Sets repository Actions variable `BLUEPRINT_PAGES` to `true`.
4. Allows the SHA-pinned actions, and optionally requires `build the wiki`
   alongside the repository's existing CI checks.

Only successful `main` builds publish. PRs, merge groups, and manual runs on
other branches never upload a Pages artifact or request deployment. No
repository setting is changed merely by adding this workflow.
