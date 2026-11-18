# Contributing to the ATLAS graph

The ATLAS wiki under `blueprint/` is the plan of the library. It is a
dependency graph of articles. Most articles stand for one Lean declaration, and
the rest are high-level nodes that are still to be broken down. Work on the
graph is tracked as GitHub issues:

- **`task:formalize`**: an article on the frontier. Its statement is ready to
  be written in Lean, or its statement is in Lean and nothing its proof needs
  is unfinished. The work is a Lean PR.
- **`task:dag-work`**: a node marked as unexpanded. The work is a graph PR
  that breaks it into child articles.

`docs/BLUEPRINT.md` covers building and syncing the wiki. This page covers
what a graph PR may change. `REVIEWING.md` holds the same rules in the form
reviewers and Codex apply.

## How the graph is stored

| What | Where | Owner |
| --- | --- | --- |
| Article text: title, statement, sources, prose | `blueprint/roadmap/**/*.md` | the wiki |
| Folder pages that list their children | `blueprint/roadmap/**/README.md` | the wiki |
| Each article's Lean declaration, `article_id` and origin | `blueprint/links/<Subject>.jsonl`, one JSON line per page | the wiki |
| Where modules and folders sit: regions, subjects, fields | `scripts/taxonomy.json` | the wiki |
| Dependencies (`## Depends on`, `## Proof depends on`) | added at build time by `sync_wiki.py lean-facts` | the compiled Lean |
| Status: stated, proved, ready to prove | derived by Autoform from the Lean | the compiled Lean |

An article's annotation names its declaration like this:

```json
{"subject": [{"type": "generic", "uri": "../roadmap/CategoryTheory/topos-theory/elementary-toposes/is-topos.md"}], "object": [{"location": {"declaration": "MathlibExt.CategoryTheory.FundamentalToposWanted.ToposTheory.IsTopos"}}], "id": "af_224b09abe36a29b48c352d8f"}
```

## Rules for every graph PR

1. **Placement.** A page sits where `scripts/taxonomy.json` places its module
   or field, and its parent folder page lists it. To move a module or folder,
   change the taxonomy in the same PR (`autoform move` rewrites the links).
2. **Faithful statements.** A page states what its declaration states,
   including every hypothesis and convention that changes the meaning:
   `x / 0 = 0`, truncated subtraction, a `[NeZero q]` argument, a list's
   default entry.
3. **Pages for declarations come from the sync.** After adding documented
   declarations, run `python scripts/sync_wiki.py declarations`, then edit the
   pages it writes. Don't hand-write a second page for a declaration.
4. **Edges.** Don't commit `## Depends on` or `## Proof depends on`; the build
   writes them from the Lean. An edge the Lean doesn't show (an argument the
   source cites, or an order among nodes still to expand) goes in
   `## Informally uses`. It must link an existing page and must not close a
   cycle.
5. **No derived files.** Don't commit `lean-facts` output, `site-src/`, `site/`
   or the dependency dump. `scripts/wiki-sync.json` and `blueprint/atlas.json`
   change only as `docs/BLUEPRINT.md` describes.
6. **Scope.** A graph PR keeps under 3,000 changed files and says
   `Closes #<issue>` for the issue it works. An expansion changes no Lean
   outside `WantedExt`.

## Nodes to expand (DAG work)

A node that still has to be broken down is an article with **no Lean
declaration** whose annotation carries the `unexpanded` marker:

```json
{"subject": [{"type": "generic", "uri": "../roadmap/ComplexGeometry/hodge-theory.md"}], "extensions": {"org.atlas-wiki": {"unexpanded": true}}}
```

Its page says in prose what the node covers, which sources it follows, and
what a good expansion contains. Folder placement follows rule 1.

To expand a node:

1. Take its `task:dag-work` issue (assign yourself).
2. Replace the node with child articles under the same folder. Write a
   low-level child as a Lean statement in `WantedExt` (`theorem_wanted` for a
   result, `def_wanted` for a definition) with a docstring. Its page then
   comes from the sync, as in rule 3. Write a child that is still high-level as
   a new marked node.
3. Remove the marker from the node you expanded: it becomes a folder page
   listing its children, or an ordinary article if it names a declaration.
4. Order the new marked nodes among themselves with `## Informally uses`; the
   Lean orders the wanted statements.

Expansions need a human code owner's review as well as Codex's, so keep each
one reviewable: one node per PR, and at most a few dozen children.

## Checks to run before opening a PR

```sh
autoform check blueprint
```

`build the wiki` runs on every PR that touches the wiki: the full build,
`lean-facts`, `autoform check --lean-root .` and the site checks that
`docs/BLUEPRINT.md` lists.
