---
kind: source
status: adopted
---

# MIT 18.757 Representations of Lie Groups (Fall 2023)

Stable public record: <https://ocw.mit.edu/courses/18-757-representations-of-lie-groups-fall-2023/>.

ATLAS v1 selected 185 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

232 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/LieGroups.json`](book-dependencies/LieGroups.json).

2 candidate dependencies are not drawn because adding
them would create a cycle between source statements. Every other verified
dependency is retained, including relations in both directions between chapters.

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Theorem 6.6 (Elliptic regularity) | `elliptic_regularity` |
| Definition 25.1 | `not_found` |
| Theorem 25.4 | `not_found` |
