---
kind: source
status: adopted
---

# MIT 18.905 Algebraic Topology I (Fall 2016)

Stable public record: <https://ocw.mit.edu/courses/18-905-algebraic-topology-i-fall-2016/>.

ATLAS v1 selected 171 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

383 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/AlgebraicTopologyI.json`](book-dependencies/AlgebraicTopologyI.json).

3 candidate dependencies are not drawn because adding
them would create a cycle between source statements. Every other verified
dependency is retained, including relations in both directions between chapters.

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Theorem 38.11 (Borsuk-Ulam) | `BorsukUlam.borsuk_ulam` |
