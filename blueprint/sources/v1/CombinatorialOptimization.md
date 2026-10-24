---
kind: source
status: adopted
---

# MIT 18.433 Combinatorial Optimization (Fall 2003)

Stable public record: <https://ocw.mit.edu/courses/18-433-combinatorial-optimization-fall-2003/>.

ATLAS v1 selected 36 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

12 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/CombinatorialOptimization.json`](book-dependencies/CombinatorialOptimization.json).

1 candidate dependencies are not drawn because adding
them would create a cycle between source statements. Every other verified
dependency is retained, including relations in both directions between chapters.

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Claim 2 (decomposition into perfect matchings) | `SimpleGraph.tight_oddset_pm_decomposition` |
