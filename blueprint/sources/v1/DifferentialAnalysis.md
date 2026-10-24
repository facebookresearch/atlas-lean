---
kind: source
status: adopted
---

# MIT 18.155 Differential Analysis (Fall 2004)

Stable public record: <https://ocw.mit.edu/courses/18-155-differential-analysis-fall-2004/>.

ATLAS v1 selected 113 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

168 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/DifferentialAnalysis.json`](book-dependencies/DifferentialAnalysis.json).

1 candidate dependencies are not drawn because adding
them would create a cycle between source statements. Every other verified
dependency is retained, including relations in both directions between chapters.

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Definition 5.1 | `HilbertSpace.IsHilbertSpace` |
| Proposition 5.3 | `HilbertSpace.riesz_representation` |
