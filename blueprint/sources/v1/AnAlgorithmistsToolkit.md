---
kind: source
status: adopted
---

# MIT 18.409 An Algorithmist's Toolkit (Fall 2009)

Stable public record: <https://ocw.mit.edu/courses/18-409-topics-in-theoretical-computer-science-an-algorithmists-toolkit-fall-2009/>.

ATLAS v1 selected 158 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

163 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/AnAlgorithmistsToolkit.json`](book-dependencies/AnAlgorithmistsToolkit.json).

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Theorem 1 (Chernoff bound / Concentration of Measure) | `Concentration.hoeffding_bound` |
