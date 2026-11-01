---
kind: source
status: adopted
---

# MIT 18.103 Fourier Analysis (Fall 2013)

Stable public record: <https://ocw.mit.edu/courses/18-103-fourier-analysis-fall-2013/>.

ATLAS v1 selected 38 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

34 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/FourierAnalysis.json`](book-dependencies/FourierAnalysis.json).

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Definition 2 | `HilbertSpace.IsHilbertSpace` |
