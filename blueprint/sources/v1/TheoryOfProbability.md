---
kind: source
status: adopted
---

# MIT 18.175 Theory of Probability (Spring 2014)

Stable public record: <https://ocw.mit.edu/courses/18-175-theory-of-probability-spring-2014/>.

ATLAS v1 selected 100 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

115 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/TheoryOfProbability.json`](book-dependencies/TheoryOfProbability.json).

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Theorem (Conditional expectation martingale) | `MeasureTheory.martingale_condExp` |
