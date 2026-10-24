---
kind: source
status: adopted
---

# Paul Garrett, Buildings and Classical Groups

Stable public record: <https://www-users.cse.umn.edu/~garrett/m/buildings/book.pdf>.

ATLAS v1 selected 74 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

35 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/Buildings.json`](book-dependencies/Buildings.json).

1 candidate dependencies are not drawn because adding
them would create a cycle between source statements. Every other verified
dependency is retained, including relations in both directions between chapters.

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Proposition | `OmegaConvolutionData.proposition_HOmega_iso_groupAlgebra` |
