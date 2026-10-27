---
kind: source
status: adopted
---

# MIT RES.18-011 Algebra I Student Notes (Fall 2021)

Stable public record: <https://ocw.mit.edu/courses/res-18-011-algebra-i-student-notes-fall-2021/>.

ATLAS v1 selected 176 statements from this source in
[`targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/targets.yaml) and evaluated the Lean declaration
matched to each in [`report.json`](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/report.json). Each roadmap article
reproduces one target's statement and the source location it names.

218 roadmap edges come from the source text rather than
the Lean code; each is recorded with its evidence in
[`book-dependencies/AlgebraNotes.json`](book-dependencies/AlgebraNotes.json).

1 candidate dependencies are not drawn because adding
them would create a cycle between source statements. Every other verified
dependency is retained, including relations in both directions between chapters.

## Targets without a linked Lean declaration

These targets have no `lean:` link: v1 matched no declaration, the
matched name is not found by Autoform's lexical scan, or another v1 book
or a root library declares the same name.

| Target | v1 match |
| --- | --- |
| Definition (Group) | `not_found` |
| Theorem (Crystallographic Restriction) | `not_found` |
| Proposition | `not_found` |
| Lemma | `not_found` |
| Proposition | `not_found` |
| Lemma | `not_found` |
| Definition | `not_found` |
| Lemma | `not_found` |
| Proposition | `not_found` |
| Theorem | `not_found` |
