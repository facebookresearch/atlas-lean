---
kind: source
status: adopted
---

# MathlibExt

Reusable, fully proved extensions to Mathlib. Source: <https://github.com/facebookresearch/atlas-lean/tree/main/MathlibExt>.

1691 modules declare 7833 public declarations. Leaving
out 145 instances, the 6378 with a docstring are
roadmap articles whose statement is that docstring, with its citations moved
to the article's sources. Theorems are proved and definitions defined unless
their module contains `sorry`.

11321 roadmap edges come from the compiled Lean: the articles each
article's statement or proof reaches, through private helpers and undocumented
declarations if need be ([`lean-dependencies.json`](lean-dependencies.json)).

38 roadmap articles have no row in the compiled
dependency dump (for example a wanted placeholder or a module excluded by a
compiled-name collision), so no dependency edges are asserted for them.
