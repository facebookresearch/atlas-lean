---
kind: source
status: adopted
---

# CSLibExt

Reusable, fully proved computer-science developments built on MathlibExt. Source: <https://github.com/facebookresearch/atlas-lean/tree/main/CSLibExt>.

332 modules declare 5092 public declarations. Leaving
out 39 instances, the 3919 with a docstring are
roadmap articles whose statement is that docstring, with its citations moved
to the article's sources. Theorems are proved and definitions defined unless
their module contains `sorry`.

16097 roadmap edges come from the compiled Lean: the articles each
article's statement or proof reaches, through private helpers and undocumented
declarations if need be ([`lean-dependencies.json`](lean-dependencies.json)).

18 roadmap articles have no row in the compiled
dependency dump (for example a wanted placeholder or a module excluded by a
compiled-name collision), so no dependency edges are asserted for them.
