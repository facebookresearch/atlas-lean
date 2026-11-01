---
kind: source
status: adopted
---

# WantedExt

Established results whose Lean implementation or proof is deferred. Source: <https://github.com/facebookresearch/atlas-lean/tree/main/WantedExt>.

578 modules declare 3325 public declarations. Leaving
out 87 instances, the 3096 with a docstring are
roadmap articles whose statement is that docstring, with its citations moved
to the article's sources. Theorems are proved and definitions defined unless
their module contains `sorry`.

1450 articles are `theorem_wanted` or `def_wanted` entries: their Lean
statements exist without proofs. A wanted theorem shows as stated and unproved;
a wanted definition shows as not stated, because a stated definition counts
as defined.

1885 roadmap edges come from the compiled Lean: the articles each
article's statement or proof reaches, through private helpers and undocumented
declarations if need be ([`lean-dependencies.json`](lean-dependencies.json)).

1459 roadmap articles have no row in the compiled
dependency dump (for example a wanted placeholder or a module excluded by a
compiled-name collision), so no dependency edges are asserted for them.
