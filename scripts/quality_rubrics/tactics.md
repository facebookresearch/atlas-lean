# Use of tactics

Is the proof written with reasonable tactics that a maintainer can read, and that
will survive Mathlib bumps?

Look for:

- **Fragile or discouraged tactics**: `erw`, `simp` that is not terminal and not
  `simp only [...]`, `simp_all` in the middle of a proof, `aesop`/`omega`/`decide`
  where a direct lemma exists, `convert` with large congruence goals, `native_decide`,
  `nlinarith`/`polyrith` with long hint lists that hide the argument, `exact?`/`apply?`
  leftovers, `sorry`, `admit`.
- **Performance**: `set_option maxHeartbeats` or `synthInstance.maxHeartbeats`
  overrides, `decide` on large goals, repeated `simp` over the same large term,
  `unfold` chains that should be API lemmas.
- **Brute force over structure**: proofs that case-split into dozens of branches
  where an induction or a Mathlib lemma would do; a `calc` of fifty steps that
  re-derives a library inequality.
- **Hygiene**: unused `have`s, `show` used only to restate the goal, `by exact`,
  `refine ?_` with nothing after it, deep nesting past four levels, terminal tactics
  followed by more tactics.
- **Good signs**: `simp only` with stable lemma lists, `gcongr`, `positivity`,
  `fun_prop`, `ext`, `field_simp`/`ring` at the end, short `calc` blocks with named steps.

Anchors:

- 5: idiomatic Mathlib-style proof; robust to bumps.
- 4: one or two discouraged patterns, easy to fix.
- 3: several fragile steps, or one performance override that should go.
- 2: the proof works mostly by brute force or many fragile steps; likely to break on a bump.
- 1: unreadable or effectively unmaintainable (very long monolithic tactic soup, heartbeat overrides throughout, `native_decide` for a mathematical fact).

For a definition, score the proofs of its auxiliary fields or instances; if there is
no proof at all, score 5 and say so.
