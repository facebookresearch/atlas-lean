# Faithfulness

Does the formal statement say what its docstring, its name and the underlying
mathematics say? Green CI proves only that Lean accepted the code.

Check clause by clause, as in [REVIEWING.md](../../REVIEWING.md#mathematical-faithfulness):

- Quantifier order and dependencies, domains and codomains, coercions, endpoints,
  indexing, finiteness and nonemptiness assumptions, constants, logical direction.
- Unfold every project-local definition the statement uses, down to Mathlib. A
  statement is only as faithful as the definitions under it.
- **Vacuity and cheating.** Reject statements whose hypotheses are contradictory or
  unsatisfiable in intended use; conclusions that are tautological once a definition
  is unfolded; structures or classes whose fields assume the desired conclusion
  (for example a `structure` that carries Riemann–Roch as a field); definitions that
  are not the named object (a "Weil divisor group" that is just `Y →₀ ℤ` with no
  geometry); encodings that make a reduction trivial (an alphabet with one symbol
  per instance).
- **Generality.** A theorem stated only for `ℝ`, `ℕ`, `Fin 3` or `ZMod p` when the
  mathematics holds in general is weaker than claimed, unless the docstring says so.
- **Docstring and name.** Overclaims, omitted cases, wrong citation, or a name that
  promises more than the statement.

Anchors:

- 5: faithful to the named result at the stated generality; definitions it uses are the standard ones.
- 4: faithful, with a cosmetic mismatch (docstring slightly loose, harmless extra hypothesis already flagged as such).
- 3: faithful in substance but noticeably less general than claimed, or depends on a nonstandard but equivalent definition that should be documented.
- 2: a material mismatch: missing or extra case, wrong direction, a definition that only partly captures the object.
- 1: vacuous, tautological, contradictory, or about a different object than claimed.

Use concrete witnesses or boundary probes (`n = 0`, empty type, trivial ring) when
they settle a concern. Do not run Lean; reason from the source.
