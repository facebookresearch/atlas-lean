# Symm

Symmetry for relative homotopies over a base.

For `H : HomotopyRelOver p f g A`, the result has start `g` and end `f`
(`ι₀` is `g`, `ι₁` is `f`), is stationary at `g` on `A`, and
`(symmHomotopy H) ≫ p = fst _ _ ≫ (g ≫ p)`. The `[Fibration p]` hypothesis is
required for this construction and the declaration does not assert transitivity.
