# Fiberwise Homotopy

Fiberwise homotopy between `n`-simplices `x y : X _⦋n⦌` over `p : X ⟶ S`,
relative to `boundary n`.

* `x` and `y` are represented by `yonedaEquiv.symm` as maps `Δ[n] ⟶ X`.
* `homotopyRel` is a homotopy `H : HomotopyRel f g (boundary n)` stationary on
  `∂Δ[n]` in the sense of `SSet.HomotopyRel`.
* `over` requires `H` to lie over the constant base simplex: `H.h ≫ p` is the
  projection to `Δ[n]` followed by the base map `f ≫ p`.
  Consequently `f ≫ p = g ≫ p`.
