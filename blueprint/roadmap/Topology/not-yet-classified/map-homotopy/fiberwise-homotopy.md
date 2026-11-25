# Fiberwise Homotopy

Map-level fiberwise homotopy between `f g : E ⟶ E'` over `p : E ⟶ B`
and `p' : E' ⟶ B`.

* `hom` is an ordinary simplicial homotopy with cylinder `E ⊗ Δ[1] ⟶ E'`.
* `over` requires the cylinder to lie over `p`: `hom.h ≫ p' = fst ≫ p`,
  constant in the interval direction. Consequently `f ≫ p' = p`
  (`fac₀`) and `g ≫ p' = p` (`fac₁`).
