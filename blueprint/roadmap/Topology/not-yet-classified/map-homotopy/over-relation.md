# Over Relation

Simplex-level over-relation witness between `n`-simplices `x y : X _⦋n⦌`
over `p : X ⟶ S`.

* `hom` is a cylinder homotopy stationary on `SSet.boundary n`.
* `base` is an arbitrary base simplex `Δ[n] ⟶ S` (not assumed constant).
* `bd` is the common boundary value `∂Δ[n] ⟶ X`.
* `over` requires the cylinder to lie over `base`.
* `boundary` requires the source simplex to restrict to `bd` on `∂Δ[n]`;
  the target restriction is derived from stationarity (`boundary_right`).
