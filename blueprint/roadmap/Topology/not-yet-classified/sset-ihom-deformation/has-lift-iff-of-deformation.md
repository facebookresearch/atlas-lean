# Has Lift iff of deformation

Deformation invariance of `HasLift`: for a cylinder square `sq : CommSq t (i ▷ Δ[1]) p b`
and endpoint identifications `ι₀ ≫ t = t₀`, `ι₁ ≫ t = t₁`, `ι₀ ≫ b = b₀`, `ι₁ ≫ b = b₁`,
lift existence for the two endpoint squares is equivalent.

Orientation: `ι₀ = δ₁` is vertex 0, `ι₁ = δ₀` is vertex 1, so the edge in the pullback
target goes from the `ι₀`-vertex to the `ι₁`-vertex.

Uses only `[Mono i]` and `[Fibration p]` and applies
`SSet.CommSq.hasLift_iff_of_edge_ihomToPullbackTgt` to the edge determined by
`curry t` and `curry b` in `pullback ((ihom A).map p) ((pre i).app Y)`.
