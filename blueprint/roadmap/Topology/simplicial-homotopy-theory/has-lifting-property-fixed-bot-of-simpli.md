# Fixed-bottom lifting from simplexwise horn lifts

Let `X, Y, E, B : SSet.{u}`, let `i : X ⟶ Y` be an anodyne extension, and let `p : E ⟶ B` and
`b : Y ⟶ B`. Assume that for every `n : ℕ`, `σ : Δ[n + 1] ⟶ Y`, and `j : Fin (n + 2)`, the
inclusion `(SSet.horn (n + 1) j).ι` has the lifting property against `p` with fixed bottom `σ
≫ b`. Then `HasLiftingPropertyFixedBot i p b`: each `a : X ⟶ E` with `a ≫ p = i ≫ b` admits `ℓ
: Y ⟶ E` satisfying `i ≫ ℓ = a` and `ℓ ≫ p = b`.
