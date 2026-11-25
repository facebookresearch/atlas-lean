# Boundary Two

Reusable gluing of three compatible edges to a map `∂Δ[2] → X`.

The three edges are `e₀₁ : Δ[1] → X` (edge `0–1`), `e₀₂ : Δ[1] → X`
(edge `0–2`), `e₁₂ : Δ[1] → X` (edge `1–2`).  The three
compatibilities are the vertex equalities

* `δ₁ ≫ e₀₁ = δ₁ ≫ e₀₂` (vertex `0`),
* `δ₀ ≫ e₀₁ = δ₁ ≫ e₁₂` (vertex `1`),
* `δ₀ ≫ e₀₂ = δ₀ ≫ e₁₂` (vertex `2`),

where `δ₀, δ₁ : Δ[0] → Δ[1]` are the two face inclusions.
The resulting map `twoDesc e₀₁ e₀₂ e₁₂` satisfies

* `boundary.ι 0 ≫ twoDesc = e₁₂` (face `0`, i.e. edge `1–2`),
* `boundary.ι 1 ≫ twoDesc = e₀₂` (face `1`, i.e. edge `0–2`),
* `boundary.ι 2 ≫ twoDesc = e₀₁` (face `2`, i.e. edge `0–1`),

in the orientation `face {i}ᶜ` opposite vertex `i`.
The construction is the two-step `BicartSq.isPushout` gluing
`Λ[2,0] = F₂ ⊔ F₁` then `∂Δ[2] = F₀ ⊔ Λ[2,0]`.
