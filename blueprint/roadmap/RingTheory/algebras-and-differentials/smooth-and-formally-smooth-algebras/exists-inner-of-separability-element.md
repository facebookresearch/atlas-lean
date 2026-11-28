# Inner derivations from a separability element

Let `k` be a commutative ring and `Λ` a ring, not necessarily commutative,
and write `Λ_k = k ⊗_ℤ Λ`. Suppose `e ∈ Λ_k ⊗_k Λ_k` is a separability
element: its image under the multiplication map `Λ_k ⊗_k Λ_k → Λ_k` is `1`,
and `(x ⊗ 1) e = e (1 ⊗ x)` for every `x ∈ Λ_k`. Let `M` be a `k`-module
with ring homomorphisms `θ : Λ → End_k M` and `ρ : Λᵐᵒᵖ → End_k M` whose
images commute (a left and a right action), and let `o : Λ → M` be an
additive derivation: `o (x y) = θ x (o y) + ρ y (o x)` for all `x, y ∈ Λ`.

Then `o` is inner: there is `ξ ∈ M` with `o x + θ x ξ - ρ x ξ = 0` for every
`x ∈ Λ`. The element `ξ` need not be unique.
