# Variable wedges become differential wedges

Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. For `n : ℕ`, `a : A`, and any `f : Fin n → σ`, the exterior
equivalence sends `a ⊗ (e_(f 0) ∧ ⋯ ∧ e_(f (n-1)))` to `a • (dX_(f 0) ∧ ⋯ ∧ dX_(f (n-1)))`,
where `e_i = single i 1`. The empty wedge is `1` when `n = 0`.
