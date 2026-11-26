# Two labelings become one lexicographic labeling

Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. The equivalence `(Fin n → α) × (Fin n → β)
≃ (Fin n → β ×ₗ α)` sends `(f,g)` to `i ↦ toLex(g(s_f⁻¹ i), f i)`. Given `h`, its inverse
takes `f(i) = (ofLex(h i)).2` and `g(j) = (ofLex(h(s_f j))).1`.
