# Lexicographic labels for successive stable sorts

Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. For `g : Fin n → β` on the sorted
positions, `successiveStableLabels f g` is `i ↦ toLex(g(s_f⁻¹ i), f i) : Fin n → β ×ₗ α`. The
second-stage `β` label is primary and the first-stage `α` label is secondary.
