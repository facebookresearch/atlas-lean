# Successive stable sorting multiplies permutations

Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. For `g : Fin n → β`, let `L(i) =
toLex(g(s_f⁻¹ i), f i)`. Then `Tuple.sort L = s_f * Tuple.sort g`, where `(p*q)(i) = p(q(i))`.
