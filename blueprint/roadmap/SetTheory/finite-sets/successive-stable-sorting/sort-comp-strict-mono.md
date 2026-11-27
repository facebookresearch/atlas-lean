# Strictly increasing relabeling preserves sorting

Let `n : ℕ` and let `α,β` be linearly ordered types. For a labeling `f : Fin n → α`, write
`s_f = Tuple.sort f`, so `s_f` maps sorted positions to input indices and `f ∘ s_f` is
nondecreasing, retaining input-index order on ties. For `g : α → β` with `StrictMono g`,
`Tuple.sort (g ∘ f) = Tuple.sort f`. Both comparisons and equal-label ties are preserved by
this relabeling.
