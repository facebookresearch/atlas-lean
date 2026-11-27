# A block permutation determines its left-position set

Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. For a permutation σ of B,
blockLeftPositions p q σ is the p-element subset {e(σ(Sum.inl i)) | i : Fin p} of Fin (p + q).
The embedding of the left block makes this set have cardinality p.
