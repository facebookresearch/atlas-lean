# Left positions are well defined on block-permutation cosets

Let p, q : ℕ, B = Fin p ⊕ Fin q, and e : B ≃ Fin (p + q) be finSumFinEquiv. Let H be the
subgroup of permutations of B that permute each block separately. The left-position map
descends to the coset space Equiv.Perm.ModSumCongr (Fin p) (Fin q). A coset represented by σ
is sent to {e(σ(Sum.inl i)) | i : Fin p}; right composition with an element of H preserves
this set.
