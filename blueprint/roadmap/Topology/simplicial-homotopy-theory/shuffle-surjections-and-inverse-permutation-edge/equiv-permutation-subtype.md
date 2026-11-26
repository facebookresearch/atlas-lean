# Ordered shuffles are block-increasing permutations

For p, q : ℕ, Shuffle p q is equivalent to the subtype of permutations σ of Fin (p + q) whose
restrictions i ↦ σ(Fin.castAdd q i) and j ↦ σ(Fin.natAdd p j) are strictly increasing. The
forward map returns s.perm with its IsShuffle proof, and the inverse packages that same
permutation.
