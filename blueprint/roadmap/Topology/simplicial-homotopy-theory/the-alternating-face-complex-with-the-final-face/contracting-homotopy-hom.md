# The contraction component is the front insertion itself

Let X be a semisimplicial object in a preadditive category C, with maps s_n : X_n ⟶ X_(n+1).
Assume s_n ≫ δ₀ = 𝟙 X_n for every n, and s_(n+1) ≫ δ_(i+1) = δ_i ≫ s_n for every i : Fin (n +
1), where the faces have the casts i.succ.castSucc and i.castSucc. For every n : ℕ,
(contractingHomotopy X s hFirst hShift).hom n (n + 1) = s_n. This identifies the sign and the
degree-raising map of the contraction of the truncated identity to zero.
