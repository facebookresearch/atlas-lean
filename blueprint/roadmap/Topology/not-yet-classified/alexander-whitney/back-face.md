# Back Face

Back face of a simplicial object: the morphism induced by `backInclusion`.

For `X : SimplicialObject C` and `h : p + q = n`, this is Mathlib's `X.δ₀Iter p`, that is
`X.map (backInclusion p q n h).op : X _⦋n⦌ ⟶ X _⦋q⦌`.
