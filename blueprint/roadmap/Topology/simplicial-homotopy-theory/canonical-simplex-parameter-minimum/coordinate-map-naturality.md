# Naturality of simplicial product-coordinate maps

Let `F(a) = Fin (a.len + 1)` for `a : SimplexCategory`. Suppose `f : F(L) × F(q) →o F(m) × F(q)` and `f' : F(L') × F(q') →o F(m') × F(q')`, with ordinal maps `δ : L' ⟶ L`, `γ : m' ⟶ m`, and `α : q' ⟶ q`, satisfy
`f.comp (OrderHom.prodMap δ.toOrderHom α.toOrderHom) = (OrderHom.prodMap γ.toOrderHom α.toOrderHom).comp f'`.
Then the induced maps in `SSet.{u}` satisfy
`(stdSimplex.map δ ⊗ₘ stdSimplex.map α) ≫ coordinateMap f = coordinateMap f' ≫ (stdSimplex.map γ ⊗ₘ stdSimplex.map α)`.
