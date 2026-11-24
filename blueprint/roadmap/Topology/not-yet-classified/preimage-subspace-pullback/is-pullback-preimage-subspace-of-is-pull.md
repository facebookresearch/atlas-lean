# Is Pullback preimage Subspace of is Pullback

Restriction of a pullback square to canonical preimages.
   Given `sq : IsPullback e₁ p₁ p b₁` and `⇑b₁ ⁻¹' U = U₁`, the square on
   `⇑p₁ ⁻¹' U₁` and `⇑p ⁻¹' U` over `e₁` is a pullback.
   Route: provider `isPullback_preimageSubspace` for canonical squares,
   `paste_horiz` for the outer square, then `IsPullback.of_right` with the
   `subspaceMap` composition equalities.
