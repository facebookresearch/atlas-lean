# The canonical map of a surjection is surjective

Let `R` be a commutative ring, `A` a
commutative Hopf algebra over `R` and `B` a commutative bialgebra over `R`. For a surjective
bialgebra map `π : A →ₐc[R] B`, the canonical map `HopfAlgebra.canMap π : A ⊗[R] A → A ⊗[R] B`,
`a ⊗ a' ↦ (a ⊗ 1) * coaction π a'`, is surjective.
