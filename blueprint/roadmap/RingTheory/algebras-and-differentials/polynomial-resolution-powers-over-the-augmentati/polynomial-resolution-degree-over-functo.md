# Resolution degree as a functor on the slice

Let `k` be a commutative ring, `A` a `k`-algebra, and `n : ℕ`. The functor
`polynomialResolutionDegreeOverFunctor k A n : Over A → Over A` sends `P` to its degree-`n`
polynomial resolution algebra with the composed augmentation to `A`. A morphism `f : P → Q`
acts by the degree-`n` component of `polynomialResolutionMap k f.left`.
