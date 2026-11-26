# Amitsur exactness in degree zero

Let `B` be a commutative `A`-algebra that is
faithfully flat as an `A`-module. If `b : B` satisfies `b ⊗ 1 = 1 ⊗ b` in `B ⊗[A] B`, then
`b = algebraMap A B a` for some `a : A`.

This is the elementwise form of Mathlib's `Algebra.IsEffective.of_faithfullyFlat`: for such `B`,
the sequence `A → B → B ⊗[A] B`, whose second map is `b ↦ b ⊗ 1 - 1 ⊗ b`, is exact.
