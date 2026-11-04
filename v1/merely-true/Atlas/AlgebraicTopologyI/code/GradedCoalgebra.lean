/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Graded.External

open scoped TensorProduct DirectSum

universe u v w

/-- **Definition 26.1 (Graded coalgebra).**  A `ι`-graded coalgebra over a
commutative ring `R` is a coalgebra structure on the direct sum
`⨁_i M i` whose coproduct `Δ : M → M ⊗ M` respects the grading: for any
homogeneous element `x ∈ M_n`, the component of `Δ x` in degree `(p, q)`
vanishes whenever `p + q ≠ n`.  In other words, `Δ(M_n) ⊆ ⨁_{p+q=n} M_p ⊗ M_q`.
This is the coalgebraic analogue of a graded algebra and is the structure
carried by the cohomology of a (Hopf) space. -/
class GradedCoalgebra (R : Type u) [CommRing R]
    {ι : Type v} [CommSemiring ι] [Module ι (Additive ℤˣ)] [DecidableEq ι]
    (M : ι → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    extends Coalgebra R (⨁ i, M i) where
  comul_respects_grading :
    ∀ (n : ι) (x : M n) (p q : ι), p + q ≠ n →
      DirectSum.component R (ι × ι)
        (fun pq : ι × ι => (M pq.1) ⊗[R] (M pq.2))
        (p, q)
        ((TensorProduct.directSum R R M M)
          (comul (DirectSum.lof R ι M n x))) = 0

/-- **Definition 26.1 / Corollary 26.2 (Cocommutative graded coalgebra).**
A graded coalgebra is *graded-cocommutative* when its coproduct is
invariant under the Koszul-signed twist on the tensor product:
`τ ∘ Δ = Δ`, where `τ : M ⊗ M → M ⊗ M` sends
`a ⊗ b ↦ (-1)^{|a||b|} b ⊗ a` on homogeneous elements.  The diagonal map
on a topological space induces such a cocommutative graded-coalgebra
structure on its singular cohomology (Cor 26.2). -/
class CommGradedCoalgebra (R : Type u) [CommRing R]
    {ι : Type v} [CommSemiring ι] [Module ι (Additive ℤˣ)] [DecidableEq ι]
    (M : ι → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    extends GradedCoalgebra R M where
  comul_comm :
    (TensorProduct.gradedComm R M M).toLinearMap ∘ₗ comul = comul
