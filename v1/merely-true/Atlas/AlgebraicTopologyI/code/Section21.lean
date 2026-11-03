/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact

namespace TensorProductsAndTor

/-- **Proposition 21.1 (Right exactness of tensor product).**  Tensoring a
short exact sequence `N' → N → N'' → 0` of `R`-modules on the left by a
fixed module `M` preserves exactness at `N` and surjectivity at `N''`.
That is, the sequence
`M ⊗ N' → M ⊗ N → M ⊗ N'' → 0` is exact.  Tensor product is *right* exact
but in general not left exact, which motivates the definition of `Tor`. -/
theorem tensor_right_exact
    {R : Type*} [CommRing R]
    {N' N N'' : Type*}
    [AddCommGroup N'] [AddCommGroup N] [AddCommGroup N'']
    [Module R N'] [Module R N] [Module R N'']
    (M : Type*) [AddCommGroup M] [Module R M]
    (f : N' →ₗ[R] N) (g : N →ₗ[R] N'')
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.lTensor M f) (LinearMap.lTensor M g) ∧
    Function.Surjective (LinearMap.lTensor M g) :=
  ⟨lTensor_exact M hfg hg, LinearMap.lTensor_surjective M hg⟩

/-- **Lemma 21.2 (Exactness of direct sums).**  A family of sequences
`M' i → M i → M'' i` is exact at each index `i` if and only if the
direct-sum sequence `⨁ M' i → ⨁ M i → ⨁ M'' i` is exact.  This formalizes
the statement that direct sums of modules commute with taking
homology/exactness; it is the key fact used to compute `Tor` of a direct
sum as a direct sum of `Tor`'s. -/
theorem directSum_exact
    {R : Type*} [Semiring R]
    {ι : Type*}
    {M' : ι → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {M'' : ι → Type*} [∀ i, AddCommMonoid (M'' i)] [∀ i, Module R (M'' i)]
    (f : ∀ i, M' i →ₗ[R] M i) (g : ∀ i, M i →ₗ[R] M'' i)
    (hexact : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff, DirectSum.ker_lmap, DirectSum.range_lmap]
  congr 1
  simp_rw [fun i => LinearMap.exact_iff.mp (hexact i)]

end TensorProductsAndTor
