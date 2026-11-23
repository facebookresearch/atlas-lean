/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Constructions.SumProd
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Localization.FractionRing

open Topology Set
open scoped TensorProduct

/-- The product of two closed embeddings is a closed embedding: if `f : X₁ → Y₁` and
`g : X₂ → Y₂` are closed embeddings, then so is `Prod.map f g : X₁ × X₂ → Y₁ × Y₂`. This
is the topological input to showing that products of separated schemes are separated. -/
theorem closedEmbedding_prodMap {X₁ Y₁ X₂ Y₂ : Type*}
    [TopologicalSpace X₁] [TopologicalSpace Y₁]
    [TopologicalSpace X₂] [TopologicalSpace Y₂]
    {f : X₁ → Y₁} {g : X₂ → Y₂}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) :
    IsClosedEmbedding (Prod.map f g) where
  toIsEmbedding := hf.toIsEmbedding.prodMap hg.toIsEmbedding
  isClosed_range := by
    rw [Set.range_prodMap]
    exact hf.isClosed_range.prod hg.isClosed_range

/-- A product of two closed sets is closed in the product topology. -/
theorem isClosed_prod_of_isClosed {Y₁ Y₂ : Type*}
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    {S₁ : Set Y₁} {S₂ : Set Y₂}
    (h₁ : IsClosed S₁) (h₂ : IsClosed S₂) :
    IsClosed (S₁ ×ˢ S₂) :=
  h₁.prod h₂

/-- The tensor product of two surjective linear maps is surjective: if `f : M → M'` and
`g : N → N'` are surjective, then `f ⊗ g : M ⊗ N → M' ⊗ N'` is surjective. This is the
algebraic counterpart of the closed embedding fact for products of affine schemes. -/
theorem tensorProduct_map_surjective {R M N M' N' : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    {f : M →ₗ[R] M'} {g : N →ₗ[R] N'}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (TensorProduct.map f g) :=
  TensorProduct.map_surjective hf hg

/-- The tensor product of two surjective `R`-algebra homomorphisms is surjective. Used to
show that closed immersions are preserved under taking products of schemes over a base. -/
theorem algHom_tensorProduct_map_surjective {R A₁ B₁ A₂ B₂ : Type*}
    [CommSemiring R] [CommSemiring A₁] [CommSemiring B₁]
    [CommSemiring A₂] [CommSemiring B₂]
    [Algebra R A₁] [Algebra R B₁] [Algebra R A₂] [Algebra R B₂]
    {φ : A₁ →ₐ[R] B₁} {ψ : A₂ →ₐ[R] B₂}
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) :
    Function.Surjective (Algebra.TensorProduct.map φ ψ) :=
  TensorProduct.map_surjective hφ hψ

/-- Two ring homomorphisms `f, g : A → B` into a domain `B` that satisfy the cross-ratio
relation `f a · g s = g a · f s` for all `a`, with `g s ≠ 0`, are equal. A separation-style
cancellation lemma used in the proof that the diagonal of a variety is closed. -/
theorem ringHom_eq_of_crossRatio {A B : Type*} [CommRing A] [CommRing B]
    [NoZeroDivisors B]
    (f g : A →+* B) {s : A}
    (hgs : g s ≠ 0)
    (h : ∀ a : A, f a * g s = g a * f s) : f = g := by
  have hs_eq : f s = g s := by
    have h1 := h 1; simp at h1; exact h1.symm
  ext a
  rw [hs_eq] at h
  exact mul_right_cancel₀ hgs (h a)

/-- Two ring homomorphisms out of a localization `S = M⁻¹R` are equal as soon as they
agree on the image of the base ring `R`. The universal property of localization. -/
theorem ringHom_eq_of_eq_on_base {R : Type*} [CommSemiring R]
    (M : Submonoid R) {S : Type*} [CommSemiring S]
    [Algebra R S] [IsLocalization M S]
    {P : Type*} [Semiring P]
    (j k : S →+* P) (h : ∀ a : R, j (algebraMap R S a) = k (algebraMap R S a)) :
    j = k :=
  IsLocalization.ringHom_ext M (RingHom.ext h)

/-- Two field homomorphisms out of a fraction field `K = Frac(A)` are equal as soon as
they agree on the image of the domain `A`. Specialization of the localization universal
property to fraction fields. -/
theorem fieldHom_eq_of_eq_on_domain {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L]
    (f g : K →+* L) (h : ∀ a : A, f (algebraMap A K a) = g (algebraMap A K a)) :
    f = g :=
  IsFractionRing.ringHom_ext h
