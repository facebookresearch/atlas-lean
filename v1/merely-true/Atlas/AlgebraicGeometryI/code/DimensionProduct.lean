/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.KrullDimensionAffineSpace
import Atlas.AlgebraicGeometryI.code.FiniteMorphismDimension
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Finite

set_option maxHeartbeats 800000

noncomputable section

open MvPolynomial

set_option backward.isDefEq.respectTransparency false

/-- The standard algebra isomorphism
`k[x₁,…,xₙ] ⊗_k k[y₁,…,yₘ] ≃ k[x₁,…,xₙ, y₁,…,yₘ]`. -/
def mvPolynomialTensorAlgEquiv (k : Type*) [CommRing k]
    (n m : ℕ) :
    TensorProduct k (MvPolynomial (Fin n) k) (MvPolynomial (Fin m) k) ≃ₐ[k]
      MvPolynomial (Fin (n + m)) k :=
  (tensorEquivSum k (Fin n) (Fin m) k).trans
    (renameEquiv k finSumFinEquiv)

/-- Computation `dim(k[x]_n ⊗_k k[x]_m) = n + m`, reflecting `A^n × A^m = A^{n+m}`. -/
theorem ringKrullDim_tensorProduct_mvPolynomial_field (k : Type*) [Field k]
    (n m : ℕ) :
    ringKrullDim (TensorProduct k (MvPolynomial (Fin n) k) (MvPolynomial (Fin m) k)) =
      ↑n + ↑m := by
  rw [dim_eq_of_ringEquiv (mvPolynomialTensorAlgEquiv k n m).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/-- Krull dimension is additive on tensor products of polynomial algebras:
`dim(A^n ⊗ A^m) = dim A^n + dim A^m`. -/
theorem ringKrullDim_tensorProduct_mvPolynomial_eq_add (k : Type*) [Field k]
    (n m : ℕ) :
    ringKrullDim (TensorProduct k (MvPolynomial (Fin n) k) (MvPolynomial (Fin m) k)) =
      ringKrullDim (MvPolynomial (Fin n) k) + ringKrullDim (MvPolynomial (Fin m) k) := by
  rw [ringKrullDim_tensorProduct_mvPolynomial_field,
      ringKrullDim_mvPolynomial_field, ringKrullDim_mvPolynomial_field]

/-- If `R` admits a Noether normalization, i.e. an injective finite `k`-algebra map
`k[x₁,…,x_s] → R`, then `dim R = s`. -/
theorem ringKrullDim_eq_of_noetherNormalization
    {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] R)
    (hinj : Function.Injective g) (hfin : g.Finite) :
    ringKrullDim R = ↑s := by
  letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) R := hfin
  have : ringKrullDim R = ringKrullDim (MvPolynomial (Fin s) k) :=
    @FiniteMorphismDimension.ringKrullDim_eq_of_injective_finite
      (MvPolynomial (Fin s) k) R _ _ g.toRingHom.toAlgebra ‹_› hinj
  rw [this, ringKrullDim_mvPolynomial_field]

/-- A nontrivial finitely generated `k`-algebra has finite Krull dimension equal to some
natural number. -/
theorem ringKrullDim_fg_algebra_eq_nat (k : Type*) [Field k]
    (R : Type*) [CommRing R] [Nontrivial R] [Algebra k R]
    [Algebra.FiniteType k R] :
    ∃ s : ℕ, ringKrullDim R = ↑s := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  exact ⟨s, ringKrullDim_eq_of_noetherNormalization s g hinj hfin⟩

/-- Helper: the tensor product of two injective `k`-algebra maps is injective (using that
every module over a field is flat). -/
theorem Algebra.TensorProduct.map_injective_of_field {k : Type*} [Field k]
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
    (f : A →ₐ[k] C) (g : B →ₐ[k] D)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map f g) := by


  have := TensorProduct.map_injective_of_flat_flat
    (f.toLinearMap) (g.toLinearMap) hf hg
  intro x y hxy
  exact this hxy

/-- Theorem 7.1: For finitely generated `k`-algebras `A` and `B`,
`dim(A ⊗_k B) = dim A + dim B`, i.e. `dim(X × Y) = dim X + dim Y`. -/
theorem ringKrullDim_tensorProduct_fg_algebra (k : Type*) [Field k]
    (A B : Type*) [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    [Nontrivial A] [Nontrivial B]
    [Nontrivial (TensorProduct k A B)] :
    ringKrullDim (TensorProduct k A B) =
      ringKrullDim A + ringKrullDim B := by

  obtain ⟨n, gA, hinjA, hfinA⟩ := exists_finite_inj_algHom_of_fg k A
  obtain ⟨m, gB, hinjB, hfinB⟩ := exists_finite_inj_algHom_of_fg k B

  have hdimA : ringKrullDim A = ↑n :=
    ringKrullDim_eq_of_noetherNormalization n gA hinjA hfinA
  have hdimB : ringKrullDim B = ↑m :=
    ringKrullDim_eq_of_noetherNormalization m gB hinjB hfinB

  let f := Algebra.TensorProduct.map gA gB
  have hf_inj : Function.Injective f :=
    Algebra.TensorProduct.map_injective_of_field gA gB hinjA hinjB

  let e := mvPolynomialTensorAlgEquiv k n m
  let g : MvPolynomial (Fin (n + m)) k →ₐ[k] TensorProduct k A B :=
    f.comp e.symm.toAlgHom
  have hg_inj : Function.Injective g := hf_inj.comp e.symm.injective


  have hg_fin : g.Finite := by


    have h1 : e.symm.toAlgHom.Finite :=
      AlgHom.Finite.of_surjective _ e.symm.surjective


    have h2 : f.Finite :=
      RingHom.Finite.tensorProductMap hfinA hfinB
    exact h2.comp h1

  have hdimAB : ringKrullDim (TensorProduct k A B) = ↑(n + m) :=
    ringKrullDim_eq_of_noetherNormalization (n + m) g hg_inj hg_fin
  rw [hdimAB, hdimA, hdimB]
  simp [Nat.cast_add]

end
