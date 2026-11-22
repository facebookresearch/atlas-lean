/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AdeleQuotientDim
import Mathlib.Order.ModularLattice

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

section Lemma22_9

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

















/-- Modular-lattice / second-isomorphism dimension identity. For submodules
$A \le B$ and any $F$ of a module $M$, the dimension of
$(B + F)/(A + F)$ plus the dimension of $(B \cap F)/(A \cap F)$ equals the
dimension of $B/A$, and finite-dimensionality is inherited. -/
theorem finrank_sup_quotient_eq {R : Type*} [DivisionRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (A B F_sub : Submodule R M) (hAB : A ≤ B)
    [hFD : FiniteDimensional R (↥B ⧸ Submodule.comap B.subtype A)]
    [hFD_inf : FiniteDimensional R (↥(B ⊓ F_sub) ⧸
        Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub))] :
    FiniteDimensional R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) ∧
    Module.finrank R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) +
      Module.finrank R (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) =
    Module.finrank R (↥B ⧸ Submodule.comap B.subtype A) := by
  set T := A ⊔ (B ⊓ F_sub) with hT_def

  have hAT : A ≤ T := le_sup_left
  have hTB : T ≤ B := sup_le hAB inf_le_left

  have h_modular : B ⊓ (A ⊔ F_sub) = T := by
    rw [sup_comm (a := A) (b := F_sub)]
    rw [← inf_sup_assoc_of_le F_sub hAB]
    rw [sup_comm]

  have hBsup : B ⊔ (A ⊔ F_sub) = B ⊔ F_sub := by
    rw [← sup_assoc, sup_eq_left.mpr hAB]

  have hABF_inf : A ⊓ (B ⊓ F_sub) = A ⊓ F_sub := by
    rw [← inf_assoc, inf_eq_left.mpr hAB]


  have e_2nd_BF := LinearMap.quotientInfEquivSupQuotient (B ⊓ F_sub) A


  have h_comap_eq_inf : Submodule.comap (B ⊓ F_sub).subtype (B ⊓ F_sub) ⊓
      Submodule.comap (B ⊓ F_sub).subtype A =
    Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub) := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
    exact ⟨fun h => ⟨h, hx.2⟩, fun ⟨h, _⟩ => h⟩


  have e_TA : (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) ≃ₗ[R]
      (↥((B ⊓ F_sub) ⊔ A) ⧸ Submodule.comap ((B ⊓ F_sub) ⊔ A).subtype A) := by
    rw [← h_comap_eq_inf]; exact e_2nd_BF

  have hTA_comm : (B ⊓ F_sub) ⊔ A = T := sup_comm (a := B ⊓ F_sub) (b := A)

  haveI : FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype A) := by
    rw [← hTA_comm]
    exact Module.Finite.equiv e_TA


  have e_2nd_B := LinearMap.quotientInfEquivSupQuotient B (A ⊔ F_sub)

  have h_comap_eq_T : Submodule.comap B.subtype B ⊓ Submodule.comap B.subtype (A ⊔ F_sub) =
      Submodule.comap B.subtype T := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    rw [← h_modular]
    exact ⟨fun h => ⟨hx, h⟩, fun ⟨_, h⟩ => h⟩

  have e_BT : (↥B ⧸ Submodule.comap B.subtype T) ≃ₗ[R]
      (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) := by
    rw [← h_comap_eq_T, ← hBsup]; exact e_2nd_B


  haveI : FiniteDimensional R (↥B ⧸ Submodule.comap B.subtype T) := by


    have h_le : Submodule.comap B.subtype A ≤ Submodule.comap B.subtype T :=
      Submodule.comap_mono hAT
    let f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[R]
        (↥B ⧸ Submodule.comap B.subtype T) :=
      (Submodule.comap B.subtype A).liftQ
        (Submodule.comap B.subtype T).mkQ
        (fun x hx => by
          simp only [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact h_le hx)
    have hf_surj : Function.Surjective f := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine ⟨Submodule.Quotient.mk y, ?_⟩
      simp only [f, Submodule.liftQ_apply, Submodule.mkQ_apply]
    exact Module.Finite.of_surjective f hf_surj

  haveI : FiniteDimensional R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) :=
    Module.Finite.equiv e_BT

  have h_chain := finrank_comap_chain A T B hAT hTB
  obtain ⟨_, h_chain_eq⟩ := h_chain

  have hd_BT : Module.finrank R (↥B ⧸ Submodule.comap B.subtype T) =
    Module.finrank R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) :=
    LinearEquiv.finrank_eq e_BT
  have hd_TA : Module.finrank R (↥T ⧸ Submodule.comap T.subtype A) =
    Module.finrank R (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) := by
    rw [← hTA_comm]; exact (LinearEquiv.finrank_eq e_TA).symm
  exact ⟨inferInstance, by omega⟩

/-- Additivity of divisor degree: $\deg(A + B) = \deg A + \deg B$. -/
lemma adeleDivisorDeg_add (A B : P →₀ ℤ) :
    adeleDivisorDeg (F := F) (k := k) (O := O) (A + B) =
    adeleDivisorDeg (F := F) (k := k) (O := O) A +
    adeleDivisorDeg (F := F) (k := k) (O := O) B := by
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_add_index (fun p => by simp) (fun p _ a b => by ring)]

/-- Behavior of divisor degree under subtraction:
$\deg(B - A) = \deg B - \deg A$. -/
lemma adeleDivisorDeg_sub (A B : P →₀ ℤ) :
    adeleDivisorDeg (F := F) (k := k) (O := O) (B - A) =
    adeleDivisorDeg (F := F) (k := k) (O := O) B -
    adeleDivisorDeg (F := F) (k := k) (O := O) A := by
  rw [sub_eq_add_neg, adeleDivisorDeg_add]
  congr 1
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_neg_index (fun p => by simp)]
  simp only [Finsupp.sum, neg_mul]
  exact Finset.sum_neg_distrib _



end Lemma22_9
