/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.HasseWalks
import Atlas.AlgebraicCombinatorics.code.YoungTableaux
import Mathlib.LinearAlgebra.Finsupp.LSum

noncomputable section

open scoped Classical

namespace WalkCountFormula

def liftU : (YoungDiagram →₀ ℤ) →ₗ[ℤ] (YoungDiagram →₀ ℤ) :=
  Finsupp.lsum ℤ (fun μ => LinearMap.id.smulRight (YoungDiagram.raisingOp μ))

def liftD : (YoungDiagram →₀ ℤ) →ₗ[ℤ] (YoungDiagram →₀ ℤ) :=
  Finsupp.lsum ℤ (fun μ => LinearMap.id.smulRight (YoungDiagram.loweringOp μ))

def iterU (n : ℕ) : (YoungDiagram →₀ ℤ) →ₗ[ℤ] (YoungDiagram →₀ ℤ) :=
  liftU ^ n

def emptyBasis : YoungDiagram →₀ ℤ := Finsupp.single ⊥ 1

@[simp]
theorem liftU_single (lam : YoungDiagram) (c : ℤ) :
    liftU (Finsupp.single lam c) = c • YoungDiagram.raisingOp lam := by
  simp only [liftU, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply]

@[simp]
theorem liftD_single (lam : YoungDiagram) (c : ℤ) :
    liftD (Finsupp.single lam c) = c • YoungDiagram.loweringOp lam := by
  simp only [liftD, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply]

theorem liftU_single_one (lam : YoungDiagram) :
    liftU (Finsupp.single lam 1) = YoungDiagram.raisingOp lam := by
  simp

theorem liftD_single_one (lam : YoungDiagram) :
    liftD (Finsupp.single lam 1) = YoungDiagram.loweringOp lam := by
  simp

lemma bot_colLen_zero : (⊥ : YoungDiagram).colLen 0 = 0 := by
  by_contra h
  have hpos : 0 < (⊥ : YoungDiagram).colLen 0 := Nat.pos_of_ne_zero h
  have hmem : (0, 0) ∈ (⊥ : YoungDiagram) := YoungDiagram.mem_iff_lt_colLen.mpr hpos
  have : (0, 0) ∈ (⊥ : YoungDiagram).cells := hmem
  simp at this

lemma removableRows_bot : YoungDiagram.removableRows ⊥ = ∅ := by
  simp only [YoungDiagram.removableRows, bot_colLen_zero, Finset.range_zero, Finset.filter_empty]

lemma coversDown_bot : YoungDiagram.coversDown ⊥ = ∅ := by
  simp only [YoungDiagram.coversDown, removableRows_bot, Finset.image_empty]

lemma loweringOp_bot : YoungDiagram.loweringOp ⊥ = 0 := by
  simp only [YoungDiagram.loweringOp, coversDown_bot, Finset.sum_empty]

theorem liftD_emptyBasis : liftD emptyBasis = 0 := by
  simp only [emptyBasis, liftD_single, one_smul, loweringOp_bot]

@[simp]
theorem iterU_zero : iterU 0 = LinearMap.id := by
  show liftU ^ 0 = LinearMap.id
  rw [pow_zero]
  rfl

theorem iterU_succ (n : ℕ) : iterU (n + 1) = iterU n ∘ₗ liftU := by
  show liftU ^ (n + 1) = (liftU ^ n) ∘ₗ liftU
  rw [pow_succ, Module.End.mul_eq_comp]

lemma raisingOp_apply (ν mu : YoungDiagram) :
    (YoungDiagram.raisingOp ν) mu = if mu ∈ ν.coversUp then 1 else 0 := by
  simp only [YoungDiagram.raisingOp]
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simp [Finset.sum_ite_eq']

lemma loweringOp_apply (σ mu : YoungDiagram) :
    (YoungDiagram.loweringOp σ) mu = if mu ∈ σ.coversDown then 1 else 0 := by
  simp only [YoungDiagram.loweringOp]
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simp [Finset.sum_ite_eq']

lemma liftD_raisingOp_apply (lam mu : YoungDiagram) :
    (liftD (YoungDiagram.raisingOp lam)) mu = YoungDiagram.DU_apply lam mu := by
  simp only [YoungDiagram.raisingOp, YoungDiagram.DU_apply, map_sum, liftD_single, one_smul]
  rw [Finset.sum_apply']

lemma liftU_loweringOp_apply (lam mu : YoungDiagram) :
    (liftU (YoungDiagram.loweringOp lam)) mu = YoungDiagram.UD_apply lam mu := by
  simp only [YoungDiagram.loweringOp, YoungDiagram.UD_apply, map_sum, liftU_single, one_smul]
  rw [Finset.sum_apply']

lemma DU_apply_eq_DUCoeff (lam mu : YoungDiagram) :
    YoungDiagram.DU_apply lam mu = ↑(YoungDiagram.DUCoeff lam mu) := by
  simp only [YoungDiagram.DU_apply, YoungDiagram.DUCoeff]
  simp_rw [loweringOp_apply]
  rw [Finset.sum_boole]

lemma UD_apply_eq_UDCoeff (lam mu : YoungDiagram) :
    YoungDiagram.UD_apply lam mu = ↑(YoungDiagram.UDCoeff lam mu) := by
  simp only [YoungDiagram.UD_apply, YoungDiagram.UDCoeff]
  simp_rw [raisingOp_apply]
  rw [Finset.sum_boole]

theorem liftD_comp_liftU_sub (f : YoungDiagram →₀ ℤ) :
    liftD (liftU f) - liftU (liftD f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    rw [add_sub_add_comm, hf, hg]
  | single a c =>
    simp only [liftU_single, liftD_single, map_smul]
    rw [← smul_sub]
    rw [show Finsupp.single a c = c • Finsupp.single a (1 : ℤ) from by
      rw [Finsupp.smul_single', mul_one]]
    congr 1
    ext mu
    simp only [Finsupp.sub_apply, Finsupp.single_apply]
    rw [liftD_raisingOp_apply, liftU_loweringOp_apply,
      DU_apply_eq_DUCoeff, UD_apply_eq_UDCoeff]
    have h := YoungDiagram.young_commutation_coeff a mu
    split_ifs with heq
    · subst heq; simp only [ite_true] at h; linarith
    · rw [if_neg heq] at h; linarith

theorem iterU_succ' (n : ℕ) : iterU (n + 1) = liftU ∘ₗ iterU n := by
  show liftU ^ (n + 1) = liftU ∘ₗ (liftU ^ n)
  rw [pow_succ', Module.End.mul_eq_comp]

lemma liftD_liftU_eq (f : YoungDiagram →₀ ℤ) :
    liftD (liftU f) = liftU (liftD f) + f := by
  have h := liftD_comp_liftU_sub f
  rw [sub_eq_iff_eq_add] at h
  rwa [add_comm] at h

theorem liftD_iterU_emptyBasis (k : ℕ) :
    liftD (iterU k emptyBasis) = (k : ℤ) • iterU (k - 1) emptyBasis := by
  induction k with
  | zero =>
    simp only [iterU_zero, LinearMap.id_apply, liftD_emptyBasis, Nat.zero_sub,
      Nat.cast_zero, zero_smul]
  | succ n ih =>
    simp only [Nat.succ_sub_one]
    rw [iterU_succ', LinearMap.comp_apply, liftD_liftU_eq, ih, map_smul]

    cases n with
    | zero =>
      simp only [Nat.zero_sub, iterU_zero, LinearMap.id_apply, Nat.cast_zero, zero_smul,
        zero_add, Nat.cast_one, one_smul]
    | succ m =>
      simp only [Nat.succ_sub_one]
      rw [← LinearMap.comp_apply (f := liftU) (g := iterU m), ← iterU_succ']

      have : ((↑(m + 1) + 1 : ℤ)) = (↑(m + 1 + 1) : ℤ) := by push_cast; ring
      rw [← this, add_smul, one_smul]

end WalkCountFormula

end
