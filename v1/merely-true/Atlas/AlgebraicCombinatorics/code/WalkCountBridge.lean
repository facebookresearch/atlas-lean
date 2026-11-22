/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff
import Atlas.AlgebraicCombinatorics.code.WalkCountOps

noncomputable section

open scoped Classical

open WalkCountFormula NormalOrderCoeff Finset

namespace WalkCountBridge

def toQ : (YoungDiagram →₀ ℤ) → (YoungDiagram →₀ ℚ) :=
  Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero

@[simp] theorem toQ_apply (f : YoungDiagram →₀ ℤ) (a : YoungDiagram) :
    (toQ f) a = ↑(f a) := by
  show Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero f a = ↑(f a)
  rw [Finsupp.mapRange_apply]

@[simp] theorem toQ_single (a : YoungDiagram) (c : ℤ) :
    toQ (Finsupp.single a c) = Finsupp.single a (↑c : ℚ) := by
  show Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero (Finsupp.single a c) = _
  rw [Finsupp.mapRange_single]

theorem toQ_zero : toQ (0 : YoungDiagram →₀ ℤ) = 0 := by ext; simp

theorem toQ_add (f g : YoungDiagram →₀ ℤ) : toQ (f + g) = toQ f + toQ g := by
  ext; simp [Int.cast_add]

theorem toQ_sub (f g : YoungDiagram →₀ ℤ) : toQ (f - g) = toQ f - toQ g := by
  ext; simp [Int.cast_sub]

theorem toQ_smul (c : ℤ) (f : YoungDiagram →₀ ℤ) : toQ (c • f) = (↑c : ℚ) • toQ f := by
  ext; simp [smul_eq_mul, Int.cast_mul]

def liftU_Q : (YoungDiagram →₀ ℚ) →ₗ[ℚ] (YoungDiagram →₀ ℚ) :=
  Finsupp.lsum ℚ fun μ => LinearMap.id.smulRight (toQ (YoungDiagram.raisingOp μ))

def liftD_Q : (YoungDiagram →₀ ℚ) →ₗ[ℚ] (YoungDiagram →₀ ℚ) :=
  Finsupp.lsum ℚ fun μ => LinearMap.id.smulRight (toQ (YoungDiagram.loweringOp μ))

def emptyBasis_Q : YoungDiagram →₀ ℚ := Finsupp.single ⊥ 1

@[simp] theorem liftU_Q_single (a : YoungDiagram) (c : ℚ) :
    liftU_Q (Finsupp.single a c) = c • toQ (YoungDiagram.raisingOp a) := by simp [liftU_Q]

@[simp] theorem liftD_Q_single (a : YoungDiagram) (c : ℚ) :
    liftD_Q (Finsupp.single a c) = c • toQ (YoungDiagram.loweringOp a) := by simp [liftD_Q]

theorem toQ_liftU (f : YoungDiagram →₀ ℤ) : toQ (liftU f) = liftU_Q (toQ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [toQ_zero]
  | add f g hf hg => simp only [map_add, toQ_add]; rw [hf, hg]
  | single a c => simp [toQ_smul]

theorem toQ_liftD (f : YoungDiagram →₀ ℤ) : toQ (liftD f) = liftD_Q (toQ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [toQ_zero]
  | add f g hf hg => simp only [map_add, toQ_add]; rw [hf, hg]
  | single a c => simp [toQ_smul]

theorem toQ_emptyBasis : toQ emptyBasis = emptyBasis_Q := by simp [emptyBasis, emptyBasis_Q]

theorem toQ_DplusU_pow (n : ℕ) (f : YoungDiagram →₀ ℤ) :
    toQ (((liftD + liftU) ^ n) f) = ((liftD_Q + liftU_Q) ^ n) (toQ f) := by
  induction n generalizing f with
  | zero =>
    simp only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_apply, LinearMap.comp_apply]
    rw [ih]
    congr 1
    show toQ ((liftD + liftU) f) = (liftD_Q + liftU_Q) (toQ f)
    simp only [LinearMap.add_apply, toQ_add, toQ_liftD, toQ_liftU]

theorem toQ_liftU_pow (n : ℕ) (f : YoungDiagram →₀ ℤ) :
    toQ ((liftU ^ n) f) = (liftU_Q ^ n) (toQ f) := by
  induction n generalizing f with
  | zero =>
    simp only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_apply, LinearMap.comp_apply, ih, toQ_liftU]

theorem liftD_Q_comp_liftU_Q_sub (f : YoungDiagram →₀ ℚ) :
    liftD_Q (liftU_Q f) - liftU_Q (liftD_Q f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add]; rw [add_sub_add_comm, hf, hg]
  | single a c =>

    have hZ := liftD_comp_liftU_sub (Finsupp.single a 1)
    simp only [liftU_single, one_smul, liftD_single, one_smul] at hZ

    simp only [liftU_Q_single, liftD_Q_single, map_smul, ← smul_sub]

    rw [← toQ_liftD (YoungDiagram.raisingOp a), ← toQ_liftU (YoungDiagram.loweringOp a)]

    rw [← toQ_sub, hZ]

    simp [Finsupp.smul_single', mul_one]

theorem liftD_Q_mul_liftU_Q_sub :
    liftD_Q * liftU_Q - liftU_Q * liftD_Q = 1 := by
  apply LinearMap.ext; intro f
  show liftD_Q (liftU_Q f) - liftU_Q (liftD_Q f) = f
  exact liftD_Q_comp_liftU_Q_sub f

theorem liftD_Q_emptyBasis_Q : liftD_Q emptyBasis_Q = 0 := by
  simp [emptyBasis_Q, loweringOp_bot, toQ_zero]

theorem liftD_Q_pow_emptyBasis_Q {j : ℕ} (hj : 0 < j) :
    (liftD_Q ^ j) emptyBasis_Q = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  induction k with
  | zero => simpa [pow_one] using liftD_Q_emptyBasis_Q
  | succ k _ =>
    rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply,
        liftD_Q_emptyBasis_Q, map_zero]

theorem pairsLE_filter_snd_zero (ℓ : ℕ) :
    (pairsLE ℓ).filter (fun p => p.2 = 0) =
    (Finset.range (ℓ + 1)).map ⟨fun i => (i, 0), fun a b h => by simpa using h⟩ := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, mem_pairsLE, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hab, hb⟩; subst hb; exact ⟨a, by omega, rfl⟩
  · rintro ⟨i, hi, heq⟩; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact ⟨by omega, rfl⟩

theorem normalOrder_term_apply (c : ℚ) (i j : ℕ) :
    (algebraMap ℚ (Module.End ℚ (YoungDiagram →₀ ℚ)) c *
      (liftU_Q ^ i * liftD_Q ^ j)) emptyBasis_Q =
    c • ((liftU_Q ^ i) ((liftD_Q ^ j) emptyBasis_Q)) := by
  show (algebraMap ℚ _ c * (liftU_Q ^ i * liftD_Q ^ j)) emptyBasis_Q = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, LinearMap.smul_apply, one_mul,
    Module.End.mul_eq_comp, LinearMap.comp_apply]

theorem normalOrder_emptyBasis_Q (ell : ℕ) :
    ((liftD_Q + liftU_Q) ^ ell) emptyBasis_Q =
      ∑ i ∈ Finset.range (ell + 1),
        normalOrderCoeff i 0 ell • ((liftU_Q ^ i) emptyBasis_Q) := by

  have hNO := NormalOrderCoeff.normalOrder_expansion liftD_Q liftU_Q
    liftD_Q_mul_liftU_Q_sub ell

  have heval : ((liftD_Q + liftU_Q) ^ ell) emptyBasis_Q =
    ∑ p ∈ pairsLE ell,
      (algebraMap ℚ _ (normalOrderCoeff p.1 p.2 ell) *
        (liftU_Q ^ p.1 * liftD_Q ^ p.2)) emptyBasis_Q := by
    conv_lhs => rw [hNO]
    rw [LinearMap.sum_apply]
  rw [heval]

  simp_rw [normalOrder_term_apply]

  rw [← Finset.sum_filter_add_sum_filter_not (pairsLE ell) (fun p => p.2 = 0)]
  have hkill : ∑ p ∈ (pairsLE ell).filter (fun p => ¬p.2 = 0),
    normalOrderCoeff p.1 p.2 ell • (liftU_Q ^ p.1) ((liftD_Q ^ p.2) emptyBasis_Q) = 0 := by
    apply Finset.sum_eq_zero; intro p hp
    simp only [Finset.mem_filter] at hp
    rw [liftD_Q_pow_emptyBasis_Q (Nat.pos_of_ne_zero hp.2), map_zero, smul_zero]
  rw [hkill, add_zero]

  rw [pairsLE_filter_snd_zero, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, pow_zero, Module.End.one_eq_id, LinearMap.id_apply]

theorem DplusU_pow_emptyBasis_eq_sum_bijCoeff_iterU
    (ell : ℕ) (lam : YoungDiagram) :
    ((((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ ell)
        WalkCountFormula.emptyBasis) lam : ℚ) =
      ∑ i ∈ Finset.range (ell + 1),
        NormalOrderCoeff.bijCoeff i 0 ell *
          ((WalkCountFormula.iterU i WalkCountFormula.emptyBasis) lam : ℚ) := by

  have hLHS : ((((liftD + liftU) ^ ell) emptyBasis) lam : ℚ) =
    (((liftD_Q + liftU_Q) ^ ell) emptyBasis_Q) lam := by
    rw [← toQ_apply]
    rw [toQ_DplusU_pow, toQ_emptyBasis]
  rw [hLHS, normalOrder_emptyBasis_Q]

  rw [Finset.sum_apply']

  congr 1; ext i
  simp only [Finsupp.smul_apply, smul_eq_mul]


  congr 1
  rw [show (liftU_Q ^ i) emptyBasis_Q = toQ ((liftU ^ i) emptyBasis) from by
    rw [toQ_liftU_pow, toQ_emptyBasis]]
  rw [toQ_apply]


  rfl

end WalkCountBridge

end
