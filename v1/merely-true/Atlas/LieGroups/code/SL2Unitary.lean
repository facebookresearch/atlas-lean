/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Representations

set_option maxHeartbeats 800000

noncomputable section

open Complex

namespace SL2IrredGKModule

def principalSeriesParamSq : SL2IrredGKModule → ℂ
  | finiteDim n => ((n + 1 : ℕ) : ℂ) ^ 2
  | principalSeries ν _ => ν ^ 2
  | discreteSeriesPlus n _ => ((n : ℂ) - 1) ^ 2
  | discreteSeriesMinus n _ => ((n : ℂ) - 1) ^ 2
  | limitDiscretePlus => 0
  | limitDiscreteMinus => 0

def IsBargmannUnitary (μ : SL2IrredGKModule) : Prop :=
  (μ.principalSeriesParamSq.im = 0) ∧
  (∀ n ∈ μ.kTypes, (n + 2 : ℤ) ∈ μ.kTypes →
    μ.principalSeriesParamSq.re < ((n + 1 : ℤ) : ℝ) ^ 2)

end SL2IrredGKModule

inductive SL2UnitaryIrred where
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | unitaryPrincipalSeries (t : ℝ) (ε : ZMod 2) (hirred : t ≠ 0 ∨ ε = 0)
  | complementarySeries (s : ℝ) (hs_ne : s ≠ 0) (hs_sq : s ^ 2 < 1)
  | trivial

namespace SL2UnitaryIrred

def toIrredGKModule : SL2UnitaryIrred → SL2IrredGKModule
  | .discreteSeriesPlus m _ =>
      if h : m ≥ 2 then SL2IrredGKModule.discreteSeriesPlus m h
      else SL2IrredGKModule.limitDiscretePlus
  | .discreteSeriesMinus m _ =>
      if h : m ≥ 2 then SL2IrredGKModule.discreteSeriesMinus m h
      else SL2IrredGKModule.limitDiscreteMinus
  | .unitaryPrincipalSeries t ε _ =>
      SL2IrredGKModule.principalSeries ((↑t : ℂ) * I) ε
  | .complementarySeries s _ _ =>
      SL2IrredGKModule.principalSeries (↑s : ℂ) (0 : ZMod 2)
  | .trivial => SL2IrredGKModule.finiteDim 0

end SL2UnitaryIrred


lemma int_sq_ge_one_of_ne_zero (k : ℤ) (hk : k ≠ 0) : 1 ≤ k ^ 2 := by
  have : k ≤ -1 ∨ k ≥ 1 := by omega
  rcases this with h | h <;> nlinarith


lemma complex_sq_im_zero (ν : ℂ) (h : (ν ^ 2).im = 0) :
    ν.re = 0 ∨ ν.im = 0 := by
  simp only [sq, mul_im] at h
  have : 2 * ν.re * ν.im = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · norm_num at h2
    · left; exact h2
  · right; exact h1


lemma zmod2_ne_zero_eq_one (ε : ZMod 2) (h : ε ≠ 0) : ε = 1 := by
  fin_cases ε
  · exact absurd rfl h
  · rfl

theorem bargmann_classification (μ : SL2IrredGKModule) :
    μ.IsBargmannUnitary ↔ ∃ ν : SL2UnitaryIrred, ν.toIrredGKModule = μ := by
  constructor
  ·
    intro ⟨h_real, h_pos⟩
    cases μ with
    | finiteDim n =>
      by_cases hn : n = 0
      · exact ⟨.trivial, by subst hn; rfl⟩
      · exfalso
        have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
        have h_in : (-(n : ℤ)) ∈ (SL2IrredGKModule.finiteDim n).kTypes := by
          simp only [SL2IrredGKModule.kTypes, Set.mem_setOf_eq]
          constructor
          · omega
          · simp [Int.natAbs_neg]
        have h_in2 : (-(n : ℤ) + 2) ∈ (SL2IrredGKModule.finiteDim n).kTypes := by
          simp only [SL2IrredGKModule.kTypes, Set.mem_setOf_eq]
          constructor
          · omega
          · omega
        have h := h_pos (-(n : ℤ)) h_in h_in2
        simp only [SL2IrredGKModule.principalSeriesParamSq] at h
        have hre : (((n + 1 : ℕ) : ℂ) ^ 2).re = ((n + 1 : ℕ) : ℝ) ^ 2 := by
          simp [sq, mul_re]
        rw [hre] at h
        have hrhs : ((-(↑n : ℤ) + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) - 1) ^ 2 := by push_cast; ring
        rw [hrhs] at h
        have hn_real : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
        have hlhs : ((n + 1 : ℕ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
        rw [hlhs] at h
        linarith [show ((n : ℝ) + 1) ^ 2 - ((n : ℝ) - 1) ^ 2 = 4 * (n : ℝ) from by ring]
    | principalSeries ν ε =>
      simp only [SL2IrredGKModule.principalSeriesParamSq] at h_real h_pos
      set a := ν.re with ha_def
      set b := ν.im with hb_def
      rcases complex_sq_im_zero ν h_real with h_re0 | h_im0
      ·
        have hν_eq : ν = (↑b : ℂ) * I := by
          apply Complex.ext <;> simp [mul_re, mul_im, h_re0, I_re, I_im, ← hb_def]
        by_cases hb0 : b = 0
        ·
          have hν0 : ν = 0 := by apply Complex.ext <;> simp [h_re0, hb0, ← hb_def]
          by_cases hε : ε = 0
          ·
            refine ⟨.unitaryPrincipalSeries 0 0 (Or.inr rfl), ?_⟩
            simp only [SL2UnitaryIrred.toIrredGKModule]
            rw [hν0, hε]
            simp only [ofReal_zero, zero_mul]
          ·
            exfalso
            have hε1 : ε = 1 := zmod2_ne_zero_eq_one ε hε
            have hmem : (-1 : ℤ) ∈ (SL2IrredGKModule.principalSeries ν ε).kTypes := by
              show ((-1 : ℤ) : ZMod 2) = ε; rw [hε1]; decide
            have hmem1 : ((-1 : ℤ) + 2) ∈ (SL2IrredGKModule.principalSeries ν ε).kTypes := by
              show ((1 : ℤ) : ZMod 2) = ε; rw [hε1]; decide
            have h1 := h_pos (-1) hmem hmem1
            rw [hν0] at h1; simp at h1
        ·
          refine ⟨.unitaryPrincipalSeries b ε (Or.inl hb0), ?_⟩
          simp only [SL2UnitaryIrred.toIrredGKModule]
          exact congrArg₂ SL2IrredGKModule.principalSeries hν_eq.symm rfl
      ·
        have hν_eq : ν = (↑a : ℂ) := by
          apply Complex.ext <;> simp [h_im0, ← ha_def]
        have hre_sq : (ν ^ 2).re = a ^ 2 := by
          simp [sq, mul_re, h_im0, ← ha_def]
        by_cases hε : ε = 0
        ·
          have hmem0 : (0 : ℤ) ∈ (SL2IrredGKModule.principalSeries ν ε).kTypes := by
            show ((0 : ℤ) : ZMod 2) = ε; rw [hε]; decide
          have hmem2 : ((0 : ℤ) + 2) ∈ (SL2IrredGKModule.principalSeries ν ε).kTypes := by
            show ((2 : ℤ) : ZMod 2) = ε; rw [hε]; decide
          have h0 := h_pos 0 hmem0 hmem2
          rw [hre_sq] at h0
          have h0' : a ^ 2 < 1 := by
            have : ((0 + 1 : ℤ) : ℝ) ^ 2 = 1 := by norm_num
            linarith
          by_cases ha0 : a = 0
          ·
            refine ⟨.unitaryPrincipalSeries 0 0 (Or.inr rfl), ?_⟩
            simp only [SL2UnitaryIrred.toIrredGKModule]
            rw [hν_eq, ha0, hε]
            simp only [ofReal_zero, zero_mul]
          ·
            refine ⟨.complementarySeries a ha0 h0', ?_⟩
            simp only [SL2UnitaryIrred.toIrredGKModule]
            exact congrArg₂ SL2IrredGKModule.principalSeries hν_eq.symm hε.symm
        ·
          exfalso
          have hε1 : ε = 1 := zmod2_ne_zero_eq_one ε hε
          have hmem : (-1 : ℤ) ∈ (SL2IrredGKModule.principalSeries ν ε).kTypes := by
            show ((-1 : ℤ) : ZMod 2) = ε; rw [hε1]; decide
          have hmem1 : ((-1 : ℤ) + 2) ∈ (SL2IrredGKModule.principalSeries ν ε).kTypes := by
            show ((1 : ℤ) : ZMod 2) = ε; rw [hε1]; decide
          have h1 := h_pos (-1) hmem hmem1
          rw [hre_sq] at h1
          have : (((-1 : ℤ) + 1 : ℤ) : ℝ) ^ 2 = 0 := by norm_num
          linarith [sq_nonneg a]
    | discreteSeriesPlus n hn =>
      exact ⟨.discreteSeriesPlus n (by omega),
        by simp [SL2UnitaryIrred.toIrredGKModule, show n ≥ 2 from hn]⟩
    | discreteSeriesMinus n hn =>
      exact ⟨.discreteSeriesMinus n (by omega),
        by simp [SL2UnitaryIrred.toIrredGKModule, show n ≥ 2 from hn]⟩
    | limitDiscretePlus =>
      exact ⟨.discreteSeriesPlus 1 (by omega),
        by simp [SL2UnitaryIrred.toIrredGKModule]⟩
    | limitDiscreteMinus =>
      exact ⟨.discreteSeriesMinus 1 (by omega),
        by simp [SL2UnitaryIrred.toIrredGKModule]⟩
  ·
    intro ⟨ν, hν⟩
    rw [← hν]
    match ν with
    | .discreteSeriesPlus m hm =>
      simp only [SL2UnitaryIrred.toIrredGKModule]
      split_ifs with h
      ·
        refine ⟨?_, ?_⟩
        · simp [SL2IrredGKModule.principalSeriesParamSq, sq, mul_im, sub_im, one_im]
        · intro n hn' hn2
          simp only [SL2IrredGKModule.principalSeriesParamSq, SL2IrredGKModule.kTypes,
                      Set.mem_setOf_eq] at *
          have hre : (((m : ℂ) - 1) ^ 2).re = ((m : ℝ) - 1) ^ 2 := by
            simp [sq, mul_re, sub_re, one_re, sub_im, one_im]
          rw [hre]
          obtain ⟨hn_ge, _⟩ := hn'
          have h1 : (n : ℝ) ≥ (m : ℝ) := by exact_mod_cast hn_ge
          have h2 : (m : ℝ) ≥ 2 := by exact_mod_cast h
          have hrhs : ((n + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
          rw [hrhs]; nlinarith
      ·
        refine ⟨by simp [SL2IrredGKModule.principalSeriesParamSq], ?_⟩
        intro n hn' hn2
        simp only [SL2IrredGKModule.principalSeriesParamSq, SL2IrredGKModule.kTypes,
                    Set.mem_setOf_eq] at *
        simp only [zero_re]
        obtain ⟨hn_ge, _⟩ := hn'
        have h1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_ge
        have hrhs : ((n + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
        rw [hrhs]; nlinarith
    | .discreteSeriesMinus m hm =>
      simp only [SL2UnitaryIrred.toIrredGKModule]
      split_ifs with h
      ·
        refine ⟨?_, ?_⟩
        · simp [SL2IrredGKModule.principalSeriesParamSq, sq, mul_im, sub_im, one_im]
        · intro n hn' hn2
          simp only [SL2IrredGKModule.principalSeriesParamSq, SL2IrredGKModule.kTypes,
                      Set.mem_setOf_eq] at *
          have hre : (((m : ℂ) - 1) ^ 2).re = ((m : ℝ) - 1) ^ 2 := by
            simp [sq, mul_re, sub_re, one_re, sub_im, one_im]
          rw [hre]
          obtain ⟨hn_le, _⟩ := hn'
          obtain ⟨hn2_le, _⟩ := hn2
          have h1 : (n : ℝ) + 2 ≤ -(m : ℝ) := by exact_mod_cast hn2_le
          have h3 : (m : ℝ) ≥ 2 := by exact_mod_cast h
          have hrhs : ((n + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
          rw [hrhs]; nlinarith
      ·
        refine ⟨by simp [SL2IrredGKModule.principalSeriesParamSq], ?_⟩
        intro n hn' hn2
        simp only [SL2IrredGKModule.principalSeriesParamSq, SL2IrredGKModule.kTypes,
                    Set.mem_setOf_eq] at *
        simp only [zero_re]
        obtain ⟨hn_le, _⟩ := hn'
        obtain ⟨hn2_le, _⟩ := hn2
        have h1 : (n : ℝ) ≤ -3 := by exact_mod_cast (show n ≤ -3 by omega)
        have hrhs : ((n + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
        rw [hrhs]; nlinarith
    | .unitaryPrincipalSeries t ε hirred =>
      refine ⟨?_, ?_⟩
      ·
        simp only [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.principalSeriesParamSq]
        rw [mul_pow, I_sq, mul_neg_one]
        simp [neg_im, sq, mul_im, ofReal_re, ofReal_im]
      ·
        intro n hn hn2
        simp only [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.principalSeriesParamSq,
              SL2IrredGKModule.kTypes, Set.mem_setOf_eq] at *
        rw [mul_pow, I_sq, mul_neg_one]
        simp only [neg_re, sq, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

        by_cases hk : (n + 1 : ℤ) = 0
        ·

          have hn_eq : n = -1 := by omega
          rcases hirred with ht_ne | hε_eq
          ·
            have : ((n + 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hk
            simp only [this, mul_zero]; nlinarith [sq_pos_of_ne_zero ht_ne]
          ·
            exfalso
            rw [hn_eq] at hn
            rw [hε_eq] at hn
            revert hn; decide
        · have h1 := int_sq_ge_one_of_ne_zero (n + 1) hk
          have h2 : (1 : ℝ) ≤ ((n + 1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast h1
          have h3 : ((n + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
          nlinarith [sq_nonneg t]
    | .complementarySeries s hs_ne hs_lt =>
      refine ⟨?_, ?_⟩
      · simp [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.principalSeriesParamSq,
              sq, mul_im, ofReal_re, ofReal_im]
      · intro n hn hn2
        simp only [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.principalSeriesParamSq,
              SL2IrredGKModule.kTypes, Set.mem_setOf_eq] at *
        simp only [sq, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

        have hne : (n + 1 : ℤ) ≠ 0 := by
          intro h_eq; rw [show n = -1 from by omega] at hn
          revert hn; decide
        have h1 := int_sq_ge_one_of_ne_zero (n + 1) hne
        have h2 : (1 : ℝ) ≤ ((n + 1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast h1
        have h3 : ((n + 1 : ℤ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 := by push_cast; ring
        have h4 : s * s = s ^ 2 := by ring
        nlinarith
    | .trivial =>
      refine ⟨?_, ?_⟩
      · simp [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.principalSeriesParamSq]
      · intro n hn hn2
        simp only [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.principalSeriesParamSq,
              SL2IrredGKModule.kTypes, Set.mem_setOf_eq] at *
        obtain ⟨_, hn_abs⟩ := hn
        obtain ⟨_, hn2_abs⟩ := hn2
        omega

end

theorem theorem_9_3_gelfand_naimark_bargmann (μ : SL2IrredGKModule) :
    μ.IsBargmannUnitary ↔ ∃ ν : SL2UnitaryIrred, ν.toIrredGKModule = μ :=
  bargmann_classification μ

section IsomorphismClauses
open Complex

theorem unitaryPrincipalSeries_neg_kTypes (t : ℝ) (ε : ZMod 2) (h : t ≠ 0 ∨ ε = 0)
    (h' : -t ≠ 0 ∨ ε = 0) :
    (SL2UnitaryIrred.unitaryPrincipalSeries t ε h).toIrredGKModule.kTypes =
    (SL2UnitaryIrred.unitaryPrincipalSeries (-t) ε h').toIrredGKModule.kTypes := by


  simp only [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.kTypes]

theorem unitaryPrincipalSeries_neg_paramSq (t : ℝ) (ε : ZMod 2) (h : t ≠ 0 ∨ ε = 0)
    (h' : -t ≠ 0 ∨ ε = 0) :
    (SL2UnitaryIrred.unitaryPrincipalSeries t ε h).toIrredGKModule.principalSeriesParamSq =
    (SL2UnitaryIrred.unitaryPrincipalSeries (-t) ε h').toIrredGKModule.principalSeriesParamSq := by
  simp only [SL2UnitaryIrred.toIrredGKModule, SL2IrredGKModule.principalSeriesParamSq]
  push_cast
  ring

end IsomorphismClauses
