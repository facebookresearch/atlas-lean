/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Representations


noncomputable section

open Complex

theorem GKModule.isIrreducibleGKModule_of_iso
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    {M : GKModule 𝔤 K 𝔨 Ad V} {N : GKModule 𝔤 K 𝔨 Ad W}
    (hiso : M.IsIsomorphicGK N) (hirr : M.IsIrreducibleGKModule) :
    N.IsIrreducibleGKModule := by
  obtain ⟨φ, hφ⟩ := hiso
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  intro U hU

  let U' := U.comap e.toLinearMap

  have hU' : M.IsSubmodule U' := by
    constructor
    ·
      intro X v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap ⁅X, v⁆ ∈ U
      rw [show e.toLinearMap ⁅X, v⁆ = φ.toLinearMap ⁅X, v⁆ from rfl, φ.lie_comm]
      exact hU.lie_invariant X (e.toLinearMap v) hv
    ·
      intro k v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap (M.σ k v) ∈ U
      rw [show e.toLinearMap (M.σ k v) = φ.toLinearMap (M.σ k v) from rfl, φ.group_comm]
      exact hU.group_invariant k (e.toLinearMap v) hv

  rcases hirr U' hU' with h | h
  ·
    left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have hew : e.symm w ∈ U' := by
      change e.toLinearMap (e.symm w) ∈ U
      simp [hw]
    have h0 := h (e.symm w) hew
    have : w = 0 := by
      have : e (e.symm w) = e 0 := by rw [h0]
      simp at this
      exact this
    exact this
  ·
    right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have : e.symm w ∈ U' := h (e.symm w)
    show w ∈ U
    have : e.toLinearMap (e.symm w) ∈ U := this
    rwa [show e.toLinearMap (e.symm w) = w from e.apply_symm_apply w] at this

def IsOddInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ) + 1

def IsEvenInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ)

inductive SL2SimpleModule where
  | finiteDim (m : ℕ)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | principalSeriesEven (s : ℂ) (hs : ¬ IsOddInteger s)
  | principalSeriesOdd (s : ℂ) (hs : ¬ IsEvenInteger s)

namespace SL2SimpleModule

def kTypes : SL2SimpleModule → Set ℤ
  | finiteDim m => { n : ℤ | n.natAbs ≤ m ∧ (n : ℤ) % 2 = (m : ℤ) % 2 }
  | discreteSeriesMinus m _ => { n : ℤ | n ≥ (m : ℤ) ∧ (n - (m : ℤ)) % 2 = 0 }
  | discreteSeriesPlus m _ => { n : ℤ | n ≤ -(m : ℤ) ∧ (n + (m : ℤ)) % 2 = 0 }
  | principalSeriesEven _ _ => { n : ℤ | n % 2 = 0 }
  | principalSeriesOdd _ _ => { n : ℤ | n % 2 = 1 ∨ n % 2 = -1 }

def casimirEigenvalue : SL2SimpleModule → ℂ
  | finiteDim m => ((m : ℂ) * ((m : ℂ) + 2)) / 4
  | discreteSeriesMinus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | discreteSeriesPlus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | principalSeriesEven s _ => (s ^ 2 - 1) / 4
  | principalSeriesOdd s _ => (s ^ 2 - 1) / 4

def IsIsomorphic : SL2SimpleModule → SL2SimpleModule → Prop
  | finiteDim m₁, finiteDim m₂ => m₁ = m₂
  | discreteSeriesMinus m₁ _, discreteSeriesMinus m₂ _ => m₁ = m₂
  | discreteSeriesPlus m₁ _, discreteSeriesPlus m₂ _ => m₁ = m₂
  | principalSeriesEven s₁ _, principalSeriesEven s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | principalSeriesOdd s₁ _, principalSeriesOdd s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | _, _ => False

end SL2SimpleModule
open SL2SimpleModule




def SL2SimpleModule.toIrredGK : SL2SimpleModule → SL2IrredGKModule
  | .finiteDim m => .finiteDim m
  | .discreteSeriesMinus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus
  | .discreteSeriesPlus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus
  | .principalSeriesEven s _ => .principalSeries s 0
  | .principalSeriesOdd s _ => .principalSeries s 1


end
