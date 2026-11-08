/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Basics
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open Complex
open scoped Classical

abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

structure SL2C_UnitaryRep where
  V : Type*
  [instNACG : NormedAddCommGroup V]
  [instIPS : InnerProductSpace ℂ V]
  [instCS : CompleteSpace V]
  action : SL2C →* V ≃ₗᵢ[ℂ] V

attribute [instance] SL2C_UnitaryRep.instNACG
  SL2C_UnitaryRep.instIPS SL2C_UnitaryRep.instCS

def SL2C_UnitaryRep.IsIrreducible (ρ : SL2C_UnitaryRep) : Prop :=
  ∀ S : Submodule ℂ ρ.V, IsClosed (S : Set ρ.V) →
    (∀ g : SL2C, ∀ v ∈ S, (ρ.action g) v ∈ S) → S = ⊥ ∨ S = ⊤

def SL2C_UnitaryRep.IsUnitarilyEquiv (ρ₁ ρ₂ : SL2C_UnitaryRep) : Prop :=
  ∃ (T : ρ₁.V ≃ₗᵢ[ℂ] ρ₂.V), ∀ g : SL2C, ∀ v : ρ₁.V,
    T (ρ₁.action g v) = ρ₂.action g (T v)

def trivialSL2CRep : SL2C_UnitaryRep where
  V := ℂ
  action :=
    { toFun := fun _ => LinearIsometryEquiv.refl ℂ ℂ
      map_one' := rfl
      map_mul' := fun _ _ => by ext; simp }

structure PSActionBundle where
  action : ℤ → ℝ → SL2C →* (lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
  symm : ∀ m t, action m t = action (-m) (-t)

structure CSActionBundle where
  action : (s : ℝ) → (-1 : ℝ) < s → s < 1 →
    SL2C →* (lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
  symm : ∀ (s : ℝ) (hs1 : (-1 : ℝ) < s) (hs2 : s < 1)
    (hs1' : (-1 : ℝ) < -s) (hs2' : -s < 1),
    action s hs1 hs2 = action (-s) hs1' hs2'










lemma lp_single_linearIndependent :
    LinearIndependent ℂ (fun i : ℕ => lp.single 2 i (1 : ℂ)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h : ∀ k : ℕ, (∑ j ∈ s, g j • lp.single 2 j (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) k =
    (0 : lp (fun _ : ℕ => ℂ) 2) k := by
    intro k; exact congr_fun (congr_arg (fun x : lp (fun _ : ℕ => ℂ) 2 => (x : ℕ → ℂ)) hg) k
  specialize h i
  simp only [lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply,
    lp.coeFn_zero, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · simp [lp.single_apply] at h; exact h
  · intro j _ hji; simp [lp.single_apply, hji]
  · intro hi'; exact absurd hi hi'

lemma lp_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) := by
  intro h
  have hli := lp_single_linearIndependent.lt_aleph0_of_finiteDimensional
  simp only [Cardinal.mk_nat] at hli
  exact lt_irrefl _ hli

lemma no_liso_lp_complex :
    IsEmpty (lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] ℂ) := by
  constructor
  intro T
  have : FiniteDimensional ℂ (lp (fun _ : ℕ => ℂ) 2) :=
    T.symm.toLinearEquiv.finiteDimensional
  exact lp_not_finiteDimensional this


structure HCBimoduleParam where
  mu : ℂ
  lam : ℂ
  diff_is_int : ∃ n : ℤ, lam - mu = (n : ℂ)

def HCBimoduleParam.Equiv (ξ₁ ξ₂ : HCBimoduleParam) : Prop :=
  (ξ₁.mu = ξ₂.mu ∧ ξ₁.lam = ξ₂.lam) ∨
  (ξ₁.mu = -ξ₂.mu ∧ ξ₁.lam = -ξ₂.lam)

def HCBimoduleParam.neg (ξ : HCBimoduleParam) : HCBimoduleParam where
  mu := -ξ.mu
  lam := -ξ.lam
  diff_is_int := by
    obtain ⟨n, hn⟩ := ξ.diff_is_int
    exact ⟨-n, by push_cast; linear_combination -hn⟩

def HCBimoduleParam.IsSameSignNonzeroIntegers (ξ : HCBimoduleParam) : Prop :=
  ∃ (n m : ℤ), n ≠ 0 ∧ m ≠ 0 ∧ (0 < n ∧ 0 < m ∨ n < 0 ∧ m < 0) ∧
    ξ.lam = (n : ℂ) ∧ ξ.mu = (m : ℂ)

def principalSeriesKTypes (k : ℤ) : Set ℕ :=
  {j : ℕ | ∃ i : ℕ, j = Int.natAbs k + 2 * i}


def IsHermitianPS (lam mu : ℂ) : Prop :=
  lam ^ 2 = starRingEnd ℂ mu ^ 2

inductive SL2C_IrredAdmissible where
  | finiteDim (n : ℕ)
  | principalSeries (lam mu : ℂ) (h_diff : ∃ k : ℤ, mu - lam = (k : ℂ))

def SL2C_IrredAdmissible.kTypes : SL2C_IrredAdmissible → Set ℕ
  | .finiteDim n => {n}
  | .principalSeries lam mu _ =>
      {j | ∃ k : ℕ, ∃ n : ℤ, mu - lam = (n : ℂ) ∧ j = Int.natAbs n + 2 * k}

end
