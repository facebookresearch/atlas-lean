/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.SL2Basics
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

open Module

noncomputable section

structure SL2GKModule
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    extends GKModule 𝔤 K 𝔨 Ad V where
  H : 𝔤
  E : 𝔤
  F : 𝔤
  bracket_HE : ⁅H, E⁆ = (2 : ℤ) • E
  bracket_HF : ⁅H, F⁆ = (-2 : ℤ) • F
  bracket_EF : ⁅E, F⁆ = H
  sl2_span : ∀ X : 𝔤, ∃ a b c : ℂ, X = a • H + b • E + c • F
  K_centralizes : ∀ k : K, Ad k H = H

namespace SL2GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {K : Type*} [Group K]
variable {𝔨 : LieSubalgebra ℂ 𝔤}
variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

def hEnd (M : SL2GKModule 𝔤 K 𝔨 Ad V) : Module.End ℂ V :=
  (LieModule.toEnd ℂ 𝔤 V) M.H

def weightSpace (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) : Submodule ℂ V :=
  Module.End.eigenspace M.hEnd (n : ℂ)

lemma mem_weightSpace_iff (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) (v : V) :
    v ∈ M.weightSpace n ↔ ⁅M.H, v⁆ = (n : ℂ) • v := by
  simp [weightSpace, hEnd]

theorem H_acts_as_scalar_on_weight_space (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) (v : V)
    (hv : v ∈ weightSpace M n) :
    ⁅M.H, v⁆ = (n : ℂ) • v :=
  (mem_weightSpace_iff M n v).mp hv

theorem E_shifts_weight (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) (v : V)
    (hv : v ∈ M.weightSpace n) :
    ⁅M.E, v⁆ ∈ M.weightSpace (n + 2) := by
  rw [mem_weightSpace_iff] at hv ⊢


  rw [leibniz_lie]


  rw [M.bracket_HE, zsmul_lie]


  rw [hv, lie_smul]


  rw [← Int.cast_smul_eq_zsmul ℂ (2 : ℤ) (⁅M.E, v⁆), ← add_smul]
  congr 1
  push_cast
  ring

theorem F_shifts_weight (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) (v : V)
    (hv : v ∈ weightSpace M n) :
    ⁅M.F, v⁆ ∈ weightSpace M (n - 2) := by
  rw [mem_weightSpace_iff] at hv ⊢


  rw [leibniz_lie M.H M.F v, M.bracket_HF, hv, zsmul_lie, lie_smul]

  rw [← Int.cast_smul_eq_zsmul ℂ (-2 : ℤ) ⁅M.F, v⁆]
  rw [← add_smul]
  congr 1
  push_cast
  ring


def iterLie (X : 𝔤) (v : V) : ℕ → V
  | 0 => v
  | k + 1 => ⁅X, iterLie X v k⁆

omit [LieAlgebra ℂ 𝔤] [Module ℂ V] [LieModule ℂ 𝔤 V] in
@[simp] lemma iterLie_zero (X : 𝔤) (v : V) : iterLie X v 0 = v := rfl
omit [LieAlgebra ℂ 𝔤] [Module ℂ V] [LieModule ℂ 𝔤 V] in
@[simp] lemma iterLie_succ (X : 𝔤) (v : V) (k : ℕ) :
    iterLie X v (k + 1) = ⁅X, iterLie X v k⁆ := rfl

theorem iterLie_E_weight_shift (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) (v : V)
    (hv : v ∈ M.weightSpace n) (k : ℕ) :
    iterLie M.E v k ∈ M.weightSpace (n + 2 * (k : ℤ)) := by
  induction k with
  | zero => simp; exact hv
  | succ k ih =>
    simp only [iterLie_succ]
    have hstep := E_shifts_weight M (n + 2 * (k : ℤ)) (iterLie M.E v k) ih
    convert hstep using 1
    congr 1; omega

theorem iterLie_F_weight_shift (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) (v : V)
    (hv : v ∈ M.weightSpace n) (k : ℕ) :
    iterLie M.F v k ∈ M.weightSpace (n - 2 * (k : ℤ)) := by
  induction k with
  | zero => simp; exact hv
  | succ k ih =>
    simp only [iterLie_succ]
    have hstep := F_shifts_weight M (n - 2 * (k : ℤ)) (iterLie M.F v k) ih
    convert hstep using 1
    congr 1; omega


lemma submodule_eq_of_le_sup_disjoint
    (A B C : Submodule ℂ V)
    (hB_le_A : B ≤ A)
    (hBC_top : B ⊔ C = ⊤)
    (hAC_bot : A ⊓ C = ⊥) :
    A = B := by
  apply le_antisymm
  · have h : A ⊓ C ⊔ B = A ⊓ (C ⊔ B) := inf_sup_assoc_of_le C hB_le_A
    have key : A ≤ A ⊓ C ⊔ B := by
      intro x hx
      have : x ∈ A ⊓ (C ⊔ B) :=
        ⟨hx, by rw [sup_comm]; exact (hBC_top ▸ Submodule.mem_top)⟩
      rwa [← h] at this
    rwa [hAC_bot, bot_sup_eq] at key
  · exact hB_le_A

lemma eigenspace_inf_span_other_eq_bot
    (f : Module.End ℂ V) (μ : ℂ)
    (S : Set V) (hS : ∀ s ∈ S, ∃ m : ℂ, m ≠ μ ∧ s ∈ f.eigenspace m) :
    f.eigenspace μ ⊓ Submodule.span ℂ S = ⊥ :=
  (Disjoint.mono_right (Submodule.span_le.mpr fun s hs =>
    let ⟨m, hm_ne, hm_mem⟩ := hS s hs
    Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem hm_ne hm_mem))
    (Module.End.independent_genEigenspace f 1 μ)).eq_bot


def ktypeSet (M : SL2GKModule 𝔤 K 𝔨 Ad V) : Set ℤ :=
  {n : ℤ | M.weightSpace n ≠ ⊥}

theorem sl2_generates (M : SL2GKModule 𝔤 K 𝔨 Ad V) (X : 𝔤) :
    ∃ a b c : ℂ, X = a • M.H + b • M.E + c • M.F :=
  M.sl2_span X

theorem K_centralizes_H (M : SL2GKModule 𝔤 K 𝔨 Ad V) (k : K) :
    Ad k M.H = M.H :=
  M.K_centralizes k

lemma K_preserves_weightSpace (M : SL2GKModule 𝔤 K 𝔨 Ad V) (j : ℤ)
    (k : K) (v : V) (hv : v ∈ M.weightSpace j) :
    M.toGKModule.σ k v ∈ M.weightSpace j := by
  rw [mem_weightSpace_iff] at hv ⊢


  have heq := M.toGKModule.equivariance k M.H v

  rw [K_centralizes_H M k] at heq

  rw [hv] at heq

  rw [map_smul] at heq

  exact heq.symm

lemma lie_action_preserves_parity_submodule (M : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hAdm : M.toGKModule.IsAdmissible)
    (n₀ : ℤ) (X : 𝔤) (v : V) (j : ℤ) (hv : v ∈ M.weightSpace j)
    (hparity : ∃ k : ℤ, j = n₀ + 2 * k) :
    ⁅X, v⁆ ∈ ⨆ (k : ℤ), M.weightSpace (n₀ + 2 * k) := by
  obtain ⟨a, b, c, hX⟩ := sl2_generates M X
  rw [hX]

  simp only [add_lie, smul_lie]


  obtain ⟨kj, hkj⟩ := hparity


  have hHv : ⁅M.H, v⁆ ∈ M.weightSpace j := by
    rw [H_acts_as_scalar_on_weight_space M j v hv]
    exact Submodule.smul_mem _ _ hv
  have hEv : ⁅M.E, v⁆ ∈ M.weightSpace (j + 2) := E_shifts_weight M j v hv
  have hFv : ⁅M.F, v⁆ ∈ M.weightSpace (j - 2) := F_shifts_weight M j v hv

  have ha : a • ⁅M.H, v⁆ ∈ ⨆ (k : ℤ), M.weightSpace (n₀ + 2 * k) := by
    apply Submodule.mem_iSup_of_mem kj
    rw [hkj] at hHv
    exact Submodule.smul_mem _ a hHv

  have hb : b • ⁅M.E, v⁆ ∈ ⨆ (k : ℤ), M.weightSpace (n₀ + 2 * k) := by
    apply Submodule.mem_iSup_of_mem (kj + 1)
    have : n₀ + 2 * (kj + 1) = j + 2 := by omega
    rw [this]
    exact Submodule.smul_mem _ b hEv

  have hc : c • ⁅M.F, v⁆ ∈ ⨆ (k : ℤ), M.weightSpace (n₀ + 2 * k) := by
    apply Submodule.mem_iSup_of_mem (kj - 1)
    have : n₀ + 2 * (kj - 1) = j - 2 := by omega
    rw [this]
    exact Submodule.smul_mem _ c hFv
  exact Submodule.add_mem _ (Submodule.add_mem _ ha hb) hc

theorem pbw_weight_same_parity
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hIrr : M.toGKModule.IsIrreducibleGKModule)
    (hAdm : M.toGKModule.IsAdmissible)
    (n m : ℤ)
    (hn : n ∈ M.ktypeSet) (hm : m ∈ M.ktypeSet) :
    Even n ↔ Even m := by

  by_contra h_contra

  set S := ⨆ k : ℤ, M.weightSpace (n + 2 * k) with hS_def

  have hS_sub : M.toGKModule.IsSubmodule S := by
    constructor
    ·
      intro X w hw


      exact Submodule.iSup_induction (motive := fun w => ⁅X, w⁆ ∈ S)
        _ hw
        (fun k v hv => lie_action_preserves_parity_submodule M hAdm n X v (n + 2 * k) hv ⟨k, rfl⟩)
        (by simp [lie_zero])
        (fun a b ha hb => by show ⁅X, a + b⁆ ∈ S; rw [lie_add]; exact Submodule.add_mem S ha hb)
    ·
      intro k w hw
      exact Submodule.iSup_induction (motive := fun w => M.toGKModule.σ k w ∈ S)
        _ hw
        (fun j v hv => Submodule.mem_iSup_of_mem j (K_preserves_weightSpace M (n + 2 * j) k v hv))
        (by simp [map_zero])
        (fun a b ha hb => by show M.toGKModule.σ k (a + b) ∈ S; rw [map_add]; exact Submodule.add_mem S ha hb)

  have hS_ne_bot : S ≠ ⊥ := by
    intro hbot

    apply hn
    rw [eq_bot_iff]

    calc M.weightSpace n
        = M.weightSpace (n + 2 * 0) := by ring_nf
      _ ≤ S := le_iSup (fun k : ℤ => M.weightSpace (n + 2 * k)) 0
      _ = ⊥ := hbot

  have hS_top : S = ⊤ := by
    rcases hIrr S hS_sub with hbot | htop
    · exact absurd hbot hS_ne_bot
    · exact htop

  have hne : ∀ k : ℤ, (m : ℂ) ≠ (↑(n + 2 * k) : ℂ) := by
    intro k heq
    have hmk : m = n + 2 * k := by exact_mod_cast heq
    exact h_contra (by subst hmk; simp [Int.even_add])

  have hdisjoint : Disjoint (M.weightSpace m) S := by
    have hind := Module.End.independent_genEigenspace M.hEnd (1 : ℕ∞)
    have hdisjoint_ind := hind (↑m)
    have hle : S ≤ ⨆ μ, ⨆ (_ : μ ≠ (↑m : ℂ)), M.hEnd.eigenspace μ := by
      apply iSup_le; intro k
      have hne_k : (↑(n + 2 * k) : ℂ) ≠ ↑m := (hne k).symm
      exact le_trans
        (le_iSup (fun _ : (↑(n + 2 * k) : ℂ) ≠ ↑m => M.hEnd.eigenspace ↑(n + 2 * k)) hne_k)
        (le_iSup (fun μ : ℂ => ⨆ (_ : μ ≠ ↑m), M.hEnd.eigenspace μ) ↑(n + 2 * k))
    exact Disjoint.mono_right hle hdisjoint_ind

  have hm_bot : M.weightSpace m = ⊥ := by
    rw [disjoint_iff] at hdisjoint
    calc M.weightSpace m
        = M.weightSpace m ⊓ ⊤ := (inf_top_eq _).symm
      _ = M.weightSpace m ⊓ S := by rw [hS_top]
      _ = ⊥ := hdisjoint

  exact hm hm_bot

end SL2GKModule

theorem sl2_linearIndependent : LinearIndependent ℂ ![sl2H, sl2E, sl2F] := by
  apply LinearIndependent.of_comp sl2C.toSubmodule.subtype
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three] at hg
  have h00 := congr_fun (congr_fun hg 0) 0
  have h01 := congr_fun (congr_fun hg 0) 1
  have h10 := congr_fun (congr_fun hg 1) 0
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
             sl2H, sl2E, sl2F, basisH_C, basisE_C, basisF_C,
             Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply,
             smul_eq_mul, Submodule.subtype_apply] at h00 h01 h10
  intro i
  fin_cases i <;> simp_all

def sl2Basis : Module.Basis (Fin 3) ℂ ↥sl2C :=
  basisOfLinearIndependentOfCardEqFinrank sl2_linearIndependent
    (by simp [Fintype.card_fin, finrank_sl2C])

end
