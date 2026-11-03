/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame
import Atlas.Buildings.code.SphericalBuilding.AdaptedBasisProof

set_option maxHeartbeats 1600000

namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


section ChamberToCompleteFlag

/-- In a strictly increasing list, indexed elements at strictly increasing positions are
strictly increasing. -/
theorem isChain_getElem_lt {α : Type*} [Preorder α] {l : List α} (hc : l.IsChain (· < ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l[i] < l[j] := by
  induction hij with
  | refl =>
    exact (List.isChain_iff_getElem.mp hc) i (by omega)
  | step _ ih =>
    have hstep := (List.isChain_iff_getElem.mp hc) _ (by omega)
    exact lt_trans (ih (by omega)) hstep

/-- Convert a chamber (maximal `SubspaceFlag`) into the corresponding `CompleteFlag` indexed
by $\mathrm{Fin}(n+1)$, where $\mathrm{spaces}\ 0 = \bot$ and $\mathrm{spaces}\ n = \top$. -/
noncomputable def chamberToCompleteFlag {n : ℕ} (σ : SubspaceFlag k n)
    (hchamber : IsChamber k n σ) (hn : n ≥ 2) : CompleteFlag k n where
  spaces i :=
    if h : i.val = 0 then ⊥
    else if h2 : i.val = n then ⊤
    else σ.chain[i.val - 1]'(by rw [hchamber]; omega)
  monotone := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Fin.le_iff_val_le_val] at hab
    simp only
    split_ifs with ha0 haN hb0 hbN hb0' hbN' <;>
      first
        | exact bot_le
        | exact le_refl _
        | exact le_top
        | (exfalso; omega)
        | skip

    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · have ha1 : a - 1 < b - 1 := by omega
      exact le_of_lt (isChain_getElem_lt σ.chain_strictly_increasing
        (by rw [hchamber]; omega) (by rw [hchamber]; omega) ha1)
  bot_eq := by simp
  top_eq := by
    simp only
    split_ifs with h0
    · omega
    · rfl

/-- The complete flag produced from a chamber is strict: $\dim_k(\mathrm{spaces}\ i) = i$ for
every $i \in \mathrm{Fin}(n+1)$. -/
theorem chamberToCompleteFlag_isStrictFlag {n : ℕ} (σ : SubspaceFlag k n)
    (hchamber : IsChamber k n σ) (hn : n ≥ 2) :
    (chamberToCompleteFlag σ hchamber hn).IsStrictFlag := by
  intro ⟨i, hi⟩
  show finrank k ↥((chamberToCompleteFlag σ hchamber hn).spaces ⟨i, hi⟩) = i
  by_cases h0 : i = 0
  · subst h0; simp [chamberToCompleteFlag]
  · by_cases hN : i = n
    · subst hN
      have heq : (chamberToCompleteFlag σ hchamber hn).spaces ⟨i, hi⟩ = ⊤ := by
        unfold chamberToCompleteFlag; simp [dif_neg h0]
      rw [heq]; simp
    · have heq : (chamberToCompleteFlag σ hchamber hn).spaces ⟨i, hi⟩ =
          σ.chain[i - 1]'(by rw [hchamber]; omega) := by
        unfold chamberToCompleteFlag; simp [dif_neg h0, dif_neg hN]
      rw [heq]

      have hlen := hchamber


      have hstrictly_increasing : ∀ (a b : ℕ) (ha : a < n - 1) (hb : b < n - 1),
          a < b → Module.finrank k (σ.chain[a]'(by rw [hlen]; exact ha)) <
                  Module.finrank k (σ.chain[b]'(by rw [hlen]; exact hb)) := by
        intro a b ha hb hab
        exact Submodule.finrank_lt_finrank_of_lt
          (isChain_getElem_lt σ.chain_strictly_increasing
            (by rw [hlen]; exact ha) (by rw [hlen]; exact hb) hab)

      have hpos : ∀ (j : ℕ) (hj : j < n - 1),
          0 < Module.finrank k (σ.chain[j]'(by rw [hlen]; exact hj)) := by
        intro j hj
        have hbot := (σ.chain_proper _ (List.getElem_mem (by rw [hlen]; exact hj))).1
        by_contra hle; push_neg at hle
        have h0 : Module.finrank k (σ.chain[j]'(by rw [hlen]; exact hj)) = 0 :=
          Nat.eq_zero_of_le_zero hle
        rw [Submodule.finrank_eq_zero] at h0
        exact hbot h0
      have hlt_n : ∀ (j : ℕ) (hj : j < n - 1),
          Module.finrank k (σ.chain[j]'(by rw [hlen]; exact hj)) < n := by
        intro j hj
        have htop := (σ.chain_proper _ (List.getElem_mem (by rw [hlen]; exact hj))).2
        have h1 := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr htop)
        simp at h1; exact h1


      have : ∀ (j : ℕ) (hj : j < n - 1),
          Module.finrank k (σ.chain[j]'(by rw [hlen]; exact hj)) = j + 1 := by


        intro j hj


        have hge : Module.finrank k (σ.chain[j]'(by rw [hlen]; exact hj)) ≥ j + 1 := by
          induction j with
          | zero => exact hpos 0 hj
          | succ j' ih =>
            have hj' : j' < n - 1 := by omega

            have h_inc := hstrictly_increasing j' (j' + 1) hj' hj (by omega)

            have h_ih := ih hj'
            omega

        have hle : Module.finrank k (σ.chain[j]'(by rw [hlen]; exact hj)) ≤ j + 1 := by
          by_contra hgt; push_neg at hgt
          have hge2 : Module.finrank k (σ.chain[j]'(by rw [hlen]; exact hj)) ≥ j + 2 := by omega


          have h_propagate : ∀ (m : ℕ) (hm : m < n - 1), j ≤ m →
              Module.finrank k (σ.chain[m]'(by rw [hlen]; exact hm)) ≥ m + 2 := by
            intro m hm hjm


            induction m with
            | zero =>

              have hj0 : j = 0 := by omega
              subst hj0
              exact hge2
            | succ m' ih_m =>
              by_cases hjm' : j = m' + 1
              · subst hjm'
                exact hge2
              · have hm'_lt : m' < n - 1 := by omega
                have hj_le_m' : j ≤ m' := by omega
                have := ih_m hm'_lt hj_le_m'
                have := hstrictly_increasing m' (m' + 1) hm'_lt hm (by omega)
                omega
          have h_last := h_propagate (n - 2) (by omega) (by omega)
          have h_bound := hlt_n (n - 2) (by omega)
          omega
        omega

      have := this (i - 1) (by omega)
      omega

/-- Every subspace appearing in the chamber's chain appears as `spaces i` of the associated
complete flag. -/
theorem chamberToCompleteFlag_contains {n : ℕ} (σ : SubspaceFlag k n)
    (hchamber : IsChamber k n σ) (hn : n ≥ 2)
    (V : Submodule k (Vec k n)) (hV : V ∈ σ.chain) :
    ∃ i : Fin (n + 1), (chamberToCompleteFlag σ hchamber hn).spaces i = V := by
  obtain ⟨j, hj_lt, rfl⟩ := List.getElem_of_mem hV
  rw [hchamber] at hj_lt
  refine ⟨⟨j + 1, by omega⟩, ?_⟩
  simp only [chamberToCompleteFlag]
  have h1 : ¬(j + 1 = 0) := by omega
  have h2 : ¬(j + 1 = n) := by omega
  simp [h2]

end ChamberToCompleteFlag


section JumpColInjectivity

/-- Symmetry of Schreier cell increments: swapping $(σ,τ)$ with $(τ,σ)$ and $(i,j)$ with
$(j,i)$ preserves the dimension increment $\dim(\mathrm{cell}_{ij}) - \dim(\mathrm{cell}_{i,j-1})$. -/
theorem schreierCell_increment_symm (σ τ : CompleteFlag k n)
    (_hσ : σ.IsStrictFlag) (_hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val)
    (j : Fin (n + 1)) (hj : 0 < j.val) :
    Module.finrank k ↥(schreierCell σ τ i hi j) -
      Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val - 1, by omega⟩) =
    Module.finrank k ↥(schreierCell τ σ j hj i) -
      Module.finrank k ↥(schreierCell τ σ j hj ⟨i.val - 1, by omega⟩) := by

  rw [schreierCell_eq_sup σ τ i hi j,
      schreierCell_eq_sup σ τ i hi ⟨j.val - 1, by omega⟩,
      schreierCell_eq_sup τ σ j hj i,
      schreierCell_eq_sup τ σ j hj ⟨i.val - 1, by omega⟩]

  set Vi := σ.spaces i
  set Vim1 := σ.spaces ⟨i.val - 1, by omega⟩
  set Wj := τ.spaces j
  set Wjm1 := τ.spaces ⟨j.val - 1, by omega⟩
  have hVle : Vim1 ≤ Vi := σ.monotone (Fin.mk_le_mk.mpr (by omega))
  have hWle : Wjm1 ≤ Wj := τ.monotone (Fin.mk_le_mk.mpr (by omega))

  have h_inf1 : Vim1 ⊓ (Vi ⊓ Wj) = Vim1 ⊓ Wj := by
    rw [← inf_assoc, inf_eq_left.mpr hVle]
  have h_inf2 : Vim1 ⊓ (Vi ⊓ Wjm1) = Vim1 ⊓ Wjm1 := by
    rw [← inf_assoc, inf_eq_left.mpr hVle]
  have h_inf3 : Wjm1 ⊓ (Wj ⊓ Vi) = Wjm1 ⊓ Vi := by
    rw [← inf_assoc, inf_eq_left.mpr hWle]
  have h_inf4 : Wjm1 ⊓ (Wj ⊓ Vim1) = Wjm1 ⊓ Vim1 := by
    rw [← inf_assoc, inf_eq_left.mpr hWle]

  have g1 := Submodule.finrank_sup_add_finrank_inf_eq Vim1 (Vi ⊓ Wj)
  have g2 := Submodule.finrank_sup_add_finrank_inf_eq Vim1 (Vi ⊓ Wjm1)
  have g3 := Submodule.finrank_sup_add_finrank_inf_eq Wjm1 (Wj ⊓ Vi)
  have g4 := Submodule.finrank_sup_add_finrank_inf_eq Wjm1 (Wj ⊓ Vim1)
  rw [h_inf1] at g1; rw [h_inf2] at g2; rw [h_inf3] at g3; rw [h_inf4] at g4

  have c1 : finrank k ↥(Vi ⊓ Wj) = finrank k ↥(Wj ⊓ Vi) := by rw [inf_comm]
  have c2 : finrank k ↥(Vi ⊓ Wjm1) = finrank k ↥(Wjm1 ⊓ Vi) := by rw [inf_comm]
  have c3 : finrank k ↥(Vim1 ⊓ Wj) = finrank k ↥(Wj ⊓ Vim1) := by rw [inf_comm]
  have c4 : finrank k ↥(Vim1 ⊓ Wjm1) = finrank k ↥(Wjm1 ⊓ Vim1) := by rw [inf_comm]
  omega

/-- The jump-column function transposes under swapping the two flags: a jump at position
$(i,j)$ in $(σ,τ)$ corresponds to a jump at $(j+1,i-1)$ in $(τ,σ)$. -/
theorem jumpCol_transpose (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val)
    (j : Fin n)
    (hj_spec : finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) =
               finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1) :
    finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ (by omega : 0 < j.val + 1) i) =
    finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ (by omega : 0 < j.val + 1)
      ⟨i.val - 1, by omega⟩) + 1 := by
  have hj1_pos : (0 : ℕ) < j.val + 1 := by omega
  have hsymm := schreierCell_increment_symm σ τ hσ hτ i hi
    ⟨j.val + 1, by omega⟩ hj1_pos


  have hge_lhs : finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) ≥
      finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) := by
    exact Submodule.finrank_mono (schreierCell_mono σ τ i hi
      ⟨j.val, by omega⟩ ⟨j.val + 1, by omega⟩ (Fin.mk_le_mk.mpr (by omega)))
  have hge : finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ hj1_pos i) ≥
      finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ hj1_pos
        ⟨i.val - 1, by omega⟩) := by
    exact Submodule.finrank_mono (schreierCell_mono τ σ ⟨j.val + 1, by omega⟩ hj1_pos
      ⟨i.val - 1, by omega⟩ i (Fin.mk_le_mk.mpr (by omega)))

  set A := finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) with hA_def
  set B := finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) with hB_def
  set C := finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ hj1_pos i) with hC_def
  set D := finrank k ↥(schreierCell τ σ ⟨j.val + 1, by omega⟩ hj1_pos ⟨i.val - 1, by omega⟩) with hD_def


  change A - B = C - D at hsymm
  omega

/-- The jump-column map $i \mapsto \mathrm{jumpCol}(i+1)$ from $\mathrm{Fin}\ n$ to
$\mathrm{Fin}\ n$ is injective; the Jordan–Hölder lines are indexed bijectively. -/
theorem jumpCol_injective (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) :
    Function.Injective (fun i : Fin n =>
      jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)) := by
  intro i₁ i₂ heq

  let f : Fin n → Fin n := fun i =>
    jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)

  change f i₁ = f i₂ at heq

  have hspec1 := jumpCol_spec σ τ hσ hτ
    ⟨i₁.val + 1, Nat.succ_lt_succ i₁.isLt⟩ (Nat.succ_pos _)

  have hspec2 := jumpCol_spec σ τ hσ hτ
    ⟨i₂.val + 1, Nat.succ_lt_succ i₂.isLt⟩ (Nat.succ_pos _)

  have htrans1 := jumpCol_transpose σ τ hσ hτ
    ⟨i₁.val + 1, Nat.succ_lt_succ i₁.isLt⟩ (Nat.succ_pos _) (f i₁) hspec1

  have htrans2 := jumpCol_transpose σ τ hσ hτ
    ⟨i₂.val + 1, Nat.succ_lt_succ i₂.isLt⟩ (Nat.succ_pos _) (f i₂) hspec2


  simp only at htrans1 htrans2

  have huniq1 := jumpCol_unique τ σ hτ hσ
    ⟨(f i₁).val + 1, by omega⟩ (by omega : 0 < (f i₁).val + 1)
    ⟨i₁.val, i₁.isLt⟩ htrans1
  have huniq2 := jumpCol_unique τ σ hτ hσ
    ⟨(f i₂).val + 1, by omega⟩ (by omega : 0 < (f i₂).val + 1)
    ⟨i₂.val, i₂.isLt⟩ htrans2


  have hval_eq : (f i₁).val = (f i₂).val := congr_arg Fin.val heq
  have hf1_lt : (f i₁).val < n := (f i₁).isLt
  have hf2_lt : (f i₂).val < n := (f i₂).isLt

  have hfin_eq : (⟨(f i₁).val + 1, by omega⟩ : Fin (n + 1)) =
      ⟨(f i₂).val + 1, by omega⟩ := Fin.ext (by simp; omega)

  have hrhs_eq : jumpCol τ σ hτ hσ ⟨(f i₁).val + 1, by omega⟩
      (by omega : 0 < (f i₁).val + 1) =
    jumpCol τ σ hτ hσ ⟨(f i₂).val + 1, by omega⟩
      (by omega : 0 < (f i₂).val + 1) := by
    congr 1
  have : (⟨i₁.val, i₁.isLt⟩ : Fin n) = ⟨i₂.val, i₂.isLt⟩ := by
    rw [huniq1, huniq2, hrhs_eq]
  exact Fin.ext (Fin.mk.inj this)

end JumpColInjectivity


section TauCompatibility

/-- If $\mathrm{jumpCol}(i+1) + 1 \le j$, then the Jordan–Hölder line $\mathrm{jhLine}\ i$
already lies inside $τ.\mathrm{spaces}\ j$. -/
theorem jhLine_mem_tau_of_le (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin n) (j : Fin (n + 1))
    (hij : (jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)).val + 1 ≤ j.val) :
    jhLine σ τ hσ hτ i ∈ τ.spaces j := by
  have hmem := jhGapVector_mem_Wj σ τ hσ hτ
    ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)
  exact τ.monotone (Fin.mk_le_mk.mpr hij) hmem

/-- The set of indices $i$ whose Jordan–Hölder line lies inside $τ.\mathrm{spaces}\ j$,
defined via $\mathrm{jumpCol}(i+1) < j$. -/
noncomputable def tauWitness (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (j : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n =>
    (jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)).val < j.val)

/-- The cardinality $|\mathrm{tauWitness}\ \sigma\ \tau\ j| = j$, by bijectivity of the
jump-column map. -/
theorem card_tauWitness_eq (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (j : Fin (n + 1)) :
    (tauWitness σ τ hσ hτ j).card = j.val := by
  set f := fun i : Fin n =>
    jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)
  have hinj : Function.Injective f := jumpCol_injective σ τ hσ hτ
  have hbij : Function.Bijective f := (Finite.injective_iff_bijective).mp hinj
  have h_tw : (tauWitness σ τ hσ hτ j) =
      Finset.univ.filter (fun i : Fin n => (f i).val < j.val) := rfl
  rw [h_tw]

  have hcard_target : (Finset.univ.filter (fun c : Fin n => c.val < j.val)).card = j.val := by
    rw [Fin.card_filter_val_lt]
    exact Nat.min_eq_right (by omega)

  let e : Fin n ≃ Fin n := Equiv.ofBijective f hbij

  have hcard_eq : (Finset.univ.filter (fun i : Fin n => (f i).val < j.val)).card =
      (Finset.univ.filter (fun c : Fin n => c.val < j.val)).card := by

    have : Finset.univ.filter (fun i : Fin n => (f i).val < j.val) =
        Finset.univ.filter (fun i : Fin n => (e i).val < j.val) := rfl
    rw [this]
    rw [show Finset.univ.filter (fun i : Fin n => (e i).val < j.val) =
        (Finset.univ.filter (fun c : Fin n => c.val < j.val)).map e.symm.toEmbedding from by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.toEmbedding_apply]
      constructor
      · intro h
        exact ⟨e i, h, by simp⟩
      · rintro ⟨c, hc, hci⟩
        have : i = e.symm c := hci.symm
        rw [this]
        simp [hc]]
    simp [Finset.card_map]
  rw [hcard_eq, hcard_target]

/-- The Jordan–Hölder frame is compatible with every $τ.\mathrm{spaces}\ j$, i.e.\
$τ.\mathrm{spaces}\ j = \bigoplus_{i \in \mathrm{tauWitness}\ j} \mathrm{jhLine}\ i$. -/
theorem jordanHolderFrame_compatible_tau (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)]
    (j : Fin (n + 1)) :
    (jordanHolderFrame σ τ hσ hτ).IsCompatible k n (τ.spaces j) := by
  use tauWitness σ τ hσ hτ j
  have hFD : FiniteDimensional k ↥(τ.spaces j) :=
    FiniteDimensional.finiteDimensional_submodule (τ.spaces j)
  symm
  apply biSup_span_singleton_eq_of_le_of_finrank (jhLine_linearIndependent σ τ hσ hτ)
  · apply iSup_le; intro i; apply iSup_le; intro hi
    simp only [tauWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    show k ∙ jhLine σ τ hσ hτ i ≤ τ.spaces j
    rw [Submodule.span_singleton_le_iff_mem]
    exact jhLine_mem_tau_of_le σ τ hσ hτ i j (by omega)
  · rw [hτ j, card_tauWitness_eq]

end TauCompatibility


/-- If $n \le 1$, then $k^n$ has no proper non-zero subspaces. -/
lemma no_proper_nonzero_subspace_of_le_one' {n : ℕ} (hn : n ≤ 1)
    (V : Submodule k (Vec k n)) (hbot : V ≠ ⊥) (htop : V ≠ ⊤) : False := by
  have hpos : 0 < finrank k V := by
    by_contra h
    push_neg at h
    have : finrank k V = 0 := Nat.eq_zero_of_le_zero h
    have := Submodule.finrank_eq_zero.mp this
    exact hbot this
  have hlt : finrank k V < n := by
    have h1 : finrank k ↥V < finrank k ↥(⊤ : Submodule k (Vec k n)) :=
      Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr htop)
    rw [finrank_top] at h1
    rwa [finrank_fin_fun] at h1
  omega

/-- If $n \le 1$, no `SubspaceFlag k n` exists (the chain would require a proper non-zero
subspace, which is impossible). -/
lemma subspaceFlag_empty_of_le_one' {n : ℕ} (hn : n ≤ 1) (σ : SubspaceFlag k n) : False := by
  obtain ⟨V, hV_mem⟩ := List.exists_mem_of_ne_nil _ σ.chain_nonempty
  exact no_proper_nonzero_subspace_of_le_one' hn V (σ.chain_proper V hV_mem).1 (σ.chain_proper V hV_mem).2


variable (k) (n : ℕ)

/-- Main: any two chambers $σ, τ$ admit a common frame, namely the Jordan–Hölder frame of
their associated complete flags. -/
noncomputable def twoChamberFrameHypUnconditional (hn : n ≥ 2) :
    TwoChamberFrameHyp k n where
  frame_of_two_chambers := fun σ τ hσ_chamber hτ_chamber => by

    let σ' := chamberToCompleteFlag σ hσ_chamber hn
    let τ' := chamberToCompleteFlag τ hτ_chamber hn
    have hσ_strict := chamberToCompleteFlag_isStrictFlag σ hσ_chamber hn
    have hτ_strict := chamberToCompleteFlag_isStrictFlag τ hτ_chamber hn

    let F := jordanHolderFrame σ' τ' hσ_strict hτ_strict
    refine ⟨F, ?_, ?_⟩
    ·
      intro V hV
      obtain ⟨i, hi⟩ := chamberToCompleteFlag_contains σ hσ_chamber hn V hV
      rw [← hi]
      exact jordanHolderFrame_compatible_sigma σ' τ' hσ_strict hτ_strict i
    ·
      intro V hV
      obtain ⟨j, hj⟩ := chamberToCompleteFlag_contains τ hτ_chamber hn V hV
      rw [← hj]
      exact jordanHolderFrame_compatible_tau σ' τ' hσ_strict hτ_strict j


/-- The common-apartment property holds unconditionally for $\mathrm{GL}_n(k)$: any two
flags lie in the apartment of some frame. The case $n \le 1$ is vacuous. -/
noncomputable def commonApartmentHypUnconditional :
    CommonApartmentHyp k n where
  refine_flags := fun σ τ => by
    by_cases hn : n ≤ 1
    · exact (subspaceFlag_empty_of_le_one' hn σ).elim
    · push_neg at hn
      have hn2 : n ≥ 2 := by omega
      exact (commonApartmentFromHyps n hn2
        (twoChamberFrameHypUnconditional k n hn2)).refine_flags σ τ

end GLnBuilding
