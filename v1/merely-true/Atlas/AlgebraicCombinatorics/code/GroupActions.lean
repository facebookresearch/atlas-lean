/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.QuotientPoset
import Atlas.AlgebraicCombinatorics.code.BooleanSperner
import Atlas.AlgebraicCombinatorics.code.BooleanUpDown
import Atlas.AlgebraicCombinatorics.code.OrderRaisingLemma

set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

open SpernerProperty MulAction Finset

namespace GroupActions

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

theorem quotientPosetCompl_antitone :
    Antitone (quotientPosetCompl (n := n) (G := G)) := by
  intro a b hab
  obtain ⟨S, T, rfl, rfl, hST⟩ := hab
  exact ⟨Finset.univ \ T, Finset.univ \ S,
    (quotientPosetCompl_mk T).symm, (quotientPosetCompl_mk S).symm,
    Finset.sdiff_subset_sdiff Subset.rfl hST⟩

theorem quotientPosetCompl_strictAnti :
    StrictAnti (quotientPosetCompl (n := n) (G := G)) := by
  intro a b hab
  obtain ⟨hab_le, hab_ne⟩ := hab
  refine ⟨quotientPosetCompl_antitone hab_le, fun hba => hab_ne ?_⟩
  have h1 := quotientPosetCompl_antitone hba
  rwa [quotientPosetCompl_involutive, quotientPosetCompl_involutive] at h1

theorem quotientPosetCompl_injective :
    Function.Injective (quotientPosetCompl (n := n) (G := G)) :=
  quotientPosetCompl_involutive.injective

theorem quotientPosetCompl_grade' (q : QuotientPoset n G) :
    letI := quotientPoset_gradeMinOrder n G
    grade ℕ (quotientPosetCompl q) = n - grade ℕ q :=
  quotientPosetRank_compl q

lemma out_card_of_grade (q : QuotientPoset n G) (i : ℕ)
    (hq : quotientPosetRank n G q = i) : q.out.card = i := by
  have h := @quotientPosetRank_mk n G q.out
  rw [Quotient.out_eq] at h; omega

def embedOrbits (i : ℕ)
    (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ) :
    BooleanUpDown.Level n i → ℝ :=
  fun ⟨S, hS⟩ =>
    f ⟨Quotient.mk (orbitRel G (Finset (Fin n))) S, by
      show quotientPosetRank n G _ = i
      rw [@quotientPosetRank_mk n G]; exact hS⟩

theorem embedOrbits_injective (i : ℕ) :
    Function.Injective (embedOrbits (n := n) (G := G) i) := by
  intro f g hfg
  ext ⟨q, hq⟩
  have hout := out_card_of_grade q i hq
  have h := congr_fun hfg ⟨q.out, hout⟩
  simp only [embedOrbits] at h
  have hrank : quotientPosetRank n G (Quotient.mk (orbitRel G _) q.out) = i := by
    rw [@quotientPosetRank_mk n G, hout]
  have heq : (⟨q, hq⟩ : { q : QuotientPoset n G // quotientPosetRank n G q = i }) =
      ⟨Quotient.mk (orbitRel G _) q.out, hrank⟩ :=
    Subtype.ext (Quotient.out_eq q).symm
  simp only [heq]
  exact h

def quotientUp (i : ℕ)
    (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ) :
    { q : QuotientPoset n G // quotientPosetRank n G q = i + 1 } → ℝ :=
  fun ⟨q, hq⟩ =>
    BooleanUpDown.up i (embedOrbits i f) ⟨q.out, out_card_of_grade q (i + 1) hq⟩

def quotientUpLinear (i : ℕ) :
    ({ q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ) →ₗ[ℝ]
    ({ q : QuotientPoset n G // quotientPosetRank n G q = i + 1 } → ℝ) :=
  { toFun := quotientUp i
    map_add' := fun f g => by
      ext ⟨q, hq⟩
      simp only [quotientUp, Pi.add_apply, BooleanUpDown.up, embedOrbits]
      rw [← Finset.sum_add_distrib]
      congr 1; ext x; split_ifs <;> ring
    map_smul' := fun c f => by
      ext ⟨q, hq⟩
      simp only [quotientUp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, BooleanUpDown.up,
        embedOrbits]
      rw [Finset.mul_sum]
      congr 1; ext x; split_ifs <;> ring }

lemma embedOrbits_invariant (i : ℕ)
    (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ)
    (σ : G) (S : Finset (Fin n)) (hS : S.card = i) :
    embedOrbits i f ⟨σ • S, by
      rw [Finset.card_smul_finset]; exact hS⟩ = embedOrbits i f ⟨S, hS⟩ := by
  simp only [embedOrbits]
  congr 1
  exact Subtype.ext (mk_smul_eq σ S)

lemma up_invariant_of_embedOrbits (i : ℕ)
    (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ)
    (T₁ T₂ : BooleanUpDown.Level n (i + 1))
    (horbit : Quotient.mk (orbitRel G (Finset (Fin n))) T₁.val =
              Quotient.mk (orbitRel G (Finset (Fin n))) T₂.val) :
    BooleanUpDown.up i (embedOrbits i f) T₁ =
    BooleanUpDown.up i (embedOrbits i f) T₂ := by
  obtain ⟨T₁, hT₁⟩ := T₁
  obtain ⟨T₂, hT₂⟩ := T₂
  simp only [BooleanUpDown.up]
  have hrel : (orbitRel G (Finset (Fin n))).r T₁ T₂ := Quotient.exact horbit
  rw [orbitRel_apply] at hrel
  obtain ⟨σ, hσ⟩ := hrel
  change σ • T₂ = T₁ at hσ
  let e : BooleanUpDown.Level n i ≃ BooleanUpDown.Level n i :=
    { toFun := fun ⟨S, hS⟩ => ⟨σ⁻¹ • S, by rw [Finset.card_smul_finset]; exact hS⟩
      invFun := fun ⟨S, hS⟩ => ⟨σ • S, by rw [Finset.card_smul_finset]; exact hS⟩
      left_inv := fun ⟨S, _⟩ => Subtype.ext (smul_inv_smul σ S)
      right_inv := fun ⟨S, _⟩ => Subtype.ext (inv_smul_smul σ S) }
  conv_rhs => rw [← Equiv.sum_comp e]
  congr 1; ext ⟨S, hS_card⟩
  simp only [e, Equiv.coe_fn_mk]
  have hiff : S ⊆ T₁ ↔ σ⁻¹ • S ⊆ T₂ := by
    constructor
    · intro h
      have h1 : σ⁻¹ • S ⊆ σ⁻¹ • T₁ := Finset.smul_finset_subset_smul_finset h
      rwa [show σ⁻¹ • T₁ = T₂ from by rw [← hσ, inv_smul_smul]] at h1
    · intro h
      have h1 : σ • (σ⁻¹ • S) ⊆ σ • T₂ := Finset.smul_finset_subset_smul_finset h
      rwa [smul_inv_smul, hσ] at h1
  simp only [show (S ⊆ T₁) = (σ⁻¹ • S ⊆ T₂) from propext hiff]
  split_ifs
  · exact (embedOrbits_invariant i f σ⁻¹ S hS_card).symm
  · rfl

theorem quotientUp_injective (i : ℕ) (hi : 2 * i + 1 ≤ n) :
    Function.Injective (quotientUp (n := n) (G := G) i) := by
  intro f g hfg
  apply embedOrbits_injective i
  apply BooleanUpDown.up_injective i (by omega : 2 * i < n)
  ext ⟨T, hT⟩
  set q := Quotient.mk (orbitRel G (Finset (Fin n))) T with hq_def
  have hqrank : quotientPosetRank n G q = i + 1 := by
    rw [hq_def, @quotientPosetRank_mk n G]; exact hT
  have h_at_rep_f := up_invariant_of_embedOrbits i f
    ⟨T, hT⟩ ⟨q.out, out_card_of_grade q (i + 1) hqrank⟩
    (by simp only [hq_def]; exact (Quotient.out_eq q).symm)
  have h_at_rep_g := up_invariant_of_embedOrbits i g
    ⟨T, hT⟩ ⟨q.out, out_card_of_grade q (i + 1) hqrank⟩
    (by simp only [hq_def]; exact (Quotient.out_eq q).symm)
  rw [h_at_rep_f, h_at_rep_g]
  exact congr_fun hfg ⟨q, hqrank⟩

theorem quotientUp_isOrderRaising (i : ℕ) :
    letI := quotientPoset_gradeMinOrder n G
    IsOrderRaisingLinearMap (quotientUpLinear (n := n) (G := G) i)
      (fun (O : { q : QuotientPoset n G // grade ℕ q = i })
           (O' : { q : QuotientPoset n G // grade ℕ q = i + 1 }) =>
        O.val < O'.val) := by
  letI := quotientPoset_gradeMinOrder n G
  intro O O' hne
  simp only [quotientUpLinear, LinearMap.coe_mk, AddHom.coe_mk,
    quotientUp, BooleanUpDown.up, embedOrbits] at hne
  by_contra h_not_lt
  apply hne
  apply Finset.sum_eq_zero
  intro ⟨S, hS_card⟩ _
  split_ifs with h_sub
  · simp only [Pi.single_apply]
    split_ifs with heq
    · exfalso; apply h_not_lt
      have hS_orbit : Quotient.mk (orbitRel G _) S = O.val := congr_arg Subtype.val heq
      refine ⟨⟨S, O'.val.out, hS_orbit, Quotient.out_eq O'.val, h_sub⟩, ?_⟩
      intro ⟨S', T', hS'eq, hT'eq, hS'T'⟩
      have hcS' : S'.card = i + 1 := by
        have := @quotientPosetRank_mk n G S'; rw [hS'eq] at this; linarith [O'.prop]
      have hcT' : T'.card = i := by
        have := @quotientPosetRank_mk n G T'; rw [hT'eq] at this; linarith [O.prop]
      have := Finset.card_le_card hS'T'
      omega
    · rfl
  · rfl

theorem quotientPoset_hasOrderRaisingMatching (i : ℕ) (hi : 2 * i + 1 ≤ n) :
    letI := quotientPoset_gradeMinOrder n G
    letI := quotientPoset_gradedPoset n G
    HasOrderRaisingMatching (α := QuotientPoset n G) i := by
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  have hU_inj : Function.Injective (quotientUpLinear (n := n) (G := G) i) := by
    intro f g hfg
    exact quotientUp_injective i hi (show quotientUp i f = quotientUp i g from hfg)
  have hU_ord := quotientUp_isOrderRaising (n := n) (G := G) i
  obtain ⟨μ, hμ_inj, hμ_ord⟩ :=
    order_matching_of_injective_order_raising _ _ hU_inj hU_ord
  refine ⟨fun q => if h : grade ℕ q = i then (μ ⟨q, h⟩).val else q, ?_, ?_, ?_⟩
  · intro x hx; simp only [dif_pos hx]; exact (μ ⟨x, hx⟩).prop
  · intro x hx; simp only [dif_pos hx]; exact hμ_ord ⟨x, hx⟩
  · intro x y hx hy heq
    simp only [dif_pos hx, dif_pos hy] at heq
    exact congr_arg Subtype.val (hμ_inj (Subtype.val_injective heq))

theorem quotientPoset_hasOrderLoweringMatching (i : ℕ) (hi : n + 1 ≤ 2 * i)
    (hin : i ≤ n) :
    letI := quotientPoset_gradeMinOrder n G
    letI := quotientPoset_gradedPoset n G
    HasOrderLoweringMatching (α := QuotientPoset n G) i := by
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  have hni : 2 * (n - i) + 1 ≤ n := by omega
  obtain ⟨φ, hφ_grade, hφ_lt, hφ_inj⟩ := quotientPoset_hasOrderRaisingMatching (n - i) hni
  let ψ : QuotientPoset n G → QuotientPoset n G :=
    fun q => quotientPosetCompl (φ (quotientPosetCompl q))
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro x hx
    show grade ℕ (ψ x) = i - 1
    simp only [ψ]
    have hc : grade ℕ (quotientPosetCompl x) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    rw [quotientPosetCompl_grade', hφ_grade _ hc]; omega
  · intro x hx
    show ψ x < x
    simp only [ψ]
    have hc : grade ℕ (quotientPosetCompl x) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    have h1 : quotientPosetCompl x < φ (quotientPosetCompl x) := hφ_lt _ hc
    have h2 := quotientPosetCompl_strictAnti h1
    rwa [quotientPosetCompl_involutive] at h2
  · intro x y hx hy heq
    show x = y
    simp only [ψ] at heq
    have hc1 : grade ℕ (quotientPosetCompl x) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    have hc2 : grade ℕ (quotientPosetCompl y) = n - i := by
      rw [quotientPosetCompl_grade']; omega
    exact quotientPosetCompl_injective
      (hφ_inj _ _ hc1 hc2 (quotientPosetCompl_injective heq))

theorem quotientPoset_hasOrderMatchings :
    letI := quotientPoset_gradeMinOrder n G
    letI := quotientPoset_gradedPoset n G
    HasOrderMatchings (α := QuotientPoset n G) (n / 2) := by
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  refine ⟨Nat.div_le_self n 2, ?_, ?_⟩
  · intro i hi; exact quotientPoset_hasOrderRaisingMatching i (by omega)
  · intro i hi hin; exact quotientPoset_hasOrderLoweringMatching i (by omega) hin

theorem boolean_quotient_unimodal :
    letI := quotientPoset_gradeMinOrder n G
    letI := quotientPoset_gradedPoset n G
    IsRankUnimodal (α := QuotientPoset n G) := by
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  exact orderMatchings_imp_unimodal (n / 2) quotientPoset_hasOrderMatchings

theorem boolean_quotient_sperner :
    letI := quotientPoset_gradeMinOrder n G
    letI := quotientPoset_gradedPoset n G
    HasSpernerProperty (α := QuotientPoset n G) := by
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  exact orderMatchings_imp_sperner (n / 2) quotientPoset_hasOrderMatchings

end GroupActions

namespace GraphIsoPoset

open SpernerProperty GroupActions

def edgeCount (m : ℕ) : ℕ := m.choose 2

section EdgeAction

variable {m : ℕ}

def EdgeSubsets (m : ℕ) : Type :=
  { s : Finset (Fin m) // s.card = 2 }

def edgeSubsetsPowersetEquiv :
    EdgeSubsets m ≃ (Finset.univ.powersetCard 2 : Finset (Finset (Fin m))) where
  toFun := fun ⟨s, hs⟩ => ⟨s, by
    rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ s, hs⟩⟩
  invFun := fun ⟨s, hs⟩ => ⟨s, by
    rw [Finset.mem_powersetCard] at hs; exact hs.2⟩
  left_inv := fun ⟨s, _⟩ => Subtype.ext rfl
  right_inv := fun ⟨s, _⟩ => Subtype.ext rfl

noncomputable instance edgeSubsets_mulAction :
    MulAction (Equiv.Perm (Fin m)) (EdgeSubsets m) where
  smul σ e := ⟨σ • e.val, by rw [Finset.card_smul_finset]; exact e.prop⟩
  one_smul e := Subtype.ext (one_smul _ e.val)
  mul_smul σ τ e := Subtype.ext (mul_smul σ τ e.val)

noncomputable instance edgeSubsets_fintype : Fintype (EdgeSubsets m) := by
  classical
  exact Fintype.ofEquiv _ edgeSubsetsPowersetEquiv.symm

lemma card_edgeSubsets (m : ℕ) : Fintype.card (EdgeSubsets m) = edgeCount m := by
  classical
  rw [Fintype.card_congr edgeSubsetsPowersetEquiv, Fintype.card_coe, edgeCount,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

noncomputable def edgeBij (m : ℕ) : EdgeSubsets m ≃ Fin (edgeCount m) :=
  Fintype.equivFinOfCardEq (card_edgeSubsets m)

noncomputable def edgeActionHom (m : ℕ) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin (edgeCount m)) :=
  ((edgeBij m).permCongrHom).toMonoidHom.comp
    (MulAction.toPermHom (Equiv.Perm (Fin m)) (EdgeSubsets m))

end EdgeAction

noncomputable def graphIsoGroup (m : ℕ) : Subgroup (Equiv.Perm (Fin (edgeCount m))) :=
  (edgeActionHom m).range

abbrev GraphPoset (m : ℕ) : Type :=
  QuotientPoset (edgeCount m) (graphIsoGroup m)

theorem graph_sequence_symmetric (m : ℕ) :
    letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m)
    letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m)
    IsRankSymmetric (α := GraphPoset m) :=
  quotientPoset_isRankSymmetric (edgeCount m) (graphIsoGroup m)

theorem graph_sequence_unimodal (m : ℕ) :
    letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m)
    letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m)
    IsRankUnimodal (α := GraphPoset m) :=
  boolean_quotient_unimodal

theorem graph_poset_sperner (m : ℕ) :
    letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m)
    letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m)
    HasSpernerProperty (α := GraphPoset m) :=
  boolean_quotient_sperner

theorem maxRankCount_eq_middle_of_symmetric_unimodal
    {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    [GradeMinOrder ℕ α] [GradedPoset α]
    (hsym : IsRankSymmetric (α := α))
    (huni : IsRankUnimodal (α := α)) :
    maxRankCount (α := α) = rankCount (α := α) (GradedPoset.rank (α := α) / 2) := by

  obtain ⟨j, hj, hinc, hdec⟩ := huni

  set n := GradedPoset.rank (α := α)

  have hj_max : ∀ i, i ≤ n → rankCount (α := α) i ≤ rankCount (α := α) j := by
    intro i hi
    by_cases hij : i ≤ j
    · exact hinc i j hij le_rfl
    · push_neg at hij
      exact hdec j i le_rfl (le_of_lt hij) hi

  have hmax_eq_j : maxRankCount (α := α) = rankCount (α := α) j := by
    apply le_antisymm
    ·
      unfold maxRankCount
      apply Finset.sup_le
      intro i hi
      rw [Finset.mem_range] at hi
      exact hj_max i (by omega)
    ·
      exact rankCount_le_maxRankCount j hj

  suffices h : rankCount (α := α) (n / 2) = rankCount (α := α) j by
    rw [hmax_eq_j, h]

  apply le_antisymm
  ·
    exact hj_max (n / 2) (Nat.div_le_self n 2)
  ·

    have hsym_j : rankCount (α := α) (n - j) = rankCount (α := α) j :=
      (hsym j hj).symm
    rw [← hsym_j]


    by_cases hjn : j ≤ n / 2
    ·
      exact hdec (n / 2) (n - j) (by omega) (by omega) (by omega)
    ·
      push_neg at hjn
      exact hinc (n - j) (n / 2) (by omega) (by omega)

theorem graph_poset_max_antichain_level (m : ℕ) :
    letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m)
    letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m)
    maxRankCount (α := GraphPoset m) = rankCount (α := GraphPoset m) (edgeCount m / 2) := by
  letI := quotientPoset_gradeMinOrder (edgeCount m) (graphIsoGroup m)
  letI := quotientPoset_gradedPoset (edgeCount m) (graphIsoGroup m)
  exact maxRankCount_eq_middle_of_symmetric_unimodal
    (graph_sequence_symmetric m) (graph_sequence_unimodal m)

end GraphIsoPoset
