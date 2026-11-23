/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Card

open Finset MulAction
open scoped Pointwise

namespace SpernerProperty

abbrev QuotientPoset (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) : Type :=
  orbitRel.Quotient G (Finset (Fin n))

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

theorem card_eq_of_orbitRel {S T : Finset (Fin n)}
    (h : (orbitRel G (Finset (Fin n))).r S T) :
    S.card = T.card := by
  rw [orbitRel_apply] at h
  obtain ⟨g, hg⟩ := h
  rw [← hg]
  exact Finset.card_smul_finset g T

theorem card_eq_of_mk_eq {S T : Finset (Fin n)}
    (h : (Quotient.mk (orbitRel G (Finset (Fin n))) S) =
         (Quotient.mk (orbitRel G (Finset (Fin n))) T)) :
    S.card = T.card :=
  card_eq_of_orbitRel (Quotient.exact h)

noncomputable def quotientPosetRank (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
    QuotientPoset n G → ℕ :=
  Quotient.lift (fun S : Finset (Fin n) => S.card)
    (fun _ _ h => card_eq_of_orbitRel h)

@[simp]
theorem quotientPosetRank_mk (S : Finset (Fin n)) :
    quotientPosetRank n G (Quotient.mk _ S) = S.card :=
  rfl

theorem quotientPosetRank_le (q : QuotientPoset n G) :
    quotientPosetRank n G q ≤ n := by
  induction q using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetRank_mk]
    exact (Finset.card_le_univ S).trans (Fintype.card_fin n).le

theorem quotientPosetRank_univ :
    quotientPosetRank n G (Quotient.mk _ Finset.univ) = n := by
  simp only [quotientPosetRank_mk, Finset.card_univ, Fintype.card_fin]

section Order

theorem mk_smul_eq (g : G) (S : Finset (Fin n)) :
    Quotient.mk (orbitRel G (Finset (Fin n))) (g • S) =
    Quotient.mk (orbitRel G (Finset (Fin n))) S := by
  apply Quotient.sound
  show g • S ∈ orbit G S
  exact ⟨g, rfl⟩

instance quotientPosetPartialOrder :
    PartialOrder (QuotientPoset n G) where
  le a b := ∃ (S T : Finset (Fin n)),
    Quotient.mk (orbitRel G _) S = a ∧
    Quotient.mk (orbitRel G _) T = b ∧ S ⊆ T
  le_refl a := by
    induction a using Quotient.inductionOn with
    | _ S => exact ⟨S, S, rfl, rfl, Finset.Subset.refl _⟩
  le_trans a b c := by
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    have hrel : (orbitRel G (Finset (Fin n))).r T₁ S₂ :=
      Quotient.exact (hT₁.trans hS₂.symm)
    rw [orbitRel_apply] at hrel
    obtain ⟨g, hg_eq⟩ := hrel
    refine ⟨g⁻¹ • S₁, T₂, ?_, hT₂, ?_⟩
    · exact (mk_smul_eq g⁻¹ S₁).trans hS₁
    · calc g⁻¹ • S₁ ⊆ g⁻¹ • T₁ :=
            Finset.smul_finset_subset_smul_finset hsub₁
        _ = S₂ := by rw [← hg_eq, inv_smul_smul]
        _ ⊆ T₂ := hsub₂
  le_antisymm a b := by
    classical
    rintro ⟨S₁, T₁, hS₁, hT₁, hsub₁⟩ ⟨S₂, T₂, hS₂, hT₂, hsub₂⟩
    have hcard_a : S₁.card = T₂.card :=
      card_eq_of_mk_eq (hS₁.trans hT₂.symm)
    have hcard_b : T₁.card = S₂.card :=
      card_eq_of_mk_eq (hT₁.trans hS₂.symm)
    have h_card_eq : S₁.card = T₁.card := by
      have h1 := Finset.card_le_card hsub₁
      have h2 := Finset.card_le_card hsub₂
      omega
    have h_eq : S₁ = T₁ := Finset.eq_of_subset_of_card_le hsub₁ h_card_eq.symm.le
    rw [← hS₁, ← hT₁, h_eq]

end Order

noncomputable instance quotientPosetFintype :
    Fintype (QuotientPoset n G) := by
  classical
  exact Quotient.fintype _

theorem quotientPoset_ne_of_card_ne {S T : Finset (Fin n)}
    (hcard : S.card ≠ T.card) :
    (Quotient.mk (orbitRel G _) S) ≠ (Quotient.mk (orbitRel G _) T) := by
  intro heq
  exact hcard (card_eq_of_mk_eq heq)

section Grading

theorem quotientPosetRank_strictMono (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
    StrictMono (quotientPosetRank n G) := by
  classical
  intro a b hab
  obtain ⟨S, T, hS, hT, hsub⟩ := hab.le
  have hne : a ≠ b := ne_of_lt hab
  have hST : S ≠ T := by
    intro heq; subst heq; exact hne (hS ▸ hT)
  have hss : S ⊂ T := lt_of_le_of_ne hsub (by intro h; exact hST h)
  calc quotientPosetRank n G a
      = S.card := by rw [← hS]; rfl
    _ < T.card := Finset.card_lt_card hss
    _ = quotientPosetRank n G b := by rw [← hT]; rfl

theorem quotientPosetRank_covBy (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    {a b : QuotientPoset n G}
    (hcov : a ⋖ b) : quotientPosetRank n G a ⋖ quotientPosetRank n G b := by
  classical
  rw [Nat.covBy_iff_add_one_eq]
  have hlt := (quotientPosetRank_strictMono n G) hcov.lt
  by_contra h
  have hgap : quotientPosetRank n G a + 2 ≤ quotientPosetRank n G b := by omega
  obtain ⟨S, T, hS, hT, hsub⟩ := hcov.lt.le
  have hcard_S : quotientPosetRank n G a = S.card := by rw [← hS]; rfl
  have hcard_T : quotientPosetRank n G b = T.card := by rw [← hT]; rfl
  have hcard_gap : S.card + 2 ≤ T.card := by omega
  have hST : S ⊆ T := hsub
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
    rw [Finset.card_sdiff_of_subset hST]; omega : 0 < (T \ S).card)
  have hx_mem := Finset.mem_sdiff.mp hx
  let M := insert x S
  have hM_sub_T : M ⊆ T := by
    intro y hy
    simp only [M, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hx_mem.1
    · exact hsub hy
  have hS_sub_M : S ⊆ M := Finset.subset_insert x S
  have hM_card : M.card = S.card + 1 := Finset.card_insert_of_notMem hx_mem.2

  have hle_SM : a ≤ Quotient.mk _ M := ⟨S, M, hS, rfl, hS_sub_M⟩
  have hne_SM : a ≠ Quotient.mk _ M := by
    intro heq
    have := card_eq_of_mk_eq (hS.trans heq)
    omega
  have hlt_SM : a < Quotient.mk _ M := lt_of_le_of_ne hle_SM hne_SM

  have hle_MT : Quotient.mk _ M ≤ b := ⟨M, T, rfl, hT, hM_sub_T⟩
  have hne_MT : Quotient.mk _ M ≠ b := by
    intro heq
    have := card_eq_of_mk_eq (heq.trans hT.symm)
    omega
  have hlt_MT : Quotient.mk _ M < b := lt_of_le_of_ne hle_MT hne_MT
  exact hcov.2 hlt_SM hlt_MT

theorem quotientPosetRank_isMin (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    {a : QuotientPoset n G}
    (hmin : IsMin a) : IsMin (quotientPosetRank n G a) := by
  classical
  suffices h : quotientPosetRank n G a = 0 by
    rw [h]; exact isMin_bot
  induction a using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetRank_mk]
    by_contra hne
    have hpos : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hsub : S.erase x ⊆ S := Finset.erase_subset x S
    have hle : Quotient.mk (orbitRel G _) (S.erase x) ≤
               Quotient.mk (orbitRel G _) S :=
      ⟨S.erase x, S, rfl, rfl, hsub⟩
    have hback := hmin hle
    obtain ⟨S', T', hS', hT', hsub'⟩ := hback
    have hcard_S' : S'.card = S.card := card_eq_of_mk_eq hS'
    have hcard_T' : T'.card = (S.erase x).card := card_eq_of_mk_eq hT'
    have := Finset.card_le_card hsub'
    rw [hcard_S', hcard_T', Finset.card_erase_of_mem hx] at this
    omega

noncomputable instance quotientPoset_gradeMinOrder (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    GradeMinOrder ℕ (QuotientPoset n G) where
  grade := quotientPosetRank n G
  grade_strictMono := quotientPosetRank_strictMono n G
  covBy_grade _ _ := quotientPosetRank_covBy n G
  isMin_grade _ := quotientPosetRank_isMin n G

noncomputable instance quotientPoset_gradedPoset (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    letI := quotientPoset_gradeMinOrder n G
    GradedPoset (QuotientPoset n G) where
  rank := n
  grade_le_rank a := by
    change quotientPosetRank n G a ≤ n
    exact quotientPosetRank_le a
  grade_rank_exists := by
    refine ⟨Quotient.mk _ Finset.univ, ?_⟩
    change quotientPosetRank n G (Quotient.mk _ Finset.univ) = n
    exact quotientPosetRank_univ

end Grading

section RankSymmetry

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

theorem smul_compl_eq (g : G) (S : Finset (Fin n)) :
    g • (Finset.univ \ S) = Finset.univ \ (g • S) := by
  rw [smul_finset_sdiff, smul_finset_univ]

noncomputable def quotientPosetCompl :
    QuotientPoset n G → QuotientPoset n G :=
  Quotient.lift
    (fun S => Quotient.mk (orbitRel G _) (Finset.univ \ S))
    (by
      intro S T h
      apply Quotient.sound
      show (orbitRel G (Finset (Fin n))).r (Finset.univ \ S) (Finset.univ \ T)
      have hST : (orbitRel G (Finset (Fin n))).r S T := h
      rw [orbitRel_apply] at hST ⊢
      obtain ⟨g, hg⟩ := hST
      refine ⟨g, ?_⟩

      change g • (Finset.univ \ T) = Finset.univ \ S
      rw [smul_compl_eq]
      change g • T = S at hg
      rw [hg])

@[simp]
theorem quotientPosetCompl_mk (S : Finset (Fin n)) :
    quotientPosetCompl (Quotient.mk (orbitRel G _) S) =
    Quotient.mk (orbitRel G _) (Finset.univ \ S) := rfl

theorem quotientPosetCompl_involutive :
    Function.Involutive (quotientPosetCompl (n := n) (G := G)) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetCompl_mk, sdiff_sdiff_right_self, inf_eq_inter,
               Finset.univ_inter]

theorem quotientPosetCompl_bijective :
    Function.Bijective (quotientPosetCompl (n := n) (G := G)) :=
  quotientPosetCompl_involutive.bijective

theorem quotientPosetRank_compl (q : QuotientPoset n G) :
    quotientPosetRank n G (quotientPosetCompl q) =
    n - quotientPosetRank n G q := by
  induction q using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetCompl_mk, quotientPosetRank_mk]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

theorem quotientPoset_rankCount_eq (i : ℕ) (hi : i ≤ n) :
    (Finset.univ.filter (fun q : QuotientPoset n G =>
      quotientPosetRank n G q = i)).card =
    (Finset.univ.filter (fun q : QuotientPoset n G =>
      quotientPosetRank n G q = (n - i))).card := by
  classical
  apply Finset.card_nbij' quotientPosetCompl quotientPosetCompl
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [quotientPosetRank_compl, hq]
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [quotientPosetRank_compl, hq]
    omega
  · intro q _
    exact quotientPosetCompl_involutive q
  · intro q _
    exact quotientPosetCompl_involutive q

theorem quotientPoset_isRankSymmetric (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
    letI := quotientPoset_gradeMinOrder n G
    letI := quotientPoset_gradedPoset n G
    IsRankSymmetric (α := QuotientPoset n G) := by
  classical
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  intro i hi
  unfold rankCount
  simp only [GradedPoset.rank]
  exact quotientPoset_rankCount_eq i hi

end RankSymmetry

end SpernerProperty
