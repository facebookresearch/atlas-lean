/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.SeparableDegree

open Polynomial Finset

noncomputable def Polynomial.L1norm {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (f : Polynomial K) : ℝ :=
  f.support.sum (fun i => v (f.coeff i))

namespace Polynomial

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (f : Polynomial K)

lemma L1norm_def : L1norm v f = f.support.sum (fun i => v (f.coeff i)) := rfl

@[simp]
lemma L1norm_zero : L1norm v (0 : K[X]) = 0 := by
  simp [L1norm]

lemma L1norm_nonneg : 0 ≤ L1norm v f :=
  Finset.sum_nonneg (fun _ _ => v.nonneg _)

lemma L1norm_eq_sum_range :
    L1norm v f = ∑ i ∈ Finset.range (f.natDegree + 1), v (f.coeff i) := by
  unfold L1norm
  apply Finset.sum_subset Polynomial.supp_subset_range_natDegree_succ
  intro i _ hi
  rw [Polynomial.mem_support_iff, not_not] at hi
  rw [hi, map_zero]

lemma L1norm_monic_eq (hf : f.Monic) :
    L1norm v f = (∑ i ∈ Finset.range f.natDegree, v (f.coeff i)) + 1 := by
  rw [L1norm_eq_sum_range, Finset.sum_range_succ, coeff_natDegree, hf.leadingCoeff, v.map_one]

lemma L1norm_monic_ge_one (hf : f.Monic) : 1 ≤ L1norm v f := by
  calc 1 = v (f.coeff f.natDegree) := by
        rw [coeff_natDegree, hf.leadingCoeff, v.map_one]
    _ ≤ L1norm v f := Finset.single_le_sum (fun i _ => v.nonneg _)
        (mem_support_iff.mpr (by rw [coeff_natDegree, hf.leadingCoeff]; exact one_ne_zero))

theorem root_norm_lt_L1norm
    {L : Type*} [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ)
    (hcompat : ∀ k : K, w (algebraMap K L k) = v k)
    (hf : f.Monic)
    {α : L} (hα : Polynomial.aeval α f = 0) :
    w α < L1norm v f := by
  by_contra habs
  push Not at habs

  have hL1_ge : 1 ≤ L1norm v f := L1norm_monic_ge_one v f hf
  have hwa1 : 1 ≤ w α := le_trans hL1_ge habs

  have hn : 0 < f.natDegree := by
    rw [Nat.pos_iff_ne_zero]; intro h0
    have hf1 : f = 1 := hf.natDegree_eq_zero.mp h0
    rw [hf1, Polynomial.aeval_one] at hα; exact one_ne_zero hα

  have heval : (Polynomial.aeval α) f = 0 := hα
  rw [aeval_eq_sum_range, Finset.sum_range_succ] at heval
  have hlead : f.coeff f.natDegree • α ^ f.natDegree = α ^ f.natDegree := by
    rw [coeff_natDegree, hf.leadingCoeff, one_smul]
  rw [hlead] at heval
  have hαn := eq_neg_of_add_eq_zero_right heval

  have hkey : w α ^ f.natDegree ≤
      ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i := by
    calc w α ^ f.natDegree
        = w (α ^ f.natDegree) := (w.map_pow α f.natDegree).symm
      _ = w (-(∑ i ∈ Finset.range f.natDegree, f.coeff i • α ^ i)) := by rw [hαn]
      _ = w (∑ i ∈ Finset.range f.natDegree, f.coeff i • α ^ i) := w.map_neg _
      _ ≤ ∑ i ∈ Finset.range f.natDegree, w (f.coeff i • α ^ i) := w.sum_le _ _
      _ = ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i := by
          congr 1; ext i; rw [Algebra.smul_def, w.map_mul, w.map_pow, hcompat]

  have hbound : ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) * w α ^ i ≤
      w α ^ (f.natDegree - 1) * ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi; rw [Finset.mem_range] at hi
    calc v (f.coeff i) * w α ^ i
        ≤ v (f.coeff i) * w α ^ (f.natDegree - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hwa1 (by omega)) (v.nonneg _)
      _ = w α ^ (f.natDegree - 1) * v (f.coeff i) := mul_comm _ _

  have hsum_eq : ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) = L1norm v f - 1 := by
    have := L1norm_monic_eq v f hf; linarith

  have hpow_eq : w α ^ f.natDegree = w α ^ (f.natDegree - 1) * w α := by
    rw [← pow_succ]; congr 1; omega
  have hpow_pos : 0 < w α ^ (f.natDegree - 1) :=
    pow_pos (lt_of_lt_of_le zero_lt_one hwa1) _

  have h1 : w α ^ (f.natDegree - 1) * w α ≤
      w α ^ (f.natDegree - 1) * (L1norm v f - 1) := by
    rw [← hpow_eq]
    calc w α ^ f.natDegree
        ≤ w α ^ (f.natDegree - 1) * ∑ i ∈ Finset.range f.natDegree, v (f.coeff i) :=
          le_trans hkey hbound
      _ = w α ^ (f.natDegree - 1) * (L1norm v f - 1) := by rw [hsum_eq]
  have hwa_le : w α ≤ L1norm v f - 1 := le_of_mul_le_mul_left h1 hpow_pos

  linarith

end Polynomial

theorem automorphism_preserves_spectralNorm
    {K : Type*} [NormedField K]
    {L : Type*} [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (α : L) :
    spectralNorm K L (σ α) = spectralNorm K L α :=
  (spectralNorm_eq_of_equiv σ α).symm

@[deprecated automorphism_preserves_spectralNorm (since := "2026-05-04")]
theorem Lemma_11_13
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (α : AlgebraicClosure K) :
    spectralNorm K (AlgebraicClosure K) (σ α) =
      spectralNorm K (AlgebraicClosure K) α :=
  automorphism_preserves_spectralNorm σ α

def BelongsTo (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (β α : AlgebraicClosure K) : Prop :=
  ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
    σ α ≠ α →
    spectralNorm K (AlgebraicClosure K) (β - α) <
      spectralNorm K (AlgebraicClosure K) (β - σ α)

open IntermediateField in
theorem krasner_lemma
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {α β : AlgebraicClosure K}
    (hsep : IsSeparable K α)
    (hbelong : BelongsTo K β α) :
    K⟮α⟯ ≤ K⟮β⟯ := by
  letI : NormedField (AlgebraicClosure K) := spectralNorm.normedField K _
  letI : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K _
  haveI : IsUltrametricDist (AlgebraicClosure K) := IsUltrametricDist.of_normedAlgebra K
  rw [IntermediateField.adjoin_simple_le_iff]
  apply IsKrasner.krasner hsep
  · exact IsAlgClosed.splits _
  · exact (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  · intro α' hconj hne
    rw [isConjRoot_iff_exists_algEquiv] at hconj
    obtain ⟨σ, hσ⟩ := hconj
    have hα' : α' = σ.symm α := by rw [← hσ]; simp
    have hne' : σ.symm α ≠ α := by rw [← hα']; exact hne.symm
    have hbel := hbelong σ.symm hne'
    rw [← NormedAlgebra.norm_eq_spectralNorm K,
        ← NormedAlgebra.norm_eq_spectralNorm K] at hbel
    subst hα'
    rw [norm_sub_rev α β]
    by_contra hle
    push Not at hle
    have h_ultra : ‖β - σ.symm α‖ ≤ max ‖β - α‖ ‖α - σ.symm α‖ := by
      have : β - σ.symm α = (β - α) + (α - σ.symm α) := by abel
      rw [this]; exact IsUltrametricDist.norm_add_le_max _ _
    linarith [max_le (le_refl ‖β - α‖) hle]

open IntermediateField in
@[deprecated krasner_lemma (since := "2026-05-04")]
theorem Lemma_11_15
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {α β : AlgebraicClosure K}
    (hsep : IsSeparable K α)
    (hbelong : BelongsTo K β α) :
    K⟮α⟯ ≤ K⟮β⟯ := krasner_lemma K hsep hbelong

lemma multiset_prod_ge_pow_of_nonneg_ge {s : Multiset ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hnonneg : ∀ x ∈ s, 0 ≤ x) (hge : ∀ x ∈ s, c ≤ x) :
    c ^ s.card ≤ s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have ha_ge : c ≤ a := hge a (Multiset.mem_cons_self _ _)
    have ha_nonneg : 0 ≤ a := hnonneg a (Multiset.mem_cons_self _ _)
    have hs_nonneg : ∀ x ∈ s, 0 ≤ x := fun x hx => hnonneg x (Multiset.mem_cons_of_mem hx)
    have hs_ge : ∀ x ∈ s, c ≤ x := fun x hx => hge x (Multiset.mem_cons_of_mem hx)
    calc c ^ s.card * c ≤ s.prod * a :=
          mul_le_mul (ih hs_nonneg hs_ge) ha_ge hc (Multiset.prod_nonneg hs_nonneg)
      _ = a * s.prod := mul_comm _ _

noncomputable def normAbsVal (K : Type*) [NormedField K] : AbsoluteValue K ℝ where
  toFun k := ‖k‖
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' := by simp [norm_eq_zero]
  add_le' := norm_add_le

open IntermediateField in
theorem continuity_of_roots
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (f : K[X]) (hf_monic : f.Monic) (hf_irr : Irreducible f) (hf_sep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
        Polynomial.L1norm (normAbsVal K) (f - g) < δ →
        ∀ β : AlgebraicClosure K, Polynomial.aeval β g = 0 →
          ∃ α : AlgebraicClosure K, Polynomial.aeval α f = 0 ∧
            BelongsTo K β α ∧ K⟮α⟯ = K⟮β⟯ := by
  classical

  letI inst_nf : NormedField (AlgebraicClosure K) := spectralNorm.normedField K _
  letI inst_na : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K _
  haveI inst_um : IsUltrametricDist (AlgebraicClosure K) :=
    IsUltrametricDist.of_normedAlgebra K
  set v := normAbsVal K with hv_def
  set fL := f.map (algebraMap K (AlgebraicClosure K)) with hfL_def
  have hfL_splits : fL.Splits := IsAlgClosed.splits fL
  have hfL_monic : fL.Monic := hf_monic.map _
  have hfL_ne : fL ≠ 0 := hfL_monic.ne_zero
  have hf_ne : f ≠ 0 := hf_monic.ne_zero
  have hfL_deg : fL.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap K (AlgebraicClosure K)).injective f
  have hf_deg_pos : 0 < f.natDegree := hf_irr.natDegree_pos
  set n := f.natDegree with hn_def
  have hroots_card : fL.roots.card = n := by
    rw [← hfL_deg]; exact hfL_splits.natDegree_eq_card_roots.symm
  have hfL_sep : fL.Separable := hf_sep.map
  have hfL_nodup : fL.roots.Nodup := Polynomial.nodup_roots hfL_sep

  set w : AbsoluteValue (AlgebraicClosure K) ℝ := normAbsVal (AlgebraicClosure K) with hw_def
  have hcompat : ∀ k : K, w (algebraMap K (AlgebraicClosure K) k) = v k := by
    intro k
    simp only [w, v, normAbsVal, AbsoluteValue.coe_mk, MulHom.coe_mk]
    rw [NormedAlgebra.norm_eq_spectralNorm K, spectralNorm_extends]

  have hroot_is_root : ∀ α : AlgebraicClosure K, α ∈ fL.roots → Polynomial.aeval α f = 0 := by
    intro α hα
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact (Polynomial.mem_roots hfL_ne).mp hα

  have hL1_ge : 1 ≤ Polynomial.L1norm v f := Polynomial.L1norm_monic_ge_one v f hf_monic
  set C := Polynomial.L1norm v f + 1 with hC_def
  have hC_pos : 0 < C := by linarith

  have exists_eps : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ α α' : AlgebraicClosure K, α ∈ fL.roots → α' ∈ fL.roots → α ≠ α' →
        ε ≤ w (α - α') := by
    by_cases hn1 : n ≤ 1
    ·
      refine ⟨1, one_pos, le_refl 1, ?_⟩
      intro α α' hα hα' hne
      exfalso; apply hne
      have h1 : fL.roots.card ≤ 1 := by omega
      have h2 : fL.roots.card = 1 := by
        rcases Nat.eq_zero_or_pos fL.roots.card with h0 | hp
        · exact absurd (Multiset.card_pos_iff_exists_mem.mpr ⟨α, hα⟩) (by omega)
        · omega
      rw [Multiset.card_eq_one] at h2
      obtain ⟨c, hc⟩ := h2
      rw [hc] at hα hα'
      rw [Multiset.mem_singleton] at hα hα'
      exact hα.trans hα'.symm

    · push_neg at hn1
      set pairs := (fL.roots.toFinset.product fL.roots.toFinset).filter (fun p => p.1 ≠ p.2)
      have hpairs_nonempty : pairs.Nonempty := by
        have h2 : 1 < fL.roots.toFinset.card := by
          rw [Multiset.toFinset_card_of_nodup hfL_nodup]; omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
        exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩
      set dists := pairs.image (fun p => w (p.1 - p.2))
      have hdists_nonempty : dists.Nonempty := hpairs_nonempty.image _
      set min_dist := dists.min' hdists_nonempty
      have hmin_pos : 0 < min_dist := by
        have hmem := Finset.min'_mem dists hdists_nonempty
        rw [Finset.mem_image] at hmem
        obtain ⟨⟨a, b⟩, hp, hpd⟩ := hmem
        rw [Finset.mem_filter] at hp
        have hab : a ≠ b := hp.2
        rw [show min_dist = w (a - b) from hpd.symm]
        exact (w.pos (sub_ne_zero.mpr hab))

      refine ⟨min 1 min_dist, lt_min one_pos hmin_pos, min_le_left _ _, ?_⟩
      intro α α' hα hα' hne
      calc min 1 min_dist ≤ min_dist := min_le_right _ _
        _ ≤ w (α - α') := by
            apply Finset.min'_le
            exact Finset.mem_image.mpr ⟨(α, α'),
              Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨Multiset.mem_toFinset.mpr hα, Multiset.mem_toFinset.mpr hα'⟩, hne⟩, rfl⟩
  obtain ⟨ε, hε_pos, hε_le1, hε_sep⟩ := exists_eps

  set δ := (ε / (2 * C)) ^ n with hδ_def
  have hδ_pos : 0 < δ := pow_pos (div_pos hε_pos (by linarith)) _
  refine ⟨δ, hδ_pos, ?_⟩
  intro g hg_monic hg_deg hfg_close β hβ_root

  have hg_ne : g ≠ 0 := hg_monic.ne_zero
  have hgL_ne : g.map (algebraMap K (AlgebraicClosure K)) ≠ 0 := (hg_monic.map _).ne_zero

  have heval_prod : Polynomial.eval β fL =
      (Multiset.map (fun α => β - α) fL.roots).prod :=
    hfL_splits.eval_eq_prod_roots_of_monic hfL_monic β
  have heval_eq_aeval : Polynomial.eval β fL = Polynomial.aeval β f := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

  have hf_eval_eq : Polynomial.aeval β f = Polynomial.aeval β (f - g) := by
    rw [map_sub, hβ_root, sub_zero]

  have hprod_eq_eval : (Multiset.map (fun α => w (β - α)) fL.roots).prod =
      w (Polynomial.aeval β f) := by
    rw [← heval_eq_aeval, heval_prod, map_multiset_prod, Multiset.map_map]; rfl

  suffices hprod_bound : (Multiset.map (fun α => w (β - α)) fL.roots).prod < (ε / 2) ^ n by

    have hε2_pos : 0 < ε / 2 := by linarith
    have hex : ∃ α ∈ fL.roots, w (β - α) < ε / 2 := by
      by_contra hall; push_neg at hall
      have hge : (ε / 2) ^ n ≤ (Multiset.map (fun α => w (β - α)) fL.roots).prod := by
        set ms := Multiset.map (fun α => w (β - α)) fL.roots
        have hcard : ms.card = n := by simp [ms, Multiset.card_map, hroots_card]
        have hle : ∀ x ∈ ms, ε / 2 ≤ x := by
          intro x hx; rw [Multiset.mem_map] at hx
          obtain ⟨α, hα, rfl⟩ := hx; exact hall α hα
        rw [← hcard]
        exact multiset_prod_ge_pow_of_nonneg_ge hε2_pos.le
          (fun x hx => le_trans (div_nonneg hε_pos.le (by norm_num)) (hle x hx)) hle
      linarith
    obtain ⟨α, hα_root, hα_close⟩ := hex
    have hα_is_root : Polynomial.aeval α f = 0 := hroot_is_root α hα_root

    have hbelong : BelongsTo K β α := by
      intro σ hσ

      have hσα_root : σ α ∈ fL.roots := by
        rw [Polynomial.mem_roots hfL_ne, Polynomial.IsRoot, hfL_def,
            Polynomial.eval_map, ← Polynomial.aeval_def]
        have h := Polynomial.aeval_algEquiv σ α

        have : (Polynomial.aeval (σ α)) f = σ ((Polynomial.aeval α) f) := by
          rw [h]; rfl
        rw [this, hα_is_root, map_zero]

      have hdist_large : ε ≤ w (α - σ α) := hε_sep α (σ α) hα_root hσα_root hσ.symm

      have hβα_w : w (β - α) < w (α - σ α) := by linarith


      rw [show spectralNorm K (AlgebraicClosure K) (β - α) = w (β - α) from by
            rw [← NormedAlgebra.norm_eq_spectralNorm K]; rfl,
          show spectralNorm K (AlgebraicClosure K) (β - σ α) = w (β - σ α) from by
            rw [← NormedAlgebra.norm_eq_spectralNorm K]; rfl]

      have hsplit : β - σ α = (β - α) + (α - σ α) := by ring
      rw [hsplit]

      have hne_w : w (β - α) ≠ w (α - σ α) := ne_of_lt hβα_w
      have : w ((β - α) + (α - σ α)) = max (w (β - α)) (w (α - σ α)) := by
        show ‖(β - α) + (α - σ α)‖ = max ‖β - α‖ ‖α - σ α‖
        exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne_w
      rw [this]
      rw [max_eq_right hβα_w.le]
      exact hβα_w

    have hα_int : IsIntegral K α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    have hmin_eq_f : minpoly K α = f := by
      have hmin_dvd : minpoly K α ∣ f := minpoly.dvd K α (by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        exact (Polynomial.mem_roots hfL_ne).mp hα_root)
      exact Polynomial.eq_of_monic_of_associated (minpoly.monic hα_int) hf_monic
        ((minpoly.irreducible hα_int).associated_of_dvd hf_irr hmin_dvd)
    have hα_sep : IsSeparable K α := by
      unfold IsSeparable; rw [hmin_eq_f]; exact hf_sep
    have hKα_sub_Kβ := krasner_lemma K hα_sep hbelong

    have hKα_eq_Kβ : K⟮α⟯ = K⟮β⟯ := by

      have hdeg_Kα : Module.finrank K K⟮α⟯ = n := by
        rw [IntermediateField.adjoin.finrank hα_int, hmin_eq_f]

      have hβ_int : IsIntegral K β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
      have hdeg_Kβ_le : Module.finrank K K⟮β⟯ ≤ n := by
        rw [IntermediateField.adjoin.finrank hβ_int]
        calc (minpoly K β).natDegree ≤ g.natDegree :=
              Polynomial.natDegree_le_of_dvd (minpoly.dvd K β hβ_root) hg_ne
          _ = n := hg_deg
      haveI : FiniteDimensional K K⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβ_int
      exact IntermediateField.eq_of_le_of_finrank_le hKα_sub_Kβ (by omega)
    exact ⟨α, hα_is_root, hbelong, hKα_eq_Kβ⟩

  rw [hprod_eq_eval, hf_eval_eq]

  set fg := f - g

  have hβ_root_gL : Polynomial.aeval β g = 0 := hβ_root
  have hβ_bound : w β < Polynomial.L1norm v g :=
    Polynomial.root_norm_lt_L1norm v g w hcompat hg_monic (by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hgL_ne).mp (by
        rw [Polynomial.mem_roots hgL_ne, Polynomial.IsRoot, Polynomial.eval_map,
            ← Polynomial.aeval_def]; exact hβ_root))
  have hgL1_ge1 : 1 ≤ Polynomial.L1norm v g := Polynomial.L1norm_monic_ge_one v g hg_monic

  have hfg_aeval : w (Polynomial.aeval β fg) ≤
      Polynomial.L1norm v fg * (Polynomial.L1norm v g) ^ n := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    set fgL := fg.map (algebraMap K (AlgebraicClosure K))
    calc w (Polynomial.eval β fgL)
        = w (∑ i ∈ Finset.range (fgL.natDegree + 1),
              fgL.coeff i * β ^ i) := by
            rw [Polynomial.eval_eq_sum_range]
      _ ≤ ∑ i ∈ Finset.range (fgL.natDegree + 1), w (fgL.coeff i * β ^ i) := w.sum_le _ _
      _ = ∑ i ∈ Finset.range (fgL.natDegree + 1), v (fg.coeff i) * w β ^ i := by
          congr 1; ext i
          rw [w.map_mul, w.map_pow]
          congr 1
          show w (fgL.coeff i) = v (fg.coeff i)
          simp only [fgL, Polynomial.coeff_map]
          exact hcompat _
      _ ≤ ∑ i ∈ Finset.range (fgL.natDegree + 1),
            v (fg.coeff i) * (Polynomial.L1norm v g) ^ n := by
          apply Finset.sum_le_sum; intro i hi
          apply mul_le_mul_of_nonneg_left _ (v.nonneg _)
          rw [Finset.mem_range] at hi
          calc w β ^ i ≤ (Polynomial.L1norm v g) ^ i :=
                pow_le_pow_left₀ (w.nonneg _) hβ_bound.le i
            _ ≤ (Polynomial.L1norm v g) ^ n :=
                pow_le_pow_right₀ hgL1_ge1 (by
                  have hfg_deg : fg.natDegree ≤ n := by
                    calc fg.natDegree ≤ max f.natDegree g.natDegree :=
                          Polynomial.natDegree_sub_le f g
                      _ = n := by rw [hn_def, hg_deg, max_self]
                  have hfgL_deg : fgL.natDegree ≤ n := by
                    rw [Polynomial.natDegree_map_eq_of_injective
                        (algebraMap K (AlgebraicClosure K)).injective]
                    exact hfg_deg
                  omega)
      _ = (∑ i ∈ Finset.range (fgL.natDegree + 1), v (fg.coeff i)) *
            (Polynomial.L1norm v g) ^ n := by rw [Finset.sum_mul]
      _ ≤ Polynomial.L1norm v fg * (Polynomial.L1norm v g) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Polynomial.L1norm_nonneg v g) _)
          rw [Polynomial.L1norm_def]
          apply le_of_eq
          apply (Finset.sum_subset _ _).symm
          · intro i hi
            rw [Finset.mem_range]
            exact Nat.lt_succ_of_le (le_trans (Polynomial.le_natDegree_of_mem_supp i hi)
              (Polynomial.natDegree_map_eq_of_injective
                (algebraMap K (AlgebraicClosure K)).injective fg ▸ le_refl _))
          · intro i _ hni
            rw [Polynomial.mem_support_iff] at hni
            push_neg at hni
            simp [hni]


  have hgL1_lt_C : Polynomial.L1norm v g < C := by
    calc Polynomial.L1norm v g
        = g.support.sum (fun i => v (g.coeff i)) := rfl
      _ ≤ (f.support ∪ fg.support).sum (fun i => v (g.coeff i)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_union, Polynomial.mem_support_iff]
            rw [Polynomial.mem_support_iff] at hi
            by_contra hall; push_neg at hall
            have : g.coeff i = f.coeff i - fg.coeff i := by
              simp [fg, Polynomial.coeff_sub]
            rw [this, hall.1, hall.2, sub_zero] at hi; exact hi rfl
          · intro _ _ _; exact v.nonneg _
      _ ≤ (f.support ∪ fg.support).sum (fun i => v (f.coeff i) + v (fg.coeff i)) := by
          apply Finset.sum_le_sum; intro i _
          have : g.coeff i = f.coeff i - fg.coeff i := by
            simp [fg, Polynomial.coeff_sub]
          rw [this]
          calc v (f.coeff i - fg.coeff i)
              = v (f.coeff i + (-(fg.coeff i))) := by ring_nf
            _ ≤ v (f.coeff i) + v (-(fg.coeff i)) := v.add_le _ _
            _ = v (f.coeff i) + v (fg.coeff i) := by rw [v.map_neg]
      _ = (f.support ∪ fg.support).sum (fun i => v (f.coeff i)) +
            (f.support ∪ fg.support).sum (fun i => v (fg.coeff i)) :=
          Finset.sum_add_distrib
      _ ≤ Polynomial.L1norm v f + Polynomial.L1norm v fg := by
          apply add_le_add
          · rw [Polynomial.L1norm_def]
            apply (Finset.sum_subset Finset.subset_union_left _).ge
            intro i _ hni
            rw [Polynomial.mem_support_iff] at hni; push_neg at hni; simp [hni]
          · rw [Polynomial.L1norm_def]
            apply (Finset.sum_subset Finset.subset_union_right _).ge
            intro i _ hni
            rw [Polynomial.mem_support_iff] at hni; push_neg at hni; simp [hni]

      _ < Polynomial.L1norm v f + δ := by linarith
      _ < C := by
          have hδ_lt_1 : δ < 1 := by
            rw [hδ_def]
            calc (ε / (2 * C)) ^ n ≤ (ε / (2 * C)) ^ 1 := by
                  apply pow_le_pow_of_le_one
                  · exact le_of_lt (div_pos hε_pos (by linarith))
                  · rw [div_le_one (by linarith : 0 < 2 * C)]
                    calc ε ≤ 1 := hε_le1
                      _ ≤ 2 * C := by linarith
                  · exact hf_deg_pos
              _ = ε / (2 * C) := pow_one _
              _ < 1 := by rw [div_lt_one (by linarith : 0 < 2 * C)]; linarith
          linarith

  calc w (Polynomial.aeval β fg)
      ≤ Polynomial.L1norm v fg * (Polynomial.L1norm v g) ^ n := hfg_aeval
    _ < δ * C ^ n := by
        apply mul_lt_mul hfg_close (pow_le_pow_left₀ (le_of_lt (by linarith)) hgL1_lt_C.le n)
          (pow_pos (by linarith) n) (le_of_lt (by linarith [Polynomial.L1norm_nonneg v fg]))
    _ = (ε / 2) ^ n := by
        rw [hδ_def, div_pow, div_mul_eq_mul_div, mul_pow,
            mul_div_mul_right _ _ (pow_ne_zero n hC_pos.ne'), div_pow]


theorem Multiset.eq_of_mem_of_mem_of_card_le_one {α : Type*} [DecidableEq α]
    {s : Multiset α} {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : s.card ≤ 1) : a = b := by
  have h1 : s.card = 0 ∨ s.card = 1 := by omega
  rcases h1 with h0 | h1
  · exact absurd (Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩) (by omega)
  · rw [Multiset.card_eq_one] at h1
    obtain ⟨c, rfl⟩ := h1
    rw [Multiset.mem_singleton] at ha hb
    rw [ha, hb]

open IntermediateField in
@[deprecated continuity_of_roots (since := "2026-05-04")]
theorem Theorem_11_19
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (f : K[X]) (hf_monic : f.Monic) (hf_irr : Irreducible f) (hf_sep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
        Polynomial.L1norm (normAbsVal K) (f - g) < δ →
        ∀ β : AlgebraicClosure K, Polynomial.aeval β g = 0 →
          ∃ α : AlgebraicClosure K, Polynomial.aeval α f = 0 ∧
            BelongsTo K β α ∧ K⟮α⟯ = K⟮β⟯ :=
  continuity_of_roots K f hf_monic hf_irr hf_sep

open IntermediateField in
theorem continuity_of_roots_irreducible_separable
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (f : K[X]) (hf_monic : f.Monic) (hf_irr : Irreducible f) (hf_sep : f.Separable) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
        Polynomial.L1norm (normAbsVal K) (f - g) < δ →
        Irreducible g ∧ g.Separable := by
  obtain ⟨δ, hδ_pos, hδ⟩ := continuity_of_roots K f hf_monic hf_irr hf_sep
  refine ⟨δ, hδ_pos, fun g hg_monic hg_deg hfg_close => ?_⟩

  have hg_deg_pos : 0 < g.natDegree := hg_deg ▸ hf_irr.natDegree_pos
  have hg_degree_ne : g.degree ≠ 0 :=
    ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hg_deg_pos)
  obtain ⟨β, hβ_root⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) g hg_degree_ne

  obtain ⟨α, hα_root, _, hKαβ⟩ := hδ g hg_monic hg_deg hfg_close β hβ_root
  have hβ_int : IsIntegral K β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral
  have hα_int : IsIntegral K α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral

  have hmin_α_eq_f : minpoly K α = f := by
    have hfL_ne : f.map (algebraMap K (AlgebraicClosure K)) ≠ 0 := (hf_monic.map _).ne_zero
    have hmin_dvd : minpoly K α ∣ f := minpoly.dvd K α (by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hfL_ne).mp (by
        rw [Polynomial.mem_roots hfL_ne, Polynomial.IsRoot, Polynomial.eval_map,
            ← Polynomial.aeval_def]; exact hα_root))
    exact Polynomial.eq_of_monic_of_associated (minpoly.monic hα_int) hf_monic
      ((minpoly.irreducible hα_int).associated_of_dvd hf_irr hmin_dvd)

  have hg_eq_min : g = minpoly K β := by
    have hmin_dvd_g : minpoly K β ∣ g := minpoly.dvd K β hβ_root
    have hmin_deg : g.natDegree ≤ (minpoly K β).natDegree := by
      rw [← IntermediateField.adjoin.finrank hβ_int]
      have h1 : Module.finrank K K⟮α⟯ = f.natDegree := by
        rw [IntermediateField.adjoin.finrank hα_int, hmin_α_eq_f]
      rw [hKαβ] at h1; omega
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ_int) hg_monic
      hmin_dvd_g hmin_deg
  constructor
  ·
    rw [hg_eq_min]; exact minpoly.irreducible hβ_int
  ·
    rw [hg_eq_min]
    have hα_sep_elem : IsSeparable K α := by
      unfold IsSeparable; rw [hmin_α_eq_f]; exact hf_sep
    haveI : Algebra.IsSeparable K K⟮α⟯ :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K
        (AlgebraicClosure K)).mpr hα_sep_elem
    haveI : Algebra.IsSeparable K K⟮β⟯ := hKαβ ▸ ‹Algebra.IsSeparable K K⟮α⟯›
    exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K
      (AlgebraicClosure K)).mp ‹Algebra.IsSeparable K K⟮β⟯›
