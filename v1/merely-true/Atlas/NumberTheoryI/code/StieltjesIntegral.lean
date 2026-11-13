/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace RiemannStieltjes

structure IntervalPartition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : Fin (n + 1) → ℝ
  first : pts ⟨0, Nat.zero_lt_succ n⟩ = a
  last : pts ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = b
  strict_mono : StrictMono pts

variable {a b : ℝ}

def IntervalPartition.IsRefinementOf (P Q : IntervalPartition a b) : Prop :=
  ∀ j : Fin (Q.n + 1), ∃ i : Fin (P.n + 1), P.pts i = Q.pts j

structure TaggedPartition (a b : ℝ) extends IntervalPartition a b where
  tags : Fin n → ℝ
  tag_mem : ∀ (k : Fin n),
    pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ ≤ tags k ∧
    tags k ≤ pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

noncomputable def stieltjesSum {𝕜 : Type*} [NormedField 𝕜]
    (PT : TaggedPartition a b) (f g : ℝ → 𝕜) : 𝕜 :=
  ∑ k : Fin PT.n,
    f (PT.tags k) * (g (PT.pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) -
                      g (PT.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))

def HasStieltjesIntegral {𝕜 : Type*} [NormedField 𝕜]
    (f g : ℝ → 𝕜) (a b : ℝ) (S : 𝕜) : Prop :=
  ∀ ε > 0, ∃ Pε : IntervalPartition a b,
    ∀ (PT : TaggedPartition a b),
      PT.toIntervalPartition.IsRefinementOf Pε →
      ‖stieltjesSum PT f g - S‖ < ε

def StieltjesIntegrable {𝕜 : Type*} [NormedField 𝕜]
    (f g : ℝ → 𝕜) (a b : ℝ) : Prop :=
  ∃ S, HasStieltjesIntegral f g a b S

theorem taggedPartitionOfPartition (P : IntervalPartition a b) :
    ∃ (PT : TaggedPartition a b), PT.toIntervalPartition = P :=
  ⟨{ n := P.n
     hn := P.hn
     pts := P.pts
     first := P.first
     last := P.last
     strict_mono := P.strict_mono
     tags := fun k => P.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
     tag_mem := fun k =>
       ⟨le_refl _, le_of_lt (P.strict_mono (Fin.mk_lt_mk.mpr (by omega)))⟩ },
   rfl⟩

noncomputable def IntervalPartition.pointSet (P : IntervalPartition a b) : Finset ℝ :=
  Finset.univ.image P.pts

lemma IntervalPartition.pts_mem_Icc (P : IntervalPartition a b)
    (i : Fin (P.n + 1)) : P.pts i ∈ Set.Icc a b :=
  ⟨by calc a = P.pts ⟨0, Nat.zero_lt_succ P.n⟩ := P.first.symm
        _ ≤ P.pts i := P.strict_mono.monotone (Fin.zero_le i),
   by calc P.pts i ≤ P.pts ⟨P.n, Nat.lt_succ_iff.mpr le_rfl⟩ :=
            P.strict_mono.monotone (Fin.le_last i)
      _ = b := P.last⟩

theorem commonRefinement (P Q : IntervalPartition a b) :
    ∃ R : IntervalPartition a b, R.IsRefinementOf P ∧ R.IsRefinementOf Q := by
  set S := P.pointSet ∪ Q.pointSet
  have ha_mem : a ∈ S := Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
    ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, P.first⟩))
  have hb_mem : b ∈ S := Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
    ⟨⟨P.n, Nat.lt_succ_iff.mpr le_rfl⟩, Finset.mem_univ _, P.last⟩))
  have hab : a ≠ b := ne_of_lt
    (calc a = P.pts ⟨0, Nat.zero_lt_succ P.n⟩ := P.first.symm
       _ < P.pts ⟨P.n, Nat.lt_succ_iff.mpr le_rfl⟩ := P.strict_mono (Fin.mk_lt_mk.mpr P.hn)
       _ = b := P.last)
  have hcard : 2 ≤ S.card :=
    calc 2 = ({a, b} : Finset ℝ).card := by simp [hab]
      _ ≤ S.card := Finset.card_le_card (by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
  set m := S.card - 1
  have hm_pos : 0 < m := by omega
  have hcard_eq : S.card = m + 1 := by omega
  let φ := S.orderEmbOfFin hcard_eq
  have hmin : S.min' ⟨a, ha_mem⟩ = a := by
    apply le_antisymm
    · exact Finset.min'_le _ _ ha_mem
    · apply Finset.le_min'
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (P.pts_mem_Icc i).1
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (Q.pts_mem_Icc i).1
  have hmax : S.max' ⟨a, ha_mem⟩ = b := by
    apply le_antisymm
    · apply Finset.max'_le
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (P.pts_mem_Icc i).2
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (Q.pts_mem_Icc i).2
    · exact Finset.le_max' _ _ hb_mem
  have hφ_first : φ ⟨0, Nat.zero_lt_succ m⟩ = a := by
    rw [show φ = S.orderEmbOfFin hcard_eq from rfl,
        Finset.orderEmbOfFin_zero hcard_eq (by omega), hmin]
  have hφ_last : φ ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩ = b := by
    have hfin : (⟨m, Nat.lt_succ_iff.mpr le_rfl⟩ : Fin (m + 1)) = ⟨m + 1 - 1, by omega⟩ := by
      simp
    rw [show φ = S.orderEmbOfFin hcard_eq from rfl, hfin,
        Finset.orderEmbOfFin_last hcard_eq (by omega), hmax]
  refine ⟨{
    n := m
    hn := hm_pos
    pts := φ
    first := hφ_first
    last := hφ_last
    strict_mono := φ.strictMono
  }, ?_, ?_⟩
  · intro j
    have : P.pts j ∈ Set.range φ := by
      rw [Finset.range_orderEmbOfFin S hcard_eq]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  · intro j
    have : Q.pts j ∈ Set.range φ := by
      rw [Finset.range_orderEmbOfFin S hcard_eq]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩

theorem hasStieltjesIntegral_unique {𝕜 : Type*} [NormedField 𝕜]
    {f g : ℝ → 𝕜} {S₁ S₂ : 𝕜}
    (h₁ : HasStieltjesIntegral f g a b S₁) (h₂ : HasStieltjesIntegral f g a b S₂) :
    S₁ = S₂ := by
  by_contra h
  have hne : 0 < ‖S₁ - S₂‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr h
  have hε : (0 : ℝ) < ‖S₁ - S₂‖ / 2 := by linarith
  obtain ⟨P₁, hP₁⟩ := h₁ (‖S₁ - S₂‖ / 2) hε
  obtain ⟨P₂, hP₂⟩ := h₂ (‖S₁ - S₂‖ / 2) hε
  obtain ⟨R, hR₁, hR₂⟩ := commonRefinement P₁ P₂
  obtain ⟨PT, hPT⟩ := taggedPartitionOfPartition R
  have h₁' := hP₁ PT (by rw [hPT]; exact hR₁)
  have h₂' := hP₂ PT (by rw [hPT]; exact hR₂)
  have key : ‖S₁ - S₂‖ ≤ ‖stieltjesSum PT f g - S₁‖ + ‖stieltjesSum PT f g - S₂‖ := by
    calc ‖S₁ - S₂‖
        = ‖(S₁ - stieltjesSum PT f g) + (stieltjesSum PT f g - S₂)‖ := by ring_nf
      _ ≤ ‖S₁ - stieltjesSum PT f g‖ + ‖stieltjesSum PT f g - S₂‖ := norm_add_le _ _
      _ = ‖stieltjesSum PT f g - S₁‖ + ‖stieltjesSum PT f g - S₂‖ := by rw [norm_sub_rev]
  linarith

noncomputable def stieltjesIntegral {𝕜 : Type*} [NormedField 𝕜]
    (f g : ℝ → 𝕜) (a b : ℝ) : 𝕜 := by
  classical exact if h : StieltjesIntegrable f g a b then h.choose else 0

theorem stieltjesIntegral_spec {𝕜 : Type*} [NormedField 𝕜]
    {f g : ℝ → 𝕜} (h : StieltjesIntegrable f g a b) :
    HasStieltjesIntegral f g a b (stieltjesIntegral f g a b) := by
  unfold stieltjesIntegral
  rw [dif_pos h]
  exact h.choose_spec

def IsBoundedVariation {𝕜 : Type*} [NormedField 𝕜] (f : ℝ → 𝕜) (a b : ℝ) : Prop :=
  ∃ M : ℝ, ∀ P : IntervalPartition a b,
    (∑ k : Fin P.n,
      ‖f (P.pts ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) -
       f (P.pts ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)‖) < M


lemma IsRefinementOf.trans {P Q R : IntervalPartition a b}
    (hPQ : P.IsRefinementOf Q) (hQR : Q.IsRefinementOf R) :
    P.IsRefinementOf R := by
  intro j
  obtain ⟨i, hi⟩ := hQR j
  obtain ⟨k, hk⟩ := hPQ i
  exact ⟨k, by rw [hk, hi]⟩

lemma IsRefinementOf.refl (P : IntervalPartition a b) :
    P.IsRefinementOf P :=
  fun j => ⟨j, rfl⟩

noncomputable def cumRefine
    (P : ℕ → IntervalPartition a b)
    (cr : ∀ Q R : IntervalPartition a b,
      ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R) :
    ℕ → IntervalPartition a b
  | 0 => P 0
  | n + 1 => (cr (cumRefine P cr n) (P (n + 1))).choose

lemma cumRefine_refines_prev
    (P : ℕ → IntervalPartition a b)
    (cr : ∀ Q R : IntervalPartition a b,
      ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R)
    (n : ℕ) : (cumRefine P cr (n + 1)).IsRefinementOf (cumRefine P cr n) :=
  (cr (cumRefine P cr n) (P (n + 1))).choose_spec.1

lemma cumRefine_refines_P
    (P : ℕ → IntervalPartition a b)
    (cr : ∀ Q R : IntervalPartition a b,
      ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R)
    (n : ℕ) : (cumRefine P cr (n + 1)).IsRefinementOf (P (n + 1)) :=
  (cr (cumRefine P cr n) (P (n + 1))).choose_spec.2

lemma cumRefine_refines_P_le
    (P : ℕ → IntervalPartition a b)
    (cr : ∀ Q R : IntervalPartition a b,
      ∃ S : IntervalPartition a b, S.IsRefinementOf Q ∧ S.IsRefinementOf R)
    (n k : ℕ) (hk : k ≤ n) : (cumRefine P cr n).IsRefinementOf (P k) := by
  induction n with
  | zero =>
    have : k = 0 := Nat.le_zero.mp hk
    subst this
    exact IsRefinementOf.refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact cumRefine_refines_P P cr n
    · exact IsRefinementOf.trans (cumRefine_refines_prev P cr n) (ih (Nat.lt_succ_iff.mp hlt))

theorem integrable_of_cauchy (f g : ℝ → ℝ) (a b : ℝ)
    (hcauchy : ∀ ε > 0, ∃ P : IntervalPartition a b,
      ∀ PT₁ PT₂ : TaggedPartition a b,
        PT₁.toIntervalPartition.IsRefinementOf P →
        PT₂.toIntervalPartition.IsRefinementOf P →
        ‖stieltjesSum PT₁ f g - stieltjesSum PT₂ f g‖ < ε) :
    StieltjesIntegrable f g a b := by

  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / (↑n + 1) := fun n => by positivity
  choose P_seq hP_seq using fun n => hcauchy (1 / (↑n + 1)) (hε n)

  let Q := cumRefine P_seq (fun P Q => commonRefinement P Q)

  choose PT_seq hPT_seq using fun n => taggedPartitionOfPartition (Q n)

  set s := fun n => stieltjesSum (PT_seq n) f g
  have hs_cauchy : CauchySeq s := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hN_pos : (0 : ℝ) < ↑N + 1 := by positivity
    have h_bound : 1 / (↑N + 1) < ε := by
      rw [div_lt_iff₀ hN_pos]
      calc 1 = ε * (1 / ε) := by field_simp
        _ < ε * (↑N + 1) := by nlinarith


    have hm_ref : (PT_seq m).toIntervalPartition.IsRefinementOf (P_seq N) := by
      rw [hPT_seq m]
      exact cumRefine_refines_P_le P_seq _ m N hm
    have hn_ref : (PT_seq n).toIntervalPartition.IsRefinementOf (P_seq N) := by
      rw [hPT_seq n]
      exact cumRefine_refines_P_le P_seq _ n N hn
    calc dist (s m) (s n) = ‖s m - s n‖ := by rw [Real.dist_eq, Real.norm_eq_abs]
      _ = ‖stieltjesSum (PT_seq m) f g - stieltjesSum (PT_seq n) f g‖ := rfl
      _ < 1 / (↑N + 1) := hP_seq N _ _ hm_ref hn_ref
      _ < ε := h_bound

  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete hs_cauchy

  refine ⟨S, fun ε hε => ?_⟩

  have hε_half : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 / ε)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hS) (ε / 2) hε_half
  set N := max N₁ N₂

  refine ⟨Q N, fun PT hPT => ?_⟩

  have hN₁_le : N₁ ≤ N := le_max_left _ _
  have hN₂_le : N₂ ≤ N := le_max_right _ _
  have hN_pos : (0 : ℝ) < ↑N₁ + 1 := by positivity
  have h1 : 1 / (↑N₁ + 1) < ε / 2 := by
    rw [div_lt_div_iff₀ hN_pos (by norm_num : (0 : ℝ) < 2)]
    have := (div_lt_iff₀ hε).mp hN₁
    nlinarith

  have hPT_ref_N : PT.toIntervalPartition.IsRefinementOf (P_seq N₁) :=
    IsRefinementOf.trans hPT (cumRefine_refines_P_le P_seq _ N N₁ hN₁_le)

  have hPTN_ref : (PT_seq N).toIntervalPartition.IsRefinementOf (P_seq N₁) := by
    rw [hPT_seq N]
    exact cumRefine_refines_P_le P_seq _ N N₁ hN₁_le
  have h_sum_close : ‖stieltjesSum PT f g - s N‖ < ε / 2 := by
    calc ‖stieltjesSum PT f g - s N‖
        = ‖stieltjesSum PT f g - stieltjesSum (PT_seq N) f g‖ := rfl
      _ < 1 / (↑N₁ + 1) := hP_seq N₁ _ _ hPT_ref_N hPTN_ref
      _ < ε / 2 := h1
  have h_seq_close : ‖s N - S‖ < ε / 2 := by
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact hN₂ N hN₂_le
  calc ‖stieltjesSum PT f g - S‖
      = ‖(stieltjesSum PT f g - s N) + (s N - S)‖ := by ring_nf
    _ ≤ ‖stieltjesSum PT f g - s N‖ + ‖s N - S‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h_sum_close h_seq_close
    _ = ε := by ring



lemma fin_sum_telescope {n : ℕ} (g : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (g ⟨i.val + 1, by omega⟩ - g ⟨i.val, by omega⟩) =
    g ⟨n, by omega⟩ - g ⟨0, by omega⟩ := by
  set h : ℕ → ℝ := fun i => g ⟨min i n, by omega⟩
  have hconv : ∀ (i : Fin n),
      g ⟨i.val + 1, by omega⟩ - g ⟨i.val, by omega⟩ = h (i.val + 1) - h i.val := by
    intro i
    simp only [h, min_eq_left (by omega : i.val ≤ n),
               min_eq_left (by omega : i.val + 1 ≤ n)]
  simp_rw [hconv]
  have hconv2 : (∑ i : Fin n, (h (i.val + 1) - h i.val)) =
      ∑ i ∈ Finset.range n, (h (i + 1) - h i) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi; rw [dif_pos (Finset.mem_range.mp hi)]
  rw [hconv2, Finset.sum_range_sub]
  simp only [h, min_self, Nat.zero_min]

end RiemannStieltjes
