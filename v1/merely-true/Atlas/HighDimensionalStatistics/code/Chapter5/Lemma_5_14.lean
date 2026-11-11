/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Atlas.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers

open Finset Real

noncomputable section

namespace SparseVarshamovGilbert

/-- Hamming distance between two binary vectors. -/
def hammingDist {d : ℕ} (ω₁ ω₂ : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω₁ i ≠ ω₂ i).card

/-- `ℓ⁰`-pseudonorm of a binary vector: number of `true` entries. -/
def l0norm {d : ℕ} (ω : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i = true).card

/-- Type of `k`-sparse binary vectors in `{0,1}^d`. -/
abbrev SparseVec (d k : ℕ) := {f : Fin d → Bool // l0norm f = k}

/-- The number of `k`-sparse binary vectors in `{0,1}^d` equals `(d choose k)`. -/
theorem sparsevec_card (d k : ℕ) : Fintype.card (SparseVec d k) = Nat.choose d k := by
  have : Fintype.card (SparseVec d k) = Fintype.card {S : Finset (Fin d) // S.card = k} := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquiv
      { toFun := fun (f : Fin d → Bool) => Finset.univ.filter (fun i => f i = true)
        invFun := fun (S : Finset (Fin d)) => fun i => decide (i ∈ S)
        left_inv := by
          intro f; ext i
          simp [Finset.mem_filter]
        right_inv := by
          intro S; ext i
          simp } ?_
    intro f
    simp only [Equiv.coe_fn_mk, l0norm]
  rw [this, Fintype.card_finset_len, Fintype.card_fin]

/-- The "ball" of `k`-sparse vectors at Hamming distance strictly less than `k/2` (integer
division) from `x`. -/
def sparseBall (d k : ℕ) (x : SparseVec d k) : Finset (SparseVec d k) :=
  Finset.univ.filter fun y => hammingDist x.val y.val < k / 2

/-- Hamming distance is symmetric. -/
lemma hammingDist_comm {d : ℕ} (f g : Fin d → Bool) :
    hammingDist f g = hammingDist g f := by
  unfold hammingDist; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ne_comm

/-- Greedy packing bound: in any finite type with symmetric "balls" of size at most `B`, there
exists a maximal packing `T` such that `|α| ≤ |T| · B` and no two elements of `T` lie in each
other's ball. -/
lemma greedy_packing_bound {α : Type} [Fintype α] [DecidableEq α]
    (ball : α → Finset α) (B : ℕ)
    (ball_self : ∀ x, x ∈ ball x)
    (ball_symm : ∀ x y, y ∈ ball x → x ∈ ball y)
    (ball_bound : ∀ x, (ball x).card ≤ B) :
    ∃ T : Finset α,
      Fintype.card α ≤ T.card * B ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → y ∉ ball x) := by
  classical

  let packings := Finset.univ.powerset.filter (fun T : Finset α =>
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → y ∉ ball x)
  have hfin : packings.Nonempty := ⟨∅, by simp [packings, Finset.mem_filter]⟩

  obtain ⟨T, hT_mem, hT_max⟩ := packings.exists_max_image Finset.card hfin
  have hT_pack := (Finset.mem_filter.mp hT_mem).2

  have hcover : ∀ z, ∃ t ∈ T, z ∈ ball t := by
    intro z
    by_cases hz : z ∈ T
    · exact ⟨z, hz, ball_self z⟩
    ·
      by_contra habs
      push Not at habs
      have : ∀ x ∈ T.cons z hz, ∀ y ∈ T.cons z hz, x ≠ y → y ∉ ball x := by
        intro x hx y hy hne
        simp only [Finset.mem_cons] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hne
        · intro hball; exact habs y hy (ball_symm _ _ hball)
        · intro hball; exact habs x hx hball
        · exact hT_pack x hx y hy hne
      linarith [hT_max (T.cons z hz)
        (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), this⟩),
        Finset.card_cons hz]

  refine ⟨T, ?_, hT_pack⟩
  calc Fintype.card α = Finset.univ.card := Finset.card_univ.symm
    _ ≤ (T.biUnion ball).card :=
        Finset.card_le_card (fun z _ => Finset.mem_biUnion.mpr (hcover z))
    _ ≤ T.sum (fun t => (ball t).card) := Finset.card_biUnion_le
    _ ≤ T.sum (fun _ => B) := Finset.sum_le_sum (fun t _ => ball_bound t)
    _ = T.card * B := by simp [Finset.sum_const, smul_eq_mul]

/-- Every `k`-sparse vector lies in its own sparse ball when `k ≥ 2`. -/
lemma self_mem_sparseBall (d k : ℕ) (hk : 2 ≤ k) (x : SparseVec d k) :
    x ∈ sparseBall d k x := by
  simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
  have : (Finset.univ.filter fun i => x.val i ≠ x.val i) = ∅ := by ext i; simp
  rw [this, Finset.card_empty]; omega

/-- There are exactly `k` indices `i : Fin d` with `i.val < k` (assuming `k ≤ d`). -/
lemma card_filter_val_lt (d k : ℕ) (hkd : k ≤ d) :
    (Finset.univ.filter (fun i : Fin d => i.val < k)).card = k := by
  rcases Nat.eq_or_lt_of_le hkd with hkd' | hkd'
  · have : (Finset.univ.filter (fun i : Fin d => i.val < k)) = Finset.univ := by
      ext i; simp [hkd']
    rw [this, Finset.card_univ, Fintype.card_fin]; omega
  · convert Fin.card_Iio (⟨k, hkd'⟩ : Fin d) using 1
    congr 1; ext ⟨i, hi⟩; simp [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]

/-- A canonical `k`-sparse vector: the indicator of `{i : Fin d | i.val < k}`. -/
def mkSparseVec (d k : ℕ) (hkd : k ≤ d) : SparseVec d k :=
  ⟨fun i => decide (i.val < k), by
    simp only [l0norm, decide_eq_true_eq]; exact card_filter_val_lt d k hkd⟩

/-- Variant of `sparseBall` using the ceiling-style radius `(k+1)/2`. -/
def sparseBallCeil (d k : ℕ) (x : SparseVec d k) : Finset (SparseVec d k) :=
  Finset.univ.filter fun y => hammingDist x.val y.val < (k + 1) / 2

/-- `sparseBall ⊆ sparseBallCeil`: enlarging the threshold by one only adds points. -/
lemma sparseBall_subset_sparseBallCeil (d k : ℕ) (x : SparseVec d k) :
    sparseBall d k x ⊆ sparseBallCeil d k x := by
  intro y hy
  simp only [sparseBall, sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  omega

/-- Support of a binary vector: the finset of indices `i` with `f i = true`. -/
def supp {d : ℕ} (f : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter fun i => f i = true

/-- Two binary vectors with the same support are equal. -/
lemma eq_of_supp_eq {d : ℕ} (f g : Fin d → Bool) (h : supp f = supp g) : f = g := by
  ext i
  have hiff : f i = true ↔ g i = true := by
    constructor <;> intro hi
    · have : i ∈ supp f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [h] at this; exact (Finset.mem_filter.mp this).2
    · have : i ∈ supp g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [← h] at this; exact (Finset.mem_filter.mp this).2
  cases hf : f i <;> cases hg : g i <;> simp_all

/-- Hamming distance via symmetric difference of supports:
`d_H(f, g) = |supp f \ supp g| + |supp g \ supp f|`. -/
lemma hammingDist_eq_sdiff_sum {d : ℕ} (f g : Fin d → Bool) :
    hammingDist f g = (supp f \ supp g).card + (supp g \ supp f).card := by
  unfold hammingDist
  rw [← Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  congr 1; ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro h; cases hf : f i <;> cases hg : g i <;> simp_all
  · rintro (⟨hf, hg⟩ | ⟨hg, hf⟩) <;> simp_all

/-- If `|A| = |B|`, then `|A \ B| = |B \ A|`. -/
lemma card_sdiff_eq_of_card_eq' {α : Type*} [DecidableEq α] {A B : Finset α}
    (h : A.card = B.card) : (A \ B).card = (B \ A).card := by
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at h2; omega

/-- `supp f \ supp g ⊆ (supp g)ᶜ`. -/
lemma sdiff_supp_subset_compl {d : ℕ} (f g : Fin d → Bool) :
    supp f \ supp g ⊆ (supp g)ᶜ := by
  rw [Finset.compl_eq_univ_sdiff]
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi ⊢
  exact hi.2

/-- Sharp counting bound on `|sparseBallCeil x|`: bounded by a sum of products
`∑_{j < (k+3)/4} C(k, j) · C(d-k, j)`. -/
theorem sparseBallCeil_card_le_tight (d k : ℕ) (_hk : 2 ≤ k) (_hkd : k ≤ d / 8)
    (x : SparseVec d k) :
    (sparseBallCeil d k x).card ≤
      ∑ j ∈ Finset.range ((k + 3) / 4), Nat.choose k j * Nat.choose (d - k) j := by
  classical
  set S := supp x.val with hS_def
  have hScard : S.card = k := x.property
  have hSccard : Sᶜ.card = d - k := by
    rw [Finset.card_compl, Fintype.card_fin, hScard]
  let f : SparseVec d k → Finset (Fin d) × Finset (Fin d) :=
    fun y => (S \ supp y.val, supp y.val \ S)
  let target := (Finset.range ((k + 3) / 4)).biUnion
    (fun j => (S.powersetCard j) ×ˢ (Sᶜ.powersetCard j))
  have hf_card : ((sparseBallCeil d k x).image f).card = (sparseBallCeil d k x).card := by
    apply Finset.card_image_of_injOn
    intro y₁ _ y₂ _ heq
    simp only [f, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    apply Subtype.ext; apply eq_of_supp_eq; ext i
    constructor <;> intro hi
    · by_cases hx : i ∈ S
      · have : i ∉ S \ supp y₁.val := fun h => (Finset.mem_sdiff.mp h).2 hi
        rw [h1] at this
        exact by_contra fun hn => this (Finset.mem_sdiff.mpr ⟨hx, hn⟩)
      · have : i ∈ supp y₁.val \ S := Finset.mem_sdiff.mpr ⟨hi, hx⟩
        rw [h2] at this; exact (Finset.mem_sdiff.mp this).1
    · by_cases hx : i ∈ S
      · have : i ∉ S \ supp y₂.val := fun h => (Finset.mem_sdiff.mp h).2 hi
        rw [← h1] at this
        exact by_contra fun hn => this (Finset.mem_sdiff.mpr ⟨hx, hn⟩)
      · have : i ∈ supp y₂.val \ S := Finset.mem_sdiff.mpr ⟨hi, hx⟩
        rw [← h2] at this; exact (Finset.mem_sdiff.mp this).1
  have hf_sub : (sparseBallCeil d k x).image f ⊆ target := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨y, hy_ball, rfl⟩ := hp
    simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and] at hy_ball
    set j := (S \ supp y.val).card
    have hj_eq : (supp y.val \ S).card = j :=
      (card_sdiff_eq_of_card_eq' (by rw [hScard]; exact y.property.symm)).symm
    have hdist_eq : hammingDist x.val y.val = j + j := by
      rw [hammingDist_eq_sdiff_sum x.val y.val, ← hS_def]; omega
    have hj_bound : j < (k + 3) / 4 := by omega
    simp only [f, target, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
               Finset.mem_powersetCard]
    exact ⟨j, hj_bound, ⟨⟨Finset.sdiff_subset, rfl⟩,
      ⟨sdiff_supp_subset_compl y.val x.val, hj_eq⟩⟩⟩
  calc (sparseBallCeil d k x).card
      = ((sparseBallCeil d k x).image f).card := hf_card.symm
    _ ≤ target.card := Finset.card_le_card hf_sub
    _ ≤ ∑ j ∈ Finset.range ((k + 3) / 4),
          ((S.powersetCard j) ×ˢ (Sᶜ.powersetCard j)).card :=
        Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range ((k + 3) / 4), Nat.choose k j * Nat.choose (d - k) j := by
        congr 1; ext j
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
            hScard, hSccard]


/-- For positive `b`, `(a / b : ℝ) - 1 < ⌊a / b⌋` (in `ℕ`). -/
lemma nat_div_cast_gt (a b : ℕ) (hb : 0 < b) : (↑a : ℝ) / ↑b - 1 < ↑(a / b : ℕ) := by
  have hb_pos : (0:ℝ) < ↑b := Nat.cast_pos.mpr hb
  have h1 := Nat.lt_div_mul_add hb (a := a)
  have h2 : (↑a : ℝ) < (↑(a / b : ℕ) + 1) * ↑b := by
    calc (↑a : ℝ) < ↑(a / b * b + b) := by exact_mod_cast h1
      _ = ↑(a / b) * ↑b + ↑b := by push_cast; ring
      _ = (↑(a / b) + 1) * ↑b := by ring
  linarith [(div_lt_iff₀ hb_pos).mpr h2]


/-- Chernoff-style ratio inequality: `C(d-k, j) · ⌈exp((k/8) log(1 + d/(2k)))⌉ ≤ C(d-k, k-j)`. -/
theorem ceil_exp_choose_le (d k j : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d / 8)
    (hj : j < (k + 3) / 4) :
    Nat.choose (d - k) j *
      ⌈Real.exp ((↑k : ℝ) / 8 * Real.log (1 + (↑d : ℝ) / (2 * ↑k)))⌉₊ ≤
    Nat.choose (d - k) (k - j) := by
  have hk1 : 1 ≤ k := by omega
  have h8kd : 8 * k ≤ d := by omega
  have hkd' : k ≤ d - k := by omega
  have h2j : 2 * j ≤ k := by omega
  set m := k - 2 * j with hm_def
  have hm_pos : 0 < m := by omega
  have hkm_pos : 0 < k ^ m := Nat.pos_of_ne_zero (by positivity)
  have h_ratio := ChernoffHelpers.choose_ratio_bound (d - k) k j h2j hkd'

  set N := ⌈Real.exp ((↑k : ℝ) / 8 * Real.log (1 + (↑d : ℝ) / (2 * ↑k)))⌉₊

  suffices hN : N * k ^ m ≤ (d - k - k + 1) ^ m by
    have h1 : k ^ m * (Nat.choose (d - k) j * N)
        ≤ (d - k - k + 1) ^ m * Nat.choose (d - k) j := by
      calc k ^ m * (Nat.choose (d - k) j * N)
          = N * k ^ m * Nat.choose (d - k) j := by ring
        _ ≤ (d - k - k + 1) ^ m * Nat.choose (d - k) j :=
          Nat.mul_le_mul_right _ hN
    exact Nat.le_of_mul_le_mul_left (le_trans h1 h_ratio) hkm_pos

  set E := Real.exp ((↑k : ℝ) / 8 * Real.log (1 + (↑d : ℝ) / (2 * ↑k)))
  set dkk1 := d - k - k + 1
  have hk_pos_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hkm_pos_r : (0 : ℝ) < ↑(k ^ m) := Nat.cast_pos.mpr hkm_pos
  have h6k := ChernoffHelpers.base_ratio_ge_six d k hk1 h8kd
  have hdkk1_eq : (dkk1 : ℕ) = d - 2 * k + 1 := by omega
  have hdkk1_ge_6k : 6 * k ≤ dkk1 := by omega
  set ratio : ℝ := ↑dkk1 / ↑k
  have hratio_pos : ratio > 0 := div_pos (by positivity) hk_pos_r
  have hratio_ge6 : ratio ≥ 6 := by
    rw [ge_iff_le, le_div_iff₀ hk_pos_r]; exact_mod_cast hdkk1_ge_6k
  have hratio_ge1 : 1 ≤ ratio := by linarith

  have hE_le_rpow : E ≤ ratio ^ ((↑k : ℝ) / 2) := by
    have h_exp := ChernoffHelpers.exp_le_ratio_pow (↑d : ℝ) (↑k : ℝ)
      (by exact_mod_cast hk1 : (↑k : ℝ) ≥ 1)
      (by exact_mod_cast h8kd : (↑d : ℝ) ≥ 8 * ↑k)
    suffices h : ((↑d : ℝ) - 2 * ↑k + 1) / ↑k = ratio from by rwa [h] at h_exp
    congr 1
    have h2k : 2 * k ≤ d := by omega
    rw [hdkk1_eq, show d - 2 * k + 1 = (d - 2 * k) + 1 from by omega]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h2k, Nat.cast_mul]; ring

  have hm_ge : (↑m : ℝ) ≥ (↑k : ℝ) / 2 + 1 / 2 := by
    have h1 : (↑m : ℝ) ≥ ↑(k / 2) + 1 := by exact_mod_cast show m ≥ k / 2 + 1 by omega
    have h2 : k ≤ 2 * (k / 2) + 1 := by omega
    linarith [show (↑k : ℝ) ≤ 2 * ↑(k / 2 : ℕ) + 1 from by exact_mod_cast h2]

  have hE_ge1 : E ≥ 1 := by
    apply Real.one_le_exp
    apply mul_nonneg
    · positivity
    · apply Real.log_nonneg
      linarith [div_nonneg (show (0:ℝ) ≤ ↑d from by positivity)
        (by positivity : (0:ℝ) < 2 * ↑k).le]

  have hratio_m_ge_2E : ratio ^ m ≥ 2 * E := by
    suffices h : ratio ^ m ≥ 2 * ratio ^ ((↑k : ℝ) / 2) by linarith
    rw [show ratio ^ m = ratio ^ (↑m : ℝ) from (Real.rpow_natCast ratio m).symm,
        show (↑m : ℝ) = ↑k / 2 + (↑m - ↑k / 2) from by ring,
        Real.rpow_add hratio_pos]
    have hrkpos : ratio ^ ((↑k : ℝ) / 2) > 0 := Real.rpow_pos_of_pos hratio_pos _
    suffices h : ratio ^ ((↑m : ℝ) - ↑k / 2) ≥ 2 by nlinarith
    calc ratio ^ ((↑m : ℝ) - ↑k / 2)
        ≥ ratio ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hratio_ge1 (by linarith)
      _ ≥ (6 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by norm_num) hratio_ge6 (by norm_num)
      _ ≥ 2 := by
          have h1 : (4:ℝ) ^ ((1:ℝ)/2) ≤ (6:ℝ) ^ ((1:ℝ)/2) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
          have h2 : (4:ℝ) ^ ((1:ℝ)/2) = 2 := by
            rw [show (4:ℝ) = (2:ℝ) ^ (2:ℕ) from by norm_num,
                show ((2:ℝ) ^ (2:ℕ)) ^ ((1:ℝ)/2) = (2:ℝ) ^ ((2:ℕ) * ((1:ℝ)/2)) from by
                  rw [← Real.rpow_natCast (2:ℝ) 2,
                      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]]
            norm_num
          linarith

  have hE_plus1 : E + 1 ≤ ratio ^ m := by linarith

  have hndiv_gt : ratio ^ m - 1 < ↑(dkk1 ^ m / k ^ m : ℕ) := by
    have : ratio ^ m = ↑(dkk1 ^ m) / ↑(k ^ m) := by
      simp [ratio, div_pow, Nat.cast_pow]
    rw [this]
    exact nat_div_cast_gt (dkk1 ^ m) (k ^ m) hkm_pos

  have hN_le : N ≤ dkk1 ^ m / k ^ m := by
    rw [Nat.ceil_le]; linarith

  exact (Nat.le_div_iff_mul_le hkm_pos).mp hN_le

/-- Chernoff counting bound for `sparseBallCeil`: combining the Chernoff ratio inequality with the
counting bound shows `|sparseBallCeil x| · ⌈exp(…)⌉ ≤ |SparseVec d k|`. -/
theorem chernoff_counting_bound_ceil (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d / 8)
    (x : SparseVec d k) :
    (sparseBallCeil d k x).card * ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊
    ≤ Fintype.card (SparseVec d k) := by
  rw [sparsevec_card]
  set E := Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * ↑k)))
  set N := ⌈E⌉₊
  have hball := sparseBallCeil_card_le_tight d k hk hkd x
  have hkd' : k ≤ d := by omega
  calc (sparseBallCeil d k x).card * N
      ≤ (∑ j ∈ Finset.range ((k + 3) / 4),
          Nat.choose k j * Nat.choose (d - k) j) * N :=
        Nat.mul_le_mul_right N hball
    _ = ∑ j ∈ Finset.range ((k + 3) / 4),
          Nat.choose k j * Nat.choose (d - k) j * N := Finset.sum_mul ..
    _ ≤ ∑ j ∈ Finset.range ((k + 3) / 4),
          Nat.choose k j * Nat.choose (d - k) (k - j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (ceil_exp_choose_le d k j hk hkd hj)
    _ ≤ Nat.choose d k := by
        have hdk : d = k + (d - k) := by omega
        have hvand : Nat.choose d k =
            ∑ j ∈ Finset.range (k + 1),
              Nat.choose k j * Nat.choose (d - k) (k - j) := by
          conv_lhs => rw [hdk]
          rw [Nat.add_choose_eq, ← Nat.succ_eq_add_one]
          exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => Nat.choose k i * Nat.choose (d - k) j) k
        rw [hvand]
        apply Finset.sum_le_sum_of_subset
        apply Finset.range_mono
        omega

/-- Chernoff counting bound for `sparseBall`: by monotonicity, the same bound holds for the
strict-radius ball. -/
theorem chernoff_counting_bound (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d / 8)
    (x : SparseVec d k) :
    (sparseBall d k x).card * ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊
    ≤ Fintype.card (SparseVec d k) :=
  calc (sparseBall d k x).card * _ ≤ (sparseBallCeil d k x).card * _ :=
        Nat.mul_le_mul_right _ (Finset.card_le_card (sparseBall_subset_sparseBallCeil d k x))
    _ ≤ _ := chernoff_counting_bound_ceil d k hk hkd x

/-- Existence of a packing parameter `N`: an integer satisfying `N ≥ exp((k/8) log(1 + d/(2k)))`,
`N ≤ |SparseVec d k|`, and `|sparseBall x| · N ≤ |SparseVec d k|` for every `x`. -/
theorem chernoff_ball_bound (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d / 8) :
    ∃ N : ℕ, 0 < N ∧
    (N : ℝ) ≥ Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))) ∧
    N ≤ Fintype.card (SparseVec d k) ∧
    ∀ x : SparseVec d k, (sparseBall d k x).card * N ≤ Fintype.card (SparseVec d k) := by

  let N := ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊
  have hkd' : k ≤ d := by omega

  let x₀ := mkSparseVec d k hkd'

  have hbound := chernoff_counting_bound d k hk hkd x₀

  have hself := self_mem_sparseBall d k hk x₀
  have hball_pos : 0 < (sparseBall d k x₀).card := Finset.card_pos.mpr ⟨x₀, hself⟩

  have hN_pos : 0 < N := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)

  have hN_le : N ≤ Fintype.card (SparseVec d k) :=
    le_trans (Nat.le_mul_of_pos_left N hball_pos) hbound
  exact ⟨N, hN_pos, Nat.le_ceil _, hN_le, fun x => chernoff_counting_bound d k hk hkd x⟩

/-- The `i`-th standard binary unit vector in `{0,1}^d`. -/
def unitVec (d : ℕ) (i : Fin d) : Fin d → Bool := fun j => i == j

/-- The `ℓ⁰`-norm of `unitVec d i` is `1`. -/
lemma l0norm_unitVec (d : ℕ) (i : Fin d) : l0norm (unitVec d i) = 1 := by
  unfold l0norm unitVec
  simp only [beq_iff_eq]
  have : (Finset.univ.filter fun j : Fin d => i = j) = {i} := by
    ext j; simp [eq_comm]
  rw [this, card_singleton]

/-- The `1`-sparse vector corresponding to coordinate `i`. -/
def sparseVecOfFin (d : ℕ) (i : Fin d) : SparseVec d 1 :=
  ⟨unitVec d i, l0norm_unitVec d i⟩

/-- The map `i ↦ sparseVecOfFin d i` is injective. -/
lemma sparseVecOfFin_injective (d : ℕ) : Function.Injective (sparseVecOfFin d) := by
  intro i j h
  simp only [sparseVecOfFin, Subtype.mk.injEq] at h
  have := congr_fun h i
  simp [unitVec, beq_iff_eq] at this
  exact this.symm

/-- Base case (`k = 1`) used in the sparse Varshamov-Gilbert proof: `d` itself satisfies the
required exponential lower bound and is at most `|SparseVec d 1|`. -/
theorem sparse_vec_k1_count (d : ℕ) (hd : 1 ≤ d / 8) :
    (d : ℝ) ≥ Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2)) ∧
    d ≤ Fintype.card (SparseVec d 1) := by
  constructor
  ·
    have hd8 : 8 ≤ d := by omega
    have hd2_pos : (0 : ℝ) < 1 + (d : ℝ) / 2 := by positivity
    calc Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2))
        ≤ Real.exp (Real.log (1 + (d : ℝ) / 2)) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_of_le_one_left (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
          linarith
      _ = 1 + (d : ℝ) / 2 := Real.exp_log hd2_pos
      _ ≤ (d : ℝ) := by
          have : (d : ℝ) ≥ 8 := by exact_mod_cast hd8
          linarith
  ·
    have h := Fintype.card_le_of_injective (sparseVecOfFin d) (sparseVecOfFin_injective d)
    rwa [Fintype.card_fin] at h

/-- Probabilistic-method form of the sparse Varshamov-Gilbert lemma: existence of `M` binary
vectors of weight exactly `k` with pairwise Hamming distance ≥ `k/2` and
`log M ≥ (k/8) log(1 + d/(2k))`. -/
theorem probabilistic_method_sparse_vg (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d / 8) :
    ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
    Real.log M ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)) ∧
    (∀ j : Fin M, l0norm (ω j) = k) ∧
    ∀ j k' : Fin M, j ≠ k' → hammingDist (ω j) (ω k') ≥ k / 2 := by
  classical
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  ·
    obtain ⟨hd_exp, hd_card⟩ := sparse_vec_k1_count d hkd
    have hd_pos : 0 < d := by omega

    let T := (Finset.univ : Finset (SparseVec d 1))
    have hT_card : d ≤ T.card := by simp only [T, Finset.card_univ]; exact hd_card
    refine ⟨T.card, by omega, fun j => (T.equivFin.symm j).val.val, ?_, ?_, ?_⟩
    ·
      simp only [Nat.cast_one]
      calc (1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * 1))
          = Real.log (Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2))) := by
            rw [Real.log_exp]; ring_nf
        _ ≤ Real.log (d : ℝ) := Real.log_le_log (Real.exp_pos _) hd_exp
        _ ≤ Real.log (T.card : ℝ) :=
            Real.log_le_log (Nat.cast_pos.mpr hd_pos) (Nat.cast_le.mpr hT_card)
    ·
      intro j; exact (T.equivFin.symm j).val.property
    ·
      intro j k' _; simp [Nat.div_eq_of_lt (by norm_num : (1 : ℕ) < 2)]
  ·
    have hk2' : 2 ≤ k := hk2
    obtain ⟨N, hN_pos, hN_exp, hN_le, hN_ball⟩ := chernoff_ball_bound d k hk2' hkd

    have hball_bound : ∀ x : SparseVec d k,
        (sparseBall d k x).card ≤ Fintype.card (SparseVec d k) / N :=
      fun x => (Nat.le_div_iff_mul_le hN_pos).mpr (hN_ball x)
    have hball_self : ∀ x : SparseVec d k, x ∈ sparseBall d k x := by
      intro x
      simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
      simp [Finset.filter_false_of_mem]; omega
    have hball_symm : ∀ x y : SparseVec d k,
        y ∈ sparseBall d k x → x ∈ sparseBall d k y := by
      intro x y; simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hammingDist_comm y.val x.val]; exact id

    let B := Fintype.card (SparseVec d k) / N
    obtain ⟨T, hsize, hT_pack⟩ := greedy_packing_bound (sparseBall d k) B
      hball_self hball_symm hball_bound

    have hB_pos : 0 < B := Nat.div_pos hN_le hN_pos
    have hTN : N ≤ T.card := by
      have : B * N ≤ T.card * B := le_trans (Nat.div_mul_le_self _ _) hsize
      rw [mul_comm T.card B] at this
      exact Nat.le_of_mul_le_mul_left this hB_pos
    have hT_pos : 0 < T.card := Nat.lt_of_lt_of_le hN_pos hTN

    refine ⟨T.card, hT_pos, fun j => (T.equivFin.symm j).val.val, ?_, ?_, ?_⟩
    ·
      calc (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))
          = Real.log (Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))) :=
            (Real.log_exp _).symm
        _ ≤ Real.log (T.card : ℝ) :=
            Real.log_le_log (Real.exp_pos _) (le_trans hN_exp (Nat.cast_le.mpr hTN))
    ·
      intro j; exact (T.equivFin.symm j).val.property
    ·
      intro j k' hne
      have hj_mem := (T.equivFin.symm j).property
      have hk_mem := (T.equivFin.symm k').property
      have hne' : (T.equivFin.symm j).val ≠ (T.equivFin.symm k').val := by
        intro h; exact hne (T.equivFin.symm.injective (Subtype.ext h))
      have := hT_pack _ hj_mem _ hk_mem hne'
      simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
      exact this

/-- **Lemma 5.14** (Sparse Varshamov-Gilbert): for `1 ≤ k ≤ d/8`, there exist binary vectors
`ω_1, …, ω_M ∈ {0,1}^d` with pairwise Hamming distance at least `k/2`, weight exactly `k`,
and `log M ≥ (k/8) log(1 + d/(2k))`. -/
theorem sparse_varshamov_gilbert (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d / 8) :
    ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
    Real.log M ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)) ∧
    (∀ j : Fin M, l0norm (ω j) = k) ∧
    ∀ j k' : Fin M, j ≠ k' → hammingDist (ω j) (ω k') ≥ k / 2 :=
  probabilistic_method_sparse_vg d k hk hkd

/-- Ceiling-radius variant of `chernoff_ball_bound`. -/
theorem chernoff_ball_bound_ceil (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d / 8) :
    ∃ N : ℕ, 0 < N ∧
    (N : ℝ) ≥ Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))) ∧
    N ≤ Fintype.card (SparseVec d k) ∧
    ∀ x : SparseVec d k, (sparseBallCeil d k x).card * N ≤ Fintype.card (SparseVec d k) := by
  let N := ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊
  have hkd' : k ≤ d := by omega
  let x₀ := mkSparseVec d k hkd'
  have hbound := chernoff_counting_bound_ceil d k hk hkd x₀
  have hself : x₀ ∈ sparseBallCeil d k x₀ := by
    simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
    have : (Finset.univ.filter fun i => x₀.val i ≠ x₀.val i) = ∅ := by ext i; simp
    rw [this, Finset.card_empty]; omega
  have hball_pos : 0 < (sparseBallCeil d k x₀).card := Finset.card_pos.mpr ⟨x₀, hself⟩
  have hN_pos : 0 < N := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hN_le : N ≤ Fintype.card (SparseVec d k) :=
    le_trans (Nat.le_mul_of_pos_left N hball_pos) hbound
  exact ⟨N, hN_pos, Nat.le_ceil _, hN_le, fun x => chernoff_counting_bound_ceil d k hk hkd x⟩

/-- `|{i : Fin d | a ≤ i.val < a + k}| = k` when `a + k ≤ d`. -/
lemma card_filter_interval (d a k : ℕ) (h : a + k ≤ d) :
    (Finset.univ.filter (fun i : Fin d => a ≤ i.val ∧ i.val < a + k)).card = k := by
  have hmk : ∀ m : Fin k, a + m.val < d := fun ⟨m, hm⟩ => by omega
  let f : Fin k → Fin d := fun m => ⟨a + m.val, hmk m⟩
  have hf_inj : Function.Injective f := by intro x y hab; ext; simp [f] at hab; omega
  have himg : (Finset.univ.filter (fun i : Fin d => a ≤ i.val ∧ i.val < a + k)) =
    (Finset.univ : Finset (Fin k)).image f := by
    ext ⟨i, _⟩; constructor
    · intro hmem; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      simp only [Finset.mem_image, Finset.mem_univ, true_and, f, Fin.ext_iff]
      exact ⟨⟨i - a, by omega⟩, by simp; omega⟩
    · intro hmem; simp only [Finset.mem_image, Finset.mem_univ, true_and, f, Fin.ext_iff] at hmem
      obtain ⟨⟨m, _⟩, hval⟩ := hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp at hval; omega
  rw [himg, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

/-- The `j`-th block of `k` consecutive indices, packaged as a `k`-sparse vector. -/
def blockSparseVec (d k : ℕ) (hkd : k ≤ d / 8) (j : Fin 8) : SparseVec d k :=
  ⟨fun i => decide (j.val * k ≤ i.val ∧ i.val < j.val * k + k), by
    simp only [l0norm, decide_eq_true_eq]
    apply card_filter_interval
    have h1 : 8 * k ≤ d := by have := Nat.div_mul_le_self d 8; omega
    nlinarith [j.isLt]⟩

/-- Distinct block indices give distinct block sparse vectors. -/
lemma blockSparseVec_injective (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d / 8) :
    Function.Injective (blockSparseVec d k hkd) := by
  intro a b heq
  have h1 : 8 * k ≤ d := by have := Nat.div_mul_le_self d 8; omega
  simp only [blockSparseVec, Subtype.mk.injEq] at heq
  have haid : a.val * k < d := by nlinarith [a.isLt]
  have hval := congr_fun heq ⟨a.val * k, haid⟩
  simp only [decide_eq_decide] at hval
  have ha_bound : a.val * k ≤ a.val * k ∧ a.val * k < a.val * k + k := ⟨le_refl _, by omega⟩
  rw [iff_true_intro ha_bound] at hval
  obtain ⟨hle, hlt⟩ := hval.mp trivial
  exact Fin.ext (by nlinarith)

/-- Two distinct block sparse vectors are at Hamming distance at least `k`. -/
lemma blockSparseVec_dist (d k : ℕ) (_hk : 1 ≤ k) (hkd : k ≤ d / 8)
    (i j : Fin 8) (hij : i ≠ j) :
    hammingDist (blockSparseVec d k hkd i).val (blockSparseVec d k hkd j).val ≥ k := by
  unfold hammingDist blockSparseVec
  simp only
  have h8k : 8 * k ≤ d := by have := Nat.div_mul_le_self d 8; omega
  have hik : i.val * k + k ≤ d := by nlinarith [i.isLt]
  calc k = (Finset.univ.filter (fun idx : Fin d =>
        i.val * k ≤ idx.val ∧ idx.val < i.val * k + k)).card :=
      (card_filter_interval d (i.val * k) k hik).symm
    _ ≤ (Finset.univ.filter (fun idx : Fin d =>
        decide (i.val * k ≤ idx.val ∧ idx.val < i.val * k + k) ≠
        decide (j.val * k ≤ idx.val ∧ idx.val < j.val * k + k))).card := by
      apply Finset.card_le_card
      intro ⟨idx, hidx⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      obtain ⟨h1, h2⟩ := hmem
      have hj_false : ¬(j.val * k ≤ idx ∧ idx < j.val * k + k) := by
        intro ⟨hj1, hj2⟩
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hi | hi
        · linarith [Nat.mul_le_mul_right k hi]
        · linarith [Nat.mul_le_mul_right k hi]
      have hi_true : decide (i.val * k ≤ idx ∧ idx < i.val * k + k) = true :=
        decide_eq_true_eq.mpr (And.intro h1 h2)
      have hj_f : decide (j.val * k ≤ idx ∧ idx < j.val * k + k) = false :=
        decide_eq_false hj_false
      rw [hi_true, hj_f]; decide

/-- If `n ≥ ⌈(k+1)/2⌉` (integer division), then `(n : ℝ) ≥ k/2`. -/
lemma nat_ceil_half_ge_real (k : ℕ) (n : ℕ) (h : n ≥ (k + 1) / 2) :
    (n : ℝ) ≥ (k : ℝ) / 2 := by
  have h2 : k ≤ ((k + 1) / 2) * 2 := by omega
  calc (k : ℝ) / 2 ≤ ((k + 1) / 2 : ℕ) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        exact_mod_cast h2
    _ ≤ (n : ℝ) := by exact_mod_cast h

/-- Two distinct binary vectors have positive Hamming distance. -/
lemma hammingDist_pos_of_ne {d : ℕ} {f g : Fin d → Bool} (h : f ≠ g) :
    0 < hammingDist f g := by
  unfold hammingDist
  rw [Finset.card_pos]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- Symmetry of `sparseBallCeil`: `y ∈ ball x ↔ x ∈ ball y`. -/
lemma sparseBallCeil_symm (d k : ℕ) (x y : SparseVec d k) :
    y ∈ sparseBallCeil d k x → x ∈ sparseBallCeil d k y := by
  simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hammingDist_comm y.val x.val]; exact id

/-- Every `k`-sparse vector lies in its own `sparseBallCeil` when `k ≥ 2`. -/
lemma self_mem_sparseBallCeil (d k : ℕ) (hk : 2 ≤ k) (x : SparseVec d k) :
    x ∈ sparseBallCeil d k x := by
  simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
  have : (Finset.univ.filter fun i => x.val i ≠ x.val i) = ∅ := by ext i; simp
  rw [this, Finset.card_empty]; omega

/-- Strengthened sparse Varshamov-Gilbert with `M ≥ 8`, using the real-valued Hamming
separation `(d_H(ω_j, ω_{k'}) : ℝ) ≥ k/2`; in particular always producing at least the eight
block-sparse vectors. -/
theorem sparse_vg_card_bound (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d / 8) :
    ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)),
    8 ≤ M ∧
    Real.log M ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)) ∧
    (∀ j : Fin M, l0norm (ω j) = k) ∧
    ∀ j k' : Fin M, j ≠ k' → (hammingDist (ω j) (ω k') : ℝ) ≥ (k : ℝ) / 2 := by
  classical
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  ·
    have hd8 : 8 ≤ d := by omega
    obtain ⟨hd_exp, hd_card⟩ := sparse_vec_k1_count d hkd
    have hd_pos : 0 < d := by omega
    let T := (Finset.univ : Finset (SparseVec d 1))
    have hT_card : d ≤ T.card := by simp only [T, Finset.card_univ]; exact hd_card
    have hT8 : 8 ≤ T.card := le_trans hd8 hT_card
    refine ⟨T.card, by omega, fun j => (T.equivFin.symm j).val.val, hT8, ?_, ?_, ?_⟩
    ·
      simp only [Nat.cast_one]
      calc (1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * 1))
          = Real.log (Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2))) := by
            rw [Real.log_exp]; ring_nf
        _ ≤ Real.log (d : ℝ) := Real.log_le_log (Real.exp_pos _) hd_exp
        _ ≤ Real.log (T.card : ℝ) :=
            Real.log_le_log (Nat.cast_pos.mpr hd_pos) (Nat.cast_le.mpr hT_card)
    ·
      intro j; exact (T.equivFin.symm j).val.property
    ·
      intro j k' hjk
      have hne : (T.equivFin.symm j).val ≠ (T.equivFin.symm k').val := by
        intro h; exact hjk (T.equivFin.symm.injective (Subtype.ext h))
      have hne_val : (T.equivFin.symm j).val.val ≠ (T.equivFin.symm k').val.val := by
        intro h; exact hne (Subtype.ext h)
      have hdist_pos := hammingDist_pos_of_ne hne_val
      simp only [Nat.cast_one]
      have : (1 : ℝ) ≤ (hammingDist (T.equivFin.symm j).val.val (T.equivFin.symm k').val.val : ℝ) :=
        Nat.one_le_cast.mpr hdist_pos
      linarith

  ·
    have hk2' : 2 ≤ k := hk2

    set expVal := Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))
    set N := ⌈expVal⌉₊ with hN_def
    have hN_pos : 0 < N := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
    have hN_ge : (N : ℝ) ≥ expVal := Nat.le_ceil _
    by_cases hN8 : 8 ≤ N
    ·
      obtain ⟨N', hN'_pos, hN'_exp, hN'_le, hN'_ball⟩ := chernoff_ball_bound_ceil d k hk2' hkd

      have hball_bound : ∀ x : SparseVec d k,
          (sparseBallCeil d k x).card ≤ Fintype.card (SparseVec d k) / N' :=
        fun x => (Nat.le_div_iff_mul_le hN'_pos).mpr (hN'_ball x)
      have hball_self : ∀ x : SparseVec d k, x ∈ sparseBallCeil d k x :=
        fun x => self_mem_sparseBallCeil d k hk2' x
      have hball_symm : ∀ x y : SparseVec d k,
          y ∈ sparseBallCeil d k x → x ∈ sparseBallCeil d k y :=
        fun x y => sparseBallCeil_symm d k x y

      let B := Fintype.card (SparseVec d k) / N'
      obtain ⟨T, hsize, hT_pack⟩ := greedy_packing_bound (sparseBallCeil d k) B
        hball_self hball_symm hball_bound
      have hB_pos : 0 < B := Nat.div_pos hN'_le hN'_pos
      have hTN : N' ≤ T.card := by
        have : B * N' ≤ T.card * B := le_trans (Nat.div_mul_le_self _ _) hsize
        rw [mul_comm T.card B] at this
        exact Nat.le_of_mul_le_mul_left this hB_pos


      have hexpVal_gt : expVal > 7 := by
        have hN_cast : (N : ℝ) ≥ 8 := by exact_mod_cast hN8
        have hceil_bound : (⌈expVal⌉₊ : ℝ) < expVal + 1 :=
          Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos _))
        linarith
      have hN'_ge8 : 8 ≤ N' := by
        have hN'_gt7 : (N' : ℝ) > 7 := lt_of_lt_of_le hexpVal_gt hN'_exp
        exact_mod_cast (show (7 : ℝ) < N' from hN'_gt7)

      have hT8 : 8 ≤ T.card := le_trans hN'_ge8 hTN
      have hT_pos : 0 < T.card := by omega
      refine ⟨T.card, hT_pos, fun j => (T.equivFin.symm j).val.val, hT8, ?_, ?_, ?_⟩
      ·
        calc (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))
            = Real.log (Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))) :=
              (Real.log_exp _).symm
          _ ≤ Real.log (T.card : ℝ) :=
              Real.log_le_log (Real.exp_pos _)
                (le_trans hN'_exp (Nat.cast_le.mpr hTN))
      ·
        intro j; exact (T.equivFin.symm j).val.property
      ·
        intro j k' hne
        have hj_mem := (T.equivFin.symm j).property
        have hk_mem := (T.equivFin.symm k').property
        have hne' : (T.equivFin.symm j).val ≠ (T.equivFin.symm k').val := by
          intro h; exact hne (T.equivFin.symm.injective (Subtype.ext h))
        have := hT_pack _ hj_mem _ hk_mem hne'
        simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
        exact nat_ceil_half_ge_real k _ this
    ·
      push Not at hN8
      refine ⟨8, by norm_num, fun j => (blockSparseVec d k hkd j).val, le_refl _, ?_, ?_, ?_⟩
      ·
        have hexp_lt : expVal < 8 := by
          calc expVal ≤ N := hN_ge
            _ < 8 := by exact_mod_cast hN8
        calc (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))
            = Real.log expVal := by rw [Real.log_exp]
          _ ≤ Real.log 8 := Real.log_le_log (Real.exp_pos _) (le_of_lt hexp_lt)
          _ = Real.log (8 : ℕ) := by norm_num
      ·
        intro j; exact (blockSparseVec d k hkd j).property
      ·
        intro j k' hjk
        have hdist := blockSparseVec_dist d k hk hkd j k' hjk
        have h1 : (k : ℝ) ≤ (hammingDist (blockSparseVec d k hkd j).val
          (blockSparseVec d k hkd k').val : ℝ) := Nat.cast_le.mpr hdist
        linarith [Nat.cast_nonneg (α := ℝ) k]

end SparseVarshamovGilbert

end
