/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Atlas.BooleanFunctions.code.Definitions
import Atlas.BooleanFunctions.code.Parseval
import Atlas.BooleanFunctions.code.TwoPointInequality
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.MeanInequalitiesPow

open Finset BigOperators Real

namespace BooleanFourier

lemma sum_chi_mul_chi_point {n : ℕ} (S T : Finset (Fin n)) :
    ∑ x : Fin n → Bool, chi S x * chi T x =
      if S = T then (2 : ℝ) ^ n else 0 := by
  split_ifs with h
  · subst h
    simp only [chi]
    conv_lhs =>
      arg 2; ext x
      rw [show (∏ i ∈ S, boolToReal (x i)) * (∏ i ∈ S, boolToReal (x i)) =
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (x i)) from
        (Finset.prod_mul_distrib).symm]
    simp only [boolToReal_mul_self, Finset.prod_const_one]
    simp [Fintype.card_bool, Fintype.card_fin]
  · obtain ⟨j, hj⟩ := Finset.symmDiff_nonempty.mpr h
    have hjmem := Finset.mem_symmDiff.mp hj
    apply Finset.sum_ninvolution (g := fun x => flipAt j x)
    · intro x
      rcases hjmem with ⟨hjS, hjT⟩ | ⟨hjT, hjS⟩
      · have h1 : chi S (flipAt j x) = -chi S x := chi_flipAt S j hjS x
        have h2 : chi T (flipAt j x) = chi T x := by
          simp only [chi, flipAt]
          apply Finset.prod_congr rfl
          intro i hi
          congr 1
          exact Function.update_of_ne (ne_of_mem_of_not_mem hi hjT) _ _
        linarith [show chi S (flipAt j x) * chi T (flipAt j x) =
          -(chi S x * chi T x) from by rw [h1, h2]; ring]
      · have h1 : chi S (flipAt j x) = chi S x := by
          simp only [chi, flipAt]
          apply Finset.prod_congr rfl
          intro i hi
          congr 1
          exact Function.update_of_ne (ne_of_mem_of_not_mem hi hjS) _ _
        have h2 : chi T (flipAt j x) = -chi T x := chi_flipAt T j hjT x
        linarith [show chi S (flipAt j x) * chi T (flipAt j x) =
          -(chi S x * chi T x) from by rw [h1, h2]; ring]
    · intro x _
      exact flipAt_ne_self j x
    · intro x
      exact Finset.mem_univ _
    · intro x
      exact flipAt_flipAt j x

noncomputable def noiseOp {n : ℕ} (ρ : ℝ) (f : BoolFn n) : BoolFn n :=
  fun x => ∑ y : Fin n → Bool,
    (∏ i : Fin n, ((1 + ρ * boolToReal (x i) * boolToReal (y i)) / 2)) * f y

lemma noise_kernel_expand {n : ℕ} (ρ : ℝ) (x y : Fin n → Bool) :
    ∏ i : Fin n, (1 + ρ * boolToReal (x i) * boolToReal (y i)) =
      ∑ S : Finset (Fin n), ρ ^ S.card * chi S x * chi S y := by
  classical
  have step1 : ∏ i : Fin n, (1 + ρ * boolToReal (x i) * boolToReal (y i)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i ∈ S, (ρ * boolToReal (x i) * boolToReal (y i)) := by
    rw [← Finset.prod_one_add]
  rw [step1, Finset.powerset_univ]
  congr 1; ext S
  simp only [chi]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]

theorem noiseOp_eq_fourier_expansion {n : ℕ} (ρ : ℝ) (f : BoolFn n) (x : Fin n → Bool) :
    noiseOp ρ f x = ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S * chi S x := by
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  simp only [noiseOp]

  have hkernel : ∀ y : Fin n → Bool,
      (∏ i : Fin n, ((1 + ρ * boolToReal (x i) * boolToReal (y i)) / 2)) =
        ((2 : ℝ) ^ n)⁻¹ *
          ∑ S : Finset (Fin n), ρ ^ S.card * chi S x * chi S y := by
    intro y
    have hprod_div : ∏ i : Fin n, ((1 + ρ * boolToReal (x i) * boolToReal (y i)) / 2) =
        ((2 : ℝ) ^ n)⁻¹ * ∏ i : Fin n, (1 + ρ * boolToReal (x i) * boolToReal (y i)) := by
      rw [show ((2 : ℝ) ^ n)⁻¹ = ∏ _i : Fin n, (2 : ℝ)⁻¹ from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [inv_pow]]
      rw [← Finset.prod_mul_distrib]
      congr 1; ext i
      rw [inv_mul_eq_div]
    rw [hprod_div, noise_kernel_expand]
  simp_rw [hkernel]

  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]


  congr 1; ext1 S
  simp only [fourierCoeff, one_div]
  conv_lhs =>
    arg 2; ext y
    rw [show ((2 : ℝ) ^ n)⁻¹ * (ρ ^ S.card * chi S x * chi S y) * f y =
        ((2 : ℝ) ^ n)⁻¹ * ρ ^ S.card * chi S x * (f y * chi S y) from by ring]
  rw [show ∑ y : Fin n → Bool,
      ((2 : ℝ) ^ n)⁻¹ * ρ ^ S.card * chi S x * (f y * chi S y) =
      ((2 : ℝ) ^ n)⁻¹ * ρ ^ S.card * chi S x *
        ∑ y : Fin n → Bool, f y * chi S y from by
    rw [← Finset.mul_sum]]
  ring

theorem noiseOp_fourierCoeff {n : ℕ} (ρ : ℝ) (f : BoolFn n) (S : Finset (Fin n)) :
    fourierCoeff (noiseOp ρ f) S = ρ ^ S.card * fourierCoeff f S := by
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)

  simp only [fourierCoeff, one_div]
  have hrewrite : ∀ y : Fin n → Bool,
      noiseOp ρ f y = ∑ T : Finset (Fin n), ρ ^ T.card * fourierCoeff f T * chi T y :=
    fun y => noiseOp_eq_fourier_expansion ρ f y
  simp_rw [hrewrite]

  have step1 : ∀ y : Fin n → Bool,
      (∑ T : Finset (Fin n),
        ρ ^ T.card * fourierCoeff f T * chi T y) * chi S y =
      ∑ T : Finset (Fin n),
        ρ ^ T.card * fourierCoeff f T * (chi T y * chi S y) := by
    intro y
    rw [Finset.sum_mul]
    congr 1; ext T; ring
  simp_rw [step1]
  rw [show ((2 : ℝ) ^ n)⁻¹ * ∑ y : Fin n → Bool,
      ∑ T : Finset (Fin n),
        ρ ^ T.card * fourierCoeff f T * (chi T y * chi S y) =
      ((2 : ℝ) ^ n)⁻¹ * ∑ T : Finset (Fin n),
        ρ ^ T.card * fourierCoeff f T *
          ∑ y : Fin n → Bool, chi T y * chi S y from by
    congr 1
    rw [Finset.sum_comm]
    congr 1; ext T
    simp_rw [← Finset.mul_sum]]
  simp_rw [sum_chi_mul_chi_point]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  simp only [fourierCoeff, one_div]
  field_simp


theorem noiseOp_l2_norm_sq {n : ℕ} (ρ : ℝ) (f : BoolFn n) :
    ∑ S : Finset (Fin n), (fourierCoeff (noiseOp ρ f) S) ^ 2 =
      ∑ S : Finset (Fin n), ρ ^ (2 * S.card) * (fourierCoeff f S) ^ 2 := by
  congr 1
  ext S
  rw [noiseOp_fourierCoeff]
  ring

noncomputable def restrictLast {n : ℕ} (f : BoolFn (n + 1)) (b : Bool) : BoolFn n :=
  fun x => f (Fin.snoc x b)

lemma sum_finBool_succ_split {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x : Fin (n + 1) → Bool, g x =
      ∑ x' : Fin n → Bool, g (Fin.snoc x' true) +
      ∑ x' : Fin n → Bool, g (Fin.snoc x' false) := by
  have heq : ∑ x : Fin (n + 1) → Bool, g x =
    ∑ p : Bool × (Fin n → Bool), g (Fin.snoc p.2 p.1) := by
    apply (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Bool)) _ _ _).symm
    intro p
    simp [Fin.snocEquiv]
  rw [heq, Fintype.sum_prod_type, Fintype.sum_bool]

theorem lpNorm_restrictLast {n : ℕ} (f : BoolFn (n + 1)) {q : ℝ} (hq : 0 < q) :
    (lpNorm q f) ^ q = (1/2) * (lpNorm q (restrictLast f true)) ^ q +
                        (1/2) * (lpNorm q (restrictLast f false)) ^ q := by
  have hbase_f : 0 ≤ (1 / (2 ^ (n + 1) : ℝ)) *
      ∑ x : Fin (n + 1) → Bool, |f x| ^ q := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _)
  have hbase_t : 0 ≤ (1 / (2 ^ n : ℝ)) *
      ∑ x : Fin n → Bool, |restrictLast f true x| ^ q := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _)
  have hbase_ff : 0 ≤ (1 / (2 ^ n : ℝ)) *
      ∑ x : Fin n → Bool, |restrictLast f false x| ^ q := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _)
  simp only [lpNorm]
  rw [← rpow_mul hbase_f, ← rpow_mul hbase_t, ← rpow_mul hbase_ff]
  have hexp : 1 / q * q = 1 := by field_simp
  rw [hexp, rpow_one, rpow_one, rpow_one]
  rw [sum_finBool_succ_split (fun x => |f x| ^ q)]
  simp only [restrictLast]
  ring_nf

lemma fourierCoeff_restrictLast {n : ℕ} (f : BoolFn (n + 1)) (b : Bool)
    (T : Finset (Fin n)) :
    fourierCoeff (restrictLast f b) T =
      fourierCoeff f (T.map Fin.castSuccEmb) +
        boolToReal b * fourierCoeff f (T.map Fin.castSuccEmb ∪ {Fin.last n}) := by
  classical
  simp only [fourierCoeff, one_div, restrictLast]

  have hsplit : ∀ (S : Finset (Fin (n + 1))),
    ∑ y : Fin (n + 1) → Bool, f y * chi S y =
      ∑ x' : Fin n → Bool, f (Fin.snoc x' true) * chi S (Fin.snoc x' true) +
      ∑ x' : Fin n → Bool, f (Fin.snoc x' false) * chi S (Fin.snoc x' false) := by
    intro S
    have heq : ∑ y : Fin (n + 1) → Bool, f y * chi S y =
      ∑ p : Bool × (Fin n → Bool), f (Fin.snoc p.2 p.1) * chi S (Fin.snoc p.2 p.1) := by
      apply (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Bool)) _ _ _).symm
      intro p; simp [Fin.snocEquiv]
    rw [heq, Fintype.sum_prod_type, Fintype.sum_bool]

  have hchi_cast : ∀ (x' : Fin n → Bool) (b' : Bool),
      chi (T.map Fin.castSuccEmb) (Fin.snoc x' b') = chi T x' := by
    intro x' b'
    simp only [chi]; rw [Finset.prod_map]; congr 1; ext i; congr 1
    exact Fin.snoc_castSucc ..

  have hchi_union : ∀ (x' : Fin n → Bool) (b' : Bool),
      chi (T.map Fin.castSuccEmb ∪ {Fin.last n}) (Fin.snoc x' b') =
        chi T x' * boolToReal b' := by
    intro x' b'
    have hdisj : Disjoint (T.map Fin.castSuccEmb) ({Fin.last n} : Finset (Fin (n + 1))) := by
      rw [Finset.disjoint_left]; intro x hx; rw [Finset.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx; simp
    simp only [chi]; rw [Finset.prod_union hdisj, Finset.prod_singleton]
    congr 1
    · rw [Finset.prod_map]; congr 1; ext i; congr 1; exact Fin.snoc_castSucc ..
    · congr 1; exact Fin.snoc_last ..
  rw [hsplit, hsplit]
  simp_rw [hchi_cast, hchi_union]
  cases b <;> simp [boolToReal, pow_succ] <;> ring

lemma noiseOp_one {n : ℕ} (f : BoolFn n) : noiseOp 1 f = f := by
  funext x
  have h := noiseOp_eq_fourier_expansion 1 f x
  simp only [one_pow, one_mul] at h
  rw [h, ← fourier_expansion f x]

lemma noiseOp_comp {n : ℕ} (ρ σ : ℝ) (f : BoolFn n) :
    noiseOp ρ (noiseOp σ f) = noiseOp (ρ * σ) f := by
  funext x
  rw [noiseOp_eq_fourier_expansion ρ (noiseOp σ f) x]
  rw [noiseOp_eq_fourier_expansion (ρ * σ) f x]
  congr 1; ext S
  rw [noiseOp_fourierCoeff, mul_pow]
  ring

lemma sum_pow_card_mul_fourierCoeff_sq_le {n : ℕ} (f : BoolFn n) (k : ℕ) (c : ℝ)
    (hc : 1 ≤ c) (hdeg : degree f ≤ k) :
    ∑ S : Finset (Fin n), c ^ S.card * (fourierCoeff f S) ^ 2 ≤
      c ^ k * ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hfS : fourierCoeff f S = 0
  · simp [hfS]
  · have hSk : S.card ≤ k := by
      have hS_mem : S ∈ Finset.univ.filter
          (fun T : Finset (Fin n) => fourierCoeff f T ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfS⟩
      exact le_trans (Finset.le_sup hS_mem) hdeg
    have hc_nonneg : 0 ≤ c := le_trans zero_le_one hc
    have hc_pow : c ^ S.card ≤ c ^ k := by
      exact pow_le_pow_right₀ hc hSk
    exact mul_le_mul_of_nonneg_right hc_pow (sq_nonneg _)

theorem hypercontractive_low_degree {n : ℕ} (f : BoolFn n) (k : ℕ) (q : ℝ)
    (hq : 2 ≤ q)
    (hdeg : degree f ≤ k)
    (h_bb : ∀ (g : BoolFn n) (ρ' : ℝ),
      0 ≤ ρ' → ρ' ≤ Real.sqrt ((2 - 1) / (q - 1)) →
      lpNorm q (noiseOp ρ' g) ≤ lpNorm 2 g) :
    lpNorm q f ≤ (q - 1) ^ ((k : ℝ) / 2) * lpNorm 2 f := by

  set ρ := 1 / Real.sqrt (q - 1) with hρ_def
  set g := noiseOp (Real.sqrt (q - 1)) f with hg_def
  have hq1_pos : (0 : ℝ) < q - 1 := by linarith

  have h_eq : noiseOp ρ g = f := by
    rw [hg_def, noiseOp_comp]
    have h_prod : ρ * Real.sqrt (q - 1) = 1 := by
      rw [hρ_def]; field_simp
    rw [h_prod, noiseOp_one]

  have hρ_nonneg : 0 ≤ ρ := by rw [hρ_def]; positivity
  have hρ_bound : ρ ≤ Real.sqrt ((2 - 1) / (q - 1)) := by
    rw [hρ_def]
    simp only [show (2 : ℝ) - 1 = 1 from by norm_num]
    rw [one_div]
    rw [show (1 : ℝ) / (q - 1) = (q - 1)⁻¹ from one_div _]
    rw [Real.sqrt_inv]
  have h_bb_applied : lpNorm q f ≤ lpNorm 2 g := by
    rw [← h_eq]; exact h_bb g ρ hρ_nonneg hρ_bound


  suffices h_norm_bound : lpNorm 2 g ≤ (q - 1) ^ ((k : ℝ) / 2) * lpNorm 2 f from
    le_trans h_bb_applied h_norm_bound


  have hg_l2_sq : ∑ S : Finset (Fin n), (fourierCoeff g S) ^ 2 =
      ∑ S : Finset (Fin n), (q - 1) ^ S.card * (fourierCoeff f S) ^ 2 := by
    rw [hg_def, noiseOp_l2_norm_sq]
    congr 1; ext S
    congr 1
    rw [show 2 * S.card = S.card + S.card from by ring, pow_add]
    rw [show Real.sqrt (q - 1) ^ S.card * Real.sqrt (q - 1) ^ S.card =
      (Real.sqrt (q - 1) * Real.sqrt (q - 1)) ^ S.card from by
        rw [← mul_pow]]
    rw [Real.mul_self_sqrt (le_of_lt hq1_pos)]

  have h_sq_bound : ∑ S : Finset (Fin n), (fourierCoeff g S) ^ 2 ≤
      (q - 1) ^ k * ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 := by
    rw [hg_l2_sq]
    exact sum_pow_card_mul_fourierCoeff_sq_le f k (q - 1) (by linarith) hdeg


  have h_lpNorm2_eq : ∀ h : BoolFn n,
      lpNorm 2 h = (∑ S : Finset (Fin n), (fourierCoeff h S) ^ 2) ^ ((1 : ℝ) / 2) := by
    intro h
    unfold lpNorm
    congr 1
    have h_abs_sq : ∀ y : Fin n → Bool, |h y| ^ (2 : ℝ) = (h y) ^ 2 := by
      intro y
      rw [show (2 : ℝ) = (↑(2 : ℕ) : ℝ) from by norm_num, rpow_natCast]
      exact sq_abs (h y)
    simp_rw [h_abs_sq]
    exact (parseval h).symm
  rw [h_lpNorm2_eq g, h_lpNorm2_eq f]

  have hf_sum_nonneg : (0 : ℝ) ≤ ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 :=
    Finset.sum_nonneg (fun S _ => sq_nonneg _)
  have hg_sum_nonneg : (0 : ℝ) ≤ ∑ S : Finset (Fin n), (fourierCoeff g S) ^ 2 :=
    Finset.sum_nonneg (fun S _ => sq_nonneg _)

  have hq1_nonneg : (0 : ℝ) ≤ q - 1 := le_of_lt hq1_pos
  rw [show (q - 1) ^ ((k : ℝ) / 2) = ((q - 1) ^ k) ^ ((1 : ℝ) / 2) from by
    rw [← rpow_natCast (q - 1) k, ← rpow_mul hq1_nonneg]
    congr 1; ring]
  rw [show ((q - 1) ^ k) ^ ((1 : ℝ) / 2) *
    (∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2) ^ ((1 : ℝ) / 2) =
    ((q - 1) ^ k * ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2) ^ ((1 : ℝ) / 2) from by
    rw [← mul_rpow (by positivity : (0 : ℝ) ≤ (q - 1) ^ k) hf_sum_nonneg]]
  exact rpow_le_rpow hg_sum_nonneg h_sq_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem fourierCoeff_noiseOp {n : ℕ} (ρ : ℝ) (f : BoolFn n) (S : Finset (Fin n)) :
    fourierCoeff (noiseOp ρ f) S = ρ ^ S.card * fourierCoeff f S :=
  noiseOp_fourierCoeff ρ f S

noncomputable def combineAssignment {n : ℕ} (J : Finset (Fin n))
    (xJ : ↥J → Bool) (z : ↥(Jᶜ) → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ J then xJ ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩

noncomputable def restrictToSubset {n : ℕ} (J : Finset (Fin n))
    (f : BoolFn n) (z : ↥(Jᶜ) → Bool) : (↥J → Bool) → ℝ :=
  fun xJ => f (combineAssignment J xJ z)

noncomputable def chiOn {n : ℕ} (J : Finset (Fin n)) (S : Finset ↥J)
    (x : ↥J → Bool) : ℝ :=
  ∏ i ∈ S, boolToReal (x i)

noncomputable def fourierCoeffOn {n : ℕ} (J : Finset (Fin n))
    (g : (↥J → Bool) → ℝ) (S : Finset ↥J) : ℝ :=
  (1 / (2 : ℝ) ^ J.card) * ∑ x : ↥J → Bool, g x * chiOn J S x

lemma subtype_map_union_left {n : ℕ} (J : Finset (Fin n))
    (S : Finset ↥J) (T : Finset ↥(Jᶜ)) :
    (S.map (Function.Embedding.subtype _) ∪
      T.map (Function.Embedding.subtype _)).subtype (· ∈ J) = S := by
  ext ⟨i, hi⟩
  simp only [Finset.mem_subtype, Finset.mem_union, Finset.mem_map,
    Function.Embedding.subtype_apply, Subtype.exists]
  constructor
  · rintro (⟨j, hj, hjS, rfl⟩ | ⟨j, hj, hjT, rfl⟩)
    · exact hjS
    · exact absurd hi (Finset.mem_compl.mp hj)
  · intro h
    left; exact ⟨i, hi, h, rfl⟩

lemma subtype_map_union_right {n : ℕ} (J : Finset (Fin n))
    (S : Finset ↥J) (T : Finset ↥(Jᶜ)) :
    (S.map (Function.Embedding.subtype _) ∪
      T.map (Function.Embedding.subtype _)).subtype (· ∈ Jᶜ) = T := by
  ext ⟨i, hi⟩
  simp only [Finset.mem_subtype, Finset.mem_union, Finset.mem_map,
    Function.Embedding.subtype_apply, Subtype.exists]
  constructor
  · rintro (⟨j, hj, hjS, rfl⟩ | ⟨j, hj, hjT, rfl⟩)
    · have : j ∈ Jᶜ := hi
      exact absurd hj (Finset.mem_compl.mp this)
    · exact hjT
  · intro h
    right; exact ⟨i, hi, h, rfl⟩

lemma finset_subtype_map_union {n : ℕ} (J : Finset (Fin n)) (U : Finset (Fin n)) :
    U = (U.subtype (· ∈ J)).map (Function.Embedding.subtype _) ∪
        (U.subtype (· ∈ Jᶜ)).map (Function.Embedding.subtype _) := by
  rw [Finset.subtype_map, Finset.subtype_map]
  have h : Finset.filter (· ∈ Jᶜ) U = Finset.filter (fun x => ¬ (x ∈ J)) U := by
    ext i; simp [Finset.mem_compl]
  rw [h]
  exact (Finset.filter_union_filter_not_eq (· ∈ J) U).symm

lemma chi_combineAssignment_eq {n : ℕ} (J : Finset (Fin n))
    (U : Finset (Fin n)) (xJ : ↥J → Bool) (z : ↥(Jᶜ) → Bool) :
    chi U (combineAssignment J xJ z) =
      chiOn J (U.subtype (· ∈ J)) xJ * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z := by
  simp only [chi, chiOn, combineAssignment]
  rw [← Finset.prod_filter_mul_prod_filter_not U (· ∈ J)]
  congr 1
  · rw [← Finset.subtype_map (· ∈ J) (s := U), Finset.prod_map]
    congr 1; ext ⟨i, hi⟩; simp [hi]
  · have hfilt : Finset.filter (fun x => ¬ x ∈ J) U = Finset.filter (· ∈ Jᶜ) U := by
      ext i; simp [Finset.mem_compl]
    rw [hfilt, ← Finset.subtype_map (· ∈ Jᶜ) (s := U), Finset.prod_map]
    congr 1; ext ⟨i, hi⟩
    have hi' : ¬ (i ∈ J) := Finset.mem_compl.mp hi
    simp [hi']

lemma sum_chiOn_mul_chiOn {n : ℕ} (J : Finset (Fin n)) (S T : Finset ↥J) :
    ∑ x : ↥J → Bool, chiOn J S x * chiOn J T x =
      if S = T then (2 : ℝ) ^ J.card else 0 := by
  split_ifs with h
  · subst h
    simp only [chiOn]
    conv_lhs =>
      arg 2; ext x
      rw [show (∏ i ∈ S, boolToReal (x i)) * (∏ i ∈ S, boolToReal (x i)) =
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (x i)) from
        (Finset.prod_mul_distrib).symm]
    simp only [boolToReal_mul_self, Finset.prod_const_one]
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  · obtain ⟨j, hj⟩ := Finset.symmDiff_nonempty.mpr h
    have hjmem := Finset.mem_symmDiff.mp hj
    apply Finset.sum_ninvolution (g := fun x => Function.update x j (!x j))
    · intro x
      have hflip_mem : ∀ (A : Finset ↥J), j ∈ A →
          chiOn J A (Function.update x j (!x j)) = -chiOn J A x := by
        intro A hjA
        simp only [chiOn]
        have h1 : ∏ i ∈ A, boolToReal (Function.update x j (!x j) i) =
            boolToReal (!x j) * ∏ i ∈ A.erase j, boolToReal (x i) := by
          rw [← Finset.mul_prod_erase A _ hjA]
          congr 1
          · simp [Function.update]
          · apply Finset.prod_congr rfl
            intro i hi
            have hne : i ≠ j := (Finset.mem_erase.mp hi).1
            simp [Function.update, hne]
        rw [h1, ← Finset.mul_prod_erase A _ hjA, boolToReal_not]
        ring
      have hflip_not_mem : ∀ (A : Finset ↥J), j ∉ A →
          chiOn J A (Function.update x j (!x j)) = chiOn J A x := by
        intro A hjA
        simp only [chiOn]
        apply Finset.prod_congr rfl
        intro i hi
        have hne : i ≠ j := ne_of_mem_of_not_mem hi hjA
        simp [Function.update, hne]
      rcases hjmem with ⟨hjS, hjT⟩ | ⟨hjT, hjS⟩
      · rw [hflip_mem S hjS, hflip_not_mem T hjT]; ring
      · rw [hflip_not_mem S hjS, hflip_mem T hjT]; ring
    · intro x _
      intro heq
      have : Function.update x j (!x j) j = x j := congr_fun heq j
      simp [Function.update] at this
    · intro x; exact Finset.mem_univ _
    · intro x
      ext i
      by_cases hij : i = j
      · subst hij; simp [Function.update, Bool.not_not]
      · simp [Function.update, hij]

theorem fourierCoeff_restrictToSubset {n : ℕ} (J : Finset (Fin n))
    (f : BoolFn n) (z : ↥(Jᶜ) → Bool) (S : Finset ↥J) :
    fourierCoeffOn J (restrictToSubset J f z) S =
      ∑ T : Finset ↥(Jᶜ),
        fourierCoeff f (S.map (Function.Embedding.subtype _) ∪
          T.map (Function.Embedding.subtype _)) *
        chiOn Jᶜ T z := by
  classical
  have h2J : (2 : ℝ) ^ J.card ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)
  simp only [fourierCoeffOn, restrictToSubset]
  conv_lhs =>
    arg 2; arg 2; ext xJ
    rw [show f (combineAssignment J xJ z) =
      ∑ U : Finset (Fin n), fourierCoeff f U * chi U (combineAssignment J xJ z)
      from fourier_expansion f (combineAssignment J xJ z)]
  simp_rw [chi_combineAssignment_eq J]
  conv_lhs =>
    arg 2; arg 2; ext xJ
    rw [show (∑ U : Finset (Fin n), fourierCoeff f U *
        (chiOn J (U.subtype (· ∈ J)) xJ * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z)) *
        chiOn J S xJ =
      ∑ U : Finset (Fin n), fourierCoeff f U * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z *
        (chiOn J (U.subtype (· ∈ J)) xJ * chiOn J S xJ) from by
      rw [Finset.sum_mul]; congr 1; ext U; ring]
  rw [show (1 / (2 : ℝ) ^ J.card) * ∑ xJ : ↥J → Bool,
      ∑ U : Finset (Fin n), fourierCoeff f U * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z *
        (chiOn J (U.subtype (· ∈ J)) xJ * chiOn J S xJ) =
    (1 / (2 : ℝ) ^ J.card) * ∑ U : Finset (Fin n),
      fourierCoeff f U * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z *
        ∑ xJ : ↥J → Bool, chiOn J (U.subtype (· ∈ J)) xJ * chiOn J S xJ from by
    congr 1; rw [Finset.sum_comm]; congr 1; ext U; rw [← Finset.mul_sum]]
  simp_rw [sum_chiOn_mul_chiOn J]
  simp only [mul_ite, mul_zero]
  conv_lhs =>
    arg 2; arg 2; ext U
    rw [show (if Finset.subtype (· ∈ J) U = S then
        fourierCoeff f U * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z * (2 : ℝ) ^ J.card
      else 0) = (2 : ℝ) ^ J.card * (if Finset.subtype (· ∈ J) U = S then
        fourierCoeff f U * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z
      else 0) from by split_ifs <;> ring]
  rw [← Finset.mul_sum, show (1 / (2 : ℝ) ^ J.card) * ((2 : ℝ) ^ J.card *
    ∑ U : Finset (Fin n), (if Finset.subtype (· ∈ J) U = S then
      fourierCoeff f U * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z else 0)) =
    ∑ U : Finset (Fin n), (if Finset.subtype (· ∈ J) U = S then
      fourierCoeff f U * chiOn Jᶜ (U.subtype (· ∈ Jᶜ)) z else 0) from by
    field_simp]

  symm
  rw [← Finset.sum_filter (s := Finset.univ) (p := fun U => Finset.subtype (· ∈ J) U = S)]
  apply Finset.sum_nbij
    (fun T => S.map (Function.Embedding.subtype _) ∪
      T.map (Function.Embedding.subtype _))
  · intro T _

    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, subtype_map_union_left J S T⟩
  · intro T₁ hT₁ T₂ hT₂ hTT
    have h' := congr_arg (Finset.subtype (· ∈ Jᶜ)) hTT
    rw [subtype_map_union_right J S T₁, subtype_map_union_right J S T₂] at h'
    exact h'
  · intro U hU
    have hUS : Finset.subtype (· ∈ J) U = S := (Finset.mem_filter.mp hU).2
    refine ⟨Finset.subtype (· ∈ Jᶜ) U, Finset.mem_univ _, ?_⟩
    show S.map _ ∪ (Finset.subtype (· ∈ Jᶜ) U).map _ = U
    rw [← hUS, ← finset_subtype_map_union J U]
  · intro T _
    congr 1
    rw [subtype_map_union_right J S T]

end BooleanFourier
