/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.Roots
import Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation

open Finset BigOperators

namespace CoxeterGroup

set_option linter.unusedSectionVars false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Support stability for $\sigma_r$ along $\{s, t\}$: if $r \in \{s, t\}$ and
$v$ is supported in $\{s, t\}$, then $\sigma_r(v)$ is also supported in
$\{s, t\}$. -/
theorem sigma_support_two (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) (r : B)
    (hr : r = s ∨ r = t) (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    ∀ u, u ≠ s → u ≠ t → sigma M r v u = 0 := by
  intro u hus hut
  have hru : r ≠ u := by
    rcases hr with rfl | rfl <;> [exact Ne.symm hus; exact Ne.symm hut]
  rw [sigma_coord_ne M r v u (Ne.symm hru)]
  exact hsupp u hus hut

/-- Iterated version of $\mathtt{sigma\_support\_two}$: support in $\{s, t\}$
is preserved under $\mathtt{wordSigma}$ for any word in the alphabet
$\{s, t\}$. -/
theorem wordSigma_support_two (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (word : List B) (halt : ∀ b ∈ word, b = s ∨ b = t) (v : B → ℝ)
    (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    ∀ u, u ≠ s → u ≠ t → wordSigma M word v u = 0 := by
  induction word with
  | nil => exact fun u hus hut => hsupp u hus hut
  | cons r rest ih =>
    intro u hus hut
    simp only [wordSigma]
    have hr : r = s ∨ r = t := halt r (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ b ∈ rest, b = s ∨ b = t :=
      fun b hb => halt b (List.mem_cons.mpr (Or.inr hb))
    exact sigma_support_two M s t hst r hr (wordSigma M rest v) (ih hrest) u hus hut

/-- The simple root $e_s$ is supported in $\{s, t\}$ (vacuously on
coordinates outside this pair). -/
theorem e_supported_two (s t : B) : ∀ u, u ≠ s → u ≠ t → (e s) u = 0 := by
  intro u hus _
  simp [e, hus]

/-- If $v$ is a positive root supported in $\{s, t\}$ with $v_t = 0$, then
$\sigma_t(v)$ is still positive (the $t$-coefficient becomes
$-2 v_s\, B_{s,t} \ge 0$). -/
theorem sigma_t_pos_of_t_zero (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hpos : IsPositive v) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
    (hvt : v t = 0) : IsPositive (sigma M t v) := by
  intro u
  by_cases hut : u = t
  ·
    rw [hut, sigma_coord_self]
    suffices h : bilinForm M v (e t) ≤ 0 by linarith [hvt]
    simp only [bilinForm, e, Pi.single_apply]
    simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    apply Finset.sum_nonpos
    intro r _
    by_cases hrt : r = t
    · simp [hrt, hvt]
    · by_cases hrs : r = s
      · rw [hrs]
        exact mul_nonpos_of_nonneg_of_nonpos (hpos s) (formVal_nonpos_of_ne M s t hst)
      · rw [hsupp r hrs hrt, zero_mul]
  · by_cases hus : u = s
    · rw [hus, sigma_coord_ne M t v s hst]
      exact hpos s
    · rw [sigma_support_two M s t hst t (Or.inr rfl) v hsupp u hus hut]

/-- Symmetric statement to $\mathtt{sigma\_t\_pos\_of\_t\_zero}$: if
$v_s = 0$, then $\sigma_s(v)$ remains positive. -/
theorem sigma_s_pos_of_s_zero (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hpos : IsPositive v) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
    (hvs : v s = 0) : IsPositive (sigma M s v) := by
  intro u
  by_cases hus : u = s
  · rw [hus, sigma_coord_self]
    suffices h : bilinForm M v (e s) ≤ 0 by linarith [hvs]
    simp only [bilinForm, e, Pi.single_apply]
    simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    apply Finset.sum_nonpos
    intro r _
    by_cases hrs : r = s
    · simp [hrs, hvs]
    · by_cases hrt : r = t
      · rw [hrt]
        exact mul_nonpos_of_nonneg_of_nonpos (hpos t)
          (formVal_nonpos_of_ne M t s (Ne.symm hst))
      · rw [hsupp r hrs hrt, zero_mul]
  · by_cases hut : u = t
    · rw [hut, sigma_coord_ne M s v t (Ne.symm hst)]
      exact hpos t
    · rw [sigma_support_two M s t hst s (Or.inl rfl) v hsupp u hus hut]

/-- For off-diagonal $s \ne t$ with $m(s, t) \ne 2$ (so $m(s, t) \ge 3$ or
$\infty$), the form value satisfies $\mathtt{formVal}\,M\,s\,t \le -1/2$,
since $\cos(\pi/3) = 1/2$. -/
theorem formVal_le_neg_half (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t ≠ 2) : formVal M s t ≤ -1/2 := by
  unfold formVal
  split
  · linarith
  · rename_i hm0
    have hm1 : M s t ≠ 1 := M.off_diagonal s t hst
    have hm_ge_3 : (M s t : ℕ) ≥ 3 := by omega
    have hm3 : (3 : ℝ) ≤ (M s t : ℝ) := by exact_mod_cast hm_ge_3
    have hm_pos : (0 : ℝ) < (M s t : ℝ) := by linarith
    have hle : Real.pi / (M s t : ℝ) ≤ Real.pi / 3 := by
      apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity) hm3
    have hge : (0 : ℝ) ≤ Real.pi / (M s t : ℝ) := by positivity
    have hpi : Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
    have hcos : Real.cos (Real.pi / (M s t : ℝ)) ≥ 1/2 := by
      rw [ge_iff_le, ← Real.cos_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hge hpi hle
    linarith

/-- Positivity at length two: when $m(s, t) \ne 2$,
$\mathtt{wordSigma}\,M\,[s, t]\,(e_s)$ is still a positive root. -/
theorem dihedral_pos_len2 (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t ≠ 2) :
    IsPositive (wordSigma M [s, t] (e s)) := by
  simp only [wordSigma]
  set v := sigma M t (e s)
  have hv_pos : IsPositive v := sigmaLin_preserves_positive_off_diagonal M t s (Ne.symm hst)
  have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
    sigma_support_two M s t hst t (Or.inr rfl) (e s) (e_supported_two s t)
  intro u
  by_cases hus : u = s
  · rw [hus, sigma_coord_self]
    have hvs : v s = 1 := by
      show sigma M t (e s) s = 1
      rw [sigma_coord_ne M t (e s) s hst]
      simp [e]
    have hbilin : bilinForm M v (e s) = 1 - 2 * formVal M s t * formVal M t s := by
      show bilinForm M (sigma M t (e s)) (e s) = _
      rw [bilinForm_sigma_general M s t (e s), bilinForm_e_e, bilinForm_e_e, formVal_diag]
    rw [hvs, hbilin, formVal_symm M t s]
    have hfv := formVal_le_neg_half M s t hst hm
    nlinarith
  · by_cases hut : u = t
    · rw [hut, sigma_coord_ne M s v t (Ne.symm hst)]
      exact hv_pos t
    · rw [sigma_support_two M s t hst s (Or.inl rfl) v hv_supp u hus hut]

/-- Closed form for $B(v, e_t)$ when $v$ is supported in $\{s, t\}$:
$B(v, e_t) = v_s\, B_{s, t} + v_t$. -/
theorem bilinForm_e_t_of_supported (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    bilinForm M v (e t) = v s * formVal M s t + v t := by
  simp only [bilinForm, e, Pi.single_apply]
  simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]

  have htail : ∀ r : B, r ≠ s → r ≠ t → v r * formVal M r t = 0 := by
    intro r hrs hrt; rw [hsupp r hrs hrt, zero_mul]
  have key : ∑ r : B, v r * formVal M r t =
      v s * formVal M s t + v t * formVal M t t := by
    have := Finset.sum_subset (Finset.subset_univ ({s, t} : Finset B))
      (fun r _ hr => by
        simp [Finset.mem_insert, Finset.mem_singleton] at hr
        push_neg at hr
        exact htail r hr.1 hr.2)
    rw [← this]
    simp [Finset.sum_pair hst]
  rw [key, formVal_diag, mul_one]

/-- Closed form for $B(v, e_s)$ when $v$ is supported in $\{s, t\}$:
$B(v, e_s) = v_s + v_t\, B_{t, s}$. -/
theorem bilinForm_e_s_of_supported (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    bilinForm M v (e s) = v s + v t * formVal M t s := by
  simp only [bilinForm, e, Pi.single_apply]
  simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have htail : ∀ r : B, r ≠ s → r ≠ t → v r * formVal M r s = 0 := by
    intro r hrs hrt; rw [hsupp r hrs hrt, zero_mul]
  have key : ∑ r : B, v r * formVal M r s =
      v s * formVal M s s + v t * formVal M t s := by
    have := Finset.sum_subset (Finset.subset_univ ({s, t} : Finset B))
      (fun r _ hr => by
        simp [Finset.mem_insert, Finset.mem_singleton] at hr
        push_neg at hr
        exact htail r hr.1 hr.2)
    rw [← this]
    simp [Finset.sum_pair hst]
  rw [key, formVal_diag, mul_one]

/-- $t$-coordinate of $\sigma_t(v)$ when $v$ is supported in $\{s, t\}$:
$(\sigma_t v)_t = -v_t - 2 v_s\, B_{s, t}$. -/
theorem sigma_t_coord_t_of_supported (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    sigma M t v t = -v t - 2 * v s * formVal M s t := by
  rw [sigma_coord_self, bilinForm_e_t_of_supported M s t hst v hsupp]
  ring

/-- $s$-coordinate of $\sigma_s(v)$ when $v$ is supported in $\{s, t\}$:
$(\sigma_s v)_s = -v_s - 2 v_t\, B_{t, s}$. -/
theorem sigma_s_coord_s_of_supported (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
    sigma M s v s = -v s - 2 * v t * formVal M t s := by
  rw [sigma_coord_self, bilinForm_e_s_of_supported M s t hst v hsupp]
  ring

/-- General positivity criterion for $\sigma_t(v)$: a positive root supported
in $\{s, t\}$ remains positive under $\sigma_t$ provided
$v_t \le -2 v_s\, B_{s, t}$. -/
theorem sigma_t_pos_general (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hpos : IsPositive v) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
    (hineq : v t ≤ -2 * v s * formVal M s t) :
    IsPositive (sigma M t v) := by
  intro u
  by_cases hut : u = t
  · rw [hut, sigma_t_coord_t_of_supported M s t hst v hsupp]
    linarith
  · by_cases hus : u = s
    · rw [hus, sigma_coord_ne M t v s hst]
      exact hpos s
    · rw [sigma_support_two M s t hst t (Or.inr rfl) v hsupp u hus hut]

/-- General positivity criterion for $\sigma_s(v)$ symmetric to the previous
lemma: a positive root supported in $\{s, t\}$ remains positive under
$\sigma_s$ when $v_s \le -2 v_t\, B_{t, s}$. -/
theorem sigma_s_pos_general (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (v : B → ℝ) (hpos : IsPositive v) (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0)
    (hineq : v s ≤ -2 * v t * formVal M t s) :
    IsPositive (sigma M s v) := by
  intro u
  by_cases hus : u = s
  · rw [hus, sigma_s_coord_s_of_supported M s t hst v hsupp]
    linarith
  · by_cases hut : u = t
    · rw [hut, sigma_coord_ne M s v t (Ne.symm hst)]
      exact hpos t
    · rw [sigma_support_two M s t hst s (Or.inl rfl) v hsupp u hus hut]

/-- Infinite-order convention: if $m(s, t) = 0$ (interpreted as $\infty$),
then $\mathtt{formVal}\,M\,s\,t = -1$. -/
theorem formVal_eq_neg_one_of_zero (M : CoxeterMatrix B) (s t : B)
    (hm : M s t = 0) : formVal M s t = -1 := by
  unfold formVal; rw [hm]; simp

/-- Even-length alternating word $s\,t\,s\,t\,\cdots$ of length $2n$ starting
with $s$, defined recursively. -/
def altWordEven (s t : B) : ℕ → List B
  | 0 => []
  | n + 1 => s :: t :: altWordEven s t n

/-- Every letter of $\mathtt{altWordEven}\,s\,t\,n$ is either $s$ or $t$. -/
theorem altWordEven_mem (s t : B) (n : ℕ) :
    ∀ b ∈ altWordEven s t n, b = s ∨ b = t := by
  induction n with
  | zero => simp [altWordEven]
  | succ k ih =>
    intro b hb
    simp [altWordEven] at hb
    rcases hb with rfl | rfl | hb
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact ih b hb

/-- $\mathtt{altWordEven}\,s\,t\,n$ has length exactly $2n$. -/
theorem altWordEven_length (s t : B) (n : ℕ) :
    (altWordEven s t n).length = 2 * n := by
  induction n with
  | zero => simp [altWordEven]
  | succ k ih => simp [altWordEven, ih]; ring

/-- Affine (infinite-order) closed forms for the dihedral iterate of $e_s$
along an even-length alternating word: the $s$-coordinate is $1 + 2n$ and
the $t$-coordinate is $2n$, reflecting the unipotent action when
$m(s, t) = \infty$. -/
theorem dihedral_coords_even_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    wordSigma M (altWordEven s t n) (e s) s = 1 + 2 * (n : ℝ) ∧
    wordSigma M (altWordEven s t n) (e s) t = 2 * (n : ℝ) := by
  have hfv : formVal M s t = -1 := formVal_eq_neg_one_of_zero M s t hm
  have hfvts : formVal M t s = -1 := by rw [formVal_symm]; exact hfv
  induction n with
  | zero =>
    simp [altWordEven, e, hst]
  | succ k ih =>
    simp only [altWordEven, wordSigma]
    set v := wordSigma M (altWordEven s t k) (e s)
    have hvs : v s = 1 + 2 * (k : ℝ) := ih.1
    have hvt : v t = 2 * (k : ℝ) := ih.2
    have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
      wordSigma_support_two M s t hst (altWordEven s t k)
        (altWordEven_mem s t k) (e s) (e_supported_two s t)

    set w := sigma M t v
    have hws : w s = v s := sigma_coord_ne M t v s hst
    have hwt : w t = -v t - 2 * v s * formVal M s t :=
      sigma_t_coord_t_of_supported M s t hst v hv_supp
    have hw_supp : ∀ u, u ≠ s → u ≠ t → w u = 0 :=
      sigma_support_two M s t hst t (Or.inr rfl) v hv_supp

    have hrs : sigma M s w s = -w s - 2 * w t * formVal M t s :=
      sigma_s_coord_s_of_supported M s t hst w hw_supp
    have hrt : sigma M s w t = w t := sigma_coord_ne M s w t (Ne.symm hst)
    constructor
    ·
      rw [hrs, hws, hwt, hvs, hvt, hfv, hfvts]
      push_cast; ring
    ·
      rw [hrt, hwt, hvs, hvt, hfv]
      push_cast; ring

/-- Odd-length analogue for $m(s, t) = \infty$: the $s$-coordinate stays
$1 + 2n$ while the $t$-coordinate becomes $2n + 2$. -/
theorem dihedral_coords_odd_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    wordSigma M (t :: altWordEven s t n) (e s) s = 1 + 2 * (n : ℝ) ∧
    wordSigma M (t :: altWordEven s t n) (e s) t = 2 * (n : ℝ) + 2 := by
  have hfv : formVal M s t = -1 := formVal_eq_neg_one_of_zero M s t hm
  simp only [wordSigma]
  set v := wordSigma M (altWordEven s t n) (e s)
  have ⟨hvs, hvt⟩ := dihedral_coords_even_infinite M s t hst hm n
  have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
    wordSigma_support_two M s t hst (altWordEven s t n)
      (altWordEven_mem s t n) (e s) (e_supported_two s t)
  constructor
  ·
    have : sigma M t v s = v s := sigma_coord_ne M t v s hst
    rw [this]; exact hvs
  ·
    have : sigma M t v t = -v t - 2 * v s * formVal M s t :=
      sigma_t_coord_t_of_supported M s t hst v hv_supp
    rw [this, show v s = 1 + 2 * (n : ℝ) from hvs, show v t = 2 * (n : ℝ) from hvt, hfv]
    ring

/-- In the infinite-order case $m(s, t) = 0$, the even-length alternating
iterate of $e_s$ is unconditionally positive. -/
theorem dihedral_pos_even_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    IsPositive (wordSigma M (altWordEven s t n) (e s)) := by
  have ⟨hvs, hvt⟩ := dihedral_coords_even_infinite M s t hst hm n
  intro u
  by_cases hus : u = s
  · rw [hus, hvs]; positivity
  · by_cases hut : u = t
    · rw [hut, hvt]; positivity
    · rw [wordSigma_support_two M s t hst (altWordEven s t n)
        (altWordEven_mem s t n) (e s) (e_supported_two s t) u hus hut]

/-- Odd-length analogue: in the infinite-order case the iterate
$\mathtt{wordSigma}\,M\,(t :: \text{altWord})\,(e_s)$ is also unconditionally
positive. -/
theorem dihedral_pos_odd_infinite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t = 0) (n : ℕ) :
    IsPositive (wordSigma M (t :: altWordEven s t n) (e s)) := by
  have ⟨hvs, hvt⟩ := dihedral_coords_odd_infinite M s t hst hm n
  intro u
  by_cases hus : u = s
  · rw [hus, hvs]; positivity
  · by_cases hut : u = t
    · rw [hut, hvt]; positivity
    · have hmem : ∀ b ∈ t :: altWordEven s t n, b = s ∨ b = t := by
        intro b hb
        simp at hb
        rcases hb with rfl | hb
        · exact Or.inr rfl
        · exact altWordEven_mem s t n b hb
      rw [wordSigma_support_two M s t hst (t :: altWordEven s t n)
        hmem (e s) (e_supported_two s t) u hus hut]

/-- Sharper bound on the form value: if $m(s, t)$ is either $\infty$ or
$\ge 4$, then $\mathtt{formVal}\,M\,s\,t \le -\sqrt{2}/2$, the value
$-\cos(\pi/4)$. -/
theorem formVal_le_neg_sqrt2_div2 (M : CoxeterMatrix B) (s t : B) (_hst : s ≠ t)
    (hm : M s t = 0 ∨ M s t ≥ 4) : formVal M s t ≤ -(Real.sqrt 2 / 2) := by
  rcases hm with hm0 | hm4
  · rw [formVal_eq_neg_one_of_zero M s t hm0]
    have : Real.sqrt 2 / 2 ≤ 1 := by
      have h2 : Real.sqrt 2 ≤ 2 := by
        have := Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
        nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 2)]
      linarith

    linarith
  · unfold formVal
    split
    ·
      omega
    · rename_i hm0
      have hm_ge_4 : (4 : ℝ) ≤ (M s t : ℝ) := by exact_mod_cast hm4
      have hm_pos : (0 : ℝ) < (M s t : ℝ) := by linarith
      have hle : Real.pi / (M s t : ℝ) ≤ Real.pi / 4 := by
        apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity) hm_ge_4
      have hge : (0 : ℝ) ≤ Real.pi / (M s t : ℝ) := by positivity
      have hpi : Real.pi / 4 ≤ Real.pi := by linarith [Real.pi_pos]
      have hcos : Real.cos (Real.pi / (M s t : ℝ)) ≥ Real.sqrt 2 / 2 := by
        rw [ge_iff_le, ← Real.cos_pi_div_four]
        exact Real.cos_le_cos_of_nonneg_of_le_pi hge hpi hle
      linarith

end CoxeterGroup
