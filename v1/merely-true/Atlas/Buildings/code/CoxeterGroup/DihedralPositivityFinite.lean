/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.DihedralPositivity

open Finset BigOperators

namespace CoxeterGroup

set_option linter.unusedSectionVars false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Chebyshev-type recurrence for $\sin$:
$\sin((n + 2) \theta) = 2 \cos\theta \sin((n + 1)\theta) - \sin(n\theta)$,
the standard three-term linear recurrence satisfied by
$U_n(\cos\theta) = \sin((n+1)\theta)/\sin\theta$. -/
theorem sin_chebyshev_recurrence (θ : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) + 2) * θ) =
      2 * Real.cos θ * Real.sin (((n : ℝ) + 1) * θ) - Real.sin ((n : ℝ) * θ) := by
  have h1 : ((n : ℝ) + 2) * θ = ((n : ℝ) + 1) * θ + θ := by ring
  have h2 : (n : ℝ) * θ = ((n : ℝ) + 1) * θ - θ := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-- For $m(s, t) \ne 0$ the bilinear form value is the negative cosine
$\mathtt{formVal}\,M\,s\,t = -\cos(\pi / m(s, t))$. -/
theorem formVal_eq_neg_cos (M : CoxeterMatrix B) (s t : B) (hm : M s t ≠ 0) :
    formVal M s t = -Real.cos (Real.pi / (M s t : ℝ)) := by
  unfold formVal; simp [hm]

/-- Closed-form formulas for the $s$- and $t$-coordinates of the dihedral
iterate $\mathtt{wordSigma}$ of $e_s$ along an even-length alternating word
when $m(s, t)$ is finite. Both coordinates are ratios of sines built from
$\theta = \pi / m(s, t)$. -/
theorem dihedral_coords_even_finite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t ≠ 0) (k : ℕ) :
    let θ := Real.pi / (M s t : ℝ)
    wordSigma M (altWordEven s t k) (e s) s =
      Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ ∧
    wordSigma M (altWordEven s t k) (e s) t =
      Real.sin (2 * (k : ℝ) * θ) / Real.sin θ := by
  intro θ
  have hm1 : M s t ≠ 1 := M.off_diagonal s t hst
  have hm_ge2 : (M s t : ℕ) ≥ 2 := by omega
  have hm_pos : (0 : ℝ) < (M s t : ℝ) := by exact_mod_cast (show 0 < M s t by omega)
  have hθ_pos : θ > 0 := div_pos Real.pi_pos hm_pos
  have hθ_lt_pi : θ < Real.pi := div_lt_self Real.pi_pos (by exact_mod_cast hm_ge2)
  have hsin_pos : Real.sin θ > 0 := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have hfv : formVal M s t = -Real.cos θ := formVal_eq_neg_cos M s t hm
  have hfvts : formVal M t s = -Real.cos θ := by rw [formVal_symm]; exact hfv
  induction k with
  | zero =>
    simp only [altWordEven, wordSigma, Nat.cast_zero, mul_zero,
               zero_add, one_mul]
    constructor
    · simp [e, div_self hsin_pos.ne']
    · simp [e, hst]
  | succ n ih =>
    obtain ⟨ih_s, ih_t⟩ := ih
    simp only [altWordEven, wordSigma]
    set v := wordSigma M (altWordEven s t n) (e s)
    have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
      wordSigma_support_two M s t hst (altWordEven s t n)
        (altWordEven_mem s t n) (e s) (e_supported_two s t)

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
      rw [hrs, hws, hwt, ih_s, ih_t, hfv, hfvts]
      have hrec1 : Real.sin ((2 * (n : ℝ) + 2) * θ) =
          2 * Real.cos θ * Real.sin ((2 * (n : ℝ) + 1) * θ) - Real.sin (2 * (n : ℝ) * θ) := by
        have := sin_chebyshev_recurrence θ (2 * n)
        convert this using 2 <;> push_cast <;> ring
      have hrec2 : Real.sin ((2 * (n : ℝ) + 3) * θ) =
          2 * Real.cos θ * Real.sin ((2 * (n : ℝ) + 2) * θ) -
            Real.sin ((2 * (n : ℝ) + 1) * θ) := by
        have := sin_chebyshev_recurrence θ (2 * n + 1)
        convert this using 2 <;> push_cast <;> ring
      have hgoal : Real.sin ((2 * (↑(n + 1) : ℝ) + 1) * θ) = Real.sin ((2 * (n : ℝ) + 3) * θ) := by
        congr 1; push_cast; ring
      rw [hgoal, hrec2, hrec1]
      field_simp
      ring
    ·
      rw [hrt, hwt, ih_s, ih_t, hfv]
      have hrec : Real.sin ((2 * (n : ℝ) + 2) * θ) =
          2 * Real.cos θ * Real.sin ((2 * (n : ℝ) + 1) * θ) - Real.sin (2 * (n : ℝ) * θ) := by
        have := sin_chebyshev_recurrence θ (2 * n)
        convert this using 2 <;> push_cast <;> ring
      have hgoal : Real.sin (2 * (↑(n + 1) : ℝ) * θ) = Real.sin ((2 * (n : ℝ) + 2) * θ) := by
        congr 1; push_cast; ring
      rw [hgoal, hrec]
      field_simp
      ring

/-- Odd-length analogue of $\mathtt{dihedral\_coords\_even\_finite}$: closed
forms for the coordinates of $\mathtt{wordSigma}\,(t :: \text{altWord})\,(e_s)$
in terms of sines at multiples of $\theta = \pi / m(s, t)$. -/
theorem dihedral_coords_odd_finite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t ≠ 0) (k : ℕ) :
    let θ := Real.pi / (M s t : ℝ)
    wordSigma M (t :: altWordEven s t k) (e s) s =
      Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sin θ ∧
    wordSigma M (t :: altWordEven s t k) (e s) t =
      Real.sin ((2 * (k : ℝ) + 2) * θ) / Real.sin θ := by
  intro θ
  have hm_pos : (0 : ℝ) < (M s t : ℝ) := by exact_mod_cast (show 0 < M s t by omega)
  have hθ_pos : θ > 0 := div_pos Real.pi_pos hm_pos
  have hm1 : M s t ≠ 1 := M.off_diagonal s t hst
  have hm_ge2 : (M s t : ℕ) ≥ 2 := by omega
  have hθ_lt_pi : θ < Real.pi := div_lt_self Real.pi_pos (by exact_mod_cast hm_ge2)
  have hsin_pos : Real.sin θ > 0 := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have hfv : formVal M s t = -Real.cos θ := formVal_eq_neg_cos M s t hm
  obtain ⟨hvs, hvt⟩ := dihedral_coords_even_finite M s t hst hm k
  simp only [wordSigma]
  set v := wordSigma M (altWordEven s t k) (e s)
  have hv_supp : ∀ u, u ≠ s → u ≠ t → v u = 0 :=
    wordSigma_support_two M s t hst (altWordEven s t k)
      (altWordEven_mem s t k) (e s) (e_supported_two s t)
  constructor
  ·
    rw [sigma_coord_ne M t v s hst]
    exact hvs
  ·
    rw [sigma_t_coord_t_of_supported M s t hst v hv_supp, hvs, hvt, hfv]
    have hθ_def : Real.pi / (↑(M.M s t) : ℝ) = θ := rfl
    simp only [hθ_def]
    have hrec : Real.sin ((2 * (k : ℝ) + 2) * θ) =
        2 * Real.cos θ * Real.sin ((2 * (k : ℝ) + 1) * θ) - Real.sin (2 * (k : ℝ) * θ) := by
      have := sin_chebyshev_recurrence θ (2 * k)
      convert this using 2 <;> push_cast <;> ring
    rw [hrec]
    field_simp
    ring

/-- Non-negativity of $\sin(n \pi / m)$ for $0 \le n \le m$, since the
argument lies in $[0, \pi]$. -/
theorem sin_nonneg_of_nat_le (m n : ℕ) (hm : m ≠ 0) (hn_le : n ≤ m) :
    0 ≤ Real.sin ((n : ℝ) * (Real.pi / (m : ℝ))) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    positivity
  · have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    have hn_real : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hn_le
    calc (n : ℝ) * (Real.pi / (m : ℝ))
        = Real.pi * ((n : ℝ) / (m : ℝ)) := by ring
      _ ≤ Real.pi * 1 := by
          apply mul_le_mul_of_nonneg_left
          · exact (div_le_one hm_pos).mpr hn_real
          · exact le_of_lt Real.pi_pos
      _ = Real.pi := mul_one _

/-- In the finite-order dihedral case ($m(s,t)$ finite), the iterate
$\mathtt{wordSigma}\,M\,(\mathtt{altWordEven}\,s\,t\,k)\,(e_s)$ is a positive
root as long as $2k < m(s, t)$. -/
theorem dihedral_pos_even_finite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t ≠ 0) (k : ℕ) (hk : 2 * k < M s t) :
    IsPositive (wordSigma M (altWordEven s t k) (e s)) := by
  have hm1 : M s t ≠ 1 := M.off_diagonal s t hst
  have hm_ge2 : (M s t : ℕ) ≥ 2 := by omega
  set θ := Real.pi / (M s t : ℝ)
  have hm_pos : (0 : ℝ) < (M s t : ℝ) := by exact_mod_cast (show 0 < M s t by omega)
  have hθ_pos : θ > 0 := div_pos Real.pi_pos hm_pos
  have hθ_lt_pi : θ < Real.pi := div_lt_self Real.pi_pos (by exact_mod_cast hm_ge2)

  have hsin_pos : Real.sin θ > 0 := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  obtain ⟨hcoord_s, hcoord_t⟩ := dihedral_coords_even_finite M s t hst hm k

  have hsin_s : 0 ≤ Real.sin ((2 * (k : ℝ) + 1) * θ) := by
    have h : 0 ≤ Real.sin (((2 * k + 1 : ℕ) : ℝ) * (Real.pi / (M s t : ℝ))) :=
      sin_nonneg_of_nat_le (M s t) (2 * k + 1) hm (by omega)
    exact (by convert h using 2; push_cast; ring)

  have hsin_t : 0 ≤ Real.sin (2 * (k : ℝ) * θ) := by
    have h : 0 ≤ Real.sin (((2 * k : ℕ) : ℝ) * (Real.pi / (M s t : ℝ))) :=
      sin_nonneg_of_nat_le (M s t) (2 * k) hm (by omega)
    exact (by convert h using 2; push_cast; ring)
  intro u
  by_cases hus : u = s
  · rw [hus, hcoord_s]; exact div_nonneg hsin_s (le_of_lt hsin_pos)
  · by_cases hut : u = t
    · rw [hut, hcoord_t]; exact div_nonneg hsin_t (le_of_lt hsin_pos)
    · exact (wordSigma_support_two M s t hst (altWordEven s t k)
        (altWordEven_mem s t k) (e s) (e_supported_two s t) u hus hut).symm ▸ le_refl 0

/-- Odd-length version of $\mathtt{dihedral\_pos\_even\_finite}$: prepending a
$t$ keeps the iterate positive as long as $2k + 1 < m(s, t)$. -/
theorem dihedral_pos_odd_finite (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (hm : M s t ≠ 0) (k : ℕ) (hk : 2 * k + 1 < M s t) :
    IsPositive (wordSigma M (t :: altWordEven s t k) (e s)) := by
  have hm_ge2 : (M s t : ℕ) ≥ 2 := by omega
  set θ := Real.pi / (M s t : ℝ)
  have hm_pos : (0 : ℝ) < (M s t : ℝ) := by exact_mod_cast (show 0 < M s t by omega)
  have hθ_pos : θ > 0 := div_pos Real.pi_pos hm_pos
  have hθ_lt_pi : θ < Real.pi := div_lt_self Real.pi_pos (by exact_mod_cast hm_ge2)

  have hsin_pos : Real.sin θ > 0 := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  obtain ⟨hcoord_s, hcoord_t⟩ := dihedral_coords_odd_finite M s t hst hm k

  have hsin_s : 0 ≤ Real.sin ((2 * (k : ℝ) + 1) * θ) := by
    have h : 0 ≤ Real.sin (((2 * k + 1 : ℕ) : ℝ) * (Real.pi / (M s t : ℝ))) :=
      sin_nonneg_of_nat_le (M s t) (2 * k + 1) hm (by omega)
    exact (by convert h using 2; push_cast; ring)

  have hsin_t : 0 ≤ Real.sin ((2 * (k : ℝ) + 2) * θ) := by
    have h : 0 ≤ Real.sin (((2 * k + 2 : ℕ) : ℝ) * (Real.pi / (M s t : ℝ))) :=
      sin_nonneg_of_nat_le (M s t) (2 * k + 2) hm (by omega)
    exact (by convert h using 2; push_cast; ring)
  intro u
  by_cases hus : u = s
  · rw [hus, hcoord_s]; exact div_nonneg hsin_s (le_of_lt hsin_pos)
  · by_cases hut : u = t
    · rw [hut, hcoord_t]; exact div_nonneg hsin_t (le_of_lt hsin_pos)
    · have hmem : ∀ b ∈ t :: altWordEven s t k, b = s ∨ b = t := by
        intro b hb; simp at hb
        rcases hb with rfl | hb
        · exact Or.inr rfl
        · exact altWordEven_mem s t k b hb
      exact (wordSigma_support_two M s t hst (t :: altWordEven s t k)
        hmem (e s) (e_supported_two s t) u hus hut).symm ▸ le_refl 0

/-- Combined dihedral positivity (even length): the alternating iterate of
$e_s$ stays positive as long as $2k < m(s, t)$ in the finite case, or
unconditionally in the infinite case $m(s, t) = 0$. -/
theorem dihedral_pos_even (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (k : ℕ) (hk : 2 * k < M s t ∨ M s t = 0) :
    IsPositive (wordSigma M (altWordEven s t k) (e s)) := by
  rcases hk with hk_fin | hm_inf
  · exact dihedral_pos_even_finite M s t hst (by omega) k hk_fin
  · exact dihedral_pos_even_infinite M s t hst hm_inf k

/-- Combined dihedral positivity (odd length): the alternating iterate
$\mathtt{wordSigma}\,M\,(t :: \text{altWord})\,(e_s)$ stays positive provided
$2k + 1 < m(s, t)$, with the infinite case $m(s, t) = 0$ unconditional. -/
theorem dihedral_pos_odd (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t)
    (k : ℕ) (hk : 2 * k + 1 < M s t ∨ M s t = 0) :
    IsPositive (wordSigma M (t :: altWordEven s t k) (e s)) := by
  rcases hk with hk_fin | hm_inf
  · exact dihedral_pos_odd_finite M s t hst (by omega) k hk_fin
  · exact dihedral_pos_odd_infinite M s t hst hm_inf k

end CoxeterGroup
