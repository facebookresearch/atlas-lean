/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Set MvPolynomial

namespace CellDecomposition

/--
A line in `ℝ²`: a one-dimensional affine subspace, packaged with a proof that
its direction has rank `1` and that its carrier set is nonempty.
-/
structure Line2 where
  carrier : AffineSubspace ℝ (Fin 2 → ℝ)
  dim_eq : Module.finrank ℝ carrier.direction = 1
  nonempty : (carrier : Set (Fin 2 → ℝ)).Nonempty

/-- Membership of a point in a `Line2`: belongs to the underlying affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier





/--
The open cell `{x : ∀ i, sign(polys i (x)) = σ i}` cut out by a sign pattern
`σ : Fin k → Bool` (with `true` meaning positive sign and `false` meaning
negative sign).
-/
noncomputable def polyCell {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) : Set (Fin 2 → ℝ) :=
  ⋂ i, if σ i then {x | eval x (polys i) > 0}
              else {x | eval x (polys i) < 0}

/--
The "wall" `⋃_i Z(polys i)`: the union of the zero sets of the polynomials,
separating the open cells `polyCell polys σ`.
-/
def polyWall {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) : Set (Fin 2 → ℝ) :=
  ⋃ i, {x | eval x (polys i) = 0}

/--
The points of a finite set `X ⊆ ℝ²` lying in the open cell `polyCell polys σ`,
returned as a `Finset`.
-/
noncomputable def signPatternCell (X : Finset (Fin 2 → ℝ))
    {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) (σ : Fin k → Bool) :
    Finset (Fin 2 → ℝ) :=
  X.filter (fun x => ∀ i, if σ i then eval x (polys i) > 0 else eval x (polys i) < 0)

/-- Every `polyCell` is open, being a finite intersection of open half-spaces
defined by polynomial inequalities. -/
lemma polyCell_isOpen {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) (σ : Fin k → Bool) :
    IsOpen (polyCell polys σ) := by
  apply isOpen_iInter_of_finite; intro i
  split_ifs
  · exact isOpen_lt continuous_const (continuous_eval _)
  · exact isOpen_lt (continuous_eval _) continuous_const

/-- The polynomial wall is closed, being a finite union of polynomial zero sets. -/
lemma polyWall_isClosed {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) :
    IsClosed (polyWall polys) := by
  apply isClosed_iUnion_of_finite; intro i
  exact isClosed_eq (continuous_eval _) continuous_const

/-- The wall together with the union of all sign-pattern open cells covers `ℝ²`. -/
lemma polyWall_union_cells {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) :
    polyWall polys ∪ ⋃ σ : Fin k → Bool, polyCell polys σ = univ := by
  ext x; simp only [mem_union, mem_iUnion, mem_univ, iff_true]
  by_cases h : ∃ i, eval x (polys i) = 0
  · left; exact mem_iUnion.mpr (h.imp fun i hi => hi)
  · right; push_neg at h
    refine ⟨fun i => decide (eval x (polys i) > 0), ?_⟩
    simp only [polyCell, mem_iInter, decide_eq_true_eq]
    intro i; have hi := h i
    split_ifs with hpos
    · exact hpos
    · push_neg at hpos; exact lt_of_le_of_ne hpos hi

/-- Distinct sign patterns give disjoint open cells. -/
lemma polyCell_pairwise_disjoint {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) :
    Pairwise fun σ τ : Fin k → Bool => Disjoint (polyCell polys σ) (polyCell polys τ) := by
  intro σ τ hne; rw [Set.disjoint_left]
  intro x hx hτ
  simp only [polyCell, mem_iInter] at hx hτ
  apply hne; funext i
  have hxi := hx i; have hτi := hτ i
  cases hσ : σ i <;> cases hτ' : τ i <;> simp_all <;> linarith

/-- Each open cell is disjoint from the wall. -/
lemma polyCell_disjoint_wall {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) : Disjoint (polyCell polys σ) (polyWall polys) := by
  rw [Set.disjoint_left]; intro x hx hw
  simp only [polyCell, mem_iInter] at hx
  simp only [polyWall, mem_iUnion] at hw
  obtain ⟨i, hi⟩ := hw
  have hxi := hx i
  cases hσi : σ i <;> simp_all <;> linarith



/--
Inductive step: after appending a polynomial `p` and the sign `true`, the
sign-pattern cell sits inside the previous cell intersected with `{x : p(x) > 0}`.
-/
lemma signPatternCell_snoc_true_subset (X : Finset (Fin 2 → ℝ)) {k : ℕ}
    (polys : Fin k → MvPolynomial (Fin 2) ℝ) (p : MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) :
    signPatternCell X (Fin.snoc polys p) (Fin.snoc σ true) ⊆
      (signPatternCell X polys σ).filter (fun x => eval x p > 0) := by
  intro x hx; simp only [signPatternCell, Finset.mem_filter] at hx ⊢
  refine ⟨⟨hx.1, fun i => ?_⟩, ?_⟩
  · have := hx.2 (Fin.castSucc i); simp [Fin.snoc_castSucc] at this; exact this
  · have := hx.2 (Fin.last k); simp [Fin.snoc_last] at this; exact this

/--
Inductive step: after appending a polynomial `p` and the sign `false`, the
sign-pattern cell sits inside the previous cell intersected with `{x : p(x) < 0}`.
-/
lemma signPatternCell_snoc_false_subset (X : Finset (Fin 2 → ℝ)) {k : ℕ}
    (polys : Fin k → MvPolynomial (Fin 2) ℝ) (p : MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) :
    signPatternCell X (Fin.snoc polys p) (Fin.snoc σ false) ⊆
      (signPatternCell X polys σ).filter (fun x => eval x p < 0) := by
  intro x hx; simp only [signPatternCell, Finset.mem_filter] at hx ⊢
  refine ⟨⟨hx.1, fun i => ?_⟩, ?_⟩
  · have := hx.2 (Fin.castSucc i); simp [Fin.snoc_castSucc] at this; exact this
  · have := hx.2 (Fin.last k); simp [Fin.snoc_last] at this; exact this

/-- Arithmetic estimate `2^j ≤ (2^{⌊(j+1)/2⌋})²` used to control degrees at each
bisection step. -/
lemma degree_bound_step (j : ℕ) : 2 ^ j ≤ (2 ^ ((j + 1) / 2)) ^ 2 := by
  have h : j ≤ 2 * ((j + 1) / 2) := by omega
  calc 2 ^ j ≤ 2 ^ (2 * ((j + 1) / 2)) := Nat.pow_le_pow_right (by norm_num) h
    _ = (2 ^ ((j + 1) / 2)) ^ 2 := by ring

/-- There are `2^k` sign patterns in `Fin k → Bool`. -/
lemma card_fin_bool_fun (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by
  simp [Fintype.card_fin, Fintype.card_bool]

/-- Closed-form for the cumulative degree sum at an even number of bisection
steps: `∑_{j<2m} 2^{⌊(j+1)/2⌋} = 3(2^m − 1)`. -/
lemma degree_sum_bound_even (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), 2 ^ ((j + 1) / 2) = 3 * (2 ^ m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h2 : (2 * m + 0 + 1) / 2 = m := by omega
    rw [h1, h2]; ring_nf; omega

/-- Cumulative degree bound after `k` bisection steps:
`∑_{j<k} 2^{⌊(j+1)/2⌋} ≤ 4 · 2^{⌊k/2⌋}`. -/
lemma degree_sum_bound (k : ℕ) :
    ∑ j ∈ Finset.range k, 2 ^ ((j + 1) / 2) ≤ 4 * 2 ^ (k / 2) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hk : k = 2 * m := by omega
    rw [hk, degree_sum_bound_even]
    have h : 2 * m / 2 = m := by omega
    rw [h]; omega
  · have hk : k = 2 * m + 1 := by omega
    rw [hk, show 2 * m + 1 = (2 * m) + 1 from by ring,
        Finset.sum_range_succ, degree_sum_bound_even]
    have h1 : (2 * m + 0 + 1) / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1]; omega

/-- For `s ≥ 1`, `s² ≤ 2^{2 log₂ s + 2}`. Used to relate the target parameter
`s` to the chosen number of bisection steps `k = 2 log₂ s + 2`. -/
lemma two_pow_log_bound (s : ℕ) (hs : 1 ≤ s) : s ^ 2 ≤ 2 ^ (2 * Nat.log 2 s + 2) := by
  have h1 : s ≤ 2 ^ (Nat.log 2 s + 1) := (Nat.lt_pow_succ_log_self (by norm_num) s).le
  calc s ^ 2 ≤ (2 ^ (Nat.log 2 s + 1)) ^ 2 := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (2 * Nat.log 2 s + 2) := by ring

/-- For `s ≥ 1`, `2^{⌊(2 log₂ s + 2) / 2⌋} ≤ 2s`. Used to convert the
`O(2^{k/2})` degree bound into an `O(s)` bound. -/
lemma two_pow_half_log_bound (s : ℕ) (hs : 1 ≤ s) :
    2 ^ ((2 * Nat.log 2 s + 2) / 2) ≤ 2 * s := by
  have h : (2 * Nat.log 2 s + 2) / 2 = Nat.log 2 s + 1 := by omega
  rw [h]
  have : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 (by omega : s ≠ 0)
  calc 2 ^ (Nat.log 2 s + 1) = 2 * 2 ^ Nat.log 2 s := by ring
    _ ≤ 2 * s := by linarith



section
open Classical

end

end CellDecomposition
