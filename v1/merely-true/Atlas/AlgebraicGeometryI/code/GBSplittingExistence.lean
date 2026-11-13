/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRoch
import Atlas.AlgebraicGeometryI.code.CohomologyP1
import Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves
import Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoff
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Fin.VecNotation

open BigOperators

namespace GBExistence

/-- Combinatorial model for `h⁰(P¹, O(d)) = max(d + 1, 0)`. -/
def h0_dim (d : ℤ) : ℕ := Int.toNat (d + 1)

/-- Combinatorial model for `h¹(P¹, O(d)) = max(−d − 1, 0)` (Serre duality). -/
def h1_dim (d : ℤ) : ℕ := Int.toNat (-d - 1)

/-- `h¹` vanishes for non-negative twists. -/
lemma h1_dim_of_nonneg {d : ℤ} (hd : 0 ≤ d) : h1_dim d = 0 := by
  unfold h1_dim; rw [Int.toNat_eq_zero]; omega

/-- `h⁰` vanishes for twists below `−1`. -/
lemma h0_dim_neg {d : ℤ} (hd : d < -1) : h0_dim d = 0 := by
  unfold h0_dim; rw [Int.toNat_eq_zero]; omega

/-- `h⁰` vanishes for twists ≤ `−1`. -/
lemma h0_dim_nonpos {d : ℤ} (hd : d ≤ -1) : h0_dim d = 0 := by
  unfold h0_dim; rw [Int.toNat_eq_zero]; omega

/-- For non-negative twists, `h⁰(O(d)) > 0`. -/
lemma h0_dim_pos {d : ℤ} (hd : 0 ≤ d) : 0 < h0_dim d := by
  unfold h0_dim
  have : (d + 1).toNat ≠ 0 := by
    intro h; have := Int.toNat_eq_zero.mp h; omega
  omega

/-- Combinatorial Riemann-Roch on `P¹`: `h⁰(O(d)) − h¹(O(d)) = d + 1`. -/
theorem euler_char_formula (d : ℤ) : (h0_dim d : ℤ) - (h1_dim d : ℤ) = d + 1 := by
  unfold h0_dim h1_dim
  by_cases hd : 0 ≤ d + 1
  · have h1 : (d + 1).toNat = (d + 1).toNat := rfl
    have h2 : (-d - 1).toNat = 0 := by rw [Int.toNat_eq_zero]; omega
    rw [h2]; push_cast; rw [Int.toNat_of_nonneg hd]; omega
  · push Not at hd
    have h1 : (d + 1).toNat = 0 := by rw [Int.toNat_eq_zero]; omega
    rw [h1]; push_cast
    rw [Int.toNat_of_nonneg (show 0 ≤ -d - 1 by omega)]
    omega

/-- `h¹(O(d)) = 0` for `d ≥ −1`. -/
lemma h1_vanishes_ge_neg1 {d : ℤ} (hd : -1 ≤ d) : h1_dim d = 0 := by
  unfold h1_dim; rw [Int.toNat_eq_zero]; omega

/-- Total `h⁰` of a direct sum `⊕ O(d_i)` indexed by `Fin n`. -/
def h0_total {n : ℕ} (degrees : Fin n → ℤ) : ℕ :=
  ∑ i, h0_dim (degrees i)

/-- Total `h¹` of a direct sum `⊕ O(d_i)` indexed by `Fin n`. -/
def h1_total {n : ℕ} (degrees : Fin n → ℤ) : ℕ :=
  ∑ i, h1_dim (degrees i)

/-- Dimension of `Ext¹(O(a), O(b)) = H¹(O(b − a))` on `P¹`. -/
def ext1_dim (a b : ℤ) : ℕ := h1_dim (b - a)

/-- `Ext¹(O(a), O(b)) = 0` when `a ≤ b`, i.e. the splitting obstruction
vanishes for line bundles in non-increasing order. -/
lemma ext1_dim_zero_of_le {a b : ℤ} (h : a ≤ b) : ext1_dim a b = 0 := by
  unfold ext1_dim; exact h1_vanishes_ge_neg1 (by omega)

/-- Finitely generated torsion-free modules over a PID are free: this is the
key algebraic input for splitting on `P¹`. -/
theorem pid_torsionFree_free (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Free R M :=
  inferInstance

/-- A splitting type: the data of `n` integer degrees `(d_1 ≥ … ≥ d_n)`
specifying a candidate decomposition `⊕ O(d_i)` in Grothendieck-Birkhoff. -/
structure SplittingType (n : ℕ) where
  degrees : Fin n → ℤ
  sorted : ∀ i j : Fin n, i ≤ j → degrees j ≤ degrees i

/-- `h⁰(⊕ O(d_i + t))` for a splitting type `s` twisted by `t`. -/
def SplittingType.h0_twisted {n : ℕ} (s : SplittingType n) (t : ℤ) : ℕ :=
  ∑ i, h0_dim (s.degrees i + t)

/-- `h¹(⊕ O(d_i + t))` for a splitting type `s` twisted by `t`. -/
def SplittingType.h1_twisted {n : ℕ} (s : SplittingType n) (t : ℤ) : ℕ :=
  ∑ i, h1_dim (s.degrees i + t)

/-- The maximum degree `d_1` in a non-empty splitting type. -/
def SplittingType.maxDegree {n : ℕ} (s : SplittingType (n + 1)) : ℤ :=
  s.degrees ⟨0, Nat.zero_lt_succ n⟩

/-- Every degree in a splitting type is bounded above by the maximum degree. -/
lemma SplittingType.le_maxDegree {n : ℕ} (s : SplittingType (n + 1))
    (i : Fin (n + 1)) : s.degrees i ≤ s.maxDegree :=
  s.sorted ⟨0, Nat.zero_lt_succ n⟩ i (Fin.zero_le i)

/-- The splitting type obtained by removing the first (maximal) summand. -/
def SplittingType.tail {n : ℕ} (s : SplittingType (n + 1)) : SplittingType n where
  degrees := fun i => s.degrees (Fin.succ i)
  sorted := fun i j hij =>
    s.sorted (Fin.succ i) (Fin.succ j) (Fin.succ_le_succ_iff.mpr hij)

/-- Decomposition of `h⁰_twisted` along the leading summand: `h⁰(O(d_1 + t)) +
h⁰(⊕_{i≥2} O(d_i + t))`. -/
theorem h0_split_decomp {n : ℕ} (s : SplittingType (n + 1)) (t : ℤ) :
    s.h0_twisted t = h0_dim (s.maxDegree + t) + s.tail.h0_twisted t := by
  simp only [SplittingType.h0_twisted, SplittingType.tail, SplittingType.maxDegree,
    Fin.sum_univ_succ]; rfl

/-- Analogous decomposition for `h¹_twisted`. -/
theorem h1_split_decomp {n : ℕ} (s : SplittingType (n + 1)) (t : ℤ) :
    s.h1_twisted t = h1_dim (s.maxDegree + t) + s.tail.h1_twisted t := by
  simp only [SplittingType.h1_twisted, SplittingType.tail, SplittingType.maxDegree,
    Fin.sum_univ_succ]; rfl

/-- Inductive `Ext¹` vanishing: extensions of the tail summands by `O(maxDegree)`
all vanish, since each tail degree is ≤ the maximum degree. -/
theorem inductive_ext1_vanishing {n : ℕ} (s : SplittingType (n + 1)) :
    ∑ i : Fin n, ext1_dim (s.tail.degrees i) s.maxDegree = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply ext1_dim_zero_of_le

  exact s.le_maxDegree (Fin.succ i)

/-- Reverse engineering: if the total `h⁰` of `⊕ O(d_i − 1)` vanishes, then
every `d_i ≤ 0`. -/
lemma degrees_le_zero_of_h0_twist_vanish {n : ℕ} (degrees : Fin n → ℤ)
    (h : h0_total (fun i => degrees i - 1) = 0) :
    ∀ i, degrees i ≤ 0 := by
  intro i
  by_contra h_pos
  push Not at h_pos
  have h1 : 0 < h0_dim (degrees i - 1) := h0_dim_pos (by omega)
  have h2 : h0_dim (degrees i - 1) ≤ h0_total (fun j => degrees j - 1) := by
    unfold h0_total
    exact Finset.single_le_sum (f := fun j => h0_dim (degrees j - 1))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Riemann-Roch for a splitting type: the Euler characteristic of `⊕ O(d_i + t)`
equals `Σ (d_i + t + 1)`. -/
theorem split_riemann_roch {n : ℕ} (s : SplittingType n) (t : ℤ) :
    (s.h0_twisted t : ℤ) - (s.h1_twisted t : ℤ) =
    ∑ i, (s.degrees i + t + 1) := by
  unfold SplittingType.h0_twisted SplittingType.h1_twisted
  push_cast
  rw [← Finset.sum_sub_distrib]
  congr 1; ext i
  exact euler_char_formula (s.degrees i + t)

/-- Specialization at `t = 0`: `χ(⊕ O(d_i)) = (Σ d_i) + n`. -/
theorem split_total_degree {n : ℕ} (s : SplittingType n) :
    (s.h0_twisted 0 : ℤ) - (s.h1_twisted 0 : ℤ) = (∑ i, s.degrees i) + n := by
  rw [split_riemann_roch]
  simp [Finset.sum_add_distrib, Finset.sum_const]

/-- Additivity of Euler characteristic along the splitting: the leading summand
and the tail contribute independently. -/
theorem split_euler_additive {n : ℕ} (s : SplittingType (n + 1)) (t : ℤ) :
    (s.h0_twisted t : ℤ) - (s.h1_twisted t : ℤ) =
    ((h0_dim (s.maxDegree + t) : ℤ) - (h1_dim (s.maxDegree + t) : ℤ)) +
    ((s.tail.h0_twisted t : ℤ) - (s.tail.h1_twisted t : ℤ)) := by
  rw [h0_split_decomp, h1_split_decomp]
  push_cast; ring

/-- A normalized splitting type with `maxDegree = 0` has positive `h⁰`, since
its leading summand is `O`. -/
theorem normalized_has_section {n : ℕ} (s : SplittingType (n + 1))
    (h_max : s.maxDegree = 0) :
    0 < s.h0_twisted 0 := by
  unfold SplittingType.h0_twisted
  set a0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  have h1 : 0 < h0_dim (s.degrees a0 + 0) := by
    simp [show s.degrees a0 = 0 from h_max]; exact h0_dim_pos le_rfl
  have h2 : h0_dim (s.degrees a0 + 0) ≤ ∑ i, h0_dim (s.degrees i + 0) :=
    Finset.single_le_sum (f := fun i => h0_dim (s.degrees i + 0))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ a0)
  linarith

/-- Bridge: the combinatorial `h0_dim` matches the actual cohomology dimension
of `H⁰(P¹, O(d))` for `d ≥ 0`. -/
theorem h0_dim_matches_cohomology (k : Type) [Field k] (d : ℤ) (hd : 0 ≤ d) :
    (h0_dim d : ℕ) = Module.finrank k (SheafCohomology.H0 k d) := by
  rw [SheafCohomology.finrank_H0_of_nonneg k d hd]; rfl

/-- Bridge: the combinatorial `h0_dim` matches `dim H⁰(P¹, O(d))` for `d < 0`,
where both vanish. -/
theorem h0_dim_matches_cohomology_neg (k : Type) [Field k] (d : ℤ) (hd : d < 0) :
    (h0_dim d : ℕ) = Module.finrank k (SheafCohomology.H0 k d) := by
  rw [SheafCohomology.finrank_H0_of_neg k d hd, h0_dim_nonpos (by omega)]

/-- Bridge: the combinatorial `h1_dim` matches `dim H¹(P¹, O(d))` for `d ≥ 0`,
where both vanish. -/
theorem h1_dim_matches_cohomology (k : Type) [Field k] (d : ℤ) (hd : 0 ≤ d) :
    (h1_dim d : ℕ) = Module.finrank k (SheafCohomology.H1 k d) := by
  rw [SheafCohomology.finrank_H1_of_nonneg k d hd, h1_dim_of_nonneg hd]

/-- Bridge: the combinatorial `h1_dim` matches `dim H¹(P¹, O(d))` for `d < 0`. -/
theorem h1_dim_matches_cohomology_neg (k : Type) [Field k] (d : ℤ) (hd : d < 0) :
    (h1_dim d : ℕ) = Module.finrank k (SheafCohomology.H1 k d) := by
  rw [SheafCohomology.finrank_H1_of_neg k d hd]; rfl

end GBExistence
