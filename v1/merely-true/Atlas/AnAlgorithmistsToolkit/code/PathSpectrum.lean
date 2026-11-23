/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Atlas.AnAlgorithmistsToolkit.code.SpectraCommonGraphs

open Real SimpleGraph Matrix Finset

namespace PathSpectrum

instance pathGraph_decRel (n : ℕ) : DecidableRel (pathGraph n).Adj := by
  intro u v
  rw [pathGraph_adj]
  exact instDecidableOr

noncomputable section

def pathGraphEigenvalue (n : ℕ) (k : Fin n) : ℝ :=
  2 - 2 * cos (π * (k : ℝ) / (n : ℝ))

def pathGraphEigenvector (n : ℕ) (k : Fin n) (u : Fin n) : ℝ :=
  cos (π * (k : ℝ) * (2 * (u.val : ℝ) + 1) / (2 * (n : ℝ)))

theorem eigenvector_interior (n : ℕ) (k : Fin n) (u : Fin n)
    (h0 : 0 < u.val) (hLast : u.val + 1 < n) :
    (lapMatrix ℝ (pathGraph n) *ᵥ pathGraphEigenvector n k) u =
    pathGraphEigenvalue n k * pathGraphEigenvector n k u := by
  rw [lapMatrix_mulVec_apply]
  have hne : (⟨u.val - 1, by omega⟩ : Fin n) ≠ ⟨u.val + 1, hLast⟩ := by
    simp [Fin.ext_iff]
  have hNeigh : (pathGraph n).neighborFinset u =
      {⟨u.val - 1, by omega⟩, ⟨u.val + 1, hLast⟩} := by
    ext v
    simp only [mem_neighborFinset, pathGraph_adj, mem_insert, mem_singleton, Fin.ext_iff]
    constructor
    · intro h; rcases h with h | h
      · right; omega
      · left; omega
    · intro h; rcases h with h | h
      · right; omega
      · left; omega
  have hdeg : (pathGraph n).degree u = 2 := by
    unfold SimpleGraph.degree; rw [hNeigh]; exact Finset.card_pair hne
  rw [hdeg, hNeigh, Finset.sum_pair hne]
  simp only [pathGraphEigenvector, pathGraphEigenvalue]
  have h1 : (↑(u.val - 1) : ℝ) = (↑u.val : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (by omega : 1 ≤ u.val)
  have h2 : (↑(u.val + 1) : ℝ) = (↑u.val : ℝ) + 1 := by push_cast; ring
  conv_lhs =>
    rw [show (↑(u.val - 1) : ℝ) = (↑u.val : ℝ) - 1 from h1]
    rw [show (↑(u.val + 1) : ℝ) = (↑u.val : ℝ) + 1 from h2]
  have harg_m : π * ↑↑k * (2 * ((↑↑u : ℝ) - 1) + 1) / (2 * ↑n) =
    π * ↑↑k * (2 * ↑↑u + 1) / (2 * ↑n) - π * ↑↑k / ↑n := by ring
  have harg_p : π * ↑↑k * (2 * ((↑↑u : ℝ) + 1) + 1) / (2 * ↑n) =
    π * ↑↑k * (2 * ↑↑u + 1) / (2 * ↑n) + π * ↑↑k / ↑n := by ring
  rw [harg_m, harg_p]
  have identity : 2 * cos (π * ↑↑k * (2 * ↑↑u + 1) / (2 * ↑n)) -
    cos (π * ↑↑k * (2 * ↑↑u + 1) / (2 * ↑n) + π * ↑↑k / ↑n) -
    cos (π * ↑↑k * (2 * ↑↑u + 1) / (2 * ↑n) - π * ↑↑k / ↑n) =
    (2 - 2 * cos (π * ↑↑k / ↑n)) * cos (π * ↑↑k * (2 * ↑↑u + 1) / (2 * ↑n)) := by
    rw [cos_add, cos_sub]; ring
  push_cast
  linarith

theorem eigenvector_zero (n : ℕ) (hn : 2 ≤ n) (k : Fin n) :
    (lapMatrix ℝ (pathGraph n) *ᵥ pathGraphEigenvector n k) ⟨0, by omega⟩ =
    pathGraphEigenvalue n k * pathGraphEigenvector n k ⟨0, by omega⟩ := by
  rw [lapMatrix_mulVec_apply]
  have hNeigh : (pathGraph n).neighborFinset ⟨0, by omega⟩ = {⟨1, by omega⟩} := by
    ext v
    simp only [mem_neighborFinset, pathGraph_adj, mem_singleton, Fin.ext_iff]
    constructor
    · intro h; rcases h with h | h <;> omega
    · intro h; left; omega
  have hdeg : (pathGraph n).degree ⟨0, by omega⟩ = 1 := by
    unfold SimpleGraph.degree; rw [hNeigh]; simp
  rw [hdeg, hNeigh, Finset.sum_singleton]
  simp only [pathGraphEigenvector, pathGraphEigenvalue]
  push_cast; norm_num

  have key : 2 * cos (π * ↑↑k / (2 * ↑n)) -
    cos (π * ↑↑k / (2 * ↑n) + π * ↑↑k / ↑n) -
    cos (π * ↑↑k / (2 * ↑n) - π * ↑↑k / ↑n) =
    (2 - 2 * cos (π * ↑↑k / ↑n)) * cos (π * ↑↑k / (2 * ↑n)) := by
    rw [cos_add, cos_sub]; ring
  have hcos_sym : cos (π * ↑↑k / (2 * ↑n) - π * ↑↑k / ↑n) =
    cos (π * ↑↑k / (2 * ↑n)) := by
    have : π * ↑↑k / (2 * (↑n : ℝ)) - π * ↑↑k / ↑n = -(π * ↑↑k / (2 * ↑n)) := by ring
    rw [this, cos_neg]
  have hcos_arg : cos (π * ↑↑k / (2 * ↑n) + π * ↑↑k / ↑n) =
    cos (π * ↑↑k * 3 / (2 * ↑n)) := by congr 1; ring
  linarith [key, hcos_sym, hcos_arg]

theorem eigenvector_last (n : ℕ) (hn : 2 ≤ n) (k : Fin n) :
    (lapMatrix ℝ (pathGraph n) *ᵥ pathGraphEigenvector n k) ⟨n - 1, by omega⟩ =
    pathGraphEigenvalue n k * pathGraphEigenvector n k ⟨n - 1, by omega⟩ := by
  rw [lapMatrix_mulVec_apply]
  have hNeigh : (pathGraph n).neighborFinset ⟨n - 1, by omega⟩ = {⟨n - 2, by omega⟩} := by
    ext v
    simp only [mem_neighborFinset, pathGraph_adj, mem_singleton, Fin.ext_iff]
    constructor
    · intro h; rcases h with h | h <;> omega
    · intro h; right; omega
  have hdeg : (pathGraph n).degree ⟨n - 1, by omega⟩ = 1 := by
    unfold SimpleGraph.degree; rw [hNeigh]; simp
  rw [hdeg, hNeigh, Finset.sum_singleton]
  simp only [pathGraphEigenvector, pathGraphEigenvalue]
  have hc1 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ n from hn)]; simp
  have hc2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n from by omega)]; simp
  conv_lhs =>
    rw [show ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 from hc1]
    rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 from hc2]
  conv_rhs =>
    rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 from hc2]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have harg_minus : π * ↑↑k * (2 * ((↑n : ℝ) - 2) + 1) / (2 * ↑n) =
    π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) - π * ↑↑k / ↑n := by
    field_simp; ring
  have harg_plus_eq : π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) + π * ↑↑k / ↑n =
    2 * π * ↑↑k - π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) := by
    field_simp; ring
  have hcos_plus_eq : cos (π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) + π * ↑↑k / ↑n) =
    cos (π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n)) := by
    rw [harg_plus_eq]
    rw [show 2 * π * ↑↑k - π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) =
      -(π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) - ↑(k.val) * (2 * π)) from by
      ring]
    rw [cos_neg, cos_sub_nat_mul_two_pi]
  have key : 2 * cos (π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n)) -
    cos (π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) + π * ↑↑k / ↑n) -
    cos (π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n) - π * ↑↑k / ↑n) =
    (2 - 2 * cos (π * ↑↑k / ↑n)) * cos (π * ↑↑k * (2 * ((↑n : ℝ) - 1) + 1) / (2 * ↑n)) := by
    rw [cos_add, cos_sub]; ring
  rw [harg_minus]
  linarith [key, hcos_plus_eq]

end

theorem pathGraph_lapMatrix_eigenvector (n : ℕ) (hn : 1 ≤ n) (k : Fin n) :
    (lapMatrix ℝ (pathGraph n)).mulVec (pathGraphEigenvector n k) =
    pathGraphEigenvalue n k • (pathGraphEigenvector n k) := by

  by_cases hn1 : n = 1
  · subst hn1
    ext u
    simp only [Pi.smul_apply, smul_eq_mul]
    have hu : u = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hu
    rw [lapMatrix_mulVec_apply]
    have hNeigh : (pathGraph 1).neighborFinset ⟨0, by omega⟩ = ∅ := by
      ext v
      constructor
      · intro hv
        rw [mem_neighborFinset, pathGraph_adj] at hv
        exact absurd hv (by have := v.isLt; omega)
      · intro hv; exact absurd hv (Finset.notMem_empty v)
    have hdeg : (pathGraph 1).degree ⟨0, by omega⟩ = 0 := by
      unfold SimpleGraph.degree; rw [hNeigh]; simp
    rw [hdeg, hNeigh, Finset.sum_empty]
    have hk : k = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hk
    simp [pathGraphEigenvalue, pathGraphEigenvector, cos_zero]
  ·
    have hn2 : 2 ≤ n := by omega
    ext u
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h0 : u.val = 0
    · have hu : u = ⟨0, by omega⟩ := Fin.ext h0
      rw [hu]; exact eigenvector_zero n hn2 k
    · by_cases hLast : u.val = n - 1
      · have hu : u = ⟨n - 1, by omega⟩ := Fin.ext hLast
        rw [hu]; exact eigenvector_last n hn2 k
      · exact eigenvector_interior n k u (by omega) (by omega)

end PathSpectrum
