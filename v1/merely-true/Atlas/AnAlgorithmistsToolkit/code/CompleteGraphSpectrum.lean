/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace CompleteGraphSpectrum

open Matrix SimpleGraph Finset BigOperators Module

theorem lapMatrix_completeGraph_apply (n : ℕ) (i j : Fin n) :
    ((completeGraph (Fin n)).lapMatrix ℝ) i j =
      if i = j then (n : ℝ) - 1 else -1 := by
  have hn : 1 ≤ n := by have := i.is_lt; omega
  by_cases h : i = j
  · subst h
    simp only [lapMatrix, degMatrix, sub_apply, diagonal_apply]
    have hirr : ¬ (completeGraph (Fin n)).Adj i i := SimpleGraph.irrefl _
    simp only [adjMatrix_apply, hirr, if_false, sub_zero]
    rw [complete_graph_degree, Fintype.card_fin]
    push_cast [Nat.cast_sub hn]; ring
  · simp only [if_neg h]
    simp only [lapMatrix, degMatrix, sub_apply, diagonal_apply, if_neg h, zero_sub]
    have hadj : (completeGraph (Fin n)).Adj i j := h
    simp [adjMatrix_apply, hadj]

theorem lapMatrix_completeGraph_mulVec (n : ℕ) (v : Fin n → ℝ) :
    ((completeGraph (Fin n)).lapMatrix ℝ).mulVec v =
      fun i => (n : ℝ) * v i - ∑ j, v j := by
  ext i
  simp only [mulVec, dotProduct, lapMatrix_completeGraph_apply]
  conv_lhs =>
    arg 2; ext j
    rw [show (if i = j then (n : ℝ) - 1 else -1) * v j =
      (n : ℝ) * (if i = j then v j else 0) - v j by split_ifs <;> ring]
  simp only [Finset.sum_sub_distrib]
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

noncomputable def completeGraphLapEnd (n : ℕ) : Module.End ℝ (Fin n → ℝ) :=
  Matrix.toLin' ((completeGraph (Fin n)).lapMatrix ℝ)

noncomputable def sumFunctional (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ j, v j
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.mul_sum]

theorem eigenspace_n_eq_ker_sumFunctional (n : ℕ) :
    (completeGraphLapEnd n).eigenspace (n : ℝ) = LinearMap.ker (sumFunctional n) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  constructor
  · intro h
    by_cases hn : n = 0
    · subst hn; simp [sumFunctional]
    · have ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      have := congr_fun h i
      simp only [completeGraphLapEnd, Matrix.toLin'_apply, lapMatrix_completeGraph_mulVec,
        Pi.smul_apply, smul_eq_mul] at this
      simp only [sumFunctional, LinearMap.coe_mk, AddHom.coe_mk]
      linarith
  · intro hv
    simp only [sumFunctional, LinearMap.coe_mk, AddHom.coe_mk] at hv
    ext i
    simp only [completeGraphLapEnd, Matrix.toLin'_apply, lapMatrix_completeGraph_mulVec,
      Pi.smul_apply, smul_eq_mul, hv, sub_zero]

theorem eigenspace_zero_eq_span_ones (n : ℕ) (hn : 1 ≤ n) :
    (completeGraphLapEnd n).eigenspace 0 = ℝ ∙ (fun _ : Fin n => (1 : ℝ)) := by
  ext v
  rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
  simp only [zero_smul]
  constructor
  · intro h
    have key : ∀ i : Fin n, (n : ℝ) * v i = ∑ j, v j := by
      intro i
      have := congr_fun h i
      simp only [completeGraphLapEnd, Matrix.toLin'_apply, lapMatrix_completeGraph_mulVec,
        Pi.zero_apply] at this
      linarith
    refine ⟨v ⟨0, by omega⟩, ?_⟩
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    have h0 := key ⟨0, by omega⟩
    have hi := key i
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_left_cancel₀ hn' (h0.trans hi.symm)
  · intro ⟨c, hc⟩
    rw [← hc]
    ext i
    simp only [completeGraphLapEnd, Matrix.toLin'_apply, lapMatrix_completeGraph_mulVec,
      Pi.zero_apply, Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_const,
      Finset.card_fin]
    ring

lemma sumFunctional_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (sumFunctional n) := by
  intro r
  exact ⟨fun i => if i = ⟨0, by omega⟩ then r else 0,
    by simp [sumFunctional, Finset.sum_ite_eq', Finset.mem_univ]⟩

theorem finrank_eigenspace_n (n : ℕ) (hn : 1 ≤ n) :
    finrank ℝ ((completeGraphLapEnd n).eigenspace (n : ℝ)) = n - 1 := by
  rw [eigenspace_n_eq_ker_sumFunctional]
  have hrn := LinearMap.finrank_range_add_finrank_ker (sumFunctional n)
  rw [Module.finrank_fin_fun] at hrn
  have hrange : LinearMap.range (sumFunctional n) = ⊤ :=
    LinearMap.range_eq_top.mpr (sumFunctional_surjective n hn)
  rw [hrange, finrank_top, finrank_self] at hrn
  omega

theorem finrank_eigenspace_zero (n : ℕ) (hn : 1 ≤ n) :
    finrank ℝ ((completeGraphLapEnd n).eigenspace 0) = 1 := by
  rw [eigenspace_zero_eq_span_ones n hn]
  exact finrank_span_singleton (show (fun _ : Fin n => (1 : ℝ)) ≠ 0 by
    intro h; exact absurd (congr_fun h ⟨0, by omega⟩) one_ne_zero)

theorem lemma15_complete_graph_spectrum (n : ℕ) (hn : 1 ≤ n) :
    finrank ℝ ((completeGraphLapEnd n).eigenspace 0) = 1 ∧
    (completeGraphLapEnd n).eigenspace 0 = ℝ ∙ (fun _ : Fin n => (1 : ℝ)) ∧
    finrank ℝ ((completeGraphLapEnd n).eigenspace (n : ℝ)) = n - 1 ∧
    (completeGraphLapEnd n).eigenspace (n : ℝ) = LinearMap.ker (sumFunctional n) :=
  ⟨finrank_eigenspace_zero n hn,
   eigenspace_zero_eq_span_ones n hn,
   finrank_eigenspace_n n hn,
   eigenspace_n_eq_ker_sumFunctional n⟩

end CompleteGraphSpectrum
