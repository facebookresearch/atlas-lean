/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Atlas.DifferentialAnalysis.code.TemperedDistributions
import Atlas.DifferentialAnalysis.code.TestFunctions
import Atlas.DifferentialAnalysis.code.SobolevEmbedding

noncomputable section

open scoped BigOperators SchwartzMap LineDeriv

namespace DistributionalKernels

variable {n : ℕ}

/-- The size `|γ| = ∑ γ i` of a multi-index `γ : Fin n → ℕ`. -/
def multiIndexSize (γ : Fin n → ℕ) : ℕ := ∑ i, γ i

/-- The finite set of multi-indices `α` that are componentwise at most `γ`. -/
def multiIndexLeqFinset (γ : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i => Finset.range (γ i + 1)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The `m`-fold distributional partial derivative in coordinate `j`, acting on a tempered distribution. -/
def iterCoordDeriv (j : Fin n) (m : ℕ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  (fun u => TemperedDistributions.distribDerivCLM
    (EuclideanSpace.single j (1 : ℝ)) u)^[m] v

/-- The multi-index distributional derivative `D^γ v`, taken coordinate by coordinate. -/
def multiIndexDistribDeriv (γ : Fin n → ℕ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  (List.finRange n).foldl (fun w j => iterCoordDeriv j (γ j) w) v

/-- Multiplication of a tempered distribution by the power `⟨x⟩^k` of the Japanese bracket. -/
def distribMulBracketPow (k : ℤ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  TemperedDistributions.distribMulCLM
    (fun (x : EuclideanSpace ℝ (Fin n)) =>
      ((TestFunctions.japaneseBracket n x : ℝ) : ℂ) ^ k) v

/-- Multiplication of a tempered distribution by a real polynomial evaluated at `x`. -/
def distribMulPoly (p : MvPolynomial (Fin n) ℝ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  TemperedDistributions.distribMulCLM
    (fun (x : EuclideanSpace ℝ (Fin n)) =>
      ((MvPolynomial.eval (fun i => x i) p : ℝ) : ℂ)) v

/-- The right-hand side of the Leibniz expansion `D^γ (p ⟨x⟩^k v)`: a sum over `α ≤ γ` of `D^{γ-α}` applied to polynomial-times-bracket-power multiples of `v`. -/
def weightedDerivRHS (γ : Fin n → ℕ) (k : ℤ)
    (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  ∑ α ∈ multiIndexLeqFinset γ,
    multiIndexDistribDeriv (γ - α)
      (distribMulPoly (coeffs α)
        (distribMulBracketPow (k - 2 * ↑(multiIndexSize (γ - α))) v))

/-- `D^0 v = v`: the zero multi-index derivative is the identity. -/
lemma multiIndexDistribDeriv_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    multiIndexDistribDeriv 0 v = v := by
  simp [multiIndexDistribDeriv, iterCoordDeriv]

/-- Multiplication by the constant polynomial `1` leaves a tempered distribution unchanged. -/
lemma distribMulPoly_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    distribMulPoly (1 : MvPolynomial (Fin n) ℝ) v = v := by
  unfold distribMulPoly
  ext φ
  simp only [TemperedDistributions.distribMulCLM_apply]
  congr 1; ext x
  simp [map_one, one_smul]

/-- For `γ = 0`, the set of multi-indices `α ≤ γ` is the singleton `{0}`. -/
lemma multiIndexLeqFinset_zero :
    multiIndexLeqFinset (0 : Fin n → ℕ) = {0} := by
  ext α
  simp only [multiIndexLeqFinset, Fintype.mem_piFinset, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · intro h; ext i; have := h i; simp at this; omega
  · intro h; subst h; intro i; simp

/-- Zero iterations of a coordinate derivative leave the distribution unchanged. -/
lemma iterCoordDeriv_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j : Fin n) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j 0 v = v := by
  simp [iterCoordDeriv]

/-- Inductive step: `(m + 1)` iterations equal one iteration applied to `m` iterations. -/
lemma iterCoordDeriv_succ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j : Fin n) (m : ℕ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j (m + 1) v =
      iterCoordDeriv j 1 (iterCoordDeriv j m v) := by
  simp only [iterCoordDeriv, Function.iterate_succ_apply',
    Function.iterate_zero, Function.id_def]

/-- The zero multi-index has size zero. -/
lemma multiIndexSize_zero : multiIndexSize (0 : Fin n → ℕ) = 0 := by
  simp [multiIndexSize]

/-- For `γ = 0`, the weighted derivative RHS reduces to plain polynomial-times-bracket multiplication. -/
lemma weightedDerivRHS_zero_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (k : ℤ) (p : MvPolynomial (Fin n) ℝ)
    (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (hc : coeffs 0 = p)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    weightedDerivRHS (0 : Fin n → ℕ) k coeffs v =
      distribMulPoly p (distribMulBracketPow k v) := by
  unfold weightedDerivRHS
  rw [multiIndexLeqFinset_zero]
  simp only [Finset.sum_singleton]
  have h0 : (0 : Fin n → ℕ) - (0 : Fin n → ℕ) = 0 := by ext i; simp
  rw [h0, multiIndexDistribDeriv_zero, hc]
  congr 1
  have : multiIndexSize (0 : Fin n → ℕ) = 0 := multiIndexSize_zero
  simp [this]


/-- Directional distributional derivatives commute on `F`-valued tempered distributions. -/
lemma distribDeriv_comm_general {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v w : EuclideanSpace ℝ (Fin n))
    (T : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    TemperedDistributions.distribDerivCLM v (TemperedDistributions.distribDerivCLM w T) =
    TemperedDistributions.distribDerivCLM w (TemperedDistributions.distribDerivCLM v T) := by
  ext φ
  simp only [TemperedDistributions.distribDerivCLM_apply, map_neg, neg_neg]
  congr 1
  exact (SchwartzRepresentation.schwartz_lineDerivOp_comm v w φ).symm

/-- Single applications of `∂_{j₀}` and `∂_j` commute. -/
lemma iterCoordDeriv_one_comm_one {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j₀ j : Fin n) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j₀ 1 (iterCoordDeriv j 1 v) =
    iterCoordDeriv j 1 (iterCoordDeriv j₀ 1 v) := by
  simp only [iterCoordDeriv, Function.iterate_one]
  exact distribDeriv_comm_general _ _ _

/-- `∂_{j₀}` commutes with `∂_j^m` for any `m`. -/
lemma iterCoordDeriv_one_comm {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j₀ j : Fin n) (m : ℕ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j₀ 1 (iterCoordDeriv j m v) =
    iterCoordDeriv j m (iterCoordDeriv j₀ 1 v) := by
  induction m generalizing v with
  | zero => simp [iterCoordDeriv_zero]
  | succ m ih =>
    rw [iterCoordDeriv_succ j m v, iterCoordDeriv_succ j m (iterCoordDeriv j₀ 1 v)]
    rw [iterCoordDeriv_one_comm_one j₀ j (iterCoordDeriv j m v)]
    congr 1
    exact ih v

/-- `∂_{j₀}` commutes with any foldl of iterated coordinate derivatives. -/
lemma iterCoordDeriv_one_comm_foldl {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j₀ : Fin n) (γ : Fin n → ℕ) (l : List (Fin n))
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j₀ 1 (l.foldl (fun w j => iterCoordDeriv j (γ j) w) v) =
    l.foldl (fun w j => iterCoordDeriv j (γ j) w) (iterCoordDeriv j₀ 1 v) := by
  induction l generalizing v with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih (iterCoordDeriv i (γ i) v)]
    congr 1
    exact iterCoordDeriv_one_comm j₀ i (γ i) v

/-- Recursive step: peel off one factor of `∂_{j₀}` from `D^γ`, reducing `γ_{j₀}` by one. -/
theorem multiIndexDistribDeriv_step {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (γ : Fin n → ℕ) (j₀ : Fin n) (hj₀ : 0 < γ j₀)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    multiIndexDistribDeriv γ v =
      iterCoordDeriv j₀ 1
        (multiIndexDistribDeriv (Function.update γ j₀ (γ j₀ - 1)) v) := by
  unfold multiIndexDistribDeriv
  suffices h : ∀ (l : List (Fin n)) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)),
    l.Nodup →
    l.foldl (fun w j => iterCoordDeriv j (γ j) w) v =
    if j₀ ∈ l then
      iterCoordDeriv j₀ 1
        (l.foldl (fun w j => iterCoordDeriv j (Function.update γ j₀ (γ j₀ - 1) j) w) v)
    else
      l.foldl (fun w j => iterCoordDeriv j (Function.update γ j₀ (γ j₀ - 1) j) w) v by
    have hmem : j₀ ∈ List.finRange n := List.mem_finRange j₀
    rw [h (List.finRange n) v (List.nodup_finRange n)]
    simp only [hmem, if_true]
  intro l
  induction l with
  | nil => intro v _; simp
  | cons i l ih =>
    intro v hnd
    simp only [List.foldl_cons]
    obtain ⟨hni, hndl⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j₀
    · subst hij
      simp only [List.mem_cons_self, if_true, Function.update_self]
      have hγ_eq : γ i = (γ i - 1) + 1 := by omega
      rw [hγ_eq, iterCoordDeriv_succ]
      rw [ih (iterCoordDeriv i 1 (iterCoordDeriv i (γ i - 1) v)) hndl]
      simp only [hni, if_false]
      rw [iterCoordDeriv_one_comm_foldl]
      have : γ i - 1 + 1 - 1 = γ i - 1 := by omega
      simp only [this]

    · have hne : i ≠ j₀ := hij
      rw [Function.update_of_ne hne]
      rw [ih (iterCoordDeriv i (γ i) v) hndl]
      by_cases hmem : j₀ ∈ l
      · simp only [List.mem_cons_of_mem i hmem, if_true, hmem, if_true]
      · simp only [show ¬ (j₀ ∈ i :: l) from fun h => by
            rcases List.mem_cons.mp h with h | h
            · exact hne h.symm
            · exact hmem h, if_false, hmem, if_false]










end DistributionalKernels

end
