/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

open Finset

namespace Minkowski

variable {n : ℕ}

def minkowskiInner (n : ℕ) (v w : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin n, v (Fin.castSucc i) * w (Fin.castSucc i) -
    v (Fin.last n) * w (Fin.last n)

def IsPositiveDefiniteOn (S : Submodule ℝ (Fin (n + 1) → ℝ)) : Prop :=
  ∀ v : Fin (n + 1) → ℝ, v ∈ S → v ≠ 0 → minkowskiInner n v v > 0

def partials (f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)) (x : Fin n → ℝ) :
    Fin n → Fin (n + 1) → ℝ :=
  fun i => fderiv ℝ f x (Pi.single i 1)

structure SpacelikeHypersurface (n : ℕ) where
  U : Set (Fin n → ℝ)
  hU : IsOpen U
  f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  smooth : ContDiffOn ℝ ⊤ f U
  linearIndep : ∀ x ∈ U, LinearIndependent ℝ (partials f x)
  spacelike : ∀ x ∈ U, IsPositiveDefiniteOn
    (Submodule.span ℝ (Set.range (partials f x)))

def orientationMatrix (f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)) (x : Fin n → ℝ)
    (ν : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (i : Fin (n + 1)) (j : Fin (n + 1)) =>
    Fin.lastCases (ν i) (fun k => partials f x k i) j

structure IsGaussNormal {n : ℕ} (S : SpacelikeHypersurface n) (x : Fin n → ℝ)
    (ν : Fin (n + 1) → ℝ) : Prop where
  timelike : minkowskiInner n ν ν = -1
  orthogonal : ∀ i : Fin n, minkowskiInner n ν (partials S.f x i) = 0
  positive_orientation : (orientationMatrix S.f x ν).det > 0


theorem minkowskiInner_smul_self {n : ℕ} (c : ℝ) (v : Fin (n + 1) → ℝ) :
    minkowskiInner n (c • v) (c • v) = c ^ 2 * minkowskiInner n v v := by
  simp only [minkowskiInner, Pi.smul_apply, smul_eq_mul]
  have h₁ : ∑ x : Fin n, c * v (Fin.castSucc x) * (c * v (Fin.castSucc x)) =
      c ^ 2 * ∑ x : Fin n, v (Fin.castSucc x) * v (Fin.castSucc x) := by
    conv_lhs => arg 2; ext x; rw [show c * v (Fin.castSucc x) * (c * v (Fin.castSucc x)) =
      c ^ 2 * (v (Fin.castSucc x) * v (Fin.castSucc x)) from by ring]
    rw [← Finset.mul_sum]
  linarith


theorem minkowskiInner_smul_left {n : ℕ} (c : ℝ) (v w : Fin (n + 1) → ℝ) :
    minkowskiInner n (c • v) w = c * minkowskiInner n v w := by
  simp only [minkowskiInner, Pi.smul_apply, smul_eq_mul]
  have h₁ : ∑ x : Fin n, c * v (Fin.castSucc x) * w (Fin.castSucc x) =
    c * ∑ x : Fin n, v (Fin.castSucc x) * w (Fin.castSucc x) := by
      conv_lhs => arg 2; ext x; rw [show c * v (Fin.castSucc x) * w (Fin.castSucc x) =
        c * (v (Fin.castSucc x) * w (Fin.castSucc x)) from by ring]
      rw [← Finset.mul_sum]
  linarith

theorem minkowski_orthogonal_complement_positive_definite {n : ℕ}
    (X : Fin (n + 1) → ℝ) (hX : minkowskiInner n X X < 0) :
    ∀ Y : Fin (n + 1) → ℝ, Y ≠ 0 → minkowskiInner n X Y = 0 →
    minkowskiInner n Y Y > 0 := by
  intro Y hY horth
  simp only [minkowskiInner] at hX horth ⊢

  set Xn := X (Fin.last n)
  set Yn := Y (Fin.last n)
  set sXX := ∑ i : Fin n, X (Fin.castSucc i) * X (Fin.castSucc i)
  set sYY := ∑ i : Fin n, Y (Fin.castSucc i) * Y (Fin.castSucc i)
  set sXY := ∑ i : Fin n, X (Fin.castSucc i) * Y (Fin.castSucc i)

  have hXn_sq : sXX < Xn * Xn := by linarith

  have hXn_ne : Xn ≠ 0 := by
    intro h
    have h1 : sXX < 0 := by linarith [show Xn * Xn = 0 from by rw [h]; ring]
    have h2 : (0 : ℝ) ≤ sXX := Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (a := X (Fin.castSucc i))
    linarith

  have horth' : sXY = Xn * Yn := by linarith

  have hsYY_pos : 0 < sYY := by
    by_contra h
    push Not at h
    have hsYY_nn : (0 : ℝ) ≤ sYY := Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (a := Y (Fin.castSucc i))
    have hsYY_zero : sYY = 0 := le_antisymm h hsYY_nn

    have hYi_zero : ∀ i : Fin n, Y (Fin.castSucc i) = 0 := by
      intro i
      have h1 : (0 : ℝ) ≤ Y (Fin.castSucc i) * Y (Fin.castSucc i) :=
        mul_self_nonneg (a := Y (Fin.castSucc i))
      have h2 : Y (Fin.castSucc i) * Y (Fin.castSucc i) ≤ sYY :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (a := Y (Fin.castSucc j)))
          (Finset.mem_univ i)
      have h3 : Y (Fin.castSucc i) * Y (Fin.castSucc i) = 0 := by linarith
      exact mul_self_eq_zero.mp h3

    have hsXY_zero : sXY = 0 := by
      simp only [sXY]
      apply Finset.sum_eq_zero
      intro i _
      rw [hYi_zero i, mul_zero]
    rw [hsXY_zero] at horth'
    have hYn_zero : Yn = 0 := by
      rcases mul_eq_zero.mp horth'.symm with h | h
      · exact absurd h hXn_ne
      · exact h

    have hY_zero : Y = 0 := by
      ext j
      simp only [Pi.zero_apply]
      by_cases hj : j = Fin.last n
      · rw [hj]; exact hYn_zero
      · have : ∃ i : Fin n, Fin.castSucc i = j := by
          have hlt : j.val < n := by
            rcases j with ⟨val, hval⟩
            simp only [Fin.last, Fin.ext_iff] at hj
            exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hval) hj
          exact ⟨⟨j.val, hlt⟩, by simp [Fin.castSucc]⟩
        obtain ⟨i, rfl⟩ := this
        exact hYi_zero i

    exact absurd hY_zero hY

  have hCS : sXY ^ 2 ≤ sXX * sYY := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => X (Fin.castSucc i)) (fun i => Y (Fin.castSucc i))
    simp only [sq] at this ⊢
    exact this

  have hXn_sq_pos : (0 : ℝ) < Xn * Xn := by
    rcases ne_iff_lt_or_gt.mp hXn_ne with h | h
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h

  have hYn_sq : Yn * Yn * (Xn * Xn) = sXY * sXY := by
    rw [horth']; ring

  have hCS' : sXY * sXY ≤ sXX * sYY := by
    have := hCS; rw [sq] at this; exact this


  nlinarith

end Minkowski
