/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Atlas.AnAlgorithmistsToolkit.code.Lattices
noncomputable section

open Matrix Finset InnerProductSpace

namespace IntegerProgramming

def IP.IsFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ x : Fin n → ℤ, A *ᵥ ((↑) ∘ x) ≤ b

def Lattice (n : ℕ) (b : Fin n → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ c : Fin n → ℤ, y = ∑ i : Fin n, (c i : ℝ) • b i}



variable {n : ℕ}

def layerSpacingBound (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((m : ℝ) * ((m : ℝ) - 1)) / 4) * (2 / Real.sqrt m)

theorem layerSpacingBound_pos {m : ℕ} (hm : 0 < m) : 0 < layerSpacingBound m := by
  unfold layerSpacingBound
  apply mul_pos
  · exact Real.rpow_pos_of_pos (by norm_num : (2:ℝ) > 0) _
  · apply div_pos (by norm_num : (0:ℝ) < 2)
    exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)

def fritzJohnRadius (n : ℕ) : ℝ := (n : ℝ) * Real.sqrt n

def layerCountBound (k : ℕ) : ℕ :=
  if k = 0 then 1
  else ⌈2 * fritzJohnRadius k / layerSpacingBound k⌉₊ + 1

theorem layerCountBound_pos : ∀ k, 0 < layerCountBound k := by
  intro k; unfold layerCountBound; split <;> omega

def lenstraBound : ℕ → ℕ
  | 0 => 1
  | n + 1 => layerCountBound (n + 1) * lenstraBound n

theorem lenstraBound_pos : ∀ n, 0 < lenstraBound n := by
  intro n
  induction n with
  | zero => simp [lenstraBound]
  | succ n ih =>
    unfold lenstraBound
    exact Nat.mul_pos (layerCountBound_pos _) ih

theorem layerCountBound_ge_ceil_ratio (k : ℕ) (hk : 0 < k) :
    (layerCountBound k : ℝ) ≥ 2 * fritzJohnRadius k / layerSpacingBound k := by
  unfold layerCountBound
  simp [show k ≠ 0 from Nat.pos_iff_ne_zero.mp hk]
  have h1 : 2 * fritzJohnRadius k / layerSpacingBound k ≤
      (↑⌈2 * fritzJohnRadius k / layerSpacingBound k⌉₊ : ℝ) := Nat.le_ceil _
  linarith

def candidateBox (n : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(lenstraBound n : ℤ)) (lenstraBound n : ℤ))

theorem candidateBox_card (n : ℕ) :
    (candidateBox n).card = (2 * lenstraBound n + 1) ^ n := by
  unfold candidateBox
  rw [Fintype.card_piFinset_const]
  congr 1; simp [Int.card_Icc]; omega


theorem layerCountBound_le_lenstraBound (k n : ℕ) (hk : k ≤ n) :
    layerCountBound k ≤ lenstraBound n := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp [layerCountBound, lenstraBound]
  | succ n ih =>
    simp only [lenstraBound]
    by_cases hkn : k ≤ n
    · calc layerCountBound k ≤ lenstraBound n := ih hkn
        _ ≤ layerCountBound (n + 1) * lenstraBound n :=
            Nat.le_mul_of_pos_left _ (layerCountBound_pos _)
    · have : k = n + 1 := by omega
      subst this
      exact Nat.le_mul_of_pos_right _ (lenstraBound_pos n)





end IntegerProgramming
