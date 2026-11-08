/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.DisagreementStability
import Atlas.BooleanFunctions.code.UniqueGames

open Finset BigOperators

namespace BooleanFourier

theorem fourierCoeff_chi_singleton {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :
    fourierCoeff (chi {i}) S = if S = {i} then 1 else 0 := by
  classical
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos
  simp only [fourierCoeff, one_div]

  have h := sum_chi_mul_chi_eq ({i} : Finset (Fin n)) S
  rw [show ∑ x : Fin n → Bool, chi ({i} : Finset (Fin n)) x * chi S x =
      ∑ x : Fin n → Bool, chi {i} x * chi S x from rfl] at h
  rw [h]
  simp only [eq_comm (a := ({i} : Finset (Fin n)))] at *
  split_ifs with heq
  ·
    exact inv_mul_cancel₀ h2n_ne
  ·
    exact mul_zero _

lemma chi_comp_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k))
    (x : Fin k → Bool) :
    chi S (x ∘ σ) = chi (S.image σ) x := by
  simp only [chi, Function.comp]

  symm
  exact Finset.prod_image (fun a _ b _ hab => σ.injective hab)

noncomputable def vertexAvgFunc {V W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGames.UniqueGame V W k) (f : W → (Fin k → Bool) → ℝ) (v : V) :
    (Fin k → Bool) → ℝ :=
  fun x => (1 / (game.left_degree : ℝ)) *
    ∑ e ∈ game.edges.filter (fun e => e.1 = v),
      f e.2 (x ∘ (game.constraint v e.2 : Equiv.Perm (Fin k)).symm)

theorem fourierCoeff_vertex_avg {V W : Type*} [DecidableEq V] [DecidableEq W] {k : ℕ}
    (game : UniqueGames.UniqueGame V W k)
    (f : W → (Fin k → Bool) → ℝ) (v : V) (S : Finset (Fin k)) :
    fourierCoeff (vertexAvgFunc game f v) S =
      (1 / (game.left_degree : ℝ)) *
        ∑ e ∈ game.edges.filter (fun e => e.1 = v),
          fourierCoeff (f e.2) (S.image (game.constraint v e.2)) := by
  simp only [fourierCoeff, vertexAvgFunc, one_div]

  have key : ∀ (w : W) (σ : Equiv.Perm (Fin k)),
      ∑ x : Fin k → Bool, f w (x ∘ ↑σ.symm) * chi S x =
      ∑ x : Fin k → Bool, f w x * chi (S.image σ) x := by
    intro w σ


    let bij : (Fin k → Bool) ≃ (Fin k → Bool) :=
      Equiv.arrowCongr σ.symm (Equiv.refl Bool)
    rw [← Equiv.sum_comp bij]
    congr 1
    funext y

    have hbij : bij y = y ∘ ↑σ := by
      ext i; simp [bij, Equiv.arrowCongr]

    have h1 : f w ((bij y) ∘ ↑σ.symm) = f w y := by
      congr 1; ext i; simp [hbij, Function.comp]

    have h2 : chi S (bij y) = chi (S.image σ) y := by
      rw [hbij]; exact chi_comp_perm σ S y
    rw [h1, h2]


  trans (game.left_degree : ℝ)⁻¹ *
    ∑ e ∈ game.edges.filter (fun e => e.1 = v),
      ((2 : ℝ) ^ k)⁻¹ * ∑ x : Fin k → Bool, f e.2 x * chi (S.image (game.constraint v e.2)) x
  ·
    trans (game.left_degree : ℝ)⁻¹ *
      ∑ e ∈ game.edges.filter (fun e => e.1 = v),
        ((2 : ℝ) ^ k)⁻¹ * ∑ x : Fin k → Bool,
          f e.2 (x ∘ ↑(game.constraint v e.2).symm) * chi S x
    ·

      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

    ·
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      exact key e.2 (game.constraint v e.2)
  ·
    rfl

theorem noiseStability_chi_singleton {n : ℕ} (ρ : ℝ) (i : Fin n) :
    noiseStability ρ (chi ({i} : Finset (Fin n))) = ρ := by
  rw [noiseStability_eq_sum]


  have h_coeff : ∀ S : Finset (Fin n),
      ρ ^ S.card * fourierCoeff (chi {i}) S ^ 2 =
        if S = {i} then ρ else 0 := by
    intro S
    rw [fourierCoeff_chi_singleton]
    split_ifs with h
    · subst h
      simp [Finset.card_singleton]
    · ring
  simp_rw [h_coeff]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]

theorem disagreementProb_dictator {n : ℕ} (ρ : ℝ) (i : Fin n) :
    disagreementProb ρ (chi ({i} : Finset (Fin n))) = (1 - ρ) / 2 := by
  rw [disagreementProb_eq, noiseStability_chi_singleton]

end BooleanFourier
