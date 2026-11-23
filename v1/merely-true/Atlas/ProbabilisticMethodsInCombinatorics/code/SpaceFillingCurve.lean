/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Finset NNReal ENNReal

namespace SpaceFillingCurve

/-- The unit square $[0,1]^2 \subseteq \mathbb{R}^2$. -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ j : Fin 2, p j ∈ Set.Icc (0 : ℝ) 1}

/-- Cyclic successor on `Fin n`: $i \mapsto (i + 1) \bmod n$. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩







/-- A distance bound $\mathrm{dist}(f(x), f(y)) \le C \cdot \mathrm{dist}(x, y)^r$ on a
pseudometric space upgrades to the mathlib `HolderWith` predicate. -/
lemma holderWith_of_dist_bound {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (C : ℝ≥0) (r : ℝ≥0) (f : X → Y)
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderWith C r f := by
  intro x y
  rw [edist_nndist, edist_nndist,
      ← ENNReal.coe_rpow_of_nonneg _ (NNReal.coe_nonneg r), ← ENNReal.coe_mul]
  exact ENNReal.coe_le_coe.mpr
    (by rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nndist]
        exact h x y)




/-- Squaring the Hölder-$1/2$ bound: $\mathrm{dist}(f(x), f(y))^2 \le C^2 \mathrm{dist}(x, y)$. -/
lemma holder_half_sq_bound {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C : ℝ≥0} {f : X → Y} (hf : HolderWith C (2⁻¹ : ℝ≥0) f) (x y : X) :
    dist (f x) (f y) ^ 2 ≤ (C : ℝ) ^ 2 * dist x y := by
  have h := hf.dist_le x y
  have hr : ((2⁻¹ : ℝ≥0) : ℝ) = (1/2 : ℝ) := by norm_num
  rw [hr] at h
  have hdist : (0 : ℝ) ≤ dist x y := dist_nonneg
  calc dist (f x) (f y) ^ 2
      ≤ (↑C * dist x y ^ (1/2 : ℝ)) ^ 2 := by
        apply sq_le_sq'
        · linarith [dist_nonneg (α := Y) (x := f x) (y := f y)]
        · exact h
    _ = C ^ 2 * (dist x y ^ (1/2 : ℝ)) ^ 2 := by ring
    _ = C ^ 2 * dist x y ^ (2 * (1/2 : ℝ)) := by
        rw [← Real.rpow_natCast (dist x y ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hdist]; norm_num
    _ = C ^ 2 * dist x y := by norm_num

/-- Telescoping sum over `Fin m`:
$\sum_{i=0}^{m-1} (f(i+1) - f(i)) = f(m) - f(0)$. -/
lemma fin_telescoping_sum (m : ℕ) (f : Fin (m + 1) → ℝ) :
    ∑ i : Fin m, (f ⟨i.val + 1, by omega⟩ - f ⟨i.val, by omega⟩) =
    f ⟨m, by omega⟩ - f ⟨0, by omega⟩ := by
  set g : ℕ → ℝ := fun k => if h : k < m + 1 then f ⟨k, h⟩ else 0
  have hg : ∀ k (hk : k < m + 1), g k = f ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hsum : ∑ i : Fin m, (f ⟨i.val + 1, by omega⟩ - f ⟨i.val, by omega⟩) =
    ∑ i : Fin m, (g (↑i + 1) - g ↑i) := by
    congr 1; ext i; rw [hg (↑i + 1) (by omega), hg ↑i (by omega)]
  rw [hsum, Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k) m,
      Finset.sum_range_sub g m, hg m (by omega), hg 0 (by omega)]

/-- For a monotone sequence valued in $[0,1]$, the total cyclic variation
$\sum_i |f(i) - f(i+1 \bmod n)|$ is at most $2$. -/
lemma monotone_cyclic_sum_le_two {n : ℕ} (f : Fin n → ℝ)
    (hf_mono : Monotone f) (hf_lo : ∀ i, 0 ≤ f i) (hf_hi : ∀ i, f i ≤ 1) :
    ∑ i : Fin n, |f i - f ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩| ≤ 2 := by
  rcases n with _ | m
  · simp
  suffices h : ∑ i : Fin (m + 1),
      |f i - f ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩| =
      2 * (f ⟨m, by omega⟩ - f ⟨0, by omega⟩) by
    rw [h]; linarith [hf_hi ⟨m, by omega⟩, hf_lo ⟨0, by omega⟩]
  have h_abs : ∀ i : Fin (m + 1),
      |f i - f ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩| =
      if h : i.val < m then f ⟨i.val + 1, by omega⟩ - f i
      else f ⟨m, by omega⟩ - f ⟨0, by omega⟩ := by
    intro i; split_ifs with hi
    · have heq : (⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) =
          ⟨i.val + 1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [heq, abs_sub_comm, abs_of_nonneg]
      linarith [hf_mono (show i ≤ (⟨i.val + 1, by omega⟩ : Fin (m + 1)) from
        Fin.mk_le_mk.mpr (by omega))]
    · have him : i.val = m := by omega
      rw [show (⟨(i.val + 1) % (m + 1), _⟩ : Fin (m + 1)) = ⟨0, by omega⟩ from
        Fin.ext (by simp [him]),
        show f i = f ⟨m, by omega⟩ from congr_arg f (Fin.ext him), abs_of_nonneg]
      linarith [hf_mono (show (⟨0, by omega⟩ : Fin (m + 1)) ≤ ⟨m, by omega⟩ from
        Fin.mk_le_mk.mpr (by omega))]
  simp_rw [h_abs]; rw [Fin.sum_univ_castSucc]
  have h_last : (if h : (Fin.last m).val < m then
      f ⟨(Fin.last m).val + 1, by omega⟩ - f (Fin.last m)
      else f ⟨m, by omega⟩ - f ⟨0, by omega⟩) = f ⟨m, by omega⟩ - f ⟨0, by omega⟩ := by
    simp [Fin.last]
  rw [h_last]
  have h_int : ∀ i : Fin m,
      (if h : (Fin.castSucc i).val < m then
        f ⟨(Fin.castSucc i).val + 1, by omega⟩ - f (Fin.castSucc i)
      else f ⟨m, by omega⟩ - f ⟨0, by omega⟩) =
      f ⟨i.val + 1, by omega⟩ - f ⟨i.val, by omega⟩ := by
    intro i; split_ifs with hi
    · simp only [Fin.val_castSucc] at hi ⊢; rfl
    · exfalso; exact hi i.isLt
  simp_rw [h_int]; linarith [fin_telescoping_sum m f]


end SpaceFillingCurve
