/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.BigOperators

open scoped SchwartzMap

noncomputable section

namespace TemperedDistributions

variable
  {𝕜 : Type*} [NormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Japanese bracket `⟨x⟩ = √(1 + ‖x‖²)` on a normed space, a smooth weight comparable to `1 + ‖x‖`. -/
noncomputable def japaneseBracket {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  Real.sqrt (1 + ‖x‖ ^ 2)

/-- The Japanese bracket is nonnegative: `0 ≤ ⟨x⟩`. -/
theorem japaneseBracket_nonneg {E : Type*} [NormedAddCommGroup E] (x : E) :
    0 ≤ japaneseBracket x :=
  Real.sqrt_nonneg _

/-- The Japanese bracket is bounded above by `1 + ‖x‖`: `⟨x⟩ ≤ 1 + ‖x‖`. -/
theorem japaneseBracket_le_one_add_norm {E : Type*} [NormedAddCommGroup E] (x : E) :
    japaneseBracket x ≤ 1 + ‖x‖ :=
  sqrt_one_add_norm_sq_le x

/-- Reverse comparison: `1 + ‖x‖ ≤ √2 · ⟨x⟩`. -/
theorem one_add_norm_le_sqrt_two_mul_japaneseBracket
    {E : Type*} [NormedAddCommGroup E] (x : E) :
    1 + ‖x‖ ≤ Real.sqrt 2 * japaneseBracket x :=
  one_add_norm_le_sqrt_two_mul_sqrt x

/-- Monotone power version: `⟨x⟩^k ≤ (1 + ‖x‖)^k`. -/
theorem japaneseBracket_pow_le_one_add_norm_pow
    {E : Type*} [NormedAddCommGroup E] (x : E) (k : ℕ) :
    japaneseBracket x ^ k ≤ (1 + ‖x‖) ^ k :=
  pow_le_pow_left₀ (japaneseBracket_nonneg x) (japaneseBracket_le_one_add_norm x) k

/-- Reverse power comparison: `(1 + ‖x‖)^k ≤ (√2)^k · ⟨x⟩^k`. -/
theorem one_add_norm_pow_le_sqrt_two_pow_mul_japaneseBracket_pow
    {E : Type*} [NormedAddCommGroup E] (x : E) (k : ℕ) :
    (1 + ‖x‖) ^ k ≤ Real.sqrt 2 ^ k * japaneseBracket x ^ k := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_le_sqrt_two_mul_japaneseBracket x) k

/-- Each weighted derivative norm `(1 + ‖x‖)^k · ‖∂^n f(x)‖` is bounded by `2^K` times the supremum of Schwartz seminorms of order at most `K`. -/
theorem weighted_norm_le_sup_seminorm {K : ℕ} {k n : ℕ} (hk : k ≤ K) (hn : n ≤ K)
    (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤
      2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f :=
  SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K, K)) hk hn f x

/-- The monomial weighted norm `‖x‖^k · ‖∂^n f(x)‖` is bounded by the weighted norm `(1 + ‖x‖)^k · ‖∂^n f(x)‖`. -/
theorem monomial_norm_le_weighted_norm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤
      (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ := by
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) k

/-- The weighted `C^k` norm of a Schwartz function: the infimum of constants `c ≥ 0` bounding `(1 + ‖x‖)^K · ‖∂^n f(x)‖` uniformly in `x`. -/
noncomputable def weightedCkNorm (K n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }

/-- The set of bounds defining `weightedCkNorm K n f` is nonempty, using Schwartz decay. -/
theorem weightedCkNorm_bounds_nonempty (K n : ℕ) (f : 𝓢(E, F)) :
    { c : ℝ | 0 ≤ c ∧ ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }.Nonempty := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := f.decay 0 n
  obtain ⟨C_K, hCKpos, hCK⟩ := f.decay K n
  refine ⟨2 ^ K * (C₀ + C_K), by positivity, fun x => ?_⟩
  have hC0_bound : ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C₀ := by
    have := hC₀ x; simp only [pow_zero, one_mul] at this; exact this
  have hCK_bound : ‖x‖ ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C_K := hCK x

  have h1 : (1 + ‖x‖) ^ K ≤ 2 ^ (K - 1) * (1 ^ K + ‖x‖ ^ K) :=
    add_pow_le zero_le_one (norm_nonneg x) K
  have h2 : (2 : ℝ) ^ (K - 1) ≤ 2 ^ K :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le K 1)
  have hxK_nonneg : (0 : ℝ) ≤ 1 + ‖x‖ ^ K := by positivity
  have h3 : (1 : ℝ) ^ K + ‖x‖ ^ K = 1 + ‖x‖ ^ K := by simp [one_pow]
  have h_add_pow : (1 + ‖x‖) ^ K ≤ 2 ^ K * (1 + ‖x‖ ^ K) := by
    calc (1 + ‖x‖) ^ K ≤ 2 ^ (K - 1) * (1 ^ K + ‖x‖ ^ K) := h1
      _ = 2 ^ (K - 1) * (1 + ‖x‖ ^ K) := by rw [h3]
      _ ≤ 2 ^ K * (1 + ‖x‖ ^ K) := by
          exact mul_le_mul_of_nonneg_right h2 hxK_nonneg
  calc (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
      ≤ 2 ^ K * (1 + ‖x‖ ^ K) * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
        mul_le_mul_of_nonneg_right h_add_pow (norm_nonneg _)
    _ = 2 ^ K * (‖iteratedFDeriv ℝ n (⇑f) x‖ + ‖x‖ ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖) := by
        ring
    _ ≤ 2 ^ K * (C₀ + C_K) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hC0_bound, hCK_bound]

/-- The set of bounds defining `weightedCkNorm K n f` is bounded below by `0`. -/
theorem weightedCkNorm_bounds_bddBelow (K n : ℕ) (f : 𝓢(E, F)) :
    BddBelow { c : ℝ | 0 ≤ c ∧ ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c } :=
  ⟨0, fun _ hc => hc.1⟩

/-- `weightedCkNorm K n f` is nonnegative. -/
theorem weightedCkNorm_nonneg (K n : ℕ) (f : 𝓢(E, F)) :
    0 ≤ weightedCkNorm K n f :=
  le_csInf (weightedCkNorm_bounds_nonempty K n f) fun _ hc => hc.1

/-- Pointwise bound: each value `(1 + ‖x‖)^K · ‖∂^n f(x)‖` is dominated by `weightedCkNorm K n f`. -/
theorem le_weightedCkNorm (K n : ℕ) (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ weightedCkNorm K n f :=
  le_csInf (weightedCkNorm_bounds_nonempty K n f) fun _ hc => hc.2 x

/-- `weightedCkNorm K n f ≤ 2^K · sup_{m ≤ (K,K)} seminorm_m f`. -/
theorem weightedCkNorm_le_sup_seminorm {K : ℕ} {n : ℕ} (hn : n ≤ K) (f : 𝓢(E, F)) :
    weightedCkNorm K n f ≤
      2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  apply csInf_le (weightedCkNorm_bounds_bddBelow K n f)
  exact ⟨by positivity, fun x =>
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K, K)) le_rfl hn f x⟩

/-- Reverse comparison: any Schwartz seminorm of order `(k, n)` with `k ≤ K` is bounded by `weightedCkNorm K n f`. -/
theorem seminorm_le_weightedCkNorm {K : ℕ} {k n : ℕ} (hk : k ≤ K)
    (f : 𝓢(E, F)) :
    SchwartzMap.seminorm 𝕜 k n f ≤ weightedCkNorm K n f := by
  apply SchwartzMap.seminorm_le_bound 𝕜 k n f (weightedCkNorm_nonneg K n f)
  intro x
  have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) k
  have h2 : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ K :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1 + ‖x‖) hk
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖
      ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact le_trans h1 h2
    _ ≤ weightedCkNorm K n f := le_weightedCkNorm K n f x

/-- The maximum of `weightedCkNorm K n f` over derivative orders `n ≤ K`. -/
noncomputable def weightedCkNormSup (K : ℕ) (f : 𝓢(E, F)) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
    (fun n => weightedCkNorm (E := E) (F := F) K n f)

/-- Individual `weightedCkNorm K n f` is bounded by the supremum `weightedCkNormSup K f` when `n ≤ K`. -/
theorem weightedCkNorm_le_weightedCkNormSup (K : ℕ) {n : ℕ} (hn : n ≤ K)
    (f : 𝓢(E, F)) :
    weightedCkNorm (E := E) (F := F) K n f ≤ weightedCkNormSup (E := E) (F := F) K f := by
  unfold weightedCkNormSup
  exact Finset.le_sup' (fun n => weightedCkNorm (E := E) (F := F) K n f)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- Schwartz seminorms with `k, n ≤ K` are bounded by `weightedCkNormSup K f`. -/
theorem seminorm_le_weightedCkNormSup {K : ℕ} {k n : ℕ} (hk : k ≤ K) (hn : n ≤ K)
    (f : 𝓢(E, F)) :
    SchwartzMap.seminorm 𝕜 k n f ≤ weightedCkNormSup (E := E) (F := F) K f :=
  le_trans (seminorm_le_weightedCkNorm hk f) (weightedCkNorm_le_weightedCkNormSup K hn f)

/-- `weightedCkNormSup K f ≤ 2^K · sup_{m ≤ (K,K)} seminorm_m f`. -/
theorem weightedCkNormSup_le_sup_seminorm (K : ℕ) (f : 𝓢(E, F)) :
    weightedCkNormSup (E := E) (F := F) K f ≤
      2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  unfold weightedCkNormSup
  simp only [Finset.sup'_le_iff, Finset.mem_range]
  intro n hn
  exact weightedCkNorm_le_sup_seminorm (Nat.lt_succ_iff.mp hn) f

/-- The sum of all Schwartz seminorms of order at most `(K, K)` applied to `f`. -/
noncomputable def monomialDerivNormSum (K : ℕ) (f : 𝓢(E, F)) : ℝ :=
  (Finset.Iic (K, K)).sum (fun m => (SchwartzMap.seminorm 𝕜 m.1 m.2) f)

/-- `monomialDerivNormSum K f` is nonnegative. -/
theorem monomialDerivNormSum_nonneg (K : ℕ) (f : 𝓢(E, F)) :
    0 ≤ monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f :=
  Finset.sum_nonneg fun m _ => apply_nonneg (SchwartzMap.seminorm 𝕜 m.1 m.2) f

/-- The supremum of Schwartz seminorms over `Iic (K, K)` is bounded by their sum. -/
theorem sup_seminorm_le_monomialDerivNormSum (K : ℕ) (f : 𝓢(E, F)) :
    (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f ≤
      monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f := by
  unfold monomialDerivNormSum
  apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun m _ =>
    apply_nonneg (SchwartzMap.seminorm 𝕜 m.1 m.2) f)
  intro i hi
  exact Finset.single_le_sum (fun m _ => apply_nonneg (SchwartzMap.seminorm 𝕜 m.1 m.2) f) hi

/-- Cardinality of `Iic (K, K)` in `ℕ × ℕ` equals `(K + 1)^2`. -/
theorem card_Iic_pair (K : ℕ) :
    (Finset.Iic (K, K)).card = (K + 1) ^ 2 := by
  rw [Finset.card_Iic_prod]
  simp [Nat.card_Iic, sq]

/-- `weightedCkNormSup K f ≤ 2^K · monomialDerivNormSum K f`. -/
theorem weightedCkNormSup_le_two_pow_mul_monomialDerivNormSum (K : ℕ) (f : 𝓢(E, F)) :
    weightedCkNormSup (E := E) (F := F) K f ≤
      2 ^ K * monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f := by
  calc weightedCkNormSup (E := E) (F := F) K f
      ≤ 2 ^ K * (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f :=
        weightedCkNormSup_le_sup_seminorm K f
    _ ≤ 2 ^ K * monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f := by
        apply mul_le_mul_of_nonneg_left (sup_seminorm_le_monomialDerivNormSum K f)
        positivity

/-- Reverse comparison: `monomialDerivNormSum K f ≤ (K + 1)^2 · weightedCkNormSup K f`. -/
theorem monomialDerivNormSum_le_sq_mul_weightedCkNormSup (K : ℕ) (f : 𝓢(E, F)) :
    monomialDerivNormSum (𝕜 := 𝕜) (E := E) (F := F) K f ≤
      ((K + 1) ^ 2 : ℕ) * weightedCkNormSup (E := E) (F := F) K f := by
  unfold monomialDerivNormSum
  have hbound : ∀ m ∈ Finset.Iic (K, K),
      (SchwartzMap.seminorm 𝕜 m.1 m.2) f ≤ weightedCkNormSup (E := E) (F := F) K f := by
    intro m hm
    exact seminorm_le_weightedCkNormSup (Finset.mem_Iic.mp hm).1 (Finset.mem_Iic.mp hm).2 f
  have h1 := Finset.sum_le_card_nsmul _ _ _ hbound
  rw [card_Iic_pair] at h1
  rwa [nsmul_eq_mul] at h1

end TemperedDistributions

namespace MultiIndexBridge

open scoped SchwartzMap

noncomputable section

variable {m : ℕ}

/-- The order `|α| = ∑ αᵢ` of a multi-index `α : Fin m → ℕ`. -/
def multiIndexOrder (α : Fin m → ℕ) : ℕ := ∑ i, α i

/-- From a tuple `σ : Fin n → Fin m` build the multi-index counting fibers of `σ`. -/
def tupleToMultiIndex {n : ℕ} (σ : Fin n → Fin m) : Fin m → ℕ :=
  fun i => (Finset.univ.filter (fun k => σ k = i)).card

/-- The total order of `tupleToMultiIndex σ` equals `n`, the length of the tuple. -/
theorem multiIndexOrder_tupleToMultiIndex {n : ℕ} (σ : Fin n → Fin m) :
    multiIndexOrder (tupleToMultiIndex σ) = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := σ)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_fin] at h
  simp only [multiIndexOrder, tupleToMultiIndex]
  exact h.symm

/-- Canonical tuple of unit direction vectors corresponding to a multi-index `β`, indexed by `Fin |β|`. -/
noncomputable def multiIndexDirections (β : Fin m → ℕ) :
    Fin (multiIndexOrder β) → EuclideanSpace ℝ (Fin m) :=
  fun k => EuclideanSpace.single ((finSigmaFinEquiv (n := β)).symm k).1 1

/-- Each entry of `multiIndexDirections β` is a standard basis vector. -/
theorem multiIndexDirections_eq_single (β : Fin m → ℕ) (k : Fin (multiIndexOrder β)) :
    ∃ i : Fin m, multiIndexDirections β k = EuclideanSpace.single i 1 :=
  ⟨_, rfl⟩

/-- Each direction vector in `multiIndexDirections β` has norm at most one. -/
theorem norm_multiIndexDirections_le (β : Fin m → ℕ) (k : Fin (multiIndexOrder β)) :
    ‖multiIndexDirections β k‖ ≤ 1 := by
  obtain ⟨i, hi⟩ := multiIndexDirections_eq_single β k
  rw [hi, PiLp.norm_single]
  simp

/-- The real monomial `x^α = ∏ᵢ (xᵢ)^(αᵢ)` associated to a multi-index `α`. -/
def realMonomial (α : Fin m → ℕ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∏ i : Fin m, (x i) ^ (α i)

/-- `|x^α| ≤ ‖x‖^{|α|}` for any multi-index `α`. -/
theorem abs_realMonomial_le_norm_pow (α : Fin m → ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    |realMonomial α x| ≤ ‖x‖ ^ multiIndexOrder α := by
  simp only [realMonomial, multiIndexOrder]
  rw [← Finset.prod_pow_eq_pow_sum, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le x i) _

/-- The mixed partial derivative `∂^β f(x)` of order `β`, expressed via the iterated Fréchet derivative applied to the canonical direction tuple. -/
noncomputable def multiIndexPartialDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β : Fin m → ℕ)
    (f : EuclideanSpace ℝ (Fin m) → F) (x : EuclideanSpace ℝ (Fin m)) : F :=
  (iteratedFDeriv ℝ (multiIndexOrder β) f x) (multiIndexDirections β)

/-- `‖∂^β f(x)‖ ≤ ‖D^{|β|} f(x)‖` where `D^k` is the iterated Fréchet derivative. -/
theorem norm_multiIndexPartialDeriv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β : Fin m → ℕ)
    (f : EuclideanSpace ℝ (Fin m) → F) (x : EuclideanSpace ℝ (Fin m)) :
    ‖multiIndexPartialDeriv β f x‖ ≤ ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ := by
  simp only [multiIndexPartialDeriv]
  calc ‖(iteratedFDeriv ℝ (multiIndexOrder β) f x) (multiIndexDirections β)‖
      ≤ ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ * ∏ k, ‖multiIndexDirections β k‖ :=
        (iteratedFDeriv ℝ (multiIndexOrder β) f x).le_opNorm _
    _ ≤ ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ * 1 := by
        gcongr
        apply Finset.prod_le_one (fun k _ => norm_nonneg _)
        intro k _
        exact norm_multiIndexDirections_le β k
    _ = ‖iteratedFDeriv ℝ (multiIndexOrder β) f x‖ := mul_one _

end
end MultiIndexBridge



namespace MultiIndexBridge

open scoped SchwartzMap
noncomputable section

variable {𝕜 : Type*} [NormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- `|x^α| · ‖D^{|β|} f(x)‖` is bounded by the Schwartz seminorm of order `(|α|, |β|)`. -/
theorem monomial_iteratedFDeriv_le_seminorm
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F))
    (x : EuclideanSpace ℝ (Fin m)) :
    |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ ≤
      SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
  calc |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖
      ≤ ‖x‖ ^ multiIndexOrder α * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
        mul_le_mul_of_nonneg_right (abs_realMonomial_le_norm_pow α x) (norm_nonneg _)
    _ ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
        SchwartzMap.le_seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f x

/-- The Euclidean norm is bounded by the sum of coordinate absolute values: `‖x‖ ≤ ∑ |xᵢ|`. -/
theorem norm_le_sum_abs (x : EuclideanSpace ℝ (Fin m)) :
    ‖x‖ ≤ ∑ i : Fin m, |x i| := by
  refine le_of_sq_le_sq ?_ (Finset.sum_nonneg fun i _ => abs_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq]
  calc ∑ i : Fin m, (x i) ^ 2
      = ∑ i : Fin m, |x i| ^ 2 := by
        congr 1; ext i; rw [sq_abs]
    _ ≤ (∑ i : Fin m, |x i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg (x i))

/-- Power-of-norm bound: `‖x‖^(k+1) ≤ m^k · ∑ |xᵢ|^(k+1)` for `x ∈ ℝ^m`. -/
theorem norm_pow_le_sum_coord_pow (x : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    ‖x‖ ^ (k + 1) ≤ (m : ℝ) ^ k * ∑ i : Fin m, |x i| ^ (k + 1) := by
  calc ‖x‖ ^ (k + 1)
      ≤ (∑ i : Fin m, |x i|) ^ (k + 1) :=
        pow_le_pow_left₀ (norm_nonneg x) (norm_le_sum_abs x) (k + 1)
    _ ≤ (↑(Finset.univ : Finset (Fin m)).card : ℝ) ^ k *
          ∑ i ∈ Finset.univ, |x i| ^ (k + 1) := by
        exact pow_sum_le_card_mul_sum_pow
          (fun i _ => abs_nonneg (x i)) k
    _ = (m : ℝ) ^ k * ∑ i : Fin m, |x i| ^ (k + 1) := by
        rw [Finset.card_fin]

/-- Single-coordinate multi-index: `k` at position `i`, zero elsewhere. -/
def coordMultiIndex (k : ℕ) (i : Fin m) : Fin m → ℕ :=
  fun j => if j = i then k else 0

/-- The order of the single-coordinate multi-index `coordMultiIndex k i` equals `k`. -/
theorem multiIndexOrder_coordMultiIndex (k : ℕ) (i : Fin m) :
    multiIndexOrder (coordMultiIndex k i) = k := by
  simp only [multiIndexOrder, coordMultiIndex]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]

/-- `|xᵢ|^k = |x^{coordMultiIndex k i}|`: a coordinate power matches the corresponding monomial. -/
theorem abs_coord_pow_eq_abs_realMonomial (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (k : ℕ) :
    |x i| ^ k = |realMonomial (coordMultiIndex k i) x| := by
  simp only [realMonomial, coordMultiIndex]
  rw [Finset.abs_prod]
  have : ∀ j : Fin m, |x j ^ (if j = i then k else 0)| =
      if j = i then |x j| ^ k else 1 := by
    intro j
    split_ifs with h
    · rw [abs_pow]
    · simp
  simp_rw [this]
  rw [Finset.prod_ite_eq']
  simp [Finset.mem_univ]

/-- The finset of all multi-indices `α : Fin m → ℕ` with each `αᵢ ≤ K`. -/
def boundedMultiIndices (m K : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m => Finset.range (K + 1))

/-- Membership criterion: `α ∈ boundedMultiIndices m K ↔ ∀ i, αᵢ ≤ K`. -/
theorem mem_boundedMultiIndices_iff (α : Fin m → ℕ) (K : ℕ) :
    α ∈ boundedMultiIndices m K ↔ ∀ i, α i ≤ K := by
  simp [boundedMultiIndices, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

/-- If the total order of `α` is at most `K`, then each coordinate is at most `K`. -/
theorem mem_boundedMultiIndices_of_multiIndexOrder_le {α : Fin m → ℕ} {K : ℕ}
    (hα : multiIndexOrder α ≤ K) :
    α ∈ boundedMultiIndices m K := by
  rw [mem_boundedMultiIndices_iff]
  intro i
  calc α i ≤ ∑ j, α j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = multiIndexOrder α := rfl
    _ ≤ K := hα

/-- Cardinality: there are `(K + 1)^m` multi-indices with each coordinate bounded by `K`. -/
theorem card_boundedMultiIndices (m K : ℕ) :
    (boundedMultiIndices m K).card = (K + 1) ^ m := by
  simp [boundedMultiIndices, Fintype.card_piFinset, Finset.card_range]

/-- Multi-indices `α` with total order `|α| ≤ K`. -/
def totalOrderBoundedMultiIndices (m K : ℕ) : Finset (Fin m → ℕ) :=
  (boundedMultiIndices m K).filter (fun α => multiIndexOrder α ≤ K)

/-- Membership: `α ∈ totalOrderBoundedMultiIndices m K ↔ |α| ≤ K`. -/
theorem mem_totalOrderBoundedMultiIndices_iff (α : Fin m → ℕ) (K : ℕ) :
    α ∈ totalOrderBoundedMultiIndices m K ↔ multiIndexOrder α ≤ K := by
  simp only [totalOrderBoundedMultiIndices, Finset.mem_filter]
  constructor
  · exact fun ⟨_, h⟩ => h
  · exact fun h => ⟨mem_boundedMultiIndices_of_multiIndexOrder_le h, h⟩

/-- `coordMultiIndex k i` belongs to `totalOrderBoundedMultiIndices m K` when `k ≤ K`. -/
theorem coordMultiIndex_mem_totalOrderBoundedMultiIndices (k : ℕ) (i : Fin m) (K : ℕ)
    (hk : k ≤ K) :
    coordMultiIndex k i ∈ totalOrderBoundedMultiIndices m K := by
  rw [mem_totalOrderBoundedMultiIndices_iff]
  rw [multiIndexOrder_coordMultiIndex]
  exact hk

/-- `tupleToMultiIndex σ` belongs to `totalOrderBoundedMultiIndices m K` whenever `n ≤ K`. -/
theorem tupleToMultiIndex_mem_totalOrderBoundedMultiIndices {n : ℕ} (σ : Fin n → Fin m)
    (K : ℕ) (hn : n ≤ K) :
    tupleToMultiIndex σ ∈ totalOrderBoundedMultiIndices m K := by
  rw [mem_totalOrderBoundedMultiIndices_iff, multiIndexOrder_tupleToMultiIndex]
  exact hn

/-- The monomial-mixed-derivative `sup` norm: the infimum of `c ≥ 0` with `|x^α| · ‖∂^β f(x)‖ ≤ c` for all `x`. -/
noncomputable def monomialDerivSupNorm
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ c }

/-- The set of bounds in `monomialDerivSupNorm` is nonempty, using Schwartz decay. -/
theorem monomialDerivSupNorm_bounds_nonempty
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, |realMonomial α x| *
      ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ c } := by
  obtain ⟨M, hMp, hMb⟩ := f.decay (multiIndexOrder α) (multiIndexOrder β)
  exact ⟨M, le_of_lt hMp, fun x =>
    calc |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖
        ≤ |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
          mul_le_mul_of_nonneg_left (norm_multiIndexPartialDeriv_le β (⇑f) x) (abs_nonneg _)
      _ ≤ ‖x‖ ^ multiIndexOrder α * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
          mul_le_mul_of_nonneg_right (abs_realMonomial_le_norm_pow α x) (norm_nonneg _)
      _ ≤ M := hMb x⟩

/-- The set of bounds in `monomialDerivSupNorm` is bounded below by `0`. -/
theorem monomialDerivSupNorm_bounds_bddBelow
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) :
    BddBelow { c | 0 ≤ c ∧ ∀ x, |realMonomial α x| *
      ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ c } :=
  ⟨0, fun _ ⟨hc, _⟩ => hc⟩

/-- `monomialDerivSupNorm α β f` is nonnegative. -/
theorem monomialDerivSupNorm_nonneg
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) :
    0 ≤ monomialDerivSupNorm α β f :=
  le_csInf (monomialDerivSupNorm_bounds_nonempty α β f) fun _ ⟨hc, _⟩ => hc

/-- Pointwise: `|x^α| · ‖∂^β f(x)‖ ≤ monomialDerivSupNorm α β f`. -/
theorem le_monomialDerivSupNorm
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F))
    (x : EuclideanSpace ℝ (Fin m)) :
    |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤
      monomialDerivSupNorm α β f :=
  le_csInf (monomialDerivSupNorm_bounds_nonempty α β f) fun _ ⟨_, hb⟩ => hb x

/-- Any uniform pointwise bound `M` dominates `monomialDerivSupNorm α β f`. -/
theorem monomialDerivSupNorm_le_bound
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F))
    {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ M) :
    monomialDerivSupNorm α β f ≤ M :=
  csInf_le (monomialDerivSupNorm_bounds_bddBelow α β f) ⟨hMp, hM⟩

/-- `monomialDerivSupNorm α β f` is bounded by the Schwartz seminorm of order `(|α|, |β|)`. -/
theorem monomialDerivSupNorm_le_seminorm
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) :
    monomialDerivSupNorm α β f ≤
      SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f := by
  apply monomialDerivSupNorm_le_bound α β f
    (apply_nonneg (SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β)) f)
  intro x
  calc |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖
      ≤ |realMonomial α x| * ‖iteratedFDeriv ℝ (multiIndexOrder β) (⇑f) x‖ :=
        mul_le_mul_of_nonneg_left (norm_multiIndexPartialDeriv_le β (⇑f) x) (abs_nonneg _)
    _ ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
        monomial_iteratedFDeriv_le_seminorm α β f x

/-- The book-style multi-index norm: sum of `monomialDerivSupNorm α β f` over all `|α|, |β| ≤ K`. -/
noncomputable def bookMultiIndexNorm (K : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) : ℝ :=
  ∑ α ∈ totalOrderBoundedMultiIndices m K, ∑ β ∈ totalOrderBoundedMultiIndices m K,
    monomialDerivSupNorm α β f

/-- `bookMultiIndexNorm K f` is nonnegative. -/
theorem bookMultiIndexNorm_nonneg (K : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) :
    0 ≤ bookMultiIndexNorm K f :=
  Finset.sum_nonneg fun α _ =>
    Finset.sum_nonneg fun β _ =>
      monomialDerivSupNorm_nonneg α β f

/-- Comparison: `bookMultiIndexNorm K f ≤ ((K + 1)^m)^2 · monomialDerivNormSum K f`. -/
theorem bookMultiIndexNorm_le_monomialDerivNormSum (K : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) :
    bookMultiIndexNorm K f ≤
      (((K + 1) ^ m : ℕ) ^ 2 : ℕ) *
        TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
  unfold bookMultiIndexNorm
  have hterm : ∀ α ∈ totalOrderBoundedMultiIndices m K,
      ∀ β ∈ totalOrderBoundedMultiIndices m K,
      monomialDerivSupNorm α β f ≤
        TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
    intro α hα β hβ
    rw [mem_totalOrderBoundedMultiIndices_iff] at hα hβ
    calc monomialDerivSupNorm α β f
        ≤ SchwartzMap.seminorm 𝕜 (multiIndexOrder α) (multiIndexOrder β) f :=
          monomialDerivSupNorm_le_seminorm α β f
      _ ≤ TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f :=
          Finset.single_le_sum
            (fun p _ => apply_nonneg (SchwartzMap.seminorm 𝕜 p.1 p.2) f)
            (Finset.mem_Iic.2 (Prod.mk_le_mk.2 ⟨hα, hβ⟩))
  have hcard_le : (totalOrderBoundedMultiIndices m K).card ≤ (K + 1) ^ m := by
    calc (totalOrderBoundedMultiIndices m K).card
        ≤ (boundedMultiIndices m K).card := Finset.card_filter_le _ _
      _ = (K + 1) ^ m := card_boundedMultiIndices m K
  have hinner : ∀ α ∈ totalOrderBoundedMultiIndices m K,
      ∑ β ∈ totalOrderBoundedMultiIndices m K, monomialDerivSupNorm α β f ≤
        ((K + 1) ^ m : ℕ) * TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
    intro α hα
    have h := Finset.sum_le_card_nsmul _ _ _ (fun β hβ => hterm α hα β hβ)
    rw [nsmul_eq_mul] at h
    calc ∑ β ∈ totalOrderBoundedMultiIndices m K, monomialDerivSupNorm α β f
        ≤ (totalOrderBoundedMultiIndices m K).card *
            TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := h
      _ ≤ ((K + 1) ^ m : ℕ) *
            TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard_le
          · exact TemperedDistributions.monomialDerivNormSum_nonneg K f
  have houter := Finset.sum_le_card_nsmul _ _ _ hinner
  rw [nsmul_eq_mul] at houter
  calc ∑ α ∈ totalOrderBoundedMultiIndices m K,
        ∑ β ∈ totalOrderBoundedMultiIndices m K, monomialDerivSupNorm α β f
      ≤ (totalOrderBoundedMultiIndices m K).card *
          (((K + 1) ^ m : ℕ) *
            TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f) := houter
    _ ≤ ((K + 1) ^ m : ℕ) *
          (((K + 1) ^ m : ℕ) *
            TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard_le
        · apply mul_nonneg
          · positivity
          · exact TemperedDistributions.monomialDerivNormSum_nonneg K f
    _ = (((K + 1) ^ m : ℕ) ^ 2 : ℕ) *
          TemperedDistributions.monomialDerivNormSum (𝕜 := 𝕜) K f := by
      push_cast; ring




/-- Decomposition of a Euclidean vector into the sum `v = ∑ᵢ vᵢ · eᵢ` over the standard basis. -/
lemma euclidean_sum_single_decomp (v : EuclideanSpace ℝ (Fin m)) :
    v = ∑ i : Fin m, (v i) • EuclideanSpace.single i (1 : ℝ) := by
  have h := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  rw [show (EuclideanSpace.basisFun (Fin m) ℝ).repr v = v from by
    simp [EuclideanSpace.basisFun]] at h
  simp only [show ∀ i, (EuclideanSpace.basisFun (Fin m) ℝ) i = EuclideanSpace.single i 1 from by
    intro i; simp [EuclideanSpace.basisFun]; rfl] at h
  exact h.symm

/-- Expansion of a continuous multilinear map `M` in the standard basis: `M v = ∑_σ (∏ₖ v_k (σ k)) · M (e_{σ k})`. -/
lemma multilinear_basis_expansion {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin m)) F)
    (v : Fin n → EuclideanSpace ℝ (Fin m)) :
    M v = ∑ σ : Fin n → Fin m,
      (∏ k, (v k) (σ k)) • M (fun k => EuclideanSpace.single (σ k) 1) := by
  conv_lhs =>
    rw [show v = fun k => ∑ i : Fin m, (v k i) • EuclideanSpace.single i 1 from
      funext (fun k => euclidean_sum_single_decomp (v k))]
  rw [M.map_sum_finset (fun k i => (v k i) • EuclideanSpace.single i 1) (fun _ => Finset.univ)]
  simp only [Fintype.piFinset_univ]
  congr 1; ext σ
  exact M.map_smul_univ (fun k => (v k) (σ k)) (fun k => EuclideanSpace.single (σ k) 1)

end

end MultiIndexBridge

namespace TemperedDistributions

open MultiIndexBridge
open scoped SchwartzMap

end TemperedDistributions

end

namespace TemperedDistributions

open scoped SchwartzMap
open MultiIndexBridge

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `⟨x⟩^K`-weighted `C^k` norm of a Schwartz function: the infimum of `c ≥ 0` bounding `⟨x⟩^K · ‖∂^n f(x)‖` uniformly. -/
noncomputable def japaneseBracketCkNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }

/-- The set of bounds for `japaneseBracketCkNorm K n f` is nonempty. -/
theorem japaneseBracketCkNorm_bounds_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) :
    { c : ℝ | 0 ≤ c ∧ ∀ x, japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }.Nonempty := by
  have h := weightedCkNorm_bounds_nonempty (E := E) K n f
  obtain ⟨c, hc0, hcb⟩ := h
  refine ⟨c, hc0, fun x => ?_⟩
  calc japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
      ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
        mul_le_mul_of_nonneg_right (japaneseBracket_pow_le_one_add_norm_pow x K) (norm_nonneg _)
    _ ≤ c := hcb x

/-- The set of bounds for `japaneseBracketCkNorm K n f` is bounded below by `0`. -/
theorem japaneseBracketCkNorm_bounds_bddBelow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) :
    BddBelow { c : ℝ | 0 ≤ c ∧ ∀ x, japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c } :=
  ⟨0, fun _ hc => hc.1⟩

/-- `japaneseBracketCkNorm K n f` is nonnegative. -/
theorem japaneseBracketCkNorm_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) :
    0 ≤ japaneseBracketCkNorm (F := F) K n f :=
  le_csInf (japaneseBracketCkNorm_bounds_nonempty K n f) fun _ hc => hc.1

/-- Pointwise: `⟨x⟩^K · ‖∂^n f(x)‖ ≤ japaneseBracketCkNorm K n f`. -/
theorem le_japaneseBracketCkNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) (x : E) :
    japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ japaneseBracketCkNorm K n f :=
  le_csInf (japaneseBracketCkNorm_bounds_nonempty K n f) fun _ ⟨_, hb⟩ => hb x

/-- `japaneseBracketCkNorm K n f ≤ weightedCkNorm K n f`. -/
theorem japaneseBracketCkNorm_le_weightedCkNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) :
    japaneseBracketCkNorm (F := F) K n f ≤ weightedCkNorm K n f := by
  apply csInf_le (japaneseBracketCkNorm_bounds_bddBelow K n f)
  refine ⟨weightedCkNorm_nonneg K n f, fun x => ?_⟩
  calc japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
      ≤ (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
        mul_le_mul_of_nonneg_right (japaneseBracket_pow_le_one_add_norm_pow x K) (norm_nonneg _)
    _ ≤ weightedCkNorm K n f := le_weightedCkNorm K n f x

/-- Reverse: `weightedCkNorm K n f ≤ (√2)^K · japaneseBracketCkNorm K n f`. -/
theorem weightedCkNorm_le_sqrt_two_pow_mul_japaneseBracketCkNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) :
    weightedCkNorm (E := E) K n f ≤
      Real.sqrt 2 ^ K * japaneseBracketCkNorm (F := F) K n f := by
  have hjb_nn := japaneseBracketCkNorm_nonneg (E := E) K n f
  apply csInf_le (weightedCkNorm_bounds_bddBelow K n f)
  refine ⟨mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) K) hjb_nn, fun x => ?_⟩
  have hle := le_japaneseBracketCkNorm (E := E) K n f x
  calc (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖
      ≤ (Real.sqrt 2 ^ K * japaneseBracket x ^ K) * ‖iteratedFDeriv ℝ n (⇑f) x‖ :=
        mul_le_mul_of_nonneg_right
          (one_add_norm_pow_le_sqrt_two_pow_mul_japaneseBracket_pow x K) (norm_nonneg _)
    _ = Real.sqrt 2 ^ K * (japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖) := by ring
    _ ≤ Real.sqrt 2 ^ K * japaneseBracketCkNorm K n f :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg (Real.sqrt_nonneg 2) K)

/-- The supremum of `japaneseBracketCkNorm K n f` over `n ≤ K`. -/
noncomputable def japaneseBracketCkNormSup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ) (f : 𝓢(E, F)) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
    (fun n => japaneseBracketCkNorm (E := E) (F := F) K n f)

/-- `japaneseBracketCkNormSup K f ≤ weightedCkNormSup K f`. -/
theorem japaneseBracketCkNormSup_le_weightedCkNormSup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ) (f : 𝓢(E, F)) :
    japaneseBracketCkNormSup (E := E) (F := F) K f ≤
      weightedCkNormSup (E := E) (F := F) K f := by
  apply Finset.sup'_le _ _ (fun n hn => ?_)
  calc japaneseBracketCkNorm K n f
      ≤ weightedCkNorm K n f := japaneseBracketCkNorm_le_weightedCkNorm K n f
    _ ≤ weightedCkNormSup K f :=
        Finset.le_sup' (fun n => weightedCkNorm (E := E) (F := F) K n f) hn

/-- Reverse: `weightedCkNormSup K f ≤ (√2)^K · japaneseBracketCkNormSup K f`. -/
theorem weightedCkNormSup_le_sqrt_two_pow_mul_japaneseBracketCkNormSup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ) (f : 𝓢(E, F)) :
    weightedCkNormSup (E := E) (F := F) K f ≤
      Real.sqrt 2 ^ K * japaneseBracketCkNormSup (E := E) (F := F) K f := by
  apply Finset.sup'_le _ _ (fun n hn => ?_)
  calc weightedCkNorm K n f
      ≤ Real.sqrt 2 ^ K * japaneseBracketCkNorm (F := F) K n f :=
        weightedCkNorm_le_sqrt_two_pow_mul_japaneseBracketCkNorm K n f
    _ ≤ Real.sqrt 2 ^ K * japaneseBracketCkNormSup K f :=
        mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun n => japaneseBracketCkNorm (E := E) (F := F) K n f) hn)
          (pow_nonneg (Real.sqrt_nonneg 2) K)

end

end TemperedDistributions

