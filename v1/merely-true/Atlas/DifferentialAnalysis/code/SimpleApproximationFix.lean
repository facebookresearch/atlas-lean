/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Filter Set Finset
open scoped ENNReal NNReal

namespace SimpleApproximation

variable {X : Type*} [MeasurableSpace X]

/-- At any point `x` where the `k`-th rational test value `r_k` satisfies
`r_k ≤ f x`, the standard `eapprox` simple-function approximation at stage
`n > k` also satisfies `r_k ≤ eapprox f n x`. -/
lemma eapprox_ge_ennrealRatEmbed {f : X → ℝ≥0∞} (hf : Measurable f)
    {k n : ℕ} (hk : k < n) (x : X) (h : SimpleFunc.ennrealRatEmbed k ≤ f x) :
    SimpleFunc.ennrealRatEmbed k ≤ SimpleFunc.eapprox f n x := by
  simp only [SimpleFunc.eapprox, SimpleFunc.approx_apply x hf]
  exact Finset.le_sup_of_le (Finset.mem_range.mpr hk) (if_pos h ▸ le_refl _)

/-- A rational lower bound on `f x` is preserved by the standard simple-function
approximation `eapprox f n` once `n` exceeds the encoding index of the
rational. -/
lemma eapprox_ge_of_rational {f : X → ℝ≥0∞} (hf : Measurable f)
    (q : ℚ) (x : X) (hqf : (ENNReal.ofNNReal (Real.toNNReal q)) ≤ f x)
    {n : ℕ} (hn : Encodable.encode q < n) :
    (ENNReal.ofNNReal (Real.toNNReal q)) ≤ SimpleFunc.eapprox f n x := by
  have h1 : SimpleFunc.ennrealRatEmbed (Encodable.encode q) ≤ f x := by
    rwa [SimpleFunc.ennrealRatEmbed_encode]
  have h2 := eapprox_ge_ennrealRatEmbed hf hn x h1
  rwa [SimpleFunc.ennrealRatEmbed_encode] at h2

/-- A small bridge lemma: the nonnegative real reduction of the rational
`k / d` (for naturals `k, d`) equals the corresponding `NNReal` quotient. -/
lemma toNNReal_nat_div (k d : ℕ) :
    Real.toNNReal ((k : ℚ) / (d : ℚ) : ℚ) = (k : ℝ≥0) / (d : ℝ≥0) := by
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [Real.toNNReal_div (Nat.cast_nonneg k)]
  simp [Real.toNNReal_coe_nat]

/-- Uniform `ε`-approximation of a measurable `[0, ∞]`-valued function `f`
on the set where `f ≤ M`: there is an `N` such that for all `n ≥ N`, every
point `x` with `f x ≤ M` satisfies `f x − eapprox f n x ≤ ε`. -/
theorem eapprox_uniform_on_bounded {f : X → ℝ≥0∞} (hf : Measurable f)
    (M : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, f x ≤ ↑M →
      f x - SimpleFunc.eapprox f n x ≤ ε := by

  by_cases hε_top : ε = ⊤
  · exact ⟨0, fun n _ x _ => by simp [hε_top]⟩

  set ε' := ε.toNNReal with hε'_def
  have hε'_pos : 0 < ε' := ENNReal.toNNReal_pos (ne_of_gt hε) hε_top
  have hε_eq : ε = ↑ε' := (ENNReal.coe_toNNReal hε_top).symm

  obtain ⟨d, hd⟩ := exists_nat_gt (ε'⁻¹ : ℝ≥0)
  have hd_pos : 0 < d := by
    by_contra h
    simp only [not_lt, Nat.le_zero] at h
    subst h; simp at hd
  have hd_inv : (d : ℝ≥0)⁻¹ ≤ ε' :=
    (inv_le_comm₀ (Nat.cast_pos.mpr hd_pos) hε'_pos).mpr (le_of_lt hd)

  set K := Nat.ceil (M * d : ℝ≥0) with hK_def

  set N := 1 + (Finset.range (K + 1)).sup
    (fun k => Encodable.encode ((k : ℚ) / (d : ℚ))) with hN_def

  refine ⟨N, fun n hn x hfx => ?_⟩

  have hfx_ne_top : f x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hfx

  set v := (f x).toNNReal with hv_def
  have hv_eq : f x = ↑v := (ENNReal.coe_toNNReal hfx_ne_top).symm
  have hv_le : v ≤ M := by
    rwa [← ENNReal.coe_le_coe, ← hv_eq]

  set k₀ := Nat.floor (v * d : ℝ≥0) with hk₀_def

  set q₀ : ℚ := (k₀ : ℚ) / (d : ℚ) with hq₀_def

  have hq₀_nonneg : (0 : ℚ) ≤ q₀ := by positivity

  have hq₀_nnreal : Real.toNNReal q₀ = (k₀ : ℝ≥0) / (d : ℝ≥0) :=
    toNNReal_nat_div k₀ d

  have hk₀d_le_v : (k₀ : ℝ≥0) / (d : ℝ≥0) ≤ v := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hd_pos)]
    exact_mod_cast Nat.floor_le (v * d).2

  have herr : v - (k₀ : ℝ≥0) / (d : ℝ≥0) ≤ ε' := by
    calc v - (k₀ : ℝ≥0) / (d : ℝ≥0)
        ≤ (d : ℝ≥0)⁻¹ := by
          rw [tsub_le_iff_right, inv_eq_one_div, ← add_div,
              le_div_iff₀ (Nat.cast_pos.mpr hd_pos), add_comm]
          exact le_of_lt (mod_cast Nat.lt_floor_add_one (v * d : ℝ≥0))
      _ ≤ ε' := hd_inv

  have hk₀_le_K : k₀ ≤ K := by
    exact le_trans (Nat.floor_le_ceil _)
      (Nat.ceil_le_ceil (mul_le_mul_left hv_le d))

  have henc : Encodable.encode q₀ < N := by
    rw [hN_def]
    have hk₀_mem : k₀ ∈ Finset.range (K + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk₀_le_K)
    have hsup : Encodable.encode q₀ ≤ (Finset.range (K + 1)).sup
        (fun k => Encodable.encode ((k : ℚ) / (d : ℚ))) := by
      rw [hq₀_def]
      exact @Finset.le_sup ℕ ℕ _ _ (Finset.range (K + 1))
        (fun k => Encodable.encode ((↑k : ℚ) / (↑d : ℚ))) k₀ hk₀_mem
    omega
  have henc_n : Encodable.encode q₀ < n := lt_of_lt_of_le henc hn

  have hq₀_le_fx : (ENNReal.ofNNReal (Real.toNNReal q₀)) ≤ f x := by
    rw [hq₀_nnreal, hv_eq]
    exact ENNReal.coe_le_coe.mpr hk₀d_le_v

  have heapprox_ge : (↑((k₀ : ℝ≥0) / (d : ℝ≥0)) : ℝ≥0∞) ≤ SimpleFunc.eapprox f n x := by
    have := eapprox_ge_of_rational hf q₀ x hq₀_le_fx henc_n
    rwa [hq₀_nnreal] at this

  calc f x - SimpleFunc.eapprox f n x
      ≤ f x - ↑((k₀ : ℝ≥0) / (d : ℝ≥0)) := tsub_le_tsub_left heapprox_ge _
    _ = ↑v - ↑((k₀ : ℝ≥0) / (d : ℝ≥0)) := by rw [hv_eq]
    _ = ↑(v - (k₀ : ℝ≥0) / (d : ℝ≥0)) := (ENNReal.coe_sub).symm
    _ ≤ ↑ε' := ENNReal.coe_le_coe.mpr herr
    _ = ε := hε_eq.symm

/-- Melrose Prop. 3.3 (Simple approximation): every measurable `[0, ∞]`-valued
function `f` is the pointwise limit of an increasing sequence of measurable
simple functions, with uniform approximation on every set `{f ≤ M}`. -/
theorem exists_monotone_simple_approx_uniform {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∃ (g : ℕ → X → ℝ≥0∞),
      (∀ n, Measurable (g n)) ∧
      (∀ n, (Set.range (g n)).Finite) ∧
      (∀ n x, g n x ≤ g (n + 1) x) ∧
      (∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x))) ∧
      (∀ (M : ℝ≥0) {ε : ℝ≥0∞}, 0 < ε →
        ∃ N, ∀ n, N ≤ n → ∀ x, f x ≤ ↑M → f x - g n x ≤ ε) := by
  refine ⟨fun n => (↑(SimpleFunc.eapprox f n) : X → ℝ≥0∞), ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact (SimpleFunc.eapprox f n).measurable
  · intro n; exact (SimpleFunc.eapprox f n).finite_range
  · intro n x; exact SimpleFunc.monotone_eapprox f (Nat.le_succ n) x
  · intro x; exact SimpleFunc.tendsto_eapprox hf x
  · intro M ε hε; exact eapprox_uniform_on_bounded hf M hε

end SimpleApproximation
