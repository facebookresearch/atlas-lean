/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Atlas.NumberTheoryI.code.HenselFactorization

noncomputable section

set_option linter.unusedSectionVars false

namespace NormedSpaceNorm

variable {K : Type*} [NontriviallyNormedField K]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]

theorem nullity (v : V) : ‖v‖ = 0 ↔ v = 0 := norm_eq_zero

end NormedSpaceNorm

namespace SupNorm

variable {K : Type*} [NontriviallyNormedField K]

end SupNorm

namespace FiniteDimensionalNormTopology

theorem complete
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V] :
    CompleteSpace V :=
  FiniteDimensional.complete K V

theorem linear_map_continuous
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    {E : Type*} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] [FiniteDimensional K E]
    {F : Type*} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F]
    (f : E →ₗ[K] F) : Continuous f :=
  LinearMap.continuous_of_finiteDimensional f

theorem completeSpace_and_continuous_linearMap
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] :
    (∀ (V : Type*) [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V],
      CompleteSpace V) ∧
    (∀ {E : Type*} [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] [FiniteDimensional K E]
      {F : Type*} [AddCommGroup F] [Module K F] [TopologicalSpace F]
      [IsTopologicalAddGroup F] [ContinuousSMul K F]
      (f : E →ₗ[K] F), Continuous f) :=
  ⟨fun V => complete K V, fun f => linear_map_continuous K f⟩

end FiniteDimensionalNormTopology


namespace AbsoluteValueExtension

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]


instance algebraIsAlgebraic : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

theorem spectralNorm_extends_norm (k : K) :
    spectralNorm K L (algebraMap K L k) = ‖k‖ :=
  spectralNorm_extends k

theorem spectralNorm_unique_extension (f : AbsoluteValue L ℝ)
    (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖)
    (x : L) : f x = spectralNorm K L x :=
  spectralNorm_unique_field_norm_ext hf_ext x

theorem finiteExtension_completeSpace : @CompleteSpace L (spectralNorm.uniformSpace K L) :=
  spectralNorm.completeSpace K L

theorem spectralNorm_le_one_iff_minpoly_coeff_norm_le_one (x : L) :
    spectralNorm K L x ≤ 1 ↔ ∀ (i : ℕ), ‖(minpoly K x).coeff i‖ ≤ 1 := by
  have hx_int : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  exact spectralValue_le_one_iff (minpoly.monic hx_int)


lemma norm_algebraMap_unit_eq_one
    {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [NormedField F]
    [Algebra R F] [IsFractionRing R F]
    (hbdd : ∀ r : R, ‖algebraMap R F r‖ ≤ 1)
    {x : R} (hu : IsUnit x) :
    ‖algebraMap R F x‖ = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have h1 := hbdd (u : R)
  have h2 := hbdd (↑u⁻¹ : R)
  have h3 : ‖algebraMap R F (u : R)‖ * ‖algebraMap R F (↑u⁻¹ : R)‖ = 1 := by
    rw [← norm_mul, ← map_mul]; simp [Units.mul_inv]
  by_contra hne
  linarith [lt_of_le_of_ne h1 hne,
            mul_le_mul_of_nonneg_left h2 (norm_nonneg (algebraMap R F (u : R)))]

lemma dvd_pow_of_norm_le_pow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {F : Type*} [NormedField F] [Algebra R F] [IsFractionRing R F]
    (hbdd : ∀ r : R, ‖algebraMap R F r‖ ≤ 1)
    (hnu : ∀ r : R, ¬IsUnit r → ‖algebraMap R F r‖ < 1)
    {π : R} (hπ : Irreducible π)
    (x : R) (n : ℕ) (hx : ‖algebraMap R F x‖ ≤ ‖algebraMap R F π‖ ^ n) :
    π ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hπ_lt : ‖algebraMap R F π‖ < 1 := hnu π hπ.1
    have hπ_pos : 0 < ‖algebraMap R F π‖ := by
      rw [norm_pos_iff]
      exact fun h0 => hπ.ne_zero ((IsFractionRing.injective R F) (by rwa [map_zero]))
    have hx_lt : ‖algebraMap R F x‖ < 1 := calc
      ‖algebraMap R F x‖ ≤ ‖algebraMap R F π‖ ^ (n + 1) := hx
      _ ≤ ‖algebraMap R F π‖ ^ 1 :=
          pow_le_pow_of_le_one hπ_pos.le hπ_lt.le (by omega)
      _ < 1 := by rwa [pow_one]
    have hx_nonunit : ¬IsUnit x := fun hu =>
      absurd (norm_algebraMap_unit_eq_one hbdd hu ▸ hx_lt) (not_lt.mpr le_rfl)
    obtain ⟨c, hc⟩ : π ∣ x := by
      have hmem : x ∈ IsLocalRing.maximalIdeal R := by
        by_contra h; exact hx_nonunit (IsLocalRing.notMem_maximalIdeal.mp h)
      rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    rw [hc, pow_succ, mul_comm (π ^ n) π]
    exact mul_dvd_mul_left π (ih c (by
      rw [hc, map_mul, norm_mul] at hx; rw [pow_succ] at hx
      nlinarith [mul_comm (‖algebraMap R F π‖ ^ n) (‖algebraMap R F π‖)]))

theorem isPrecomplete_maximalIdeal_of_completeSpace_fractionField
    (F : Type*) [NormedField F] [CompleteSpace F]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R F] [IsFractionRing R F]
    (hbdd : ∀ r : R, ‖algebraMap R F r‖ ≤ 1)
    (hnu : ∀ r : R, ¬IsUnit r → ‖algebraMap R F r‖ < 1)
    (hbdd_surj : ∀ x : F, ‖x‖ ≤ 1 → ∃ r : R, algebraMap R F r = x) :
    IsPrecomplete (IsLocalRing.maximalIdeal R) R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ_lt : ‖algebraMap R F π‖ < 1 := hnu π hπ.1
  constructor
  intro f hf
  set g : ℕ → F := fun n => algebraMap R F (f n)

  have hdiff : ∀ {m n : ℕ}, m ≤ n → ‖g m - g n‖ ≤ ‖algebraMap R F π‖ ^ m := by
    intro m n hmn
    simp only [g, ← map_sub]
    have hmem : f m - f n ∈ (IsLocalRing.maximalIdeal R) ^ m := by
      have := SModEq.sub_mem.mp (hf hmn); simpa using this
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [hc, map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hbdd c)

  have hcauchy : CauchySeq g := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hπ_lt
    exact ⟨N, fun n hn => by
      rw [dist_eq_norm, norm_sub_rev]; exact lt_of_le_of_lt (hdiff hn) hN⟩

  obtain ⟨L', hL'⟩ := cauchySeq_tendsto_of_complete hcauchy

  have hL'_bdd : ‖L'‖ ≤ 1 :=
    le_of_tendsto hL'.norm (Filter.Eventually.of_forall (fun n => hbdd (f n)))

  obtain ⟨L, hL⟩ := hbdd_surj L' hL'_bdd

  have hconv_rate : ∀ n, ‖g n - L'‖ ≤ ‖algebraMap R F π‖ ^ n := fun n =>
    le_of_tendsto (tendsto_const_nhds.sub hL').norm
      (Filter.eventually_atTop.mpr ⟨n, fun k hk => hdiff hk⟩)

  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem]
  suffices f n - L ∈ (IsLocalRing.maximalIdeal R) ^ n by simpa
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact dvd_pow_of_norm_le_pow hbdd hnu hπ (f n - L) n (by
    simp only [map_sub, hL]; exact hconv_rate n)









theorem spectralNorm_extension_exists_unique :
    (∀ (k : K), spectralNorm K L (algebraMap K L k) = ‖k‖) ∧
    (∀ (f : AbsoluteValue L ℝ) (hf_ext : ∀ (x : K), f (algebraMap K L x) = ‖x‖)
      (x : L), f x = spectralNorm K L x) :=
  ⟨spectralNorm_extends_norm K L, spectralNorm_unique_extension K L⟩

theorem finiteExtension_complete_and_valuation_ring :
    @CompleteSpace L (spectralNorm.uniformSpace K L) ∧
    (∀ (x : L), spectralNorm K L x ≤ 1 ↔ ∀ (i : ℕ), ‖(minpoly K x).coeff i‖ ≤ 1) :=
  ⟨finiteExtension_completeSpace K L, spectralNorm_le_one_iff_minpoly_coeff_norm_le_one K L⟩


end AbsoluteValueExtension

namespace ValuationFormula

lemma val_one {L : Type*} [Field L] (v : L → ℤ)
    (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b) :
    v 1 = 0 := by
  have h := hv 1 1 one_ne_zero one_ne_zero; simp at h; linarith

lemma val_inv {L : Type*} [Field L] (v : L → ℤ)
    (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)
    (a : L) (ha : a ≠ 0) : v a⁻¹ = -v a := by
  have h := hv a a⁻¹ ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha] at h
  linarith [val_one v hv]

lemma val_pow_nat {L : Type*} [Field L] (v : L → ℤ)
    (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)
    (a : L) (ha : a ≠ 0) (n : ℕ) : v (a ^ n) = (n : ℤ) * v a := by
  induction n with
  | zero => simp [val_one v hv]
  | succ n ih =>
    rw [pow_succ, hv _ _ (pow_ne_zero _ ha) ha, ih]
    push_cast; ring

lemma val_zpow {L : Type*} [Field L] (v : L → ℤ)
    (hv : ∀ a b : L, a ≠ 0 → b ≠ 0 → v (a * b) = v a + v b)
    (a : L) (ha : a ≠ 0) (n : ℤ) : v (a ^ n) = n * v a := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact val_pow_nat v hv a ha n
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [val_inv v hv _ (pow_ne_zero _ ha), val_pow_nat v hv a ha]
    simp [Int.negSucc_eq]; ring

lemma norm_zpow {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (x : L) (n : ℤ) : Algebra.norm K (x ^ n) = (Algebra.norm K x) ^ n := by
  cases n with
  | ofNat n => simp [zpow_natCast, map_pow]
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [Algebra.norm_inv, map_pow]

theorem dvr_norm_decomp
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (v_K : K → ℤ) (v_L : L → ℤ) (π_L : L)
    (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
    (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
    (hπ_L : π_L ≠ 0) (hπ_L_val : v_L π_L = 1)
    (x : L) (hx : x ≠ 0) :
    ∃ (u : L), u ≠ 0 ∧ v_L u = 0 ∧
      v_K (Algebra.norm K x) = v_K (Algebra.norm K u) + v_L x * v_K (Algebra.norm K π_L) := by

  set n := v_L x with hn_def
  set u := x * (π_L ^ n)⁻¹ with hu_def
  have hu_ne : u ≠ 0 := mul_ne_zero hx (inv_ne_zero (zpow_ne_zero _ hπ_L))
  refine ⟨u, hu_ne, ?_, ?_⟩
  ·
    rw [hu_def, hv_L _ _ hx (inv_ne_zero (zpow_ne_zero _ hπ_L))]
    rw [val_inv v_L hv_L _ (zpow_ne_zero _ hπ_L)]
    rw [val_zpow v_L hv_L π_L hπ_L n, hπ_L_val]
    ring
  ·
    have hx_eq : x = u * π_L ^ n := by
      rw [hu_def, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hπ_L), mul_one]
    rw [hx_eq, map_mul (Algebra.norm K), norm_zpow]

    have hNu_ne : Algebra.norm K u ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]; exact hu_ne
    have hNπ_pow_ne : (Algebra.norm K π_L) ^ n ≠ 0 :=
      zpow_ne_zero _ (by rw [Ne, Algebra.norm_eq_zero_iff]; exact hπ_L)
    rw [hv_K _ _ hNu_ne hNπ_pow_ne]
    congr 1
    exact val_zpow v_K hv_K _ (by rw [Ne, Algebra.norm_eq_zero_iff]; exact hπ_L) n

theorem norm_valuation_identity
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (v_K : K → ℤ) (v_L : L → ℤ) (π_L : L) (f_q : ℕ)
    (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
    (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
    (_hf_q : 0 < f_q)
    (hπ_L : π_L ≠ 0) (hπ_L_val : v_L π_L = 1)
    (h_unif_norm : v_K (Algebra.norm K π_L) = (f_q : ℤ))
    (h_unit_norm : ∀ u : L, u ≠ 0 → v_L u = 0 → v_K (Algebra.norm K u) = 0)
    (x : L) (hx : x ≠ 0) :
    v_K (Algebra.norm K x) = (f_q : ℤ) * v_L x := by


  obtain ⟨u, hu_ne, hu_unit, h_decomp⟩ :=
    dvr_norm_decomp v_K v_L π_L hv_K hv_L hπ_L hπ_L_val x hx
  rw [h_decomp]

  rw [h_unit_norm u hu_ne hu_unit]

  rw [h_unif_norm]

  ring

theorem valuation_formula
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (v_K : K → ℤ) (v_L : L → ℤ) (π_L : L) (f_q : ℕ)
    (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
    (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
    (hf_q : 0 < f_q)
    (hπ_L : π_L ≠ 0) (hπ_L_val : v_L π_L = 1)
    (h_unif_norm : v_K (Algebra.norm K π_L) = (f_q : ℤ))
    (h_unit_norm : ∀ u : L, u ≠ 0 → v_L u = 0 → v_K (Algebra.norm K u) = 0)
    (x : L) (hx : x ≠ 0) :
    (v_L x : ℚ) = (1 : ℚ) / (f_q : ℚ) * (v_K (Algebra.norm K x) : ℚ) := by

  have h_identity :=
    norm_valuation_identity v_K v_L π_L f_q hv_K hv_L hf_q hπ_L hπ_L_val
      h_unif_norm h_unit_norm x hx

  have hfq_ne : (f_q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hf_q)
  rw [h_identity]
  push_cast
  field_simp

end ValuationFormula

theorem valuation_eq_inv_residueDeg_mul_norm_valuation
    {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (v_K : K → ℤ) (v_L : L → ℤ) (π_L : L) (f_q : ℕ)
    (hv_K : ∀ a b : K, a ≠ 0 → b ≠ 0 → v_K (a * b) = v_K a + v_K b)
    (hv_L : ∀ a b : L, a ≠ 0 → b ≠ 0 → v_L (a * b) = v_L a + v_L b)
    (hf_q : 0 < f_q)
    (hπ_L : π_L ≠ 0) (hπ_L_val : v_L π_L = 1)
    (h_unif_norm : v_K (Algebra.norm K π_L) = (f_q : ℤ))
    (h_unit_norm : ∀ u : L, u ≠ 0 → v_L u = 0 → v_K (Algebra.norm K u) = 0)
    (x : L) (hx : x ≠ 0) :
    (v_L x : ℚ) = (1 : ℚ) / (f_q : ℚ) * (v_K (Algebra.norm K x) : ℚ) :=
  ValuationFormula.valuation_formula v_K v_L π_L f_q hv_K hv_L hf_q hπ_L hπ_L_val
    h_unif_norm h_unit_norm x hx

end
