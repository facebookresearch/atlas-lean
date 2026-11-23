/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CohomologyP1
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic

namespace SheafCohomology


section SheafCondition

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- The "restriction to the cover" map for an `A`-module `M`: it sends `m` to the
pair of its images in the localizations away from `f` and from `g`. This is the
first map of the Čech complex for the two-element cover `{D(f), D(g)}`. -/
noncomputable def locProductMap (f g : A) :
    M →ₗ[A] LocalizedModule (Submonoid.powers f) M × LocalizedModule (Submonoid.powers g) M :=
  LinearMap.prod
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)

/-- Sheaf condition (separation/injectivity): if `f, g` generate the unit ideal,
then the product of the two localization maps is injective. This is the `H⁰`
part of the Čech sheaf condition for `{D(f), D(g)}`. -/
theorem locProductMap_injective {f g : A} (hfg : Ideal.span {f, g} = ⊤) :
    Function.Injective (locProductMap (M := M) f g) := by
  rw [← LinearMap.ker_eq_bot]
  ext m
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hm

    have hf : (LocalizedModule.mkLinearMap (Submonoid.powers f) M) m = 0 := by
      have := congr_arg Prod.fst hm; simp [locProductMap] at this; exact this
    have hg : (LocalizedModule.mkLinearMap (Submonoid.powers g) M) m = 0 := by
      have := congr_arg Prod.snd hm; simp [locProductMap] at this; exact this

    have hf_ker : m ∈ (LocalizedModule.mkLinearMap (Submonoid.powers f) M).ker :=
      LinearMap.mem_ker.mpr hf
    have hg_ker : m ∈ (LocalizedModule.mkLinearMap (Submonoid.powers g) M).ker :=
      LinearMap.mem_ker.mpr hg
    rw [LocalizedModule.mem_ker_mkLinearMap_iff] at hf_ker hg_ker
    obtain ⟨_, ⟨n, rfl⟩, hrf⟩ := hf_ker
    obtain ⟨_, ⟨k, rfl⟩, hrg⟩ := hg_ker
    change f ^ n • m = 0 at hrf
    change g ^ k • m = 0 at hrg

    have h_pow : Ideal.span ((fun x => x ^ (n + k)) '' {f, g}) = ⊤ :=
      Ideal.span_pow_eq_top {f, g} hfg (n + k)
    have h1 : (1 : A) ∈ Ideal.span ((fun x => x ^ (n + k)) '' {f, g}) := by
      rw [h_pow]; exact Submodule.mem_top
    simp only [Set.image_insert_eq, Set.image_singleton] at h1
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨a, b, hab⟩ := h1

    have hfN : f ^ (n + k) • m = 0 := by
      rw [show f ^ (n + k) = f ^ k * f ^ n from by ring, mul_smul, hrf, smul_zero]
    have hgN : g ^ (n + k) • m = 0 := by
      rw [show g ^ (n + k) = g ^ n * g ^ k from by ring, mul_smul, hrg, smul_zero]

    have : (1 : A) • m = 0 := by
      rw [← hab, add_smul, mul_smul, mul_smul, hfN, hgN, smul_zero, smul_zero, add_zero]
    rwa [one_smul] at this
  · intro hm; simp [hm, locProductMap, map_zero]

end SheafCondition


section Flatness

variable (A : Type*) [CommRing A] (f : A)

/-- Flatness of localization at a single element: `A[f⁻¹]` is `A`-flat.
This is essential for showing that taking cohomology commutes with localization. -/
theorem localization_away_flat : Module.Flat A (Localization.Away f) :=
  IsLocalization.flat (Localization.Away f) (Submonoid.powers f)

end Flatness


section CechComplex

variable (A : Type*) [CommRing A] (f g : A)

/-- `f` becomes a unit in `A[(fg)⁻¹]`. -/
lemma isUnit_algebraMap_of_away_mul_left :
    IsUnit (algebraMap A (Localization.Away (f * g)) f) := by
  have hu := IsLocalization.map_units (Localization.Away (f * g))
    (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g))
  simp at hu; exact hu.1

/-- `g` becomes a unit in `A[(fg)⁻¹]`. -/
lemma isUnit_algebraMap_of_away_mul_right :
    IsUnit (algebraMap A (Localization.Away (f * g)) g) := by
  have hu := IsLocalization.map_units (Localization.Away (f * g))
    (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g))
  simp at hu; exact hu.2

/-- The restriction `A[f⁻¹] → A[(fg)⁻¹]` induced by the universal property
of localization. This is one of the two Čech restriction maps for `{D(f), D(g)}`. -/
noncomputable def cechMapFromF :
    Localization.Away f →+* Localization.Away (f * g) :=
  Localization.awayLift (algebraMap A (Localization.Away (f * g))) f
    (isUnit_algebraMap_of_away_mul_left A f g)

/-- The restriction `A[g⁻¹] → A[(fg)⁻¹]` induced by the universal property
of localization. -/
noncomputable def cechMapFromG :
    Localization.Away g →+* Localization.Away (f * g) :=
  Localization.awayLift (algebraMap A (Localization.Away (f * g))) g
    (isUnit_algebraMap_of_away_mul_right A f g)

/-- The Čech differential `d` applied to an element of `A` coming from both
`A[f⁻¹]` and `A[g⁻¹]` gives zero. This expresses `d ∘ d = 0` at the `H⁰` level. -/
theorem cech_dsquared_zero (a : A) :
    cechMapFromF A f g (algebraMap A (Localization.Away f) a) -
    cechMapFromG A f g (algebraMap A (Localization.Away g) a) = 0 := by
  simp only [cechMapFromF, cechMapFromG, Localization.awayLift,
    IsLocalization.Away.lift_eq]
  ring

/-- The Čech differential `A[f⁻¹] × A[g⁻¹] → A[(fg)⁻¹]`, sending
`(s, t) ↦ s|_{D(fg)} - t|_{D(fg)}`. Its cokernel is `H¹` for the two-element cover. -/
noncomputable def cechDifferential :
    Localization.Away f × Localization.Away g → Localization.Away (f * g) :=
  fun p => cechMapFromF A f g p.1 - cechMapFromG A f g p.2

/-- The restriction map from `A[f⁻¹]` agrees with `algebraMap A _` on elements
of `A`. -/
lemma cechMapFromF_algebraMap (a : A) :
    cechMapFromF A f g (algebraMap A _ a) = algebraMap A _ a := by
  simp [cechMapFromF, Localization.awayLift, IsLocalization.Away.lift_eq]

/-- The restriction map from `A[g⁻¹]` agrees with `algebraMap A _` on elements
of `A`. -/
lemma cechMapFromG_algebraMap (a : A) :
    cechMapFromG A f g (algebraMap A _ a) = algebraMap A _ a := by
  simp [cechMapFromG, Localization.awayLift, IsLocalization.Away.lift_eq]

/-- Sending the formal inverse of `f` in `A[f⁻¹]` into `A[(fg)⁻¹]` and multiplying
by `f` yields `1`. -/
lemma cechMapFromF_invSelf_mul :
    cechMapFromF A f g (IsLocalization.Away.invSelf (S := Localization.Away f) f) *
    algebraMap A (Localization.Away (f * g)) f = 1 := by
  conv_lhs => rw [← cechMapFromF_algebraMap A f g f]
  rw [← map_mul, show IsLocalization.Away.invSelf f *
    algebraMap A (Localization.Away f) f = 1 from by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf f]
  exact map_one _

/-- Sending the formal inverse of `g` in `A[g⁻¹]` into `A[(fg)⁻¹]` and multiplying
by `g` yields `1`. -/
lemma cechMapFromG_invSelf_mul :
    cechMapFromG A f g (IsLocalization.Away.invSelf (S := Localization.Away g) g) *
    algebraMap A (Localization.Away (f * g)) g = 1 := by
  conv_lhs => rw [← cechMapFromG_algebraMap A f g g]
  rw [← map_mul, show IsLocalization.Away.invSelf g *
    algebraMap A (Localization.Away g) g = 1 from by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf g]
  exact map_one _

/-- Iterated version of `cechMapFromF_invSelf_mul`: pushing `f⁻ⁿ` into
`A[(fg)⁻¹]` and multiplying by `fⁿ` gives `1`. -/
lemma cechMapFromF_invSelf_pow_mul (n : ℕ) :
    cechMapFromF A f g (IsLocalization.Away.invSelf
      (S := Localization.Away f) f ^ n) *
    algebraMap A (Localization.Away (f * g)) (f ^ n) = 1 := by
  conv_lhs => rw [map_pow (algebraMap A _)]
  rw [map_pow (cechMapFromF A f g), ← mul_pow,
    cechMapFromF_invSelf_mul A f g, one_pow]

/-- Iterated version of `cechMapFromG_invSelf_mul`: pushing `g⁻ⁿ` into
`A[(fg)⁻¹]` and multiplying by `gⁿ` gives `1`. -/
lemma cechMapFromG_invSelf_pow_mul (n : ℕ) :
    cechMapFromG A f g (IsLocalization.Away.invSelf
      (S := Localization.Away g) g ^ n) *
    algebraMap A (Localization.Away (f * g)) (g ^ n) = 1 := by
  conv_lhs => rw [map_pow (algebraMap A _)]
  rw [map_pow (cechMapFromG A f g), ← mul_pow,
    cechMapFromG_invSelf_mul A f g, one_pow]

/-- Computation of the Čech restriction map from `A[f⁻¹]` on an element of the
form `c / fⁿ`, cleared by `(fg)ⁿ`: the result is `c · gⁿ`. -/
lemma cechMapFromF_mul_fgpow (c : A) (n : ℕ) :
    cechMapFromF A f g (algebraMap A _ c *
      IsLocalization.Away.invSelf (S := Localization.Away f) f ^ n) *
    algebraMap A _ ((f * g) ^ n) =
    algebraMap A _ c * algebraMap A _ (g ^ n) := by
  rw [map_mul, cechMapFromF_algebraMap, mul_assoc,
    show (f * g) ^ n = f ^ n * g ^ n from mul_pow f g n, map_mul,
    show cechMapFromF A f g _ *
      (algebraMap A _ (f ^ n) * algebraMap A _ (g ^ n)) =
      (cechMapFromF A f g _ * algebraMap A _ (f ^ n)) *
        algebraMap A _ (g ^ n) from by ring,
    cechMapFromF_invSelf_pow_mul A f g n, one_mul]

/-- Computation of the Čech restriction map from `A[g⁻¹]` on an element of the
form `c / gⁿ`, cleared by `(fg)ⁿ`: the result is `c · fⁿ`. -/
lemma cechMapFromG_mul_fgpow (c : A) (n : ℕ) :
    cechMapFromG A f g (algebraMap A _ c *
      IsLocalization.Away.invSelf (S := Localization.Away g) g ^ n) *
    algebraMap A _ ((f * g) ^ n) =
    algebraMap A _ c * algebraMap A _ (f ^ n) := by
  rw [map_mul, cechMapFromG_algebraMap, mul_assoc,
    show (f * g) ^ n = f ^ n * g ^ n from mul_pow f g n, map_mul,
    show cechMapFromG A f g _ *
      (algebraMap A _ (f ^ n) * algebraMap A _ (g ^ n)) =
      algebraMap A _ (f ^ n) *
        (cechMapFromG A f g _ * algebraMap A _ (g ^ n)) from by ring,
    cechMapFromG_invSelf_pow_mul A f g n, mul_one]

/-- Vanishing of Čech `H¹` for the structure sheaf on an affine open:
if `f, g` generate the unit ideal of `A`, then the Čech differential
`A[f⁻¹] × A[g⁻¹] → A[(fg)⁻¹]` is surjective. Equivalently, `H¹` of the
two-element cover by basic opens vanishes for the structure sheaf — the
algebraic origin of affine acyclicity. -/
theorem cech_H1_vanishes
    (hfg : Ideal.span ({f, g} : Set A) = ⊤) :
    Function.Surjective (cechDifferential A f g) := by

  have hcop : IsCoprime f g := by
    have h1 : (1 : A) ∈ Ideal.span ({f, g} : Set A) := by
      rw [hfg]; exact Submodule.mem_top
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨a, b, hab⟩ := h1
    exact ⟨a, b, hab⟩

  intro z
  obtain ⟨⟨a, ⟨_, ⟨n, rfl⟩⟩⟩, hz⟩ :=
    IsLocalization.surj (Submonoid.powers (f * g)) z

  simp only at hz

  obtain ⟨α, β, hαβ⟩ := hcop.pow (m := n) (n := n)


  let x_f := algebraMap A (Localization.Away f) (a * β) *
    IsLocalization.Away.invSelf (S := Localization.Away f) f ^ n
  let x_g := algebraMap A (Localization.Away g) (-(a * α)) *
    IsLocalization.Away.invSelf (S := Localization.Away g) g ^ n
  refine ⟨(x_f, x_g), ?_⟩

  show cechMapFromF A f g x_f - cechMapFromG A f g x_g = z

  have hunit : IsUnit (algebraMap A (Localization.Away (f * g))
      ((f * g) ^ n)) :=
    IsLocalization.map_units _
      (⟨(f * g) ^ n, n, rfl⟩ : Submonoid.powers (f * g))
  apply hunit.mul_right_cancel

  rw [hz, sub_mul, cechMapFromF_mul_fgpow A f g (a * β) n,
    cechMapFromG_mul_fgpow A f g (-(a * α)) n]

  simp only [← map_mul, ← map_sub]
  congr 1
  calc a * β * g ^ n - -(a * α) * f ^ n
      = a * β * g ^ n + a * α * f ^ n := by ring
    _ = a * 1 := by rw [← hαβ]; ring
    _ = a := mul_one _

end CechComplex


section SerreDuality

open CohomologyP1

variable (k : Type) [Field k]

/-- `H⁰(ℙ¹, O(n))`, realized concretely as the Čech `H⁰` of degree `n` sections. -/
abbrev H0 (n : ℤ) : Type := ↥(CechH0 k n)

/-- `H¹(ℙ¹, O(n))`, realized concretely as the quotient of Laurent series in one
variable by the sum of "non-negative degree" and "degree `≤ n`" subspaces. -/
abbrev H1 (n : ℤ) : Type := (ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)

/-- `H⁰(ℙ¹, O(n)) = 0` for `n < 0`: no global sections in negative degree. -/
lemma finrank_H0_of_neg (n : ℤ) (hn : n < 0) :
    Module.finrank k (H0 k n) = 0 := by
  show Module.finrank k ↥(CechH0 k n) = 0
  rw [H0_vanishes_neg k n hn]
  exact finrank_bot k (ℤ →₀ k)

/-- `dim H⁰(ℙ¹, O(n)) = n + 1` for `n ≥ 0`: the global sections of `O(n)` are
the homogeneous polynomials of degree `n` in two variables. -/
lemma finrank_H0_of_nonneg (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (H0 k n) = (n + 1).toNat := by
  show Module.finrank k ↥(CechH0 k n) = (n + 1).toNat
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [finrank_H0_nonneg]
  simp

/-- `H¹(ℙ¹, O(n)) = 0` for `n ≥ 0`: higher cohomology of non-negative twists
vanishes on ℙ¹. -/
lemma finrank_H1_of_nonneg (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (H1 k n) = 0 := by
  show Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) = 0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact finrank_H1_nonneg k m

/-- `dim H¹(ℙ¹, O(n)) = -n - 1` for `n < 0`: combinatorial count of Laurent terms
of strictly negative degree above the cutoff `n`. -/
lemma finrank_H1_of_neg (n : ℤ) (hn : n < 0) :
    Module.finrank k (H1 k n) = (-n - 1).toNat :=
  finrank_H1_neg k n hn

/-- Serre duality on ℙ¹, non-negative case: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`.
For `n ≥ 0` both sides vanish, confirming the duality. The canonical bundle on
ℙ¹ is `O(-2)`, so `O(n)∨ ⊗ K = O(-2 - n)`. -/
theorem serre_duality_nonneg (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
  rw [finrank_H1_of_nonneg k n hn, finrank_H0_of_neg k (-2 - n) (by omega)]

/-- Serre duality on ℙ¹, negative case: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`.
For `n < 0`, `-2 - n` may be `≥ 0` or `= -1`; both sub-cases give matching
dimensions. -/
theorem serre_duality_neg (n : ℤ) (hn : n < 0) :
    Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
  rw [finrank_H1_of_neg k n hn]
  by_cases h : -2 - n < 0
  ·
    rw [finrank_H0_of_neg k (-2 - n) h]

    have : n = -1 := by omega
    subst this; simp
  ·
    push Not at h
    rw [finrank_H0_of_nonneg k (-2 - n) h]

    congr 1; omega

end SerreDuality


section EulerCharacteristic

open CohomologyP1

variable (k : Type) [Field k]

/-- Euler characteristic of `O(n)` on ℙ¹: `χ(O(n)) = h⁰(O(n)) - h¹(O(n)) = n + 1`.
This is the Riemann–Roch formula for line bundles on ℙ¹ (genus `0`). -/
theorem euler_characteristic (n : ℤ) :
    (Module.finrank k (H0 k n) : ℤ) -
    (Module.finrank k (H1 k n) : ℤ) = n + 1 := by
  by_cases hn : 0 ≤ n
  ·
    rw [finrank_H0_of_nonneg k n hn, finrank_H1_of_nonneg k n hn]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ n + 1)]
  ·
    push Not at hn
    rw [finrank_H0_of_neg k n hn, finrank_H1_of_neg k n hn]
    simp; omega

end EulerCharacteristic

end SheafCohomology
