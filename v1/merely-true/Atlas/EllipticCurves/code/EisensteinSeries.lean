/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Lattice
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

open Complex

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The weight-`k` Eisenstein series of a lattice `L`, defined as `G_k(L) = ∑' l∈L \{0},
1 / l^k`. Packaged as `L.G k` from `ComplexLattice`. -/
def eisensteinSeries (k : ℕ) : ℂ := L.G k

/-- Definitional unfolding of `L.eisensteinSeries k` as the sum
`∑' l : L.lattice, (l^k)⁻¹`. -/
@[simp]
theorem eisensteinSeries_def (k : ℕ) :
    L.eisensteinSeries k = ∑' l : L.lattice, ((↑l : ℂ) ^ k)⁻¹ := rfl

/-- For `k > 2`, the family `l ↦ (l^k)⁻¹` indexed by the lattice `L` is summable, with
sum equal to the weight-`k` Eisenstein series `L.eisensteinSeries k`. -/
theorem hasSum_eisensteinSeries {k : ℕ} (hk : 2 < k) :
    HasSum (fun l : L.lattice ↦ ((↑l : ℂ) ^ k)⁻¹) (L.eisensteinSeries k) := by
  have h := L.hasSum_sumInvPow 0 hk
  simp only [sub_zero] at h
  rwa [congrFun L.sumInvPow_zero k] at h

/-- For `k > 2`, the family `l ↦ (l^k)⁻¹` is summable. -/
theorem summable_eisensteinSeries {k : ℕ} (hk : 2 < k) :
    Summable (fun l : L.lattice ↦ ((↑l : ℂ) ^ k)⁻¹) :=
  (L.hasSum_eisensteinSeries hk).summable

/-- For `k > 2`, the family `l ↦ (l^k)⁻¹` is absolutely summable (norm summable). -/
theorem summable_norm_eisensteinSeries {k : ℕ} (hk : 2 < k) :
    Summable (fun l : L.lattice ↦ ‖((↑l : ℂ) ^ k)⁻¹‖) :=
  (L.summable_eisensteinSeries hk).norm

/-- The classical modular invariant `g₂(L)` equals `60` times the weight-4 Eisenstein
series `G_4(L)`. -/
theorem g₂_eq : L.g₂ = 60 * L.eisensteinSeries 4 := rfl

/-- The classical modular invariant `g₃(L)` equals `140` times the weight-6 Eisenstein
series `G_6(L)`. -/
theorem g₃_eq : L.g₃ = 140 * L.eisensteinSeries 6 := rfl

/-- The lattice `ℤ + ℤτ ⊂ ℂ` associated to a point `τ` in the upper half-plane. -/
def ofUpperHalfPlane (τ : UpperHalfPlane) : ComplexLattice :=
  ComplexLattice.mk' 1 (τ : ℂ) (by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨?_, ?_⟩
    · intro h
      have := τ.coe_im_pos
      simp [h] at this
    · intro a ha
      have him := τ.coe_im_pos
      have him2 : (a • (τ : ℂ)).im = (1 : ℂ).im := congr_arg Complex.im ha
      simp [Complex.one_im] at him2
      rcases him2 with ha0 | him0
      · rw [ha0] at ha; simp at ha
      · exact absurd him0 (ne_of_gt him))

end ComplexLattice

open scoped UpperHalfPlane

/-- The function `τ ↦ g₂(ℤ + ℤτ)` on the upper half-plane. -/
def g₂Function (τ : ℍ) : ℂ :=
  (ComplexLattice.ofUpperHalfPlane τ).g₂

/-- The function `τ ↦ g₃(ℤ + ℤτ)` on the upper half-plane. -/
def g₃Function (τ : ℍ) : ℂ :=
  (ComplexLattice.ofUpperHalfPlane τ).g₃

/-- The modular discriminant function `Δ(τ) = g₂(τ)^3 - 27 g₃(τ)^2` on the upper
half-plane. -/
def discriminantFunction (τ : ℍ) : ℂ :=
  (ComplexLattice.ofUpperHalfPlane τ).discriminantLattice

/-- The modular `j`-function `j(τ) = 1728 g₂(τ)^3 / Δ(τ)` on the upper half-plane. -/
def jFunction (τ : ℍ) : ℂ :=
  (ComplexLattice.ofUpperHalfPlane τ).jInvariantLattice

section Theorem_15_8

open ComplexLattice Pointwise

/-- The translation `τ ↦ τ + 1` on the upper half-plane (it preserves the upper half-plane
because the imaginary part is unchanged). -/
def UpperHalfPlane.addOne (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) + 1, by
    simp only [Complex.add_im, Complex.one_im, add_zero]
    exact τ.2⟩

/-- The inversion `τ ↦ -1/τ` on the upper half-plane (preserves the upper half-plane
because `Im(-1/τ) = Im τ / |τ|² > 0`). -/
def UpperHalfPlane.negInv (τ : ℍ) : ℍ :=
  ⟨-(τ : ℂ)⁻¹, by
    have him := τ.2
    have hτne : (τ : ℂ) ≠ 0 := by
      intro h; rw [h] at him; simp at him
    simp only [Complex.neg_im, Complex.inv_im]
    have : -(-((τ : ℂ)).im / Complex.normSq (τ : ℂ)) =
        ((τ : ℂ)).im / Complex.normSq (τ : ℂ) := by ring
    rw [this]
    exact div_pos him (Complex.normSq_pos.mpr hτne)⟩

/-- The lattices `ℤ + ℤτ` and `ℤ + ℤ(τ + 1)` coincide as subsets of `ℂ`, since
`τ + 1` is obtained from `τ` by an `SL₂(ℤ)`-translation. -/
theorem lattice_ofUpperHalfPlane_eq_addOne (τ : ℍ) :
    (ofUpperHalfPlane τ).lattice = (ofUpperHalfPlane τ.addOne).lattice := by
  ext x
  simp only [mem_lattice_iff, UpperHalfPlane.addOne]
  simp only [ofUpperHalfPlane, mk']
  constructor
  · rintro ⟨n₁, n₂, rfl⟩
    exact ⟨n₁ - n₂, n₂, by push_cast; ring⟩
  · rintro ⟨n₁, n₂, rfl⟩
    exact ⟨n₁ + n₂, n₂, by push_cast; ring⟩

/-- The lattices `ℤ + ℤτ` and `ℤ + ℤ(-1/τ)` are homothetic via the scalar `τ⁻¹`. -/
theorem isHomothetic_ofUpperHalfPlane_negInv (τ : ℍ) :
    IsHomothetic (ofUpperHalfPlane τ) (ofUpperHalfPlane τ.negInv) := by
  have hτne : (τ : ℂ) ≠ 0 := by
    intro h; have := τ.2; rw [h] at this; simp at this
  refine ⟨(τ : ℂ)⁻¹, inv_ne_zero hτne, ?_⟩
  ext x
  simp only [Set.mem_smul_set]
  constructor
  · intro hx
    rw [SetLike.mem_coe, mem_lattice_iff] at hx
    obtain ⟨n₁, n₂, rfl⟩ := hx
    refine ⟨(-n₂ : ℂ) * 1 + (n₁ : ℂ) * (τ : ℂ), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_lattice_iff]
      exact ⟨-n₂, n₁, by simp [ofUpperHalfPlane, mk']⟩
    · simp only [smul_eq_mul, ofUpperHalfPlane, mk', UpperHalfPlane.negInv]
      field_simp
      ring
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_lattice_iff] at hy
    obtain ⟨n₁, n₂, rfl⟩ := hy
    rw [SetLike.mem_coe, mem_lattice_iff]
    refine ⟨n₂, -n₁, ?_⟩
    simp only [smul_eq_mul, Int.cast_neg, ofUpperHalfPlane, mk', UpperHalfPlane.negInv]
    field_simp
    ring

/-- The `j`-invariant of a complex lattice depends only on the underlying set of lattice
points: if `L.lattice = L'.lattice`, then `j(L) = j(L')`. -/
theorem ComplexLattice.jInvariantLattice_eq_of_lattice_eq {L L' : ComplexLattice}
    (h : L.lattice = L'.lattice) : L.jInvariantLattice = L'.jInvariantLattice := by
  have hG : ∀ k, L.G k = L'.G k := by
    intro k
    show ∑' l : L.lattice, ((l : ℂ) ^ k)⁻¹ = ∑' l : L'.lattice, ((l : ℂ) ^ k)⁻¹
    rw [h]
  have hg₂ : L.g₂ = L'.g₂ := by rw [g₂_eq, g₂_eq]; exact congrArg (60 * ·) (hG 4)
  have hg₃ : L.g₃ = L'.g₃ := by rw [g₃_eq, g₃_eq]; exact congrArg (140 * ·) (hG 6)
  have hΔ : L.discriminantLattice = L'.discriminantLattice := by
    simp only [discriminantLattice_def, hg₂, hg₃]
  unfold jInvariantLattice
  rw [hg₂, hΔ]

/-- The `j`-invariant is homothety-invariant: if `L` and `L'` are homothetic lattices,
then they have the same `j`-invariant. -/
theorem ComplexLattice.jInvariantLattice_eq_of_isHomothetic {L L' : ComplexLattice}
    (h : IsHomothetic L L') : L'.jInvariantLattice = L.jInvariantLattice := by
  obtain ⟨c, hc, hlat⟩ := h

  have hfwd : ∀ (l' : L'.lattice), c⁻¹ * (l' : ℂ) ∈ L.lattice := by
    intro l'
    have hl' : (l' : ℂ) ∈ (L'.lattice : Set ℂ) := l'.2
    rw [hlat] at hl'
    obtain ⟨w, hw, hwval⟩ := hl'
    have : (l' : ℂ) = c * w := by rw [← hwval]; simp [smul_eq_mul]
    rw [this, show c⁻¹ * (c * w) = w from by field_simp]
    exact hw
  have hbwd : ∀ (l : L.lattice), c * (l : ℂ) ∈ L'.lattice := by
    intro l
    have hl : (l : ℂ) ∈ (L.lattice : Set ℂ) := l.2
    have : c * (l : ℂ) ∈ (L'.lattice : Set ℂ) := by
      rw [hlat]; exact ⟨(l : ℂ), hl, by simp [smul_eq_mul]⟩
    exact this
  let hequiv : L'.lattice ≃ L.lattice :=
    ⟨fun l' => ⟨c⁻¹ * (l' : ℂ), hfwd l'⟩,
    fun l => ⟨c * (l : ℂ), hbwd l⟩,
    fun l' => Subtype.ext (by field_simp),
    fun l => Subtype.ext (by field_simp)⟩

  have hG : ∀ k, L'.eisensteinSeries k = c⁻¹ ^ k * L.eisensteinSeries k := by
    intro k
    simp only [eisensteinSeries_def]
    rw [← Equiv.tsum_eq hequiv, ← tsum_mul_left]
    congr 1; ext l'
    simp only [hequiv, Equiv.coe_fn_mk]
    rw [mul_pow, mul_inv, inv_pow, inv_inv, inv_mul_cancel_left₀ (pow_ne_zero k hc)]

  have hg₂ : L'.g₂ = c⁻¹ ^ 4 * L.g₂ := by
    rw [g₂_eq, g₂_eq, hG 4]; ring
  have hg₃ : L'.g₃ = c⁻¹ ^ 6 * L.g₃ := by
    rw [g₃_eq, g₃_eq, hG 6]; ring

  simp only [jInvariantLattice_def, hg₂, hg₃]
  have hc_ne : c⁻¹ ^ 12 ≠ 0 := pow_ne_zero _ (inv_ne_zero hc)

  have hnum : 1728 * (c⁻¹ ^ 4 * L.g₂) ^ 3 = c⁻¹ ^ 12 * (1728 * L.g₂ ^ 3) := by ring
  have hden : (c⁻¹ ^ 4 * L.g₂) ^ 3 - 27 * (c⁻¹ ^ 6 * L.g₃) ^ 2 =
      c⁻¹ ^ 12 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hc_ne]

/-- The `j`-function is invariant under translation by 1: `j(τ + 1) = j(τ)`.
This is one of the modular-invariance properties of `j` in Theorem 15.8
of Sutherland's *Elliptic Curves*. -/
theorem jFunction_add_one (τ : ℍ) : jFunction τ.addOne = jFunction τ := by
  unfold jFunction
  exact (ComplexLattice.jInvariantLattice_eq_of_lattice_eq
    (lattice_ofUpperHalfPlane_eq_addOne τ)).symm

/-- The `j`-function is invariant under `τ ↦ -1/τ`: `j(-1/τ) = j(τ)`.
This is the second modular-invariance property of `j` in Theorem 15.8
of Sutherland's *Elliptic Curves*. -/
theorem jFunction_neg_inv (τ : ℍ) : jFunction τ.negInv = jFunction τ := by
  unfold jFunction
  exact ComplexLattice.jInvariantLattice_eq_of_isHomothetic
    (isHomothetic_ofUpperHalfPlane_negInv τ)

/-- Extension of `g₂Function` to all of `ℂ`, set to `0` outside the upper half-plane. -/
def g₂Ext (z : ℂ) : ℂ := if h : 0 < z.im then g₂Function ⟨z, h⟩ else 0

/-- Extension of `g₃Function` to all of `ℂ`, set to `0` outside the upper half-plane. -/
def g₃Ext (z : ℂ) : ℂ := if h : 0 < z.im then g₃Function ⟨z, h⟩ else 0




/-- Definitional equality expressing the extended `j`-function on the upper half-plane
in terms of the extended `g₂` and `g₃`: `j(z) = 1728 g₂(z)^3 / (g₂(z)^3 - 27 g₃(z)^2)`. -/
theorem jFunction_ext_eq (z : ℂ) (hz : 0 < z.im) :
    (if h : 0 < z.im then jFunction ⟨z, h⟩ else 0) =
      1728 * g₂Ext z ^ 3 / (g₂Ext z ^ 3 - 27 * g₃Ext z ^ 2) := by
  simp only [hz, dite_true, g₂Ext, g₃Ext, jFunction, ComplexLattice.jInvariantLattice,
    ComplexLattice.discriminantLattice, g₂Function, g₃Function]



end Theorem_15_8

end
