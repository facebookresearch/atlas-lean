/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Lattice
import Atlas.EllipticCurves.code.EisensteinSeries

open Complex PeriodPair

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- The Weierstrass `℘`-function associated to the complex lattice `L`, packaged
as a function `ℂ → ℂ`. -/
def weierstrassPFun (z : ℂ) : ℂ := L.weierstrassP z

/-- The Weierstrass `℘`-function is differentiable on the complement of the
lattice. -/
theorem weierstrassPFun_differentiableOn :
    DifferentiableOn ℂ L.weierstrassPFun (↑L.lattice : Set ℂ)ᶜ :=
  L.differentiableOn_weierstrassP

/-- The Weierstrass `℘`-function is differentiable at any point not in the
lattice. -/
theorem weierstrassPFun_differentiableAt {z₀ : ℂ} (hz₀ : z₀ ∉ (L.lattice : Set ℂ)) :
    DifferentiableAt ℂ L.weierstrassPFun z₀ :=
  (L.weierstrassPFun_differentiableOn z₀ hz₀).differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz₀)

/-- The Weierstrass `℘`-function is analytic on neighborhoods of points off
the lattice. -/
theorem weierstrassPFun_analyticOnNhd :
    AnalyticOnNhd ℂ L.weierstrassPFun (↑L.lattice : Set ℂ)ᶜ :=
  L.analyticOnNhd_weierstrassP

/-- The Weierstrass `℘`-function is a meromorphic function on `ℂ`. -/
theorem weierstrassPFun_meromorphic : Meromorphic L.weierstrassPFun :=
  L.meromorphic_weierstrassP

/-- At every lattice point `l₀`, the Weierstrass `℘`-function has a pole of
order `2`. -/
theorem weierstrassPFun_order (l₀ : ℂ) (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt L.weierstrassPFun l₀ = -2 :=
  L.order_weierstrassP l₀ h

/-- The Weierstrass `℘`-function is an even function: `℘(-z) = ℘(z)`. -/
@[simp]
theorem weierstrassPFun_even (z : ℂ) :
    L.weierstrassPFun (-z) = L.weierstrassPFun z :=
  L.weierstrassP_neg z

/-- The Laurent expansion of `℘(z) - 1/z²` near `0`: the coefficients are
expressed in terms of the Eisenstein series of weight `2n + 4`. -/
theorem weierstrassPFun_laurentExpansion (z : ℂ)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖) :
    HasSum (fun n : ℕ ↦ (2 * (↑n : ℂ) + 3) * L.eisensteinSeries (2 * n + 4) *
        z ^ (2 * n + 2))
      (L.weierstrassPFun z - 1 / z ^ 2) := by

  show HasSum (fun n : ℕ ↦ (2 * (↑n : ℂ) + 3) * L.G (2 * n + 4) * z ^ (2 * n + 2))
    (L.weierstrassP z - 1 / z ^ 2)

  have hsum : HasSum (fun i ↦ (L.weierstrassPExceptSeries 0 0).coeff i * z ^ i)
      (L.weierstrassPExcept 0 z) := by
    have h := L.weierstrassPExceptSeries_hasSum 0 z 0 (fun l hl => by simpa using hz l hl)
    simpa using h

  have heq : L.weierstrassP z - 1 / z ^ 2 = L.weierstrassPExcept 0 z := by
    have h0 : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
    have h := L.weierstrassPExcept_add ⟨0, h0⟩ z
    simp only [sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      one_div, inv_zero, sub_zero] at h
    rw [one_div]; linear_combination -h

  rw [heq]
  rw [show (fun n : ℕ ↦ (2 * (↑n : ℂ) + 3) * L.G (2 * n + 4) * z ^ (2 * n + 2)) =
    (fun i ↦ (L.weierstrassPExceptSeries 0 0).coeff i * z ^ i) ∘ (fun n ↦ 2 * n + 2) from by
    ext n
    congr 1
    simp only [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars,
      show (2 * n + 2 : ℕ) ≠ 0 from by omega, ↓reduceIte,
      L.lattice.zero_mem, sub_zero, zero_pow (by omega : (2 * n + 2) + 2 ≠ 0),
      inv_zero, sub_zero]
    rw [congrFun L.sumInvPow_zero]
    push_cast; ring]
  rw [Function.Injective.hasSum_iff (fun a b h => by omega)]
  · exact hsum


  · intro x hx
    simp only [Set.mem_range, not_exists] at hx
    by_cases hx0 : x = 0
    · subst hx0
      simp [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars]
    · have hodd : Odd x := by
        by_contra h
        have heven := Nat.not_odd_iff_even.mp h
        obtain ⟨m, hm⟩ := heven
        exact absurd (show 2 * (m - 1) + 2 = x by omega) (hx (m - 1))
      have hodd2 : Odd (x + 2) := hodd.add_even even_two
      simp only [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars, hx0,
        ↓reduceIte, L.lattice.zero_mem, sub_zero, zero_pow (by omega : x + 2 ≠ 0),
        inv_zero, sub_zero]
      rw [congrFun L.sumInvPow_zero, L.G_eq_zero_of_odd _ hodd2, mul_zero, zero_mul]

/-- The derivative `℘'` of the Weierstrass `℘`-function as a function `ℂ → ℂ`. -/
def derivWeierstrassPFun (z : ℂ) : ℂ := L.derivWeierstrassP z

/-- The derivative of the Weierstrass `℘`-function is meromorphic on `ℂ`. -/
theorem derivWeierstrassPFun_meromorphic : Meromorphic L.derivWeierstrassPFun :=
  L.meromorphic_derivWeierstrassP

/-- The derivative of the Weierstrass `℘`-function is an odd function:
`℘'(-z) = -℘'(z)`. -/
@[simp]
theorem derivWeierstrassPFun_odd (z : ℂ) :
    L.derivWeierstrassPFun (-z) = - L.derivWeierstrassPFun z :=
  L.derivWeierstrassP_neg z

/-- The derivative `℘'` is analytic on neighborhoods of points off the
lattice. -/
theorem derivWeierstrassPFun_analyticOnNhd :
    AnalyticOnNhd ℂ L.derivWeierstrassPFun (↑L.lattice : Set ℂ)ᶜ :=
  L.analyticOnNhd_derivWeierstrassP

/-- At every lattice point `l₀`, the derivative `℘'` has a pole of order `3`. -/
theorem derivWeierstrassPFun_order (l₀ : ℂ) (h : l₀ ∈ L.lattice) :
    meromorphicOrderAt L.derivWeierstrassPFun l₀ = -3 := by
  show meromorphicOrderAt L.derivWeierstrassP l₀ = -3
  rw [show (-3 : WithTop ℤ) = ((-3 : ℤ) : WithTop ℤ) from rfl]
  rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_derivWeierstrassP l₀)]
  refine ⟨fun z ↦ (z - l₀) ^ 3 * L.derivWeierstrassPExcept l₀ z - 2, ?_, ?_, ?_⟩
  · have : AnalyticAt ℂ (L.derivWeierstrassPExcept l₀) l₀ := by
      apply L.analyticOnNhd_derivWeierstrassPExcept l₀
      simp [Set.mem_compl_iff, Set.mem_diff, h]
    fun_prop
  · simp [sub_self]
  · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ l₀)
    have hne3 : (z - l₀) ^ 3 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
    have hsub := L.derivWeierstrassPExcept_sub ⟨l₀, h⟩ z
    rw [← hsub]
    simp only [smul_eq_mul, zpow_neg, zpow_ofNat]
    rw [mul_sub, inv_mul_cancel_left₀ hne3]
    ring

/-- `℘` is doubly periodic: adding any lattice vector to the argument leaves
the value unchanged. -/
theorem weierstrassPFun_add_lattice (z : ℂ) (ω : ℂ) (hω : ω ∈ L.lattice) :
    L.weierstrassPFun (z + ω) = L.weierstrassPFun z :=
  L.weierstrassP_add_coe z ⟨ω, hω⟩

/-- `℘'` is doubly periodic: adding any lattice vector to the argument leaves
the value unchanged. -/
theorem derivWeierstrassPFun_add_lattice (z : ℂ) (ω : ℂ) (hω : ω ∈ L.lattice) :
    L.derivWeierstrassPFun (z + ω) = L.derivWeierstrassPFun z :=
  L.derivWeierstrassP_add_coe z ⟨ω, hω⟩

/-- The invariant `g₂` of the lattice, defined as `60` times the Eisenstein
series of weight `4`. -/
def g₂Fun : ℂ := 60 * L.eisensteinSeries 4

/-- The invariant `g₃` of the lattice, defined as `140` times the Eisenstein
series of weight `6`. -/
def g₃Fun : ℂ := 140 * L.eisensteinSeries 6

/-- `g₂Fun` agrees definitionally with the field `g₂` of the lattice. -/
@[simp]
theorem g₂Fun_eq : L.g₂Fun = L.g₂ := rfl

/-- `g₃Fun` agrees definitionally with the field `g₃` of the lattice. -/
@[simp]
theorem g₃Fun_eq : L.g₃Fun = L.g₃ := rfl

/-- The differential equation satisfied by the Weierstrass `℘`-function:
`(℘'(z))² = 4 ℘(z)³ - g₂ ℘(z) - g₃`, for `z` not in the lattice. -/
theorem weierstrassPFun_differentialEquation (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) :
    L.derivWeierstrassPFun z ^ 2 =
      4 * L.weierstrassPFun z ^ 3 - L.g₂Fun * L.weierstrassPFun z - L.g₃Fun :=
  L.derivWeierstrassP_sq z hz

end ComplexLattice

end
