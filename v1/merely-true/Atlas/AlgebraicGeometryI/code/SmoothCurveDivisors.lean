/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.PicardGroup

noncomputable section

open IsDedekindDomain

namespace SmoothCurveDivisors


variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


/-- **Weil divisor group of a smooth curve**: the free abelian group on the
height-one points (closed points) of `Spec R`. -/
abbrev WeilDivisorGroupCurve := HeightOneSpectrum R →₀ ℤ

/-- For a fractional ideal `I`, only finitely many height-one primes appear
non-trivially in the factorization. -/
def countFinite (I : FractionalIdeal (nonZeroDivisors R) K) :
    {v : HeightOneSpectrum R | FractionalIdeal.count K v I ≠ 0}.Finite := by
  have h := FractionalIdeal.finite_factors I
  rwa [Filter.eventually_cofinite] at h

/-- **Divisor of a fractional ideal**: sends an invertible fractional ideal `I` to
its formal sum of valuations `Σ v_P(I) · [P]` over height-one primes `P`. -/
def fwdFun (I : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    HeightOneSpectrum R →₀ ℤ where
  toFun := fun v => FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors R) K)
  support := (countFinite R K I).toFinset
  mem_support_toFun := by intro v; simp [Set.Finite.mem_toFinset]

/-- **Fractional ideal from a divisor**: sends a finitely supported `f : v ↦ nᵥ`
to the product `∏ᵥ Pᵥ^{nᵥ}`, the corresponding invertible fractional ideal. -/
def bwdFun (f : HeightOneSpectrum R →₀ ℤ) :
    (FractionalIdeal (nonZeroDivisors R) K)ˣ :=
  Units.mk0 (f.prod (fun v n => (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ n))
    (by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.mpr fun v _ =>
        zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

/-- Two non-zero fractional ideals with the same valuation at every height-one
prime are equal — unique factorization for Dedekind domains. -/
lemma eq_of_count_eq {I J : FractionalIdeal (nonZeroDivisors R) K}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  congr 1; funext v; exact congrArg _ (h v)

/-- Left-inverse: rebuilding a fractional ideal from its valuation vector recovers
the original ideal. -/
lemma bwd_fwd (I : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    bwdFun R K (fwdFun R K I) = I := by
  ext1
  simp only [bwdFun, Units.val_mk0]
  apply eq_of_count_eq R K
  · rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  · exact Units.ne_zero I
  · intro v
    rw [FractionalIdeal.count_finsuppProd]
    simp [fwdFun]

/-- Right-inverse: reading off the valuation vector of the ideal `∏ Pᵥ^{nᵥ}`
gives back `(nᵥ)`. -/
lemma fwd_bwd (f : HeightOneSpectrum R →₀ ℤ) :
    fwdFun R K (bwdFun R K f) = f := by
  ext v
  simp only [fwdFun, Finsupp.coe_mk, bwdFun, Units.val_mk0]
  exact FractionalIdeal.count_finsuppProd K v f

/-- Multiplicativity of the divisor map: `div(I · J) = div(I) + div(J)`. -/
lemma fwd_mul (I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    fwdFun R K (I * J) = fwdFun R K I + fwdFun R K J := by
  ext v
  simp only [fwdFun, Finsupp.coe_mk, Finsupp.add_apply, Units.val_mul]
  exact FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)

/-- **Divisor isomorphism for a smooth curve**: the group of invertible
fractional ideals (with multiplication) is isomorphic, as an additive group, to
the free abelian group on the height-one primes. -/
def weilDivisor_sum_of_points_equiv :
    Additive (FractionalIdeal (nonZeroDivisors R) K)ˣ ≃+
      (HeightOneSpectrum R →₀ ℤ) where
  toFun := fun I => fwdFun R K (Additive.toMul I)
  invFun := fun f => Additive.ofMul (bwdFun R K f)
  left_inv := by
    intro I
    show Additive.ofMul (bwdFun R K (fwdFun R K (Additive.toMul I))) = I
    exact congrArg Additive.ofMul (bwd_fwd R K (Additive.toMul I))
  right_inv := by
    intro f
    exact fwd_bwd R K f
  map_add' := by
    intro I J
    show fwdFun R K (Additive.toMul (I + J)) =
      fwdFun R K (Additive.toMul I) + fwdFun R K (Additive.toMul J)
    change fwdFun R K (Additive.toMul I * Additive.toMul J) =
      fwdFun R K (Additive.toMul I) + fwdFun R K (Additive.toMul J)
    exact fwd_mul R K (Additive.toMul I) (Additive.toMul J)

/-- The underlying additive homomorphism of `weilDivisor_sum_of_points_equiv`. -/
def weilDivisor_sum_of_points :
    Additive (FractionalIdeal (nonZeroDivisors R) K)ˣ →+
      (HeightOneSpectrum R →₀ ℤ) :=
  (weilDivisor_sum_of_points_equiv R K).toAddMonoidHom

/-- Injectivity: distinct invertible fractional ideals have distinct divisors. -/
theorem weilDivisor_sum_of_points_injective :
    Function.Injective (weilDivisor_sum_of_points R K) :=
  (weilDivisor_sum_of_points_equiv R K).injective

/-- Surjectivity: every Weil divisor on a smooth curve is the divisor of some
invertible fractional ideal. -/
theorem weilDivisor_sum_of_points_surjective :
    Function.Surjective (weilDivisor_sum_of_points R K) :=
  (weilDivisor_sum_of_points_equiv R K).surjective


/-- **Class group ≅ Picard group** for a Dedekind domain `R`: the ideal class
group of `R` agrees with the Picard group of `Spec R`. This is the algebraic
incarnation of "divisor classes = line bundles" on a smooth curve. -/
def weilDivisorClassGroup_iso_pic :
    ClassGroup R ≃* CommRing.Pic R :=
  ClassGroup.equivPic R

end SmoothCurveDivisors

end
