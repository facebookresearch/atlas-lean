/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.ResidueSum
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Kaehler.Basic

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical
  IsDedekindDomain

universe u

variable {k : Type u} [Field k]

namespace ResidueSumZero


/-- The residue of a Laurent series over `k`: the coefficient of `t^{-1}`,
i.e. the algebraic residue at the origin. -/
noncomputable def laurentResidue (f : LaurentSeries k) : k :=
  f.coeff (-1)

/-- The residue of the zero Laurent series is zero. -/
@[simp]
lemma laurentResidue_zero : laurentResidue (0 : LaurentSeries k) = 0 := by
  simp [laurentResidue, HahnSeries.coeff_zero]

/-- Additivity of the residue. -/
lemma laurentResidue_add (f g : LaurentSeries k) :
    laurentResidue (f + g) = laurentResidue f + laurentResidue g := by
  simp [laurentResidue, HahnSeries.coeff_add]

/-- The residue commutes with finite sums. -/
lemma laurentResidue_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries k) :
    laurentResidue (∑ i ∈ s, f i) = ∑ i ∈ s, laurentResidue (f i) := by
  simp [laurentResidue, HahnSeries.coeff_sum]

/-- The residue is `k`-linear in the scalar action. -/
lemma laurentResidue_smul (c : k) (f : LaurentSeries k) :
    laurentResidue (c • f) = c * laurentResidue f := by
  simp [laurentResidue, HahnSeries.coeff_smul, smul_eq_mul]

/-- A regular power series (no principal part) has residue zero. -/
lemma laurentResidue_ofPowerSeries (f : PowerSeries k) :
    laurentResidue (f : LaurentSeries k) = 0 := by
  simp [laurentResidue, PowerSeries.coeff_coe]

/-- The simple pole `c · t^{-1}`, the basic Laurent series with residue `c`. -/
noncomputable def simplePole (c : k) : LaurentSeries k :=
  HahnSeries.single (-1 : ℤ) c

/-- The residue of the simple pole `c · t^{-1}` is `c`. -/
@[simp]
lemma laurentResidue_simplePole (c : k) :
    laurentResidue (simplePole c) = c := by
  simp [laurentResidue, simplePole]

/-- A Laurent series with no negative-order coefficients (i.e., a holomorphic
germ) has zero residue. -/
lemma laurentResidue_nonneg_order (f : LaurentSeries k)
    (hf : ∀ n : ℤ, n < 0 → f.coeff n = 0) :
    laurentResidue f = 0 :=
  hf (-1) (by omega)

/-- The residue assembled as a `k`-linear map `LaurentSeries k →ₗ[k] k`. -/
noncomputable def laurentResidueLinearMap : LaurentSeries k →ₗ[k] k where
  toFun := laurentResidue
  map_add' := laurentResidue_add
  map_smul' c f := by simp [laurentResidue_smul]


/-- An abstract partial-fraction differential: `n` simple poles at distinct
points `a_i` with residues `c_i`. The algebraic shadow of a rational
differential on `ℙ¹`. -/
structure PartialFracDiff (k : Type*) [Field k] where
  n : ℕ
  c : Fin n → k
  a : Fin n → k
  hdist : Function.Injective a

/-- The local Laurent expansion of `ω` at its `j`-th pole: a pure simple pole
with coefficient `c_j`. -/
noncomputable def PartialFracDiff.localExpansionAtPole
    (ω : PartialFracDiff k) (j : Fin ω.n) : LaurentSeries k :=
  simplePole (ω.c j)

/-- The local Laurent expansion at infinity: a simple pole with residue equal
to `−Σ c_i`, enforcing the residue theorem on `ℙ¹`. -/
noncomputable def PartialFracDiff.localExpansionAtInf
    (ω : PartialFracDiff k) : LaurentSeries k :=
  simplePole (-(∑ i, ω.c i))

/-- The Laurent residue of `ω` at its `j`-th pole equals the prescribed
coefficient `c_j`. -/
theorem PartialFracDiff.residue_at_pole (ω : PartialFracDiff k) (j : Fin ω.n) :
    laurentResidue (ω.localExpansionAtPole j) = ω.c j := by
  simp [localExpansionAtPole]

/-- The Laurent residue at infinity equals `−Σ c_i`. -/
theorem PartialFracDiff.residue_at_inf (ω : PartialFracDiff k) :
    laurentResidue ω.localExpansionAtInf = -(∑ i, ω.c i) := by
  simp [localExpansionAtInf]

/-- Residue theorem for the abstract partial-fraction differential: the sum
over all poles (finite plus infinity) vanishes. -/
theorem PartialFracDiff.residue_sum_zero (ω : PartialFracDiff k) :
    (∑ j, laurentResidue (ω.localExpansionAtPole j)) +
    laurentResidue ω.localExpansionAtInf = 0 := by
  simp only [residue_at_pole, residue_at_inf]
  exact add_neg_cancel _

/-- Compatibility: the Laurent residue at a pole agrees with the polynomial
partial-fraction residue. -/
theorem PartialFracDiff.residue_agrees_with_polynomial
    (ω : PartialFracDiff k) (j : Fin ω.n) :
    laurentResidue (ω.localExpansionAtPole j) =
    ResidueSum.residuePartialFrac ω.c ω.a j := by
  rw [residue_at_pole, ResidueSum.residue_partial_frac_eq_coeff _ _ _ ω.hdist]

/-- Explicit residue identity on `ℙ¹`: `Σ c_j + (−Σ c_j) = 0`. -/
theorem residue_sum_zero_P1_explicit (ω : PartialFracDiff k) :
    (∑ j : Fin ω.n, ω.c j) + (-(∑ j : Fin ω.n, ω.c j)) = 0 :=
  add_neg_cancel _


/-- A smooth proper curve over `k` packaged with its scheme, its Dedekind
coordinate ring `A`, function field `K`, and the necessary algebra/tower
instances. The algebraic data needed to state the residue theorem. -/
structure SmoothProperCurve (k : Type u) [Field k] where
  X : Scheme.{u}
  overSpecK : X.Over (Spec (.of k))
  proper : @IsProper _ _ (X ↘ (Spec (.of k)))
  smooth : @SmoothOfRelativeDimension 1 _ _ (X ↘ (Spec (.of k)))
  A : Type u
  instCommRingA : CommRing A
  instIsDomainA : IsDomain A
  instIsDedekindDomainA : IsDedekindDomain A
  instAlgebraKA : Algebra k A
  K : Type u
  instFieldK : Field K
  instAlgebraAK : Algebra A K
  instIsFractionRing : IsFractionRing A K
  instAlgebraKK : Algebra k K
  instIsScalarTower : IsScalarTower k A K

variable (C : SmoothProperCurve k)

instance : CommRing C.A := C.instCommRingA
instance : IsDomain C.A := C.instIsDomainA
instance : IsDedekindDomain C.A := C.instIsDedekindDomainA
instance : Algebra k C.A := C.instAlgebraKA
instance : Field C.K := C.instFieldK
instance : Algebra C.A C.K := C.instAlgebraAK
instance : IsFractionRing C.A C.K := C.instIsFractionRing
instance : Algebra k C.K := C.instAlgebraKK
instance : IsScalarTower k C.A C.K := C.instIsScalarTower







/-- Consistency check: the polynomial residue sum from `ResidueSum` agrees
with the abstract residue-sum-zero identity. -/
theorem residue_sum_consistent (n : ℕ) (c a : Fin n → k) (hdist : Function.Injective a) :
    (∑ i, ResidueSum.residuePartialFrac c a i) +
    ResidueSum.residueAtInfPartialFrac c a = 0 :=
  ResidueSum.residue_sum_partial_frac c a hdist

/-- Compatibility: the polynomial residue at the `j`-th pole equals the
Laurent residue of the simple pole `c_j · t^{-1}`. -/
theorem polynomial_residue_eq_laurent (n : ℕ) (c a : Fin n → k)
    (hdist : Function.Injective a) (j : Fin n) :
    ResidueSum.residuePartialFrac c a j =
    laurentResidue (simplePole (c j)) := by
  rw [ResidueSum.residue_partial_frac_eq_coeff c a j hdist, laurentResidue_simplePole]

end ResidueSumZero

end
