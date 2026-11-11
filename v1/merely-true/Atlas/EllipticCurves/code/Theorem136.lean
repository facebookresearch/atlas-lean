/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.OrdinarySupersingular
import Atlas.EllipticCurves.code.PointCounting
import Atlas.EllipticCurves.code.EndAlgebra
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Finrank

open Module Polynomial
open scoped TensorProduct

universe u

namespace EllipticCurve

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- The Frobenius discriminant $\Delta_\pi = t^2 - 4q \in \mathbb{Q}$, where $t$ is the trace of
Frobenius and $q = \#F$ is the cardinality of the base finite field (Section 13.6). -/
noncomputable def frobeniusDiscriminantQ (W : WeierstrassCurve.Affine F) : ℚ :=
  ((Hasse.traceFrobenius W : ℤ) ^ 2 - 4 * (Fintype.card F : ℤ) : ℤ)

/-- The defining polynomial $X^2 - \Delta_\pi$ of the endomorphism algebra, where
$\Delta_\pi = t^2 - 4q$ is the Frobenius discriminant. Adjoining a root yields an order
in the imaginary quadratic field $\mathbb{Q}(\sqrt{\Delta_\pi})$. -/
noncomputable def endPoly (W : WeierstrassCurve.Affine F) : ℚ[X] :=
  X ^ 2 - C (frobeniusDiscriminantQ W)

/-- The polynomial $X^2 - \Delta_\pi$ is nonzero. -/
lemma endPoly_ne_zero (W : WeierstrassCurve.Affine F) : endPoly W ≠ 0 :=
  X_pow_sub_C_ne_zero (by norm_num : 0 < 2) _

/-- The polynomial $X^2 - \Delta_\pi$ has degree $2 \neq 0$, which guarantees that
`AdjoinRoot (endPoly W)` is nontrivial. -/
lemma endPoly_degree_ne_zero (W : WeierstrassCurve.Affine F) :
    (endPoly W).degree ≠ 0 := by
  unfold endPoly
  simp [degree_X_pow_sub_C (by norm_num : 0 < 2)]

/-- The polynomial $X^2 - \Delta_\pi$ has natural degree $2$. -/
lemma endPoly_natDegree (W : WeierstrassCurve.Affine F) :
    (endPoly W).natDegree = 2 := by
  unfold endPoly; simp

/-- The endomorphism algebra $\mathrm{End}^0(E) = \mathbb{Q}[X]/(X^2 - \Delta_\pi)$ presented
abstractly as the quotient algebra adjoining a square root of the Frobenius discriminant
(Theorem 13.6). -/
noncomputable def EndAlgebra (W : WeierstrassCurve.Affine F) : Type :=
  AdjoinRoot (endPoly W)

/-- The endomorphism algebra inherits the commutative ring structure from `AdjoinRoot`. -/
noncomputable instance EndAlgebra.instCommRing
    (W : WeierstrassCurve.Affine F) : CommRing (EndAlgebra W) :=
  inferInstanceAs (CommRing (AdjoinRoot (endPoly W)))

/-- The (noncommutative) ring instance on the endomorphism algebra obtained by forgetting
commutativity. -/
@[instance, reducible] noncomputable def EndAlgebra.instRing
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : Ring (EndAlgebra W) :=
  (EndAlgebra.instCommRing W).toRing

/-- The $\mathbb{Q}$-algebra structure on the endomorphism algebra inherited from
`AdjoinRoot`. -/
@[instance, reducible] noncomputable def EndAlgebra.instAlgebra
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : Algebra ℚ (EndAlgebra W) :=
  inferInstanceAs (Algebra ℚ (AdjoinRoot (endPoly W)))

/-- Since $\deg(X^2 - \Delta_\pi) \neq 0$, the endomorphism algebra is nontrivial. -/
noncomputable instance EndAlgebra.instNontrivial
    (W : WeierstrassCurve.Affine F) : Nontrivial (EndAlgebra W) :=
  AdjoinRoot.nontrivial (f := endPoly W) (endPoly_degree_ne_zero W)

/-- The endomorphism algebra is finite-dimensional over $\mathbb{Q}$: in fact it has dimension
$2$ (cf. `endAlg_finrank_eq_two`), as $\mathrm{End}^0(E)$ is an imaginary quadratic field. -/
@[instance, reducible] noncomputable def EndAlgebra.instFiniteDimensional
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    @FiniteDimensional ℚ (EndAlgebra W) _
      (EndAlgebra.instRing W).toAddCommGroup
      (@Algebra.toModule ℚ (EndAlgebra W) _ _ (EndAlgebra.instAlgebra W)) :=
  (AdjoinRoot.powerBasis (endPoly_ne_zero W)).finite

/-- The square root of the Frobenius discriminant $\sqrt{\Delta_\pi}$ inside the endomorphism
algebra, realised as the adjoined root of $X^2 - \Delta_\pi$. -/
noncomputable def EndAlgebra.sqrtD
    (W : WeierstrassCurve.Affine F) : EndAlgebra W :=
  AdjoinRoot.root (endPoly W)

/-- The Frobenius endomorphism $\pi$ inside the endomorphism algebra, expressed as
$\pi = t/2 + \sqrt{\Delta_\pi}/2$ where $t$ is the trace of Frobenius. This element satisfies
$\pi^2 - t\pi + q = 0$ (Theorem 13.6, the characteristic polynomial of Frobenius). -/
noncomputable def EndAlgebra.frobenius
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : EndAlgebra W :=
  algebraMap ℚ _ (((Hasse.traceFrobenius W : ℤ) : ℚ) / 2) +
    (1 / 2 : ℚ) • EndAlgebra.sqrtD W

/-- The defining relation $(\sqrt{\Delta_\pi})^2 = \Delta_\pi$ inside the endomorphism
algebra, obtained directly from the polynomial $X^2 - \Delta_\pi$. -/
lemma EndAlgebra.sqrtD_sq (W : WeierstrassCurve.Affine F) :
    EndAlgebra.sqrtD W ^ 2 =
      algebraMap ℚ (EndAlgebra W) (frobeniusDiscriminantQ W) := by
  have h := AdjoinRoot.eval₂_root (endPoly W)
  change Polynomial.eval₂ (AdjoinRoot.of (endPoly W))
    (AdjoinRoot.root (endPoly W)) (endPoly W) = 0 at h
  unfold endPoly at h
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

end EllipticCurve

namespace EndomorphismRingOverFiniteField

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- The integer Frobenius discriminant $\Delta_\pi = t^2 - 4q$, where $t$ is the trace of
Frobenius and $q = \#F$. By Hasse's bound this quantity is $\leq 0$ (Section 13.6). -/
noncomputable def frobeniusDiscriminant (W : WeierstrassCurve.Affine F) : ℤ :=
  (Hasse.traceFrobenius W) ^ 2 - 4 * (Fintype.card F : ℤ)

/-- Unfolding lemma: the Frobenius discriminant equals $t^2 - 4q$. -/
@[simp]
theorem frobeniusDiscriminant_def (W : WeierstrassCurve.Affine F) :
    frobeniusDiscriminant W = (Hasse.traceFrobenius W) ^ 2 - 4 * (Fintype.card F : ℤ) :=
  rfl

/-- The integer-valued and rational-valued Frobenius discriminants agree after coercion. -/
lemma frobeniusDiscriminant_eq_Q (W : WeierstrassCurve.Affine F) :
    (frobeniusDiscriminant W : ℚ) = EllipticCurve.frobeniusDiscriminantQ W := by
  simp [frobeniusDiscriminant, EllipticCurve.frobeniusDiscriminantQ]


/-- The condition that the Frobenius endomorphism $\pi$ is not an integer scalar, equivalently
that $t^2 \neq 4q$, equivalently that $E/F$ is ordinary in the sense of Theorem 13.6. -/
def frobeniusNotInt (W : WeierstrassCurve.Affine F) : Prop :=
  (Hasse.traceFrobenius W) ^ 2 ≠ 4 * (Fintype.card F : ℤ)



/-- $\dim_\mathbb{Q} \mathrm{End}^0(E) = 2$: the endomorphism algebra is a $2$-dimensional
$\mathbb{Q}$-algebra, the imaginary quadratic field $\mathbb{Q}(\sqrt{\Delta_\pi})$ (part
of Theorem 13.6). -/
theorem endAlg_finrank_eq_two (E : WeierstrassCurve.Affine F)
    (hq : 0 < Fintype.card F)
    (hnotint : frobeniusNotInt E) :
    Module.finrank ℚ (EllipticCurve.EndAlgebra E) = 2 := by
  show Module.finrank ℚ (AdjoinRoot (EllipticCurve.endPoly E)) = 2
  have hne := EllipticCurve.endPoly_ne_zero E
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne]
  exact EllipticCurve.endPoly_natDegree E





end EndomorphismRingOverFiniteField
