/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Atlas.AlgebraicGeometryI.code.BlowupAtPoint

open Polynomial AlgebraicGeometry

noncomputable section

namespace Prop34Blowup

variable {R : Type*} [CommRing R]

/-- The image of an ideal `𝔪 ⊆ R` inside the Rees algebra `R[𝔪 t]`. -/
noncomputable def reesIdealFromBase (𝔪 : Ideal R) : Ideal (reesAlgebra 𝔪) :=
  Ideal.map (algebraMap R (reesAlgebra 𝔪)) 𝔪

/-- The associated graded ring `gr_𝔪 R = ⨁ 𝔪^n / 𝔪^{n+1}`, defined as the Rees algebra
quotiented by the image of `𝔪`. -/
def assocGradedRing (𝔪 : Ideal R) : Type _ :=
  (reesAlgebra 𝔪) ⧸ reesIdealFromBase 𝔪

/-- The commutative ring structure on the associated graded ring. -/
noncomputable instance assocGradedRing.commRing (𝔪 : Ideal R) :
    CommRing (assocGradedRing 𝔪) :=
  Ideal.Quotient.commRing (reesIdealFromBase 𝔪)

/-- The fibre of the blowup over the centre, realised as the tensor product
`reesAlgebra 𝔪 ⊗_R R/𝔪`. -/
abbrev exceptionalFiberRing (𝔪 : Ideal R) :=
  TensorProduct R (↥(reesAlgebra 𝔪)) (R ⧸ 𝔪)

/-- Algebra structure on the associated graded ring over the Rees algebra. -/
noncomputable instance assocGradedRing.algebraRees (𝔪 : Ideal R) :
    Algebra (↥(reesAlgebra 𝔪)) (assocGradedRing 𝔪) := by
  unfold assocGradedRing; exact Ideal.Quotient.algebra _

/-- Algebra isomorphism between the associated graded ring and the exceptional fibre
ring, viewed over the Rees algebra. -/
noncomputable def assocGraded_equivExceptionalFiber (𝔪 : Ideal R) :
    assocGradedRing 𝔪 ≃ₐ[↥(reesAlgebra 𝔪)] exceptionalFiberRing 𝔪 := by
  unfold assocGradedRing
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot (↥(reesAlgebra 𝔪)) 𝔪

/-- Ring isomorphism `gr_𝔪 R ≅ reesAlgebra 𝔪 ⊗_R R/𝔪`. -/
noncomputable def assocGraded_ringEquivExceptionalFiber (𝔪 : Ideal R) :
    assocGradedRing 𝔪 ≃+* exceptionalFiberRing 𝔪 :=
  (assocGraded_equivExceptionalFiber 𝔪).toRingEquiv

/-- The tangent cone scheme: `Spec (gr_𝔪 R)`. -/
noncomputable def tangentConeScheme (𝔪 : Ideal R) : Scheme :=
  Spec (.of (assocGradedRing 𝔪))

/-- The exceptional fibre of the blowup as a scheme. -/
noncomputable def exceptionalFiberScheme (𝔪 : Ideal R) : Scheme :=
  Spec (.of (exceptionalFiberRing 𝔪))

/-- Proposition 34 (key isomorphism): the tangent cone scheme is canonically isomorphic
to the exceptional fibre of the blowup. -/
noncomputable def tangentCone_isoExceptionalFiber (𝔪 : Ideal R) :
    tangentConeScheme 𝔪 ≅ exceptionalFiberScheme 𝔪 := by
  unfold tangentConeScheme exceptionalFiberScheme
  exact Scheme.Spec.mapIso
    (assocGraded_ringEquivExceptionalFiber 𝔪).symm.toCommRingCatIso.op

/-- The `R`-algebra endomorphism of `R[X]` sending `X ↦ c · X`, used to define the
scaling action on the Rees algebra. -/
noncomputable def scaleAlgHom (c : R) : R[X] →ₐ[R] R[X] :=
  aeval (C c * X)

/-- Scaling by `1` is the identity on `R[X]`. -/
lemma scaleAlgHom_one : scaleAlgHom (1 : R) = AlgHom.id R R[X] := by
  ext; unfold scaleAlgHom; simp [map_one, one_mul]

/-- Scaling by `c₁` then `c₂` is the same as scaling by `c₁ · c₂`. -/
lemma scaleAlgHom_comp (c₁ c₂ : R) :
    (scaleAlgHom c₁).comp (scaleAlgHom c₂) = scaleAlgHom (c₁ * c₂) := by
  ext
  unfold scaleAlgHom
  simp only [AlgHom.comp_apply, aeval_X]
  simp only [aeval_def, eval₂_mul, eval₂_C, eval₂_X, Polynomial.algebraMap_eq]
  rw [← mul_assoc, ← C_mul, mul_comm c₂ c₁]

/-- Scaling preserves membership in the Rees algebra. -/
lemma scaleAlgHom_mem_reesAlgebra (I : Ideal R) (c : R)
    (f : R[X]) (hf : f ∈ reesAlgebra I) :
    (scaleAlgHom c : R[X] →ₐ[R] R[X]) f ∈ reesAlgebra I := by
  have h : (reesAlgebra I).map (scaleAlgHom c) ≤ reesAlgebra I := by
    rw [← adjoin_monomial_eq_reesAlgebra, ← Algebra.adjoin_image R (scaleAlgHom c)]
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp only [SetLike.mem_coe, Submodule.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [adjoin_monomial_eq_reesAlgebra, SetLike.mem_coe]
    unfold scaleAlgHom
    simp only [aeval_def, eval₂_monomial, Polynomial.algebraMap_eq, pow_one]
    rw [← mul_assoc, ← map_mul, C_mul_X_eq_monomial, reesAlgebra.monomial_mem, pow_one]
    exact I.mul_mem_right c hr
  exact h ⟨f, hf, rfl⟩

/-- The induced scaling ring homomorphism on the Rees algebra. -/
noncomputable def scaleOnRees (I : Ideal R) (c : R) : reesAlgebra I →+* reesAlgebra I where
  toFun f := ⟨scaleAlgHom c f.val, scaleAlgHom_mem_reesAlgebra I c f.val f.prop⟩
  map_one' := Subtype.ext (map_one (scaleAlgHom c))
  map_mul' x y := Subtype.ext (map_mul (scaleAlgHom c) x.val y.val)
  map_zero' := Subtype.ext (map_zero (scaleAlgHom c))
  map_add' x y := Subtype.ext (map_add (scaleAlgHom c) x.val y.val)

/-- The scaling action on the Rees algebra fixes elements of `R`. -/
lemma scaleOnRees_algebraMap (I : Ideal R) (c : R) (r : R) :
    scaleOnRees I c (algebraMap R (reesAlgebra I) r) = algebraMap R (reesAlgebra I) r :=
  Subtype.ext ((scaleAlgHom c).commutes r)

/-- The base ideal `I · R[Rt]` is invariant under the scaling map. -/
lemma reesIdealFromBase_le_comap_scaleOnRees (I : Ideal R) (c : R) :
    reesIdealFromBase I ≤ (reesIdealFromBase I).comap (scaleOnRees I c) := by
  unfold reesIdealFromBase
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  show scaleOnRees I c (algebraMap R (reesAlgebra I) r) ∈
    Ideal.map (algebraMap R (reesAlgebra I)) I
  rw [scaleOnRees_algebraMap]
  exact Ideal.mem_map_of_mem _ hr

/-- The descended scaling action on the associated graded ring. -/
noncomputable def scaleOnGraded (I : Ideal R) (c : R) :
    assocGradedRing I →+* assocGradedRing I :=
  Ideal.Quotient.lift (reesIdealFromBase I)
    ((Ideal.Quotient.mk (reesIdealFromBase I)).comp (scaleOnRees I c))
    (fun x hx => by
      show Ideal.Quotient.mk _ (scaleOnRees I c x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact reesIdealFromBase_le_comap_scaleOnRees I c hx)

/-- The unit `1 ∈ R` acts as the identity on the associated graded ring. -/
theorem scaleOnGraded_one (I : Ideal R) :
    scaleOnGraded I (1 : R) = RingHom.id (assocGradedRing I) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [scaleOnGraded, RingHom.comp_apply, Ideal.Quotient.lift_mk]
  show Ideal.Quotient.mk _ (scaleOnRees I 1 x) = Ideal.Quotient.mk _ x
  congr 1
  apply Subtype.ext
  show scaleAlgHom 1 x.val = x.val
  rw [show scaleAlgHom (1 : R) = AlgHom.id R R[X] from scaleAlgHom_one]
  simp

/-- The scaling action is multiplicative on the associated graded ring. -/
theorem scaleOnGraded_comp (I : Ideal R) (c₁ c₂ : R) :
    scaleOnGraded I (c₁ * c₂) = (scaleOnGraded I c₁).comp (scaleOnGraded I c₂) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [scaleOnGraded, RingHom.comp_apply, Ideal.Quotient.lift_mk]
  show Ideal.Quotient.mk _ (scaleOnRees I (c₁ * c₂) x) =
    Ideal.Quotient.mk _ (scaleOnRees I c₁ (scaleOnRees I c₂ x))
  congr 1
  apply Subtype.ext
  show scaleAlgHom (c₁ * c₂) x.val = scaleAlgHom c₁ (scaleAlgHom c₂ x.val)
  rw [← AlgHom.comp_apply, ← scaleAlgHom_comp]

/-- Proposition 34: the tangent cone is canonically isomorphic to the exceptional
fibre, and the scaling action is a group action. -/
theorem proposition_34_blowup_properties (𝔪 : Ideal R) :

    Nonempty (tangentConeScheme 𝔪 ≅ exceptionalFiberScheme 𝔪) ∧

    (scaleOnGraded 𝔪 1 = RingHom.id _) ∧
    (∀ c₁ c₂ : R, scaleOnGraded 𝔪 (c₁ * c₂) =
      (scaleOnGraded 𝔪 c₁).comp (scaleOnGraded 𝔪 c₂)) :=
  ⟨⟨tangentCone_isoExceptionalFiber 𝔪⟩,
   scaleOnGraded_one 𝔪,
   scaleOnGraded_comp 𝔪⟩


end Prop34Blowup

namespace Prop38TangentCone



end Prop38TangentCone

end
