/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.ClassGroupRatFunc
import Atlas.ArithmeticGeometry.code.DegreePullback

namespace ArithmeticGeometry

/-- An axiomatic structure for a smooth projective curve $C/k$: it bundles the function field, divisor group, degree-zero Picard group $\operatorname{Pic}^0(C)$, set of rational points, principal divisor map, class map, genus, and the basic compatibilities between them. -/
structure SmoothProjectiveCurve (k : Type*) [Field k] where
  FunField : Type*
  [fieldInst : Field FunField]
  [algebraInst : Algebra k FunField]
  DivGroup : Type*
  [divGroupInst : AddCommGroup DivGroup]
  Pic0 : Type*
  [pic0Inst : AddCommGroup Pic0]
  RatPoint : Type*
  pointToDivisor : RatPoint → DivGroup
  degreeMap : DivGroup →+ ℤ
  degree_point : ∀ P : RatPoint, degreeMap (pointToDivisor P) = 1
  principalDiv : FunField → DivGroup
  degree_principalDiv : ∀ f : FunField, degreeMap (principalDiv f) = 0
  classMap : DivGroup →+ Pic0
  principalDiv_in_kernel : ∀ f : FunField, f ≠ 0 → classMap (principalDiv f) = 0
  classMap_surj : ∀ x : Pic0, ∃ D : DivGroup, degreeMap D = 0 ∧ classMap D = x
  classMap_eq_zero_iff : ∀ D : DivGroup, degreeMap D = 0 →
    (classMap D = 0 ↔ ∃ f : FunField, f ≠ 0 ∧ principalDiv f = D)
  pointToDivisor_injective : Function.Injective pointToDivisor
  principalDiv_algebraMap : ∀ a : k, principalDiv (algebraMap k FunField a) = 0
  isAlgebraic_implies_mem_range_algebraMap :
    ∀ f : FunField, IsAlgebraic k f → f ∈ Set.range (algebraMap k FunField)
  genusVal : ℕ
  exists_two_ratPoints_of_algClosed : IsAlgClosed k → ∃ P Q : RatPoint, P ≠ Q
  principalDiv_mul : ∀ (f g : FunField), f ≠ 0 → g ≠ 0 →
    principalDiv (f * g) = principalDiv f + principalDiv g

attribute [instance] SmoothProjectiveCurve.fieldInst
  SmoothProjectiveCurve.algebraInst
  SmoothProjectiveCurve.divGroupInst
  SmoothProjectiveCurve.pic0Inst

variable {k : Type*} [Field k]



/-- Over an algebraically closed field, a smooth projective curve has at least two distinct rational points. -/
theorem SmoothProjectiveCurve.exists_two_ratPoints (C : SmoothProjectiveCurve k)
    [IsAlgClosed k] : ∃ P Q : C.RatPoint, P ≠ Q :=
  C.exists_two_ratPoints_of_algClosed ‹IsAlgClosed k›

/-- If $f \in k(C)$ has a nonzero principal divisor, then $f$ is transcendental over $k$ (an algebraic element would lie in $k \subseteq k(C)$ and have trivial divisor). -/
theorem SmoothProjectiveCurve.transcendental_of_principalDiv_ne_zero
    (C : SmoothProjectiveCurve k)
    (f : C.FunField) (hf : C.principalDiv f ≠ 0) : Transcendental k f := by

  intro hfalg
  apply hf

  obtain ⟨a, ha⟩ := C.isAlgebraic_implies_mem_range_algebraMap f hfalg

  rw [← ha, C.principalDiv_algebraMap]

/-- Helper lemma: if a subfield $K \subseteq F$ equals all of $F$, then $F$ has dimension $1$ as a $K$-vector space. -/
lemma finrank_eq_one_of_subfield_eq_top {F : Type*} [Field F]
    (K : Subfield F) (h : K = ⊤) : Module.finrank K F = 1 := by
  subst h
  have hbij : Function.Bijective (algebraMap (↥(⊤ : Subfield F)) F) :=
    ⟨Subtype.val_injective, fun x => ⟨⟨x, Subfield.mem_top x⟩, rfl⟩⟩
  have hle : LinearEquiv (RingHom.id ↥(⊤ : Subfield F)) ↥(⊤ : Subfield F) F :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij
  rw [← hle.finrank_eq]
  exact Module.finrank_self _



/-- A smooth projective curve $C/k$ is isomorphic to $\mathbb{P}^1_k$ iff its function field $k(C)$ is $k$-algebra isomorphic to the rational function field $k(t)$. -/
def SmoothProjectiveCurve.IsIsomorphicToP1 (C : SmoothProjectiveCurve k) : Prop :=
  Nonempty (C.FunField ≃ₐ[k] RatFunc k)

/-- The Picard group $\operatorname{Pic}^0(C)$ is trivial iff every degree-zero divisor class is the identity. -/
def SmoothProjectiveCurve.Pic0IsTrivial (C : SmoothProjectiveCurve k) : Prop :=
  ∀ x : C.Pic0, x = 0











/-- Over an algebraically closed field, a smooth projective curve has two distinct rational points. -/
theorem exists_distinct_rational_points [IsAlgClosed k]
    (C : SmoothProjectiveCurve k) : ∃ P Q : C.RatPoint, P ≠ Q :=
  C.exists_two_ratPoints

/-- If $f \in k(C)$ has divisor $(P) - (Q)$ with $P \neq Q$, then $f$ is transcendental and induces an injective $k$-algebra homomorphism $k(t) \hookrightarrow k(C)$ by $t \mapsto f$. -/
theorem exists_injective_algHom_of_nontrivial_div (C : SmoothProjectiveCurve k)
    {P Q : C.RatPoint} (hPQ : P ≠ Q)
    {f : C.FunField} (_hf : f ≠ 0)
    (hdiv : C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q)) :
    ∃ φ : RatFunc k →ₐ[k] C.FunField, Function.Injective φ := by

  have hdiv_ne : C.principalDiv f ≠ 0 := by
    rw [hdiv]
    intro h
    apply hPQ
    apply C.pointToDivisor_injective
    rw [add_neg_eq_zero] at h
    exact h

  have hf_trans : Transcendental k f := C.transcendental_of_principalDiv_ne_zero f hdiv_ne

  have hinj : Function.Injective (Polynomial.aeval (R := k) f) :=
    transcendental_iff_injective.mp hf_trans

  exact ⟨_, RatFunc.liftAlgHom_injective _ hinj⟩


/-- A bijective $k$-algebra homomorphism $k(t) \to k(C)$ gives the isomorphism $C \cong \mathbb{P}^1_k$. -/
theorem iso_of_bijective_algHom (C : SmoothProjectiveCurve k)
    (φ : RatFunc k →ₐ[k] C.FunField)
    (hφ : Function.Bijective φ) :
    C.IsIsomorphicToP1 :=
  ⟨(AlgEquiv.ofBijective φ hφ).symm⟩


/-- If $\operatorname{Pic}^0(C) = 0$, then for any two rational points $P, Q$, the degree-zero divisor $(P) - (Q)$ is principal: there is a function $f \in k(C)$ with $\operatorname{div}(f) = (P) - (Q)$. -/
theorem principal_of_Pic0_trivial (C : SmoothProjectiveCurve k)
    (htriv : C.Pic0IsTrivial) (P Q : C.RatPoint) :
    ∃ f : C.FunField, f ≠ 0 ∧
      C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q) := by

  have hdeg : C.degreeMap (C.pointToDivisor P + (-C.pointToDivisor Q)) = 0 := by
    rw [map_add, map_neg, C.degree_point P, C.degree_point Q]; omega

  have hcl : C.classMap (C.pointToDivisor P + (-C.pointToDivisor Q)) = 0 :=
    htriv _

  rwa [C.classMap_eq_zero_iff _ hdeg] at hcl



end ArithmeticGeometry
