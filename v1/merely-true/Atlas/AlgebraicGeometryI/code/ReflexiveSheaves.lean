/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Ideal.Basic

noncomputable section

namespace ReflexiveSheaf

open Module

/-- The dual sheaf `F^∨ = Hom_R(F, R)` of a module `M`, the local analog of
the dual of a sheaf of `𝒪_X`-modules. -/
abbrev dualSheaf (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] :=
  Module.Dual R M

/-- The double dual sheaf `F^{∨∨}` of a module, the target of the reflexivity
map `F → F^{∨∨}`. -/
abbrev doubleDualSheaf (R : Type*) (M : Type*)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :=
  Module.Dual R (Module.Dual R M)

/-- The reflexivity map `F → F^{∨∨}`, evaluation at the dual. -/
abbrev doubleDualMap (R : Type*) (M : Type*)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    M →ₗ[R] doubleDualSheaf R M :=
  Module.Dual.eval R M

section ReflexivityCharacterization

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- `M` is reflexive iff the evaluation map `M → M^{∨∨}` is a bijection. -/
theorem isReflexive_iff_eval_bijective :
    IsReflexive R M ↔ Function.Bijective (Dual.eval R M) :=
  ⟨fun h => h.bijective_dual_eval', fun h => ⟨h⟩⟩

/-- Evaluation formula: `(eval m)(φ) = φ(m)`. -/
theorem eval_apply_eq (m : M) (φ : Dual R M) :
    doubleDualMap R M m φ = φ m :=
  rfl

end ReflexivityCharacterization

section DoubleDualIso

variable {R : Type*} [CommRing R]

/-- A finitely generated projective module (a locally free sheaf) is reflexive:
the double-dual map is an isomorphism. -/
theorem locallyFree_isReflexive (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    IsReflexive R M :=
  Module.instIsReflexiveOfFiniteOfProjective R M

/-- The double-dual isomorphism `M ≃ M^{∨∨}` packaged as a `LinearEquiv` for
finitely generated projective modules. -/
def doubleDualLocallyFree (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    M ≃ₗ[R] doubleDualSheaf R M :=
  haveI : IsReflexive R M := Module.instIsReflexiveOfFiniteOfProjective R M
  Module.evalEquiv R M

/-- Free modules of finite rank are reflexive. -/
instance freeModule_isReflexive (n : ℕ) : IsReflexive R (Fin n → R) :=
  Module.instIsReflexiveOfFiniteOfProjective R _

end DoubleDualIso

section TensorHomIdentity

/-- The natural identification `Hom_R(M, N) ≃ M^∨ ⊗ N` for a finitely-generated
free `M`, the basic dual-tensor-hom isomorphism for locally free sheaves. -/
def dualTensorHomLocallyFree (R : Type*) (M : Type*) (N : Type*)
    [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module.Free R M] [Module.Finite R M] :
    (M →ₗ[R] N) ≃ₗ[R] TensorProduct R (Module.Dual R M) N :=
  (dualTensorHomEquiv R M N).symm

end TensorHomIdentity

section RankOneDual

variable (R : Type*) [CommRing R]

/-- The ring of endomorphisms of the rank-one free module is isomorphic to `R`
itself, via evaluation at a basis vector. -/
def endRankOneEquiv : ((Fin 1 → R) →ₗ[R] (Fin 1 → R)) ≃ₗ[R] R :=
  (LinearEquiv.arrowCongr (LinearEquiv.funUnique (Fin 1) R R)
    (LinearEquiv.funUnique (Fin 1) R R)).trans (LinearMap.ringLmapEquivSelf R R R)

/-- The dual-tensor-hom contraction for the rank-one free module collapses to
the ring `R`. -/
def dualTensorRankOneIso :
    TensorProduct R (Module.Dual R (Fin 1 → R)) (Fin 1 → R) ≃ₗ[R] R :=
  (dualTensorHomEquiv R (Fin 1 → R) (Fin 1 → R)).trans (endRankOneEquiv R)

/-- An invertible sheaf (here represented as the rank-one free module) is reflexive. -/
instance invertibleSheaf_isReflexive : IsReflexive R (Fin 1 → R) :=
  Module.instIsReflexiveOfFiniteOfProjective R _

end RankOneDual

end ReflexiveSheaf
