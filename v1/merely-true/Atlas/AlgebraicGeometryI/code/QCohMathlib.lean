/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Atlas.AlgebraicGeometryI.code.QCohTildeFunctor

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace QCohMathlib

variable {R : CommRingCat.{u}}

/-- The tilde functor `Mod R → (Spec R).Modules` is faithful. -/
instance tilde_functor_faithful : (tilde.functor R).Faithful :=
  tilde.fullyFaithfulFunctor.faithful

/-- The tilde functor `Mod R → (Spec R).Modules` is full. -/
instance tilde_functor_full : (tilde.functor R).Full :=
  tilde.fullyFaithfulFunctor.full

/-- Packaged fully-faithful structure for the tilde functor, exposing both
fullness and faithfulness simultaneously. -/
def tilde_fullyFaithful : (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

/-- The tilde functor is the left adjoint of the `tilde ⊣ Γ` adjunction. -/
instance tilde_isLeftAdjoint : (tilde.functor R).IsLeftAdjoint :=
  tilde.adjunction.isLeftAdjoint

/-- For every module `M`, the sheaf `M̃` is quasi-coherent (Cor 16). -/
instance tilde_isQuasicoherent (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent := inferInstance

/-- The corestriction of tilde to its essential image is an equivalence of
categories, since tilde is fully faithful. -/
instance tilde_toEssImage_isEquivalence :
    (tilde.functor R).toEssImage.IsEquivalence :=
  Functor.IsEquivalence.mk

end QCohMathlib
