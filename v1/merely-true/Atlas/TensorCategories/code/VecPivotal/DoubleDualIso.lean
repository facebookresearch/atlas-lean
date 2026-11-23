/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory Module

universe u

variable (k : Type u) [Field k]

/-- The double-dual endofunctor on `FGModuleCat k`, sending `V` to `(V*)*` and
acting on morphisms by `f ↦ f.dualMap.dualMap`. -/
noncomputable def doubleDualFunctor : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k where
  obj V := FGModuleCat.of k (Module.Dual k (Module.Dual k V))
  map f := FGModuleCat.ofHom (f.hom.hom.dualMap.dualMap)
  map_id X := by ext x φ; rfl
  map_comp f g := by ext x φ; rfl

/-- The natural isomorphism between the identity functor on `FGModuleCat k` and the
double-dual functor, given componentwise by the canonical evaluation map. -/
noncomputable def doubleDualNatIso :
    (𝟭 (FGModuleCat.{u} k)) ≅ doubleDualFunctor k :=
  NatIso.ofComponents
    (fun V => (Module.evalEquiv k V).toFGModuleCatIso)
    (fun {V W} f => by ext v; rfl)
