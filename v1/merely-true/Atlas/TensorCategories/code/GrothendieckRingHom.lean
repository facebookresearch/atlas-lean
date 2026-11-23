/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.GrothendieckRing

namespace FusionRing

/-- Proposition 1.16.2: A quasi-tensor functor `F : C → D` induces a unital ring
homomorphism `[F] : Gr(C) → Gr(D)`. Combinatorially, a `FusionRingHom` between fusion rings
induces a ring homomorphism on the underlying Grothendieck rings whose coefficient action
is the original `grMap`. -/
theorem Proposition_1_16_2
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) :
    ∃ f : GrRingOf R →+* GrRingOf S,
      ∀ a, (f a).coeff = φ.grMap a.coeff :=
  ⟨φ.inducedRingHom, fun _ => rfl⟩

end FusionRing
