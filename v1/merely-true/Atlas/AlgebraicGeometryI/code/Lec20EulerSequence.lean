/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.TwistSheaf
import Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective

set_option maxHeartbeats 800000

open QCohProjective TwistSheaf

noncomputable section

namespace EulerSequence

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- A `k`-linear map between the degree-`d` components of two graded module data over `ℙⁿ`. -/
abbrev GrLinMap (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearMap k k _ _ (RingHom.id k) (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- A `k`-linear equivalence between the degree-`d` components of two graded module data. -/
abbrev GrLinEquiv (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k)
    ⟨RingHom.id_comp _, RingHom.comp_id _⟩ ⟨RingHom.id_comp _, RingHom.comp_id _⟩
    (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- A short exact sequence `0 → L → M → R → 0` of graded module data, with degree-wise
injectivity, surjectivity, and exactness at the middle. -/
structure GradedSES where
  left : GradedModuleData.{u, u} k n
  middle : GradedModuleData.{u, u} k n
  right : GradedModuleData.{u, u} k n
  f : ∀ d : ℤ, GrLinMap k n left middle d
  g : ∀ d : ℤ, GrLinMap k n middle right d
  f_injective : ∀ d : ℤ, Function.Injective (f d)
  g_surjective : ∀ d : ℤ, Function.Surjective (g d)
  exact_middle : ∀ (d : ℤ) (x : middle.component d),
    @Eq (right.component d) (g d x)
      (@Zero.zero (right.component d) (right.instACG d).toAddCommMonoid.toZero) ↔
    ∃ a : left.component d, (f d) a = x

/-- The graded module `O(-1)^{n+1}` on `ℙⁿ`, formed as a `(n+1)`-fold direct sum of the
Serre twist `O(-1)`; this is the middle term of the Euler sequence. -/
def directSumTwist : GradedModuleData.{u, u} k n where
  component d := Fin (n + 1) → (serreTwist k n (-1)).component d
  instACG _d := Pi.addCommGroup
  instMod d := @Pi.module (Fin (n + 1)) (fun _ => (serreTwist k n (-1)).component d) k _
    (fun _ => ((serreTwist k n (-1)).instACG d).toAddCommMonoid)
    (fun _ => (serreTwist k n (-1)).instMod d)
  gsmul i j s v := fun idx =>
    (serreTwist k n (-1)).gsmul i j s (v idx)

/-- The type of graded module data on `ℙⁿ` is inhabited (witnessed by the structure sheaf). -/
instance : Nonempty (GradedModuleData.{u, u} k n) :=
  ⟨structureSheafData k n⟩


/-- The canonical bundle `K_{ℙⁿ}` as a graded module datum, equal to the Serre twist
`O(-(n+1))`. -/
noncomputable def canonicalBundleGM : GradedModuleData.{u, u} k n :=
  serreTwist k n (-(↑n + 1 : ℤ))


/-- The canonical bundle on `ℙⁿ` agrees degreewise with the Serre twist `O(-(n+1))`. -/
theorem canonical_bundle_eq_twist :
    ∀ d : ℤ, Nonempty (GrLinEquiv k n (canonicalBundleGM k n) (serreTwist k n (-(↑n + 1 : ℤ))) d) := by
  intro d


  exact ⟨LinearEquiv.refl k _⟩

end EulerSequence

end
