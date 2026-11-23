/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Over

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory

universe u

/-- An *affine variety* over a field `k` (Def 2, Lec 2): a scheme `X` over `Spec k` that is
isomorphic to `Spec Γ(X, O_X)`, is locally of finite type over `k`, and is reduced. -/
class IsAffineVariety (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    Prop where
  toSpecΓ_isIso : IsIso X.toSpecΓ
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (.of k))
  isReduced : AlgebraicGeometry.IsReduced X

/-- Any affine variety is in particular an affine scheme. -/
lemma IsAffineVariety.isAffine {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [h : IsAffineVariety k X] : IsAffine X :=
  ⟨h.toSpecΓ_isIso⟩

attribute [instance] IsAffineVariety.toSpecΓ_isIso IsAffineVariety.locallyOfFiniteType
  IsAffineVariety.isReduced

/-- A `k`-algebra `A` gives `Spec A` the structure of a scheme over `Spec k` via the structure map
of the algebra. -/
noncomputable instance specOverSpec (k : Type u) [Field k] (A : Type u) [CommRing A]
    [Algebra k A] : (Spec (.of A)).Over (Spec (.of k)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap k A))⟩

/-- For `A` a reduced finitely-generated `k`-algebra, `Spec A` is an affine variety over `k`. -/
noncomputable instance specIsAffineVariety (k : Type u) [Field k] (A : Type u) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [_root_.IsReduced A] :
    IsAffineVariety k (Spec (.of A)) where
  toSpecΓ_isIso := (isAffine_Spec _).1
  locallyOfFiniteType := by
    rw [show (Spec (.of A) ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k A))
      from rfl]
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) |>.mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  isReduced := inferInstance

end AlgebraicGeometry.Scheme
