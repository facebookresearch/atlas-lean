/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.FiniteType
import Mathlib.CategoryTheory.Iso
import Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- Theorem 2.2 (first half): For an affine algebraic variety `X` over `k`, the canonical
map `X → Spec Γ(X, ⊤)` is an isomorphism. -/
theorem Theorem2_2_isIso_toSpecΓ
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [Definition3_AlgebraicVariety k X f] [IsAffine X] :
    IsIso X.toSpecΓ :=
  inferInstance

/-- Theorem 2.2 (second half): For an affine algebraic variety, the global section ring
`Γ(X, ⊤)` is reduced. -/
theorem Theorem2_2_globalSections_isReduced
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [hvar : Definition3_AlgebraicVariety k X f] [IsAffine X] :
    _root_.IsReduced Γ(X, ⊤) := by
  haveI : AlgebraicGeometry.IsReduced X := hvar.reduced
  infer_instance

/-- Theorem 2.2 (third half): For an affine algebraic variety, the global section ring
`Γ(X, ⊤)` is a finitely generated `k`-algebra. -/
theorem Theorem2_2_globalSections_finiteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [hvar : Definition3_AlgebraicVariety k X f] [IsAffine X] :
    RingHom.FiniteType (f.appTop.hom) := by
  haveI : LocallyOfFiniteType f := hvar.locallyOfFiniteType
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance

/-- Theorem 2.2 (full equivalence): Affine algebraic varieties over `k` correspond exactly
to spectra `Spec A` of finitely generated reduced `k`-algebras `A`. -/
theorem Theorem2_2_affineVariety_iff_spec
    (k : Type u) [Field k] :

    (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
      [Definition3_AlgebraicVariety k X f] [IsAffine X],
      IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧

    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  ⟨fun X f _ _ => Theorem2_2_forward k X f,
   fun A _ _ _ _ => Theorem2_2_backward k A⟩

end
