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
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- For an affine algebraic variety `X` over `k`, the canonical map `X → Spec Γ(X, O_X)` is an
isomorphism. -/
theorem affineVariety_isIso_toSpecΓ
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [Definition3_AlgebraicVariety k X f] [IsAffine X] :
    IsIso X.toSpecΓ :=
  inferInstance

/-- The global sections ring `Γ(X, O_X)` of an affine algebraic variety is reduced. -/
theorem affineVariety_globalSections_isReduced
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [hvar : Definition3_AlgebraicVariety k X f] [IsAffine X] :
    _root_.IsReduced Γ(X, ⊤) := by
  haveI : AlgebraicGeometry.IsReduced X := hvar.reduced
  infer_instance

/-- The structure map `k → Γ(X, O_X)` of an affine algebraic variety is of finite type, i.e.
`Γ(X, O_X)` is a finitely generated `k`-algebra. -/
theorem affineVariety_globalSections_finiteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [hvar : Definition3_AlgebraicVariety k X f] [IsAffine X] :
    RingHom.FiniteType (f.appTop.hom) := by
  haveI : LocallyOfFiniteType f := hvar.locallyOfFiniteType
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance

/-- Forward direction of Theorem 3.1: an affine algebraic variety `X` satisfies `X ≅ Spec Γ(X)`,
its global sections form a reduced finitely-generated `k`-algebra. -/
theorem affineVariety_forward
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [hvar : Definition3_AlgebraicVariety k X f] [IsAffine X] :
    IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom) :=
  ⟨affineVariety_isIso_toSpecΓ k X f,
   affineVariety_globalSections_isReduced k X f,
   affineVariety_globalSections_finiteType k X f⟩

/-- Converse direction: if `A` is a reduced finitely-generated `k`-algebra, then `Spec A` is an
affine algebraic variety over `k`. -/
theorem affineVariety_backward
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsReduced A] :
    Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) where
  locallyOfFiniteType := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    rw [show (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap k A))) = (algebraMap k A) from rfl]
    rw [RingHom.finiteType_algebraMap]
    exact inferInstance
  quasiCompact := inferInstance
  reduced := inferInstance

/-- Combined two directions of Theorem 3.1: an algebraic variety `X` over `k` is affine if and
only if it is `Spec A` for some reduced finitely-generated `k`-algebra `A`. -/
theorem affineVariety_iff_spec_fg_reduced
    (k : Type u) [Field k] :

    (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
      [Definition3_AlgebraicVariety k X f] [IsAffine X],
      IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧

    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  ⟨fun X f _ _ => affineVariety_forward k X f,
   fun A _ _ _ _ => affineVariety_backward k A⟩

/-- Theorem 3.1 (Lec 2/3): Over an algebraically closed field `k`, an algebraic variety is affine
iff it is `Spec A` for some reduced finitely-generated `k`-algebra `A`. -/
theorem Theorem3_1_affineVariety_iff_fg_reduced_algebra
    (k : Type u) [Field k] [IsAlgClosed k] :

    (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
      [Definition3_AlgebraicVariety k X f] [IsAffine X],
      IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧

    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  affineVariety_iff_spec_fg_reduced k

end
