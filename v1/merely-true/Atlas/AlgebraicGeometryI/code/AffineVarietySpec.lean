/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.AffineVarietyDef

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

/-- For an affine variety `X` over `k`, the global sections `Γ(X, O_X)` form a reduced ring. -/
theorem IsAffineVariety.globalSections_isReduced
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [h : IsAffineVariety k X] :
    _root_.IsReduced Γ(X, ⊤) := by
  haveI : AlgebraicGeometry.IsReduced X := h.isReduced
  infer_instance

/-- For an affine variety `X` over `k`, the structure map `k → Γ(X, O_X)` is of finite type. -/
theorem IsAffineVariety.appTop_finiteType
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [h : IsAffineVariety k X] :
    RingHom.FiniteType ((X ↘ Spec (.of k)).appTop.hom) := by
  haveI : IsAffine X := ⟨h.toSpecΓ_isIso⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := h.locallyOfFiniteType
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance

/-- Theorem 2.2 (Lec 2): the two equivalent characterizations of affine varieties — every affine
variety `X` over `k` satisfies `X ≅ Spec Γ(X)` with reduced finitely-generated coordinate ring,
and conversely `Spec A` for any such `A` is an affine variety. -/
theorem Theorem2_2_affineVariety_iff_spec_IsAffineVariety (k : Type u) [Field k] :
    (∀ (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffineVariety k X],
      IsIso X.toSpecΓ ∧
      _root_.IsReduced Γ(X, ⊤) ∧
      RingHom.FiniteType ((X ↘ Spec (.of k)).appTop.hom)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [_root_.IsReduced A],
      IsAffineVariety k (Spec (.of A))) := by
  constructor
  · intro X _ h
    exact ⟨h.toSpecΓ_isIso,
      h.globalSections_isReduced,
      h.appTop_finiteType⟩
  · intro A _ _ _ _
    infer_instance

end
end AlgebraicGeometry.Scheme
