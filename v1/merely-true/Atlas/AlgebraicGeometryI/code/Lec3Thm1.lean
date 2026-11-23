/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties
import Mathlib.FieldTheory.IsAlgClosed.Basic

open AlgebraicGeometry CategoryTheory

noncomputable section

universe v

/-- Lecture 3, Theorem 3.1: characterisation of affine algebraic varieties over an algebraically
closed field as `Spec A` for reduced finitely generated `k`-algebras `A`. -/
theorem thm3_1_affine_iff_spec_g16
    (k : Type v) [Field k] [IsAlgClosed k] :

    (∀ (X : Scheme.{v}) (f : X ⟶ Spec (CommRingCat.of k))
      [Definition3_AlgebraicVariety k X f] [IsAffine X],
      IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧

    (∀ (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  thm31_affine_variety_characterization (k := k)

end
