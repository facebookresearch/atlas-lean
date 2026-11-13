/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- Definition 3: An algebraic variety over `k` is a scheme `X` with a morphism `f : X → Spec k`
that is locally of finite type, quasicompact, and whose total space is reduced. -/
class Definition3_AlgebraicVariety (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f
  quasiCompact : QuasiCompact f
  reduced : AlgebraicGeometry.IsReduced X

/-- Theorem 2.2 (forward direction): An affine algebraic variety `X` over `k` is canonically
isomorphic to `Spec Γ(X, ⊤)`, with reduced and finite-type global sections. -/
theorem Theorem2_2_forward
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [hvar : Definition3_AlgebraicVariety k X f] [IsAffine X] :
    IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom) := by
  haveI : AlgebraicGeometry.IsReduced X := hvar.reduced
  haveI : LocallyOfFiniteType f := hvar.locallyOfFiniteType
  exact ⟨inferInstance, inferInstance,
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance⟩

/-- Theorem 2.2 (backward direction): For any finitely generated reduced `k`-algebra `A`,
the affine scheme `Spec A` is an algebraic variety over `k`. -/
theorem Theorem2_2_backward
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

/-- Theorem 2.2 (full characterisation): A scheme over `k` is an affine algebraic variety
iff it is `Spec A` for a finitely generated reduced `k`-algebra `A`. -/
theorem thm22_affine_variety_characterization
    (k : Type u) [Field k] :

    (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
      [Definition3_AlgebraicVariety k X f] [IsAffine X],
      IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧

    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  ⟨fun X f _ _ => Theorem2_2_forward k X f, fun A _ _ _ _ => Theorem2_2_backward k A⟩

/-- Restatement of the affine-variety characterisation, packaged under the index used
in Lecture 3. -/
theorem thm31_affine_variety_characterization
    (k : Type u) [Field k] :

    (∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
      [Definition3_AlgebraicVariety k X f] [IsAffine X],
      IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧

    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A],
      Definition3_AlgebraicVariety k (Spec (CommRingCat.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
  thm22_affine_variety_characterization k

/-- Lemma 2 (part 1): A closed subscheme of an affine scheme is affine. -/
theorem Lemma2_ClosedSubspaceAffine
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] :
    IsAffine Z :=
  isAffine_of_isAffineHom i

/-- Lemma 2 (part 2): A closed immersion into an affine scheme induces a surjection on
global sections. -/
theorem Lemma2_GlobalSectionsSurjective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] :
    Function.Surjective i.appTop :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- Lemma 2 (combined): A closed subscheme of an affine scheme is affine and the closed
immersion is surjective on global sections. -/
theorem Lemma2_combined
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] :
    IsAffine Z ∧ Function.Surjective i.appTop :=
  ⟨Lemma2_ClosedSubspaceAffine i, Lemma2_GlobalSectionsSurjective i⟩

/-- Corollary 2: A reduced closed subscheme of an algebraic variety is again an algebraic
variety (with composed structure map to `Spec k`). -/
theorem Corollary2_ClosedSubspaceOfVariety
    (k : Type u) [Field k] (X Z : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k))
    [Definition3_AlgebraicVariety k X f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [AlgebraicGeometry.IsReduced Z] :
    Definition3_AlgebraicVariety k Z (i ≫ f) where
  locallyOfFiniteType := by
    haveI : LocallyOfFiniteType f := Definition3_AlgebraicVariety.locallyOfFiniteType
    infer_instance
  quasiCompact := by
    haveI : QuasiCompact f := Definition3_AlgebraicVariety.quasiCompact
    infer_instance
  reduced := inferInstance

/-- Theorem 2.3 (Hilbert basis): The polynomial ring `k[x₁, …, xₙ]` over a field is
Noetherian. -/
theorem Theorem2_3_HilbertBasis_PolynomialRing
    (k : Type u) [Field k] (n : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin n) k) :=
  inferInstance

/-- The natural ℕ-grading of `k[x₀, …, xₙ]` by total degree, used to define `ℙⁿ_k = Proj`. -/
def polynomialGrading (k : Type u) [Field k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The degree-grading of `k[x₀, …, xₙ]` gives it the structure of a graded ring. -/
instance polynomialGradedRing (k : Type u) [Field k] (n : ℕ) :
    GradedRing (polynomialGrading k n) :=
  MvPolynomial.gradedAlgebra

/-- Definition 4: The projective `n`-space `ℙⁿ_k`, realised as `Proj k[x₀, …, xₙ]`. -/
def Definition4_ProjectiveSpace (k : Type u) [Field k] (n : ℕ) : Scheme :=
  AlgebraicGeometry.Proj (polynomialGrading k n)

/-- The underlying topological space of `ℙⁿ_k`. -/
instance Definition4_ProjectiveSpace_topologicalSpace (k : Type u) [Field k] (n : ℕ) :
    TopologicalSpace (Definition4_ProjectiveSpace k n) :=
  inferInstance

/-- The structure sheaf `O_{ℙⁿ_k}` of projective space. -/
def Definition4_structureSheaf (k : Type u) [Field k] (n : ℕ) :
    TopCat.Presheaf CommRingCat (Definition4_ProjectiveSpace k n).carrier :=
  (Definition4_ProjectiveSpace k n).presheaf
