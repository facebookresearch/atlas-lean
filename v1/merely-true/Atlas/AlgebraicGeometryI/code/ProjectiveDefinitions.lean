/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open AlgebraicGeometry CategoryTheory

universe u

namespace ProjectiveDefinitions

/-- The standard grading on the polynomial ring `k[x_0, ..., x_n]` by total degree, where
`polynomialGrading k n d` is the `k`-submodule of homogeneous polynomials of degree `d`. -/
noncomputable abbrev polynomialGrading (k : Type u) [CommRing k] (n : ℕ) :
    ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The polynomial ring `k[x_0, ..., x_n]` is a graded ring under the total-degree
grading. -/
noncomputable instance polynomialGradedAlgebra (k : Type u) [CommRing k] (n : ℕ) :
    GradedRing (polynomialGrading k n) :=
  MvPolynomial.gradedAlgebra

/-- Projective `n`-space over a commutative ring `k`, defined as
`ℙ^n_k := Proj k[x_0, ..., x_n]` with the standard grading. -/
noncomputable def ProjectiveSpace (k : Type u) [CommRing k] (n : ℕ) : Scheme :=
  Proj (polynomialGrading k n)

/-- The structure morphism `ℙ^n_k → Spec k` of projective `n`-space, induced by the
inclusion of the degree-zero piece into the graded polynomial ring. -/
noncomputable def ProjectiveSpace.structureMorphism (k : Type u) [CommRing k] (n : ℕ) :
    ProjectiveSpace k n ⟶ Spec (CommRingCat.of ↥((polynomialGrading k n) 0)) :=
  Proj.toSpecZero (polynomialGrading k n)

/-- Projective `n`-space `ℙ^n_k` is a separated scheme. -/
theorem ProjectiveSpace.isSeparated (k : Type u) [CommRing k] (n : ℕ) :
    Scheme.IsSeparated (ProjectiveSpace k n) := by
  unfold ProjectiveSpace
  infer_instance

/-- A scheme `X` is a **projective variety** over `k` if it admits a closed immersion
into some projective space `ℙ^n_k`. -/
def IsProjectiveVariety (k : Type u) [CommRing k] (X : Scheme) : Prop :=
  ∃ (n : ℕ) (ι : X ⟶ ProjectiveSpace k n), IsClosedImmersion ι

/-- A scheme `X` is a **quasi-projective variety** over `k` if it is an open subscheme of
a projective variety: there exists a closed immersion `Y ↪ ℙ^n_k` and an open immersion
`X ↪ Y`. -/
def IsQuasiProjectiveVariety (k : Type u) [CommRing k] (X : Scheme) : Prop :=
  ∃ (n : ℕ) (Y : Scheme) (ι : Y ⟶ ProjectiveSpace k n) (_ : IsClosedImmersion ι)
    (j : X ⟶ Y), IsOpenImmersion j

/-- Every projective variety is quasi-projective: take the open immersion to be the
identity. -/
theorem IsProjectiveVariety.isQuasiProjective {k : Type u} [CommRing k] {X : Scheme}
    (h : IsProjectiveVariety k X) : IsQuasiProjectiveVariety k X := by
  obtain ⟨n, ι, hι⟩ := h
  exact ⟨n, X, ι, hι, 𝟙 X, inferInstance⟩

/-- Projective space `ℙ^n_k` is itself a projective variety, via the identity closed
immersion. -/
theorem projectiveSpace_isProjective (k : Type u) [CommRing k] (n : ℕ) :
    IsProjectiveVariety k (ProjectiveSpace k n) :=
  ⟨n, 𝟙 _, inferInstance⟩

/-- Projective space `ℙ^n_k` is in particular quasi-projective. -/
theorem projectiveSpace_isQuasiProjective (k : Type u) [CommRing k] (n : ℕ) :
    IsQuasiProjectiveVariety k (ProjectiveSpace k n) :=
  (projectiveSpace_isProjective k n).isQuasiProjective

/-- A closed subscheme of a projective variety is again a projective variety: compose the
closed immersion `X ↪ Y` with a closed immersion `Y ↪ ℙ^n_k`. -/
theorem IsProjectiveVariety.of_closedImmersion {k : Type u} [CommRing k]
    {X Y : Scheme} (hY : IsProjectiveVariety k Y)
    (ι : X ⟶ Y) [hι : IsClosedImmersion ι] : IsProjectiveVariety k X := by
  obtain ⟨n, j, hj⟩ := hY
  exact ⟨n, ι ≫ j, inferInstance⟩

/-- An open subscheme of a quasi-projective variety is again quasi-projective: compose
the open immersion `X ↪ Y` with the existing open immersion of `Y` into a projective
variety. -/
theorem IsQuasiProjectiveVariety.of_openImmersion {k : Type u} [CommRing k]
    {X Y : Scheme} (hY : IsQuasiProjectiveVariety k Y)
    (j : X ⟶ Y) [hj : IsOpenImmersion j] : IsQuasiProjectiveVariety k X := by
  obtain ⟨n, Z, ι, hι, f, hf⟩ := hY
  exact ⟨n, Z, ι, hι, j ≫ f, inferInstance⟩

end ProjectiveDefinitions
