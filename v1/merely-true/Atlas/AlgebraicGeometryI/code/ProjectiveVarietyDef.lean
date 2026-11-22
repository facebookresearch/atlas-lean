/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective `n`-space `P^n_k` as the `Proj` of the standard graded polynomial ring
in `n + 1` variables over `k`. -/
def ProjectiveScheme (k : Type*) [CommRing k] (n : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

/-- A scheme `X` is a projective variety over `k` if it admits a closed immersion into
some projective space `P^n_k`. -/
def AlgebraicGeometry.Scheme.IsProjectiveVariety (k : Type*) [CommRing k]
    (X : Scheme) : Prop :=
  ∃ (n : ℕ) (f : X ⟶ ProjectiveScheme k n), IsClosedImmersion f

end
