/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.FiniteType

section HilbertNoether

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {G : Type*} [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]

instance fixedPoints_isInvariant :
    Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G where
  isInvariant a ha := ⟨⟨a, ha⟩, rfl⟩

theorem hilbert_noether_integral :
    Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
  Algebra.IsInvariant.isIntegral _ A G

theorem hilbert_noether_module_finite
    [Algebra.FiniteType R A] :
    Module.Finite (FixedPoints.subalgebra R A G) A := by
  have : Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
    hilbert_noether_integral (R := R) (A := A) (G := G)
  have : Algebra.FiniteType (FixedPoints.subalgebra R A G) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (FixedPoints.subalgebra R A G) A
  exact Algebra.IsIntegral.finite

theorem hilbert_noether_fg
    [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FiniteType R (FixedPoints.subalgebra R A G) :=
  ⟨fg_of_fg_of_fg R (↥(FixedPoints.subalgebra R A G)) A
    (Algebra.FiniteType.out (R := R) (A := A))
    (hilbert_noether_module_finite (R := R) (A := A) (G := G)).1
    Subtype.val_injective⟩

end HilbertNoether
