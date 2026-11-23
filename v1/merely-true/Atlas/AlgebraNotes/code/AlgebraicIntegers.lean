/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Order.Atoms
import Mathlib.RingTheory.PrincipalIdealDomain

namespace AlgebraicIntegers

theorem ideal_le_maximal {R : Type*} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≠ ⊤) : ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M :=
  Ideal.exists_le_maximal I hI

end AlgebraicIntegers
