/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE

open IsLocalRing Module

namespace DiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R]

variable [IsNoetherianRing R] [IsLocalRing R]

theorem dvr_tfae (hR : ¬IsField R) :
    List.TFAE
      [IsDiscreteValuationRing R,
       ValuationRing R,
       IsDedekindDomain R,
       IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime,
       (maximalIdeal R).IsPrincipal,
       finrank (ResidueField R) (CotangentSpace R) = 1,
       ∀ (I : Ideal R), I ≠ ⊥ → ∃ n : ℕ, I = maximalIdeal R ^ n] :=
  IsDiscreteValuationRing.TFAE R hR

end DiscreteValuationRing
