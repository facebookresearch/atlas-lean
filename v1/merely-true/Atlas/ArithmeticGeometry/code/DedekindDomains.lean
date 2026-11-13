/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Basic

open Ideal Ring

/-- If $A$ is a Noetherian, integrally closed domain of Krull dimension $\leq 1$ (i.e. a Dedekind domain), then the localization $A_P$ at any nonzero prime $P$ is a discrete valuation ring. -/
theorem integrally_closed_noetherian_dim_one_localization_isDVR
    (A : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  haveI : IsDedekindDomain A :=
    (isDedekindDomain_iff A (FractionRing A)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
       fun hx => (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hx⟩
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP
    (Localization.AtPrime P)
