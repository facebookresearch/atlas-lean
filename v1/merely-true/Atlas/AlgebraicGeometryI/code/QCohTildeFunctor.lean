/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

namespace QCohTildeFunctor

open Submodule

/-- An element of a module is zero whenever its image in every maximal
localization vanishes; the standard local-to-global zero criterion. -/
theorem element_zero_of_localization_zero {R : Type*} [CommRing R]
    {N : Type*} [AddCommGroup N] [Module R N]
    (n : N) (h : ∀ (P : Ideal R) [P.IsMaximal],
      LocalizedModule.mkLinearMap P.primeCompl N n = 0) :
    n = 0 :=
  @Module.eq_of_localization_maximal R N _ _ _
    (fun P _ => LocalizedModule P.primeCompl N)
    (fun P _ => inferInstance) (fun P _ => inferInstance)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl N)
    (fun P _ => inferInstance)
    n 0 (fun P _ => by rw [h P, map_zero])

/-- Iterated localization `T = N^{-1}(M^{-1} R)` realizes `T` as a localization
of `R` at a single combined submonoid, the transitivity-of-localization principle. -/
theorem localization_localization_isLocalization'
    {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S] [Algebra R S]
    [IsLocalization M S] (N : Submonoid S) (T : Type*) [CommRing T] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [IsLocalization N T] :
    IsLocalization (IsLocalization.localizationLocalizationSubmodule M N) T :=
  IsLocalization.localization_localization_isLocalization M N T

end QCohTildeFunctor
