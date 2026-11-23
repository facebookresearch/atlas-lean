/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup

namespace IsDedekindDomain

theorem uniqueFactorizationMonoid_iff_isPrincipalIdealRing
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    UniqueFactorizationMonoid R ↔ IsPrincipalIdealRing R := by
  constructor
  · intro
    exact IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid R
  · intro
    exact PrincipalIdealRing.to_uniqueFactorizationMonoid

theorem isPrincipalIdealRing_iff_subsingleton_classGroup
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    IsPrincipalIdealRing R ↔ Subsingleton (ClassGroup R) := by
  constructor
  · intro
    have : Fintype.card (ClassGroup R) = 1 := card_classGroup_eq_one
    rw [← Fintype.card_le_one_iff_subsingleton]
    omega
  · intro
    letI : Fintype (ClassGroup R) := Fintype.ofSubsingleton (default : ClassGroup R)
    rw [← card_classGroup_eq_one_iff]
    exact Fintype.card_ofSubsingleton _

theorem uniqueFactorizationMonoid_iff_subsingleton_classGroup
    (R : Type*) [CommRing R] [IsDedekindDomain R] :
    UniqueFactorizationMonoid R ↔ Subsingleton (ClassGroup R) :=
  (uniqueFactorizationMonoid_iff_isPrincipalIdealRing R).trans
    (isPrincipalIdealRing_iff_subsingleton_classGroup R)

end IsDedekindDomain
