/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity

open Algebra

section TracePairingDef

variable (A : Type*) [CommRing A]
variable (B : Type*) [CommRing B] [Algebra A B]

noncomputable def tracePairing : LinearMap.BilinForm A B :=
  Algebra.traceForm A B

end TracePairingDef

section AKLB

variable (A : Type*) [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra A L] [IsScalarTower A K L]
variable (B : Type*) [CommRing B] [IsDomain B] [Algebra B L] [IsIntegralClosure B A L]
  [Algebra A B] [IsScalarTower A B L]

include A K in
theorem prop_5_17_isFractionRing : IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L B

omit [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [IsDomain B] in
include K in
theorem prop_5_18_norm_isIntegral (b : B) :
    IsIntegral A (Algebra.norm K (algebraMap B L b)) :=
  Algebra.isIntegral_norm K ((IsIntegralClosure.isIntegral A L b).algebraMap)

omit [IsDomain A] [IsFractionRing A K] [IsDomain B] in
include K in
theorem prop_5_18_trace_isIntegral (b : B) :
    IsIntegral A (Algebra.trace K L (algebraMap B L b)) :=
  Algebra.isIntegral_trace ((IsIntegralClosure.isIntegral A L b).algebraMap)

omit [FiniteDimensional K L] in

omit [FiniteDimensional K L] in
theorem thm_5_20_traceForm_symmetric :
    (Algebra.traceForm K L).IsSymm :=
  Algebra.traceForm_isSymm K

variable [Algebra.IsSeparable K L] in
theorem thm_5_20_nondegenerate_of_separable :
    (Algebra.traceForm K L).Nondegenerate :=
  traceForm_nondegenerate K L

theorem thm_5_20_separable_of_nondegenerate
    (hnd : (Algebra.traceForm K L).Nondegenerate) :
    Algebra.IsSeparable K L :=
  ((traceForm_nondegenerate_tfae K L).out 2 0).mp hnd

theorem thm_5_20_nondegenerate_iff_separable :
    [Algebra.IsSeparable K L, Algebra.trace K L ≠ 0,
     (Algebra.traceForm K L).Nondegenerate].TFAE :=
  traceForm_nondegenerate_tfae K L

omit [IsDomain B] in
include K L in
variable [IsDedekindDomain A] [Algebra.IsSeparable K L] in
theorem prop_5_22_finite : Module.Finite A B :=
  IsIntegralClosure.finite A K L B

omit [IsDomain B] in
include K L in
variable [IsDedekindDomain A] [Algebra.IsSeparable K L] in
theorem prop_5_22_isNoetherian : IsNoetherian A B :=
  IsIntegralClosure.isNoetherian A K L B

end AKLB

alias traceForm_symmetric := thm_5_20_traceForm_symmetric
