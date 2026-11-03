/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch

open RiemannRochSpace

/-- Data packaging a base extension $k \hookrightarrow k'$ for a smooth projective curve
$(C, F/k)$: a new curve $C'$ over a field $F'/k'$, together with a `RiemannRochData` structure on
$(C', F', k')$ and explicit divisor base-extension and restriction maps. -/
structure BaseExtensionData
    (C : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k] where
  C' : Type*
  F' : Type*
  k' : Type*
  field_k' : Field k'
  field_F' : Field F'
  algebra_k_k' : Algebra k k'
  algebra_k'_F' : Algebra k' F'
  rrData' : RiemannRochData C' F' k'
  baseExtDiv : CurveDivisor C → CurveDivisor C'
  restrictDiv : CurveDivisor C' → CurveDivisor C

attribute [instance] BaseExtensionData.field_k' BaseExtensionData.field_F'
  BaseExtensionData.algebra_k_k' BaseExtensionData.algebra_k'_F'
  BaseExtensionData.rrData'





