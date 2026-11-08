/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open MeasureTheory Real Complex Set
open scoped Topology

theorem Complex.betaIntegral_eq_Gamma_mul_div_Lecture18 (z w : ℂ)
    (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.betaIntegral z w = Complex.Gamma z * Complex.Gamma w / Complex.Gamma (z + w) :=
  Complex.betaIntegral_eq_Gamma_mul_div z w hz hw
