/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory

namespace Chapter5.Problem52

/-- Real-valued KL divergence used in Problem 5.2: `(klDiv P Q).toReal`. -/
noncomputable def klDivReal {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  (klDiv P Q).toReal

end Chapter5.Problem52
