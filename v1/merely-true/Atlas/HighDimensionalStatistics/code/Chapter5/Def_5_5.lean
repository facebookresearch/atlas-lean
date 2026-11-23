/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory

set_option maxHeartbeats 4800000

open InformationTheory MeasureTheory MeasureTheory.Measure

noncomputable section

namespace Rigollet.Chapter5

/-- Kullback–Leibler divergence (Definition 5.5):
`KL(P ‖ Q) = ∫ log(dP/dQ) dP` if `P ≪ Q`, else `+∞`. Wraps Mathlib's `klDiv`. -/
noncomputable def klDivergence {Omega : Type*} [MeasurableSpace Omega]
    (P Q : Measure Omega) : ENNReal :=
  klDiv P Q

section Prop_5_6

/-- Nonnegativity part of Proposition 5.6: `KL(P ‖ Q) ≥ 0` for all measures. -/
theorem prop_5_6_nonneg {Omega : Type*} [MeasurableSpace Omega]
    (P Q : Measure Omega) : (0 : ENNReal) ≤ klDiv P Q :=
  zero_le _

/-- Gibbs' inequality, real-valued form: under absolute continuity and
integrability of the log-likelihood ratio,
`∫ llr P Q dP + Q(Ω) - P(Ω) ≥ 0`. -/
theorem prop_5_6_gibbs_real {Omega : Type*} [MeasurableSpace Omega]
    {P Q : Measure Omega} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P.AbsolutelyContinuous Q) (h_int : Integrable (llr P Q) P) :
    0 ≤ ∫ x, llr P Q x ∂P + Q.real Set.univ - P.real Set.univ :=
  integral_llr_add_sub_measure_univ_nonneg hPQ h_int

/-- The Radon–Nikodym derivative of a product measure factorises:
`d(P₁ × P₂)/d(Q₁ × Q₂)(x, y) = (dP₁/dQ₁)(x) · (dP₂/dQ₂)(y)` (a.e.). -/
theorem rnDeriv_prod_eq {alpha beta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    {P1 Q1 : Measure alpha} {P2 Q2 : Measure beta}
    [SigmaFinite P1] [SigmaFinite Q1]
    [SigmaFinite P2] [SigmaFinite Q2]
    (_hac1 : P1.AbsolutelyContinuous Q1)
    (_hac2 : P2.AbsolutelyContinuous Q2) :
    (P1.prod P2).rnDeriv (Q1.prod Q2)
      =ᵐ[Q1.prod Q2] fun x => P1.rnDeriv Q1 x.1 * P2.rnDeriv Q2 x.2 := by
  exact InfoTheory.rnDeriv_prod_eq _hac1 _hac2

/-- Tensorisation part of Proposition 5.6: for product probability measures,
`KL(P₁ × P₂ ‖ Q₁ × Q₂) = KL(P₁ ‖ Q₁) + KL(P₂ ‖ Q₂)`. -/
theorem prop_5_6_tensorization {alpha beta : Type*}
    {_ : MeasurableSpace alpha} {_ : MeasurableSpace beta}
    {P1 Q1 : Measure alpha} {P2 Q2 : Measure beta}
    (hP1 : IsProbabilityMeasure P1) (hQ1 : IsProbabilityMeasure Q1)
    (hP2 : IsProbabilityMeasure P2) (hQ2 : IsProbabilityMeasure Q2)
    (hPQ1 : P1.AbsolutelyContinuous Q1) (hPQ2 : P2.AbsolutelyContinuous Q2)
    (h_int1 : Integrable (llr P1 Q1) P1)
    (h_int2 : Integrable (llr P2 Q2) P2) :
    klDiv (P1.prod P2) (Q1.prod Q2) = klDiv P1 Q1 + klDiv P2 Q2 := by
    haveI := hP1; haveI := hQ1; haveI := hP2; haveI := hQ2
    exact InfoTheory.klDiv_prod_eq hPQ1 hPQ2 h_int1 h_int2

end Prop_5_6

end Rigollet.Chapter5
