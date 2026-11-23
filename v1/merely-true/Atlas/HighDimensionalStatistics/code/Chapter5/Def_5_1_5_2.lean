/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory

noncomputable section

namespace Minimax

/-- Squared Euclidean distance `‖θ₁ - θ₂‖₂² = ∑ i, (θ₁ i - θ₂ i)²` on `Fin d → ℝ`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- A Gaussian sequence model: dimension `d`, sample size `n`, noise level `σ`,
parameter set `Θ ⊆ ℝ^d`, and a family of probability measures `P θ` on `ℝ^d` with
the standard KL-divergence formula `KL(P_θ₁ ‖ P_θ₀) = n‖θ₁ - θ₀‖² / (2σ²)`, plus
measurability/integrability hypotheses needed to talk about minimax risk. -/
structure GaussianSequenceModel where
  d : ℕ
  n : ℕ
  σ : ℝ
  hσ : 0 < σ
  hn : 0 < n
  Θ : Set (Fin d → ℝ)
  P : (Fin d → ℝ) → Measure (Fin d → ℝ)
  hP_prob : ∀ θ : Fin d → ℝ, IsProbabilityMeasure (P θ)
  hP_ac : ∀ θ₀ θ₁ : Fin d → ℝ, (P θ₀).AbsolutelyContinuous (P θ₁)
  hP_kl_toReal : ∀ θ₀ θ₁ : Fin d → ℝ,
    (InformationTheory.klDiv (P θ₁) (P θ₀)).toReal =
      n * sqDist θ₁ θ₀ / (2 * σ ^ 2)
  hP_kl_ne_top : ∀ θ₀ θ₁ : Fin d → ℝ,
    InformationTheory.klDiv (P θ₁) (P θ₀) ≠ ⊤
  hP_integrable : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
    MeasureTheory.Integrable (fun Y => sqDist (θhat Y) θ) (P θ)
  hP_aestronglyMeasurable : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ),
    MeasureTheory.AEStronglyMeasurable (fun Y => sqDist (θhat Y) θ) (P θ)
  hP_measurableSet_sqDist_ge : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)) (θ : Fin d → ℝ) (c : ℝ),
    MeasurableSet {Y | sqDist (θhat Y) θ ≥ c}
  hP_bddAbove : ∀ (Θ' : Set (Fin d → ℝ)) (θhat : (Fin d → ℝ) → (Fin d → ℝ)),
    BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ Θ'),
      ∫ Y, sqDist (θhat Y) θ ∂(P θ))
  hMeasurable_θhat : ∀ (θhat : (Fin d → ℝ) → (Fin d → ℝ)), Measurable θhat

/-- Per-observation noise variance `σ² / n` of a Gaussian sequence model. -/
def GaussianSequenceModel.noiseVariance (gsm : GaussianSequenceModel) : ℝ :=
  gsm.σ ^ 2 / gsm.n

/-- An estimator in dimension `d` is just a measurable map `ℝ^d → ℝ^d`
sending observations to a parameter estimate. -/
def Estimator (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

/-- The identity map is an estimator, so `Estimator d` is nonempty. -/
instance {d : ℕ} : Nonempty (Estimator d) := ⟨id⟩

/-- Mean squared error risk `E_θ ‖θ̂(Y) - θ‖²` of an estimator under `P θ`. -/
def risk (gsm : GaussianSequenceModel) (θhat : Estimator gsm.d)
    (θ : Fin gsm.d → ℝ) : ℝ :=
  ∫ Y, sqDist (θhat Y) θ ∂(gsm.P θ)

/-- Worst-case risk `sup_{θ ∈ Θ} E_θ ‖θ̂(Y) - θ‖²` of an estimator. -/
def supRisk (gsm : GaussianSequenceModel) (θhat : Estimator gsm.d) : ℝ :=
  ⨆ θ ∈ gsm.Θ, risk gsm θhat θ

/-- Minimax risk `inf_{θ̂} sup_{θ ∈ Θ} E_θ ‖θ̂(Y) - θ‖²` over all estimators. -/
def minimaxRisk (gsm : GaussianSequenceModel) : ℝ :=
  ⨅ (θhat : Estimator gsm.d), supRisk gsm θhat

/-- Expectation-form minimax optimality (Definition 5.1): an estimator `θ̂` is
minimax optimal at rate `φ` if both `sup_θ E_θ ‖θ̂ - θ‖² ≤ C·φ` for some `C > 0`
and the minimax risk over `Θ` is at least `C'·φ` for some `C' > 0`. -/
def IsMinimaxOptimal_Expectation (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : Prop :=

  (∃ C : ℝ, 0 < C ∧ supRisk gsm θhat ≤ C * φ) ∧

  (∃ C' : ℝ, 0 < C' ∧ minimaxRisk gsm ≥ C' * φ)

/-- Worst-case probability that the squared error of `θ̂` exceeds `φ`:
`sup_{θ ∈ Θ} P_θ(‖θ̂(Y) - θ‖² ≥ φ)`. -/
def supProbLargeError (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : ℝ :=
  ⨆ θ ∈ gsm.Θ, (gsm.P θ {Y | sqDist (θhat Y) θ ≥ φ}).toReal

/-- Minimax high-probability error: `inf_{θ̂} sup_{θ ∈ Θ} P_θ(‖θ̂ - θ‖² ≥ φ)`. -/
def minimaxProbLargeError (gsm : GaussianSequenceModel) (φ : ℝ) : ℝ :=
  ⨅ (θhat : Estimator gsm.d), supProbLargeError gsm θhat φ

/-- Expectation-form upper bound: `∃ C > 0`, `sup_θ E_θ ‖θ̂ - θ‖² ≤ C·φ`. -/
def upperBound_expectation (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ supRisk gsm θhat ≤ C * φ

/-- High-probability upper bound: `∃ C > 0`, for every `θ ∈ Θ`,
`P_θ(‖θ̂ - θ‖² ≥ C·φ) ≤ 1/d²`. -/
def upperBound_highProb (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ θ ∈ gsm.Θ, (gsm.P θ {Y | sqDist (θhat Y) θ ≥ C * φ}).toReal ≤
      1 / (gsm.d : ℝ) ^ 2

/-- High-probability minimax optimality (Definition 5.2): an estimator `θ̂` has
an expectation or high-probability upper bound at rate `φ`, and the minimax
high-probability error at rate `φ` is bounded below by some `C' > 0`. -/
def IsMinimaxOptimal_HighProb (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : Prop :=

  (upperBound_expectation gsm θhat φ ∨ upperBound_highProb gsm θhat φ) ∧

  (∃ C' : ℝ, 0 < C' ∧ minimaxProbLargeError gsm φ ≥ C')

/-- Definition 5.1 of Rigollet–Hütter: minimax optimality in expectation. -/
def definition_5_1 (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : Prop :=
  IsMinimaxOptimal_Expectation gsm θhat φ

/-- `φ` is the minimax-optimal rate for `θ̂` over `gsm` iff `θ̂` is minimax
optimal in expectation at rate `φ`. -/
def minimaxOptimalRate (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : Prop :=
  IsMinimaxOptimal_Expectation gsm θhat φ

/-- Definition 5.2 of Rigollet–Hütter: minimax optimality in high probability. -/
def definition_5_2 (gsm : GaussianSequenceModel)
    (θhat : Estimator gsm.d) (φ : ℝ) : Prop :=
  IsMinimaxOptimal_HighProb gsm θhat φ

end Minimax
