/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy

namespace CM18




/-- Verification wrapper for Corollary 2.0.3: at $\epsilon = 0$, the derivative of
the Lagrangian $\mathcal{L}(\widetilde{\varphi}, \widetilde{\nabla} \widetilde{\varphi},
\widetilde{m})$ with respect to the flow parameter decomposes into contributions from
the scalar field, its gradient, and the metric, as predicted by the corollary. -/
theorem corollary_deriv_L_flow_verified {n : ℕ}
    (L : MetricLagrangian n) (Psi : FlowMap n) (phi : ScalarField n)
    (m : Metric n) (x : Spacetime n)
    (hL_smooth : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) ×
      (Fin (n + 1) → Fin (n + 1) → ℝ) => L p.1 p.2.1 p.2.2))
    (hphi : ContDiff ℝ ⊤ phi)
    (hm : ∀ alpha beta, ContDiff ℝ ⊤ (fun y => m y alpha beta)) :
    deriv (fun eps =>
      L (transformedField Psi phi eps x)
        (fun mu => transformedGradient Psi phi eps x mu)
        (fun mu nu => transformedMetric Psi m eps x mu nu)) 0 =
      -(deriv (fun v => L v (spacetimeGradient phi x) (m x)) (phi x)) *
        (∑ alpha : Fin (n + 1), Psi.Y x alpha * spacetimeGradient phi x alpha)
      - ∑ mu : Fin (n + 1),
        (fderiv ℝ (fun p => L (phi x) p (m x)) (spacetimeGradient phi x)
          (Pi.single mu 1)) *
        fderiv ℝ (fun y => ∑ alpha : Fin (n + 1),
          Psi.Y y alpha * spacetimeGradient phi y alpha) x (Pi.single mu 1)
      - ∑ mu : Fin (n + 1), ∑ nu : Fin (n + 1), dL_dm L phi m x mu nu *
        (∑ alpha : Fin (n + 1),
          m x alpha nu * fderiv ℝ (fun y => Psi.Y y alpha) x (Pi.single mu 1)
        + ∑ alpha : Fin (n + 1),
          m x mu alpha * fderiv ℝ (fun y => Psi.Y y alpha) x (Pi.single nu 1)
        + ∑ alpha : Fin (n + 1),
          Psi.Y x alpha * fderiv ℝ (fun y => m y mu nu) x (Pi.single alpha 1)) :=
  corollary_deriv_L_flow L Psi phi m x hL_smooth hphi hm



end CM18
