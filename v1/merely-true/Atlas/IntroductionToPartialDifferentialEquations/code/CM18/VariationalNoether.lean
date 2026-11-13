/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy


open CM18

/-- Proposition 2.0.2 (packaged): derivatives with respect to the flow parameter
$\epsilon$ at $\epsilon = 0$ of the transformed scalar field $\widetilde{\varphi}$,
its gradient $\widetilde{\nabla}_\mu \widetilde{\varphi}$, the metric
$\widetilde{m}_{\mu\nu}$, the inverse metric $(\widetilde{m}^{-1})^{\mu\nu}$,
and $\det M^{-1}$, expressed in terms of the generating vector field $Y$. -/
theorem flow_param_derivatives {n : ℕ}
    (Psi : FlowMap n) (phi : ScalarField n) (m : Metric n)
    (mInv : InverseMetric n)
    (hphi : ContDiff ℝ ⊤ phi) (xt : Spacetime n)
    (hm : ∀ alpha beta, ContDiff ℝ ⊤ (fun y => m y alpha beta))
    (hmInv : ∀ alpha beta, ContDiff ℝ ⊤ (fun y => mInv y alpha beta)) :

    (deriv (fun eps => transformedField Psi phi eps xt) 0 =
      -(∑ alpha : Fin (n + 1),
        Psi.Y xt alpha * spacetimeGradient phi xt alpha)) ∧

    (∀ mu : Fin (n + 1),
      deriv (fun eps => transformedGradient Psi phi eps xt mu) 0 =
        -fderiv ℝ (fun y => ∑ alpha : Fin (n + 1),
          Psi.Y y alpha * spacetimeGradient phi y alpha) xt (Pi.single mu 1)) ∧

    (∀ mu nu : Fin (n + 1),
      deriv (fun eps => transformedMetric Psi m eps xt mu nu) 0 =
        -(∑ alpha : Fin (n + 1),
          m xt alpha nu * fderiv ℝ (fun y => Psi.Y y alpha) xt (Pi.single mu 1)
        + ∑ alpha : Fin (n + 1),
          m xt mu alpha * fderiv ℝ (fun y => Psi.Y y alpha) xt (Pi.single nu 1)
        + ∑ alpha : Fin (n + 1),
          Psi.Y xt alpha * fderiv ℝ (fun y => m y mu nu) xt (Pi.single alpha 1))) ∧

    (∀ mu nu : Fin (n + 1),
      deriv (fun eps => transformedInverseMetric Psi mInv eps xt mu nu) 0 =
        ∑ alpha : Fin (n + 1),
          mInv xt alpha nu * fderiv ℝ (fun y => Psi.Y y mu) xt (Pi.single alpha 1)
        + ∑ alpha : Fin (n + 1),
          mInv xt mu alpha * fderiv ℝ (fun y => Psi.Y y nu) xt (Pi.single alpha 1)
        - ∑ alpha : Fin (n + 1),
          Psi.Y xt alpha * fderiv ℝ (fun y => mInv y mu nu) xt (Pi.single alpha 1)) ∧

    (deriv (fun eps =>
      Matrix.det (Matrix.of (fun mu nu => Psi.invJacobian eps xt mu nu))) 0 =
      -(∑ alpha : Fin (n + 1),
        fderiv ℝ (fun y => Psi.Y y alpha) xt (Pi.single alpha 1))) := by
  exact ⟨
    flow_deriv_scalar Psi phi hphi xt,
    fun mu => flow_deriv_gradient Psi phi hphi xt mu,
    fun mu nu => flow_deriv_metric Psi m xt mu nu hm,
    fun mu nu => flow_deriv_inverse_metric Psi mInv xt mu nu hmInv,
    flow_deriv_det_invJacobian Psi xt⟩
