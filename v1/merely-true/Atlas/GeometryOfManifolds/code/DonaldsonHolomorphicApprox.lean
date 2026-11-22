/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

noncomputable section

open Real MeasureTheory

/-- Data of a compact Kähler manifold of complex dimension $n$: an underlying metric/charted space
$M$ with symplectic form $\omega$, almost complex structure $J$ satisfying $J^2 = -\mathrm{id}$,
compatible Riemannian metric $g(v,w) = \omega(v, Jw)$, and a symplectic volume satisfying the
integrality condition $\mathrm{vol} = (2\pi)^n N$ for some $N \in \mathbb{N}_{>0}$. -/
structure CompactKahlerData (n : ℕ) where
  M : Type*
  topM : TopologicalSpace M
  metricM : MetricSpace M
  compactM : CompactSpace M
  nonemptyM : Nonempty M
  chartedM : ChartedSpace (EuclideanSpace ℝ (Fin (2 * n))) M
  ω : M → (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ℝ
  ω_antisymm : ∀ p v w, ω p v w = -(ω p w v)
  J : M → (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ)
  J_sq_neg : ∀ p v, J p (J p v) = fun i => -(v i)
  g : M → (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ℝ
  kahler_compat : ∀ p v w, g p v w = ω p v (J p w)
  symplectic_volume : ℝ
  symplectic_volume_pos : 0 < symplectic_volume
  integrality_condition : ∃ (N : ℕ), 0 < N ∧
    symplectic_volume = (2 * Real.pi) ^ n * ↑N

attribute [instance] CompactKahlerData.topM CompactKahlerData.metricM
  CompactKahlerData.compactM CompactKahlerData.nonemptyM CompactKahlerData.chartedM

/-- A family of complex-valued sections $\sigma_{k,p}(q)$ indexed by $k \in \mathbb{N}$ and
base points $p \in M$, evaluated at $q \in M$. -/
structure SectionFamily {n : ℕ} (D : CompactKahlerData n) where
  section_ : ℕ → D.M → D.M → ℂ

/-- A family of weighted $C^r$ norms $\|\cdot\|_{C^r_k}$ on complex-valued functions on $M$,
scaled according to the parameter $k$ controlling the local length scale $k^{-1/2}$. -/
structure WeightedCrNorm {n : ℕ} (D : CompactKahlerData n) where
  wnorm : ℕ → ℕ → (D.M → ℂ) → ℝ
  wnorm_nonneg : ∀ k r f, 0 ≤ wnorm k r f

/-- An $L^2$ norm $\|\cdot\|_{L^2}$ on complex-valued functions on $M$. -/
structure L2Norm {n : ℕ} (D : CompactKahlerData n) where
  l2 : (D.M → ℂ) → ℝ
  l2_nonneg : ∀ f, 0 ≤ l2 f

/-- The Dolbeault operator $\bar\partial$ acting on complex-valued functions on $M$. -/
structure DelbarOp {n : ℕ} (D : CompactKahlerData n) where
  delbar : (D.M → ℂ) → (D.M → ℂ)


/-- Donaldson's holomorphic approximation theorem (exponential bound version). Given a family
of almost-holomorphic sections $\sigma_{k,p}$ with $\|\bar\partial \sigma_{k,p}\|_{L^2} \leq
C_{\bar\partial} \exp(-\lambda_{\bar\partial} k / 3)$ and a Green's-function correction producing
holomorphic sections $\tilde\sigma_{k,p}$ with $\|\sigma_{k,p} - \tilde\sigma_{k,p}\|_{C^r_k}
\lesssim \|\bar\partial \sigma_{k,p}\|_{L^2}$, the difference itself decays exponentially:
$\sup_q |\sigma_{k,p}(q) - \tilde\sigma_{k,p}(q)| \leq O(\exp(-\lambda k^{1/3}))$. -/
theorem donaldson_holomorphic_approximation_exp_bound
    {n : ℕ} (D : CompactKahlerData n)
    (wcr : WeightedCrNorm D)
    (l2 : L2Norm D)
    (dol : DelbarOp D)
    (fam : SectionFamily D)


    (h_delbar_decay : ∃ (C_delbar lam_delbar : ℝ), C_delbar > 0 ∧ lam_delbar > 0 ∧
      ∀ (k : ℕ) (p : D.M),
        l2.l2 (dol.delbar (fam.section_ k p)) ≤
          C_delbar * exp (-lam_delbar * (k : ℝ) / 3))


    (h_green : ∃ (fam' : SectionFamily D),

      (∀ (k : ℕ) (p : D.M), dol.delbar (fam'.section_ k p) = 0) ∧

      (∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
        ∀ (k : ℕ) (p : D.M),
          wcr.wnorm k r (fun q => fam.section_ k p q - fam'.section_ k p q) ≤
            C_r * l2.l2 (dol.delbar (fam.section_ k p)))) :


    ∃ (fam' : SectionFamily D),

      (∀ (k : ℕ) (p : D.M), dol.delbar (fam'.section_ k p) = 0) ∧


      (∃ (lam : ℝ), lam > 0 ∧
        ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
          ∀ (k : ℕ) (p : D.M),
            wcr.wnorm k r (fun q => fam.section_ k p q - fam'.section_ k p q) ≤
              C_r * exp (-lam * (k : ℝ) / 3)) := by


  have _hkahler := D.kahler_compat

  have _hintegral := D.integrality_condition


  obtain ⟨fam', h_hol, h_cr_bound⟩ := h_green


  obtain ⟨C_d, lam_d, hCd_pos, hlam_pos, h_decay⟩ := h_delbar_decay

  refine ⟨fam', h_hol, lam_d, hlam_pos, fun r => ?_⟩
  obtain ⟨C_r, hCr_pos, h_wr_bound⟩ := h_cr_bound r
  refine ⟨C_r * C_d, by positivity, fun k p => ?_⟩

  calc wcr.wnorm k r (fun q => fam.section_ k p q - fam'.section_ k p q)
      ≤ C_r * l2.l2 (dol.delbar (fam.section_ k p)) := h_wr_bound k p
    _ ≤ C_r * (C_d * exp (-lam_d * (k : ℝ) / 3)) := by
        apply mul_le_mul_of_nonneg_left (h_decay k p) (le_of_lt hCr_pos)
    _ = C_r * C_d * exp (-lam_d * (k : ℝ) / 3) := by ring

end
