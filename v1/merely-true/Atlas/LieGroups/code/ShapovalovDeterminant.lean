/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.JantzenFiltration

noncomputable section

universe u_mod u_ch

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}

open Classical

structure KostantPartitionFn (rd : PositiveRootData Δ) where
  K : (Δ.𝔥 →ₗ[R] R) → ℕ
  K_zero : K 0 = 1
  K_zero_outside : ∀ β, ¬ rd.IsInQPlus β → K β = 0

structure ShapovalovDeterminantData
    {rd : PositiveRootData Δ}
    (wg : WeylGroupData Δ)
    (cd : RootCorootData rd)
    (kpf : KostantPartitionFn rd) where
  shapovalovForm : (β : Δ.𝔥 →ₗ[R] R) → (lam : Δ.𝔥 →ₗ[R] R) →
    Matrix (Fin (kpf.K β)) (Fin (kpf.K β)) R
  D : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  D_eq_det : ∀ (β lam : Δ.𝔥 →ₗ[R] R),
    D β lam = (shapovalovForm β lam).det
  D_formula : ∀ (β : Δ.𝔥 →ₗ[R] R), rd.IsInQPlus β →
    ∀ (N : ℕ), (∀ α ∈ rd.posRoots, ∀ n : ℕ, N < n → kpf.K (β - n • α) = 0) →
    ∃ (c : R), c ≠ 0 ∧
      ∀ (lam : Δ.𝔥 →ₗ[R] R),
        D β lam = c *
          ∏ α ∈ rd.posRoots,
            ∏ n ∈ Finset.Icc 1 N,
              (cd.corootPairing (lam + wg.ρ) α - (n : R)) ^ (kpf.K (β - n • α))

end
