/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLn

namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

structure CompleteFlag (k : Type*) [Field k] (n : ℕ) where
  spaces : Fin (n + 1) → Submodule k (Vec k n)
  monotone : Monotone spaces
  bot_eq : spaces ⟨0, Nat.zero_lt_succ n⟩ = ⊥
  top_eq : spaces ⟨n, Nat.lt_succ_of_le le_rfl⟩ = ⊤

/-- The Schreier refinement cell at row $i$ and column $j$:
$\sigma_i \cap (\sigma_{i-1} + \tau_j)$, interpolating between $\sigma_{i-1}$ and $\sigma_i$
along the chain $\tau$. -/
def schreierCell (σ τ : CompleteFlag k n)
    (i : Fin (n + 1)) (hi : 0 < i.val) (j : Fin (n + 1)) : Submodule k (Vec k n) :=
  σ.spaces i ⊓ (σ.spaces ⟨i.val - 1, by omega⟩ ⊔ τ.spaces j)

/-- At column $0$, the Schreier cell collapses to $\sigma_{i-1}$. -/
theorem schreierCell_zero (σ τ : CompleteFlag k n)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    schreierCell σ τ i hi ⟨0, Nat.zero_lt_succ n⟩ =
      σ.spaces ⟨i.val - 1, by omega⟩ := by
  unfold schreierCell
  rw [τ.bot_eq, sup_bot_eq]
  apply inf_eq_right.mpr
  apply σ.monotone
  simp only [Fin.le_iff_val_le_val]
  omega

/-- At the last column, the Schreier cell equals $\sigma_i$. -/
theorem schreierCell_last (σ τ : CompleteFlag k n)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    schreierCell σ τ i hi ⟨n, Nat.lt_succ_of_le le_rfl⟩ = σ.spaces i := by
  unfold schreierCell
  rw [τ.top_eq, sup_top_eq, inf_top_eq]

/-- Monotonicity of Schreier cells in the column index $j$. -/
theorem schreierCell_mono (σ τ : CompleteFlag k n)
    (i : Fin (n + 1)) (hi : 0 < i.val) (j j' : Fin (n + 1)) (hjj' : j ≤ j') :
    schreierCell σ τ i hi j ≤ schreierCell σ τ i hi j' := by
  unfold schreierCell
  exact inf_le_inf_left _ (sup_le_sup_left (τ.monotone hjj') _)

end GLnBuilding
