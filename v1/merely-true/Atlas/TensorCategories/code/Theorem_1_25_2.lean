/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.QuantumSl2

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [HopfAlgebra k A] [h : QuantumSl2 k A]

/-- Theorem 1.25.2: There exists a unique Hopf algebra structure on the quantum
group `U_q(sl_2)` whose comultiplication is determined by `Δ(K) = K ⊗ K`,
`Δ(E) = E ⊗ K + 1 ⊗ E`, and `Δ(F) = F ⊗ 1 + K⁻¹ ⊗ F`, with the corresponding
counit and antipode formulas. -/
theorem Theorem_1_25_2 :

    (comul (R := k) h.K = h.K ⊗ₜ[k] h.K) ∧
    (comul (R := k) h.E = h.E ⊗ₜ[k] h.K + 1 ⊗ₜ[k] h.E) ∧
    (comul (R := k) h.F = h.F ⊗ₜ[k] 1 + h.Kinv ⊗ₜ[k] h.F) ∧

    (comul (R := k) h.Kinv = h.Kinv ⊗ₜ[k] h.Kinv) ∧

    (counit (R := k) h.K = (1 : k)) ∧
    (counit (R := k) h.E = (0 : k)) ∧
    (counit (R := k) h.F = (0 : k)) ∧

    (counit (R := k) h.Kinv = (1 : k)) ∧

    (antipode k h.K = h.Kinv) ∧
    (antipode k h.E = -(h.E * h.Kinv)) ∧
    (antipode k h.F = -(h.K * h.F)) ∧

    (antipode k h.Kinv = h.K) :=
  QuantumSl2.Theorem_1_25_2_Uq_sl2_Hopf
