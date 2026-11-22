/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.EffaceableUniversal
import Atlas.AlgebraicGeometryI.code.SheafCohomology

noncomputable section

open CohomologyP1 SheafCohomology CategoryTheory CategoryTheory.Limits

namespace SheafCohDerived


section CechDeltaFunctorData

variable (k : Type) [Field k]

/-- Numerical data for the Čech `δ`-functor on `ℙ¹`: the dimensions
`h⁰(O(n))`, `h¹(O(n))`, their characteristic formulas, and the Euler identity. -/
structure CechDeltaFunctorP1 (k : Type) [Field k] where
  dimH0 : ℤ → ℕ
  dimH1 : ℤ → ℕ
  dimH0_nonneg : ∀ n : ℤ, 0 ≤ n → dimH0 n = (n + 1).toNat
  dimH0_neg : ∀ n : ℤ, n < 0 → dimH0 n = 0
  dimH1_nonneg : ∀ n : ℤ, 0 ≤ n → dimH1 n = 0
  dimH1_neg : ∀ n : ℤ, n < 0 → dimH1 n = (-n - 1).toNat
  euler : ∀ n : ℤ, (dimH0 n : ℤ) - (dimH1 n : ℤ) = n + 1

/-- Construct the Čech `δ`-functor on `ℙ¹` from the explicit sheaf cohomology
groups `H⁰`, `H¹`. -/
def mkCechDeltaFunctorP1 : CechDeltaFunctorP1 k where
  dimH0 := fun n => Module.finrank k (H0 k n)
  dimH1 := fun n => Module.finrank k (H1 k n)
  dimH0_nonneg := fun n hn => finrank_H0_of_nonneg k n hn
  dimH0_neg := fun n hn => finrank_H0_of_neg k n hn
  dimH1_nonneg := fun n hn => finrank_H1_of_nonneg k n hn
  dimH1_neg := fun n hn => finrank_H1_of_neg k n hn
  euler := fun n => euler_characteristic k n

end CechDeltaFunctorData


section LongExactNumerics

variable (k : Type) [Field k]

end LongExactNumerics


section Effaceability

variable (k : Type) [Field k]

end Effaceability


section EulerDerived

variable (k : Type) [Field k]

/-- Additive step of the Euler characteristic on `ℙ¹`: `χ(O(n+1)) − χ(O(n)) = 1`. -/
theorem euler_chi_additive_step (n : ℤ) :
    ((Module.finrank k (H0 k (n + 1)) : ℤ) - (Module.finrank k (H1 k (n + 1)) : ℤ)) -
    ((Module.finrank k (H0 k n) : ℤ) - (Module.finrank k (H1 k n) : ℤ)) = 1 := by
  rw [euler_characteristic k (n + 1), euler_characteristic k n]
  ring

/-- Derived version of Serre duality on `ℙ¹`: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`. -/
theorem serre_duality_derived (n : ℤ) :
    Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
  by_cases hn : 0 ≤ n
  · exact serre_duality_nonneg k n hn
  · push Not at hn; exact serre_duality_neg k n hn

end EulerDerived


section Bridge

variable (k : Type) [Field k]

/-- Effaceability witness: for every `n`, there exists `N ≥ max 0 n` with
`H¹(O(N)) = 0`. -/
theorem cech_effaceability_witness (n : ℤ) :
    ∃ N : ℤ, 0 ≤ N ∧ n ≤ N ∧ Module.finrank k (H1 k N) = 0 := by
  refine ⟨max 0 n, le_max_left 0 n, le_max_right 0 n, ?_⟩
  exact finrank_H1_of_nonneg k (max 0 n) (le_max_left 0 n)

end Bridge

end SheafCohDerived
