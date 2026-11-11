/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Int.Interval

set_option maxHeartbeats 400000

namespace CohomologyP1

variable (k : Type) [Field k]


/-- The submodule of finitely supported integer-indexed `k`-functions supported on `ℤ_{≥0}`,
modelling the global sections of `O(n)` on one affine chart of `P^1`. -/
noncomputable def NonNeg : Submodule k (ℤ →₀ k) :=
  Finsupp.supported k k (Set.Ici 0)

/-- The submodule of finitely supported integer-indexed `k`-functions supported on `(-∞, n]`,
modelling the other affine chart contribution to `O(n)` on `P^1`. -/
noncomputable def AtMost (n : ℤ) : Submodule k (ℤ →₀ k) :=
  Finsupp.supported k k (Set.Iic n)

/-- The Čech `H^0(P^1, O(n))`: the intersection of the two chart submodules `NonNeg` and
`AtMost n`. -/
noncomputable def CechH0 (n : ℤ) : Submodule k (ℤ →₀ k) :=
  NonNeg k ⊓ AtMost k n


/-- `CechH0 k n` equals the submodule supported on the integer interval `[0, n]`. -/
theorem cechH0_eq_supported (n : ℤ) :
    CechH0 k n = Finsupp.supported k k (Set.Icc 0 n) := by
  simp only [CechH0, NonNeg, AtMost, ← Finsupp.supported_inter, Set.Ici_inter_Iic]

/-- The sum of the two chart submodules equals the submodule supported on
`Set.Ici 0 ∪ Set.Iic n`. -/
theorem sum_eq_supported (n : ℤ) :
    NonNeg k ⊔ AtMost k n = Finsupp.supported k k (Set.Ici 0 ∪ Set.Iic n) := by
  simp only [NonNeg, AtMost, ← Finsupp.supported_union]

/-- The set-theoretic complement of `Ici 0 ∪ Iic n` in `ℤ` is the open interval `Ioo n 0`. -/
lemma complement_union (n : ℤ) :
    (Set.Ici (0 : ℤ) ∪ Set.Iic n)ᶜ = Set.Ioo n 0 := by
  ext x; simp [Set.mem_Ioo]; omega

/-- The `k`-dimension of the submodule of finsupps supported on a finite set `S ⊆ ℤ` equals the
cardinality of `S`. -/
lemma finrank_supported_eq_card (S : Set ℤ) [Fintype S] :
    Module.finrank k ↥(Finsupp.supported k k S) = Fintype.card S := by
  rw [(Finsupp.supportedEquivFinsupp (R := k) (M := k) S).finrank_eq,
      Module.finrank_finsupp, Module.finrank_self, mul_one]


/-- `H^0(P^1, O(n)) = n + 1` for `n ≥ 0`. -/
theorem finrank_H0_nonneg (n : ℕ) :
    Module.finrank k ↥(CechH0 k ↑n) = n + 1 := by
  rw [cechH0_eq_supported, finrank_supported_eq_card]
  rw [← Set.toFinset_card, Set.toFinset_Icc, Int.card_Icc]
  simp

/-- For `n ≥ 0`, the two chart submodules sum to the entire space, so `H^1(P^1, O(n)) = 0`. -/
theorem H1_vanishes_nonneg (n : ℕ) :
    NonNeg k ⊔ AtMost k ↑n = ⊤ := by
  rw [sum_eq_supported, ← Finsupp.supported_univ]
  congr 1
  ext x; simp [Set.mem_Ici, Set.mem_Iic]; omega

/-- `H^1(P^1, O(n)) = 0` for `n ≥ 0`. -/
theorem finrank_H1_nonneg (n : ℕ) :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k ↑n)) = 0 := by
  rw [H1_vanishes_nonneg]
  haveI : Subsingleton ((ℤ →₀ k) ⧸ (⊤ : Submodule k (ℤ →₀ k))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton


/-- For `n < 0`, `H^0(P^1, O(n)) = 0`. -/
theorem H0_vanishes_neg (n : ℤ) (hn : n < 0) :
    CechH0 k n = ⊥ := by
  rw [cechH0_eq_supported, ← Finsupp.supported_empty]
  congr 1
  ext x; simp [Set.mem_Icc]; omega

/-- Linear equivalence between the cokernel of the Čech differential and the submodule supported
on the missing integer range `Set.Ioo n 0`. -/
noncomputable def H1_equiv_supported_complement (n : ℤ) :
    ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) ≃ₗ[k]
      ↥(Finsupp.supported k k (Set.Ioo n 0)) := by
  rw [sum_eq_supported]
  have hc : IsCompl (Finsupp.supported k k (Set.Ici (0 : ℤ) ∪ Set.Iic n))
      (Finsupp.supported k k (Set.Ioo n 0)) := by
    rw [← complement_union]
    exact ⟨Finsupp.disjoint_supported_supported isCompl_compl.disjoint,
           Finsupp.codisjoint_supported_supported isCompl_compl.codisjoint⟩
  exact Submodule.quotientEquivOfIsCompl _ _ hc

/-- For `n < 0`, `H^1(P^1, O(n))` has dimension `(-n - 1).toNat`. -/
theorem finrank_H1_neg (n : ℤ) (_ : n < 0) :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) = (-n - 1).toNat := by
  rw [(H1_equiv_supported_complement k n).finrank_eq, finrank_supported_eq_card]
  rw [← Set.toFinset_card, Set.toFinset_Ioo, Int.card_Ioo]
  ring_nf


/-- `H^0(P^1, O(-1)) = 0`. -/
theorem H0_O_neg1 : CechH0 k (-1) = ⊥ :=
  H0_vanishes_neg k (-1) (by norm_num)

/-- `H^1(P^1, O(-1)) = 0`. -/
theorem finrank_H1_O_neg1 :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k (-1))) = 0 := by
  have := finrank_H1_neg k (-1) (by norm_num : (-1 : ℤ) < 0)
  simpa using this

/-- `H^1(P^1, O(-2))` is 1-dimensional (Serre duality dual to `H^0(O)`). -/
theorem finrank_H1_O_neg2 :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k (-2))) = 1 := by
  have := finrank_H1_neg k (-2) (by norm_num : (-2 : ℤ) < 0)
  simpa using this

end CohomologyP1
