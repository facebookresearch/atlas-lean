/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Basis

noncomputable section

open KaehlerDifferential Module

universe u

section RankComputation

variable (k : Type u) [Field k] (n : ℕ)

/-- The module of Kähler differentials of `k[x₀, …, x_n]` over `k` is free of rank `n + 1`. -/
theorem rank_kahler_polynomial :
    Module.finrank (MvPolynomial (Fin (n+1)) k)
      (Ω[MvPolynomial (Fin (n+1)) k⁄k]) = n + 1 := by
  rw [Module.finrank_eq_card_basis (mvPolynomialBasis k (Fin (n + 1))), Fintype.card_fin]

/-- The Kähler differential module is finitely generated. -/
instance kahler_mvpoly_finite :
    Module.Finite (MvPolynomial (Fin (n+1)) k)
      (Ω[MvPolynomial (Fin (n+1)) k⁄k]) :=
  Module.Finite.of_basis (mvPolynomialBasis k (Fin (n + 1)))

/-- The determinant (top exterior power) of the Kähler differential module is free of rank `1`,
giving the canonical bundle of affine `(n+1)`-space. -/
theorem det_kahler_rank_one :
    Module.finrank (MvPolynomial (Fin (n+1)) k)
      (⋀[MvPolynomial (Fin (n+1)) k]^(n + 1)
        (Ω[MvPolynomial (Fin (n+1)) k⁄k])) = 1 := by
  rw [exteriorPower.finrank_eq, rank_kahler_polynomial, Nat.choose_self]

/-- The `p`-th exterior power of the Kähler differential module has rank `(n+1 choose p)`. -/
theorem exterior_power_kahler_rank (p : ℕ) :
    Module.finrank (MvPolynomial (Fin (n+1)) k)
      (⋀[MvPolynomial (Fin (n+1)) k]^p
        (Ω[MvPolynomial (Fin (n+1)) k⁄k])) = Nat.choose (n + 1) p := by
  rw [exteriorPower.finrank_eq, rank_kahler_polynomial]

end RankComputation

section CanonicalBundleIso

open Set

variable (k : Type u) [Field k] (n : ℕ)

/-- The canonical bundle of `A^{n+1}_k` (top exterior power of Kähler differentials) is free. -/
theorem canonical_bundle_free :
    Module.Free (MvPolynomial (Fin (n+1)) k)
      (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) :=
  inferInstance

/-- A basis (of cardinality 1) for the top exterior power of Kähler differentials. -/
noncomputable def exteriorPowerKahlerBasis :
    Basis (Fin 1) (MvPolynomial (Fin (n+1)) k)
      (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) :=
  ((mvPolynomialBasis k (Fin (n+1))).exteriorPower (n+1)).reindex
    (Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, powersetCard.card, Nat.card_fin, Nat.choose_self]; simp))

/-- Linear equivalence between the canonical bundle of `A^{n+1}_k` and the structure sheaf
(rank-one free module), arising from the chosen basis. -/
noncomputable def canonicalBundleLinearEquiv :
    (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k]))
      ≃ₗ[MvPolynomial (Fin (n+1)) k] (Fin 1 → MvPolynomial (Fin (n+1)) k) :=
  (exteriorPowerKahlerBasis k n).equivFun

/-- Combined statement: the canonical bundle of `A^{n+1}_k` is free of rank one. -/
theorem canonical_bundle_free_rank_one :
    Module.Free (MvPolynomial (Fin (n+1)) k)
      (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) ∧
    Module.finrank (MvPolynomial (Fin (n+1)) k)
      (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) = 1 := by
  refine ⟨inferInstance, ?_⟩
  rw [exteriorPower.finrank_eq, finrank_eq_card_basis (mvPolynomialBasis k (Fin (n + 1))),
    Fintype.card_fin, Nat.choose_self]

end CanonicalBundleIso

end
