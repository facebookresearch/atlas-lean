/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Polynomial.HilbertPoly

set_option maxHeartbeats 800000

open MvPolynomial

noncomputable section

/-- Finiteness instance: monomials in `n` variables of total degree `d` form a finite set. -/
instance Finsupp.fintypeDegreeEq (n d : ℕ) :
    Fintype {s : Fin n →₀ ℕ | s.degree = d} :=
  ((Finsupp.finite_of_degree_le d).subset (fun _ hx => le_of_eq hx)).fintype

/-- Equivalence between degree-`d` monomials in `n` variables and `d`-element multisets in `Fin n`. -/
def degreeEquivSym (n d : ℕ) :
    {s : Fin n →₀ ℕ | s.degree = d} ≃ Sym (Fin n) d :=
  (Equiv.subtypeEquivRight (fun s => by simp [Finsupp.degree, Finsupp.sum, id])).trans
    (Sym.equivNatSum (Fin n) d).symm

/-- The number of degree-`d` monomials in `n` variables is `C(n + d - 1, d)` (multiset coefficient). -/
theorem card_degree_eq_choose (n d : ℕ) :
    Fintype.card {s : Fin n →₀ ℕ | s.degree = d} = (n + d - 1).choose d := by
  rw [Fintype.card_congr (degreeEquivSym n d), Sym.card_sym_eq_choose, Fintype.card_fin]

/-- The space of degree-`d` homogeneous polynomials in `n` variables over a field is
finite-dimensional. -/
theorem homogeneousSubmodule_finiteDimensional (k : Type*) [Field k]
    (n d : ℕ) :
    Module.Finite k (homogeneousSubmodule (Fin n) k d) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.equiv
    (Finsupp.supportedEquivFinsupp (M := k) (R := k) {s : Fin n →₀ ℕ | s.degree = d}).symm

/-- The dimension of degree-`d` homogeneous polynomials equals the number of degree-`d` monomials. -/
theorem homogeneousSubmodule_finrank_eq_card (k : Type*) [Field k]
    (n d : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin n) k d) =
      Fintype.card {s : Fin n →₀ ℕ | s.degree = d} := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  let S : Set (Fin n →₀ ℕ) := {s | s.degree = d}
  show Module.finrank k ↥(Finsupp.supported k k S) = _
  rw [LinearEquiv.finrank_eq (Finsupp.supportedEquivFinsupp (M := k) (R := k) S),
    Module.finrank_finsupp_self]

/-- Dimension of the space of degree-`d` forms in `n` variables is `C(n + d - 1, d)`. -/
theorem homogeneousSubmodule_finrank (k : Type*) [Field k]
    (n d : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin n) k d) = (n + d - 1).choose d := by
  rw [homogeneousSubmodule_finrank_eq_card, card_degree_eq_choose]

/-- The Hilbert function of `P^n_k`: dimension of degree-`d` forms in `n + 1` variables. -/
def hilbertFun (k : Type*) [Field k] (n : ℕ) (d : ℕ) : ℕ :=
  Module.finrank k (homogeneousSubmodule (Fin (n + 1)) k d)

/-- Closed form: `H_{P^n}(d) = C(n + d, n)`. -/
theorem hilbert_fun_eq_choose (k : Type*) [Field k] (n d : ℕ) :
    hilbertFun k n d = (n + d).choose n := by
  unfold hilbertFun
  rw [homogeneousSubmodule_finrank]
  have h1 : n + 1 + d - 1 = n + d := by omega
  rw [h1, Nat.choose_symm_add.symm]

/-- Hilbert function of a quotient ring: dimension of the degree-`d` part of
`k[x_0, ..., x_n] / I`. -/
def hilbertFunQuotient (k : Type*) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (d : ℕ) : ℕ :=
  Module.finrank k (homogeneousSubmodule (Fin (n + 1)) k d ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) k d).subtype
      (I.restrictScalars k))

/-- The Hilbert function of `P^n` is polynomial of degree exactly `n`. -/
theorem hilbert_fun_is_polynomial (k : Type*) [Field k] (n : ℕ) :
    ∃ p : Polynomial ℚ, (∀ d : ℕ, (hilbertFun k n d : ℚ) = p.eval (d : ℚ)) ∧
      p.natDegree = n := by
  refine ⟨Polynomial.preHilbertPoly ℚ n 0, ?_, Polynomial.natDegree_preHilbertPoly ℚ n 0⟩
  intro d
  rw [hilbert_fun_eq_choose, Polynomial.preHilbertPoly_eq_choose_sub_add ℚ n (Nat.zero_le d)]
  simp [add_comm]

/-- The Hilbert polynomial of `P^n` has degree `n`. -/
theorem hilbert_polynomial_degree (n : ℕ) :
    (Polynomial.preHilbertPoly ℚ n 0).natDegree = n :=
  Polynomial.natDegree_preHilbertPoly ℚ n 0

/-- The leading coefficient of the Hilbert polynomial of `P^n` is `1/n!`. -/
theorem hilbert_polynomial_leading_coeff (n : ℕ) :
    (Polynomial.preHilbertPoly ℚ n 0).leadingCoeff = (↑(Nat.factorial n) : ℚ)⁻¹ :=
  Polynomial.leadingCoeff_preHilbertPoly ℚ n 0

/-- The Hilbert function of `P^n` is monotonically nondecreasing in `d`. -/
theorem hilbert_fun_mono (k : Type*) [Field k] (n d : ℕ) :
    hilbertFun k n d ≤ hilbertFun k n (d + 1) := by
  simp only [hilbert_fun_eq_choose]
  exact Nat.choose_le_choose n (by omega)

end
