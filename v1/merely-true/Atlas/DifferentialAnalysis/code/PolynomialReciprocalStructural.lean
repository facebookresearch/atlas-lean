/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Atlas.DifferentialAnalysis.code.SmoothingOperators
import Atlas.DifferentialAnalysis.code.QuotientFDerivStep

open MvPolynomial Finsupp

noncomputable section

namespace DifferentialOperators

variable {σ : Type*} {R : Type*} [CommRing R]

/-- A polynomial of total degree zero has zero partial derivative with respect to any variable. -/
lemma pderiv_eq_zero_of_totalDegree_zero {p : MvPolynomial σ R}
    {j : σ} (h : p.totalDegree = 0) : pderiv j p = 0 := by
  rw [← support_sum_monomial_coeff p, map_sum]
  apply Finset.sum_eq_zero
  intro v hv
  have hv_zero : v = 0 := by
    ext x; simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hne
    have hmem : x ∈ v.support := Finsupp.mem_support_iff.mpr hne
    have : v x ≤ v.sum (fun _ e => e) :=
      Finset.single_le_sum (fun y _ => Nat.zero_le (v y)) hmem
    have := le_totalDegree hv; omega
  rw [hv_zero, pderiv_monomial]; simp

/-- The total degree of a partial derivative `∂ᵢ p` is at most `p.totalDegree - 1`. -/
lemma totalDegree_pderiv_le {i : σ} {p : MvPolynomial σ R} :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff p]
  rw [map_sum]
  apply le_trans (totalDegree_finset_sum _ _)
  apply Finset.sup_le
  intro v hv
  simp only [pderiv_monomial]
  by_cases hvi : v i = 0
  · rw [hvi, Nat.cast_zero, mul_zero, map_zero, totalDegree_zero]; exact Nat.zero_le _
  · apply le_trans (totalDegree_monomial_le _ _)
    have hvi_pos : 1 ≤ v i := Nat.one_le_iff_ne_zero.mpr hvi
    have hle_v : Finsupp.single i 1 ≤ v := Finsupp.single_le_iff.mpr hvi_pos
    have hcancel : v - Finsupp.single i 1 + Finsupp.single i 1 = v :=
      tsub_add_cancel_of_le hle_v
    have hsum_single : (Finsupp.single i (1 : ℕ)).sum (fun _ => id) = 1 := by
      rw [Finsupp.sum_single_index] <;> rfl
    have hsum_eq : (v - Finsupp.single i 1).sum (fun _ => id) + 1 =
        (v.sum fun _ => id) := by
      conv_rhs => rw [← hcancel]
      rw [Finsupp.sum_add_index (by intro _; simp) (by intros; simp [id])]
      rw [hsum_single]
    have hle_deg : (v.sum fun _ => id) ≤ p.totalDegree := le_totalDegree hv
    omega

/-- The natural-number scalar multiple `k • p` has total degree at most `p.totalDegree`. -/
lemma totalDegree_nsmul_le (k : ℕ) (p : MvPolynomial σ R) :
    (k • p).totalDegree ≤ p.totalDegree := by
  rw [nsmul_eq_mul]
  have hk : (k : MvPolynomial σ R) = C (k : R) := by simp [map_natCast]
  calc ((k : MvPolynomial σ R) * p).totalDegree
      ≤ (k : MvPolynomial σ R).totalDegree + p.totalDegree := totalDegree_mul _ _
    _ = 0 + p.totalDegree := by rw [hk, totalDegree_C]
    _ = p.totalDegree := Nat.zero_add _

variable {n : ℕ}

/-- Iterated partial derivative of a complex-valued function on `ℝⁿ` along the list of coordinate
directions `js`, applied left-to-right via `List.foldl`. -/
def iteratedPartialDeriv (js : List (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  js.foldl (fun g j => fun ξ => fderiv ℝ g ξ (EuclideanSpace.single j 1)) f

/-- Unfolding `iteratedPartialDeriv` on a cons list: differentiating along `j :: rest` is
differentiating along `rest` the function obtained by taking one partial derivative along `j`. -/
@[simp]
lemma iteratedPartialDeriv_cons (j : Fin n) (rest : List (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    iteratedPartialDeriv (j :: rest) f =
      iteratedPartialDeriv rest (fun ξ => fderiv ℝ f ξ (EuclideanSpace.single j 1)) := rfl

/-- Recursive definition of the numerator polynomial obtained when differentiating `1 / P` along
the list of directions `js`; see Lemma 11.14 of Melrose for the resulting structural identity. -/
def reciprocalNumerator (P : MvPolynomial (Fin n) ℂ) :
    List (Fin n) → MvPolynomial (Fin n) ℂ
  | [] => 1
  | j :: rest =>
    let L := reciprocalNumerator P rest
    P * pderiv j L - (1 + rest.length : ℕ) • (L * pderiv j P)

/-- The total degree of `reciprocalNumerator P js` is bounded by `(m - 1) * js.length` whenever
`P.totalDegree ≤ m` and `m ≥ 1`. -/
@[simp]
theorem reciprocalNumerator_totalDegree (P : MvPolynomial (Fin n) ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hdeg : P.totalDegree ≤ m)
    (js : List (Fin n)) :
    (reciprocalNumerator P js).totalDegree ≤ (m - 1) * js.length := by
  induction js with
  | nil =>
    simp only [reciprocalNumerator, List.length_nil, Nat.mul_zero]
    exact le_of_eq totalDegree_one
  | cons j rest ih =>
    simp only [reciprocalNumerator, List.length_cons]
    set L := reciprocalNumerator P rest
    have h2 : ((1 + rest.length : ℕ) • (L * pderiv j P)).totalDegree
        ≤ (m - 1) * rest.length + (m - 1) :=
      calc ((1 + rest.length : ℕ) • (L * pderiv j P)).totalDegree
          ≤ (L * pderiv j P).totalDegree := totalDegree_nsmul_le _ _
        _ ≤ L.totalDegree + (pderiv j P).totalDegree := totalDegree_mul _ _
        _ ≤ (m - 1) * rest.length + (P.totalDegree - 1) :=
            Nat.add_le_add ih totalDegree_pderiv_le
        _ ≤ (m - 1) * rest.length + (m - 1) :=
            Nat.add_le_add_left (Nat.sub_le_sub_right hdeg 1) _
    have h1 : (P * pderiv j L).totalDegree ≤ (m - 1) * rest.length + (m - 1) := by
      by_cases hL_deg : L.totalDegree = 0
      · rw [pderiv_eq_zero_of_totalDegree_zero hL_deg, mul_zero, totalDegree_zero]
        exact Nat.zero_le _
      · calc (P * pderiv j L).totalDegree
            ≤ P.totalDegree + (pderiv j L).totalDegree := totalDegree_mul _ _
          _ ≤ m + (L.totalDegree - 1) := Nat.add_le_add hdeg totalDegree_pderiv_le
          _ ≤ m + ((m - 1) * rest.length - 1) :=
              Nat.add_le_add_left (Nat.sub_le_sub_right ih 1) _
          _ ≤ (m - 1) * rest.length + (m - 1) := by
              have : 1 ≤ (m - 1) * rest.length := by
                have : 1 ≤ L.totalDegree := Nat.one_le_iff_ne_zero.mpr hL_deg
                omega
              omega
    calc (P * pderiv j L - (1 + rest.length : ℕ) • (L * pderiv j P)).totalDegree
        ≤ max (P * pderiv j L).totalDegree
            ((1 + rest.length : ℕ) • (L * pderiv j P)).totalDegree :=
          totalDegree_sub _ _
      _ ≤ max ((m - 1) * rest.length + (m - 1)) ((m - 1) * rest.length + (m - 1)) :=
          max_le_max h1 h2
      _ = (m - 1) * rest.length + (m - 1) := max_self _
      _ = (m - 1) * (rest.length + 1) := by ring

/-- Left-fold version of the reciprocal numerator construction, threading a running numerator `Q`
and a running power index `k` along the list of differentiation directions. -/
def foldNumerator (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin n) ℂ → ℕ → List (Fin n) → MvPolynomial (Fin n) ℂ
  | Q, _, [] => Q
  | Q, k, j :: rest => foldNumerator P (P * pderiv j Q - k • (Q * pderiv j P)) (k + 1) rest

/-- Cons-unfolding lemma for `foldNumerator`: prepending a direction performs one quotient-rule
step on the running numerator and increments the power index. -/
@[simp]
lemma foldNumerator_cons (P Q : MvPolynomial (Fin n) ℂ) (k : ℕ) (j : Fin n)
    (rest : List (Fin n)) :
    foldNumerator P Q k (j :: rest) =
      foldNumerator P (P * pderiv j Q - k • (Q * pderiv j P)) (k + 1) rest := rfl

/-- Partial derivatives on a multivariate polynomial commute: `∂ᵢ ∂ⱼ p = ∂ⱼ ∂ᵢ p`. -/
theorem pderiv_pderiv_comm {σ : Type*} {R : Type*} [CommSemiring R]
    (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k ih =>
    simp only [pderiv_mul, map_add]
    have hXij : (pderiv i) ((pderiv j) (X k : MvPolynomial σ R)) = 0 := by
      by_cases hjk : k = j
      · subst hjk; simp
      · rw [pderiv_X_of_ne hjk]; simp
    have hXji : (pderiv j) ((pderiv i) (X k : MvPolynomial σ R)) = 0 := by
      by_cases hik : k = i
      · subst hik; simp
      · rw [pderiv_X_of_ne hik]; simp
    simp only [hXij, hXji, mul_zero, add_zero]
    rw [ih]; ring

/-- Concatenation lemma: folding along `js₁ ++ js₂` equals folding along `js₂` starting from the
result of folding along `js₁`, with the running index shifted by `js₁.length`. -/
lemma foldNumerator_append (P Q : MvPolynomial (Fin n) ℂ) (k : ℕ)
    (js₁ js₂ : List (Fin n)) :
    foldNumerator P Q k (js₁ ++ js₂) =
      foldNumerator P (foldNumerator P Q k js₁) (k + js₁.length) js₂ := by
  induction js₁ generalizing Q k with
  | nil => simp [foldNumerator]
  | cons j rest ih =>
    simp only [List.cons_append, foldNumerator, List.length_cons]
    rw [ih]
    congr 1
    omega

set_option maxHeartbeats 400000 in
/-- Append-singleton recursion for `reciprocalNumerator`: appending a single direction `j` to `js`
applies one more quotient-rule step. -/
lemma reciprocalNumerator_append_singleton (P : MvPolynomial (Fin n) ℂ)
    (js : List (Fin n)) (j : Fin n) :
    reciprocalNumerator P (js ++ [j]) =
      P * pderiv j (reciprocalNumerator P js) -
        (1 + js.length : ℕ) • (reciprocalNumerator P js * pderiv j P) := by
  induction js with
  | nil => simp [reciprocalNumerator, List.length]
  | cons j₁ rest ih =>
    simp only [List.cons_append, reciprocalNumerator, List.length_cons, List.length_append]
    rw [ih]
    set L := reciprocalNumerator P rest
    have hcomm_L : (pderiv j₁) ((pderiv j) L) = (pderiv j) ((pderiv j₁) L) :=
      pderiv_pderiv_comm j₁ j L
    have hcomm_P : (pderiv j₁) ((pderiv j) P) = (pderiv j) ((pderiv j₁) P) :=
      pderiv_pderiv_comm j₁ j P
    simp only [map_sub, map_nsmul, pderiv_mul, List.length_nil]
    rw [hcomm_L, hcomm_P]
    ring

set_option maxHeartbeats 400000 in
/-- The fold form `foldNumerator P 1 1 js` agrees with the recursive form `reciprocalNumerator P
js`. -/
theorem foldNumerator_eq_reciprocalNumerator {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (js : List (Fin n)) :
    foldNumerator P 1 1 js = reciprocalNumerator P js := by
  induction js using List.reverseRecOn with
  | nil => simp [foldNumerator, reciprocalNumerator]
  | append_singleton js j ih =>
    rw [foldNumerator_append, reciprocalNumerator_append_singleton]
    simp only [foldNumerator]
    rw [ih]

open Filter in
/-- If two functions agree on a neighborhood of `ξ`, then their iterated partial derivatives along
`js` agree at `ξ`. -/
lemma iteratedPartialDeriv_eventuallyEq_nhds
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℂ}
    {ξ : EuclideanSpace ℝ (Fin n)}
    (js : List (Fin n))
    (heq : g₁ =ᶠ[nhds ξ] g₂) :
    iteratedPartialDeriv js g₁ ξ = iteratedPartialDeriv js g₂ ξ := by
  suffices h : ∀ (g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℂ)
      (ξ : EuclideanSpace ℝ (Fin n)) (js : List (Fin n)),
      g₁ =ᶠ[nhds ξ] g₂ →
      iteratedPartialDeriv js g₁ =ᶠ[nhds ξ] iteratedPartialDeriv js g₂ by
    exact (h g₁ g₂ ξ js heq).self_of_nhds
  intro g₁' g₂' ξ' js'
  induction js' generalizing g₁' g₂' ξ' with
  | nil => exact id
  | cons j rest ih =>
    intro heq'
    rw [iteratedPartialDeriv_cons, iteratedPartialDeriv_cons]
    apply ih
    exact (heq'.fderiv (𝕜 := ℝ)).fun_comp (· (EuclideanSpace.single j 1))

set_option maxHeartbeats 800000 in
/-- Identity matching repeated partial differentiation of `Q / Pᵏ` (in a neighborhood where
`P ≠ 0`) with `foldNumerator P Q k js` divided by `P^(k + js.length)`. -/
theorem foldNumerator_identity {n : ℕ} (P Q : MvPolynomial (Fin n) ℂ) (k : ℕ)
    (js : List (Fin n)) :
    ∀ ξ : EuclideanSpace ℝ (Fin n),
      evalAtReal P ξ ≠ 0 →
      iteratedPartialDeriv js (fun ξ' => evalAtReal Q ξ' / (evalAtReal P ξ') ^ k) ξ =
        evalAtReal (foldNumerator P Q k js) ξ / (evalAtReal P ξ) ^ (k + js.length) := by
  induction js generalizing Q k with
  | nil =>
    intro ξ _hP
    simp [iteratedPartialDeriv, foldNumerator]

  | cons j rest ih =>
    intro ξ hP
    rw [iteratedPartialDeriv_cons, foldNumerator_cons, List.length_cons]
    set Q' := P * pderiv j Q - k • (Q * pderiv j P)

    have hcont : Continuous (evalAtReal P) :=
      (evalAtReal_differentiable P).continuous
    have hopen : IsOpen {ξ' | evalAtReal P ξ' ≠ 0} :=
      isOpen_ne_fun hcont continuous_const
    have hnhds : {ξ' | evalAtReal P ξ' ≠ 0} ∈ nhds ξ :=
      hopen.mem_nhds hP

    have hfun_eq : (fun ξ' => fderiv ℝ
        (fun ξ'' => evalAtReal Q ξ'' / (evalAtReal P ξ'') ^ k) ξ'
        (EuclideanSpace.single j 1)) =ᶠ[nhds ξ]
      (fun ξ' => evalAtReal Q' ξ' / (evalAtReal P ξ') ^ (k + 1)) := by
      apply Filter.eventuallyEq_iff_exists_mem.mpr
      exact ⟨{ξ' | evalAtReal P ξ' ≠ 0}, hnhds, fun ξ' hξ' =>
        quotient_fderiv_step P Q k j ξ' hξ'⟩

    rw [iteratedPartialDeriv_eventuallyEq_nhds rest hfun_eq]

    have key := ih Q' (k + 1) ξ hP
    rw [key]
    congr 2
    omega

set_option maxHeartbeats 800000 in
/-- Analytic identity for the reciprocal polynomial: where `P ≠ 0`, the iterated partial derivative
of `1 / P` equals `reciprocalNumerator P js` divided by `P^(1 + js.length)`. -/
theorem reciprocal_poly_analytic_identity
    {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (js : List (Fin n)) :
    ∀ ξ : EuclideanSpace ℝ (Fin n),
      evalAtReal P ξ ≠ 0 →
      iteratedPartialDeriv js (polyReciprocal P) ξ =
        evalAtReal (reciprocalNumerator P js) ξ / (evalAtReal P ξ) ^ (1 + js.length) := by
  intro ξ hP

  have h1 : polyReciprocal P = fun ξ' => evalAtReal 1 ξ' / (evalAtReal P ξ') ^ 1 := by
    funext ξ'
    simp only [polyReciprocal, evalAtReal, map_one, pow_one, one_div]
  rw [h1]

  have h2 := foldNumerator_identity P 1 1 js ξ hP
  rw [h2]

  rw [foldNumerator_eq_reciprocalNumerator]

/-- Structural form of Melrose Lemma 11.14: there exists a polynomial `L` of total degree at most
`(m - 1) * js.length` such that the iterated partial derivative of `1 / P` (where `P ≠ 0`) equals
`L / P^(1 + js.length)`. -/
theorem reciprocal_poly_structural (P : MvPolynomial (Fin n) ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hdeg : P.totalDegree ≤ m)
    (js : List (Fin n)) :
    ∃ L : MvPolynomial (Fin n) ℂ,
      L.totalDegree ≤ (m - 1) * js.length ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n),
        evalAtReal P ξ ≠ 0 →
        iteratedPartialDeriv js (polyReciprocal P) ξ =
          evalAtReal L ξ / (evalAtReal P ξ) ^ (1 + js.length) :=
  ⟨reciprocalNumerator P js,
   reciprocalNumerator_totalDegree P m hm hdeg js,
   reciprocal_poly_analytic_identity P js⟩

end DifferentialOperators

end
