/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor

open Polynomial


section TopologicalGroup

/-- *Proposition-valued version of `IsTopologicalGroup`*: a group $G$ with a topology such
that multiplication and inversion are continuous. Used as a `Prop` (rather than a structure)
so it can be carried through hypotheses without instance issues. -/
structure TopologicalGroupProp (G : Type*) [TopologicalSpace G] [Group G] : Prop where
  mul_continuous : Continuous (fun p : G × G => p.1 * p.2)
  inv_continuous : Continuous (Inv.inv : G → G)

/-- *From a Mathlib `IsTopologicalGroup` instance, derive `TopologicalGroupProp`*. -/
theorem TopologicalGroupProp.of_isTopologicalGroup
    (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    TopologicalGroupProp G :=
  ⟨continuous_mul, continuous_inv⟩

/-- *From `TopologicalGroupProp`, construct an `IsTopologicalGroup` instance*. -/
theorem TopologicalGroupProp.toIsTopologicalGroup
    {G : Type*} [TopologicalSpace G] [Group G] (h : TopologicalGroupProp G) :
    IsTopologicalGroup G :=
  { continuous_mul := h.mul_continuous
    continuous_inv := h.inv_continuous }

end TopologicalGroup


section ClopenSubsets

universe u v

variable (K : Type u) [Field K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
  [hv : Valued K Γ₀]


/-- *Valuation subring is open*: in a valued field $K$, the valuation subring $\mathcal{O}_v
= \{x \in K : v(x) \le 1\}$ is an open subset of $K$. -/
theorem valuationRing_isOpen :
    IsOpen (hv.v.valuationSubring : Set K) :=
  Valued.isOpen_valuationSubring K

/-- *Valuation subring is closed*: the valuation subring is also closed in $K$ — this is the
non-archimedean analogue of the fact that closed balls are closed. -/
theorem valuationRing_isClosed :
    IsClosed (hv.v.valuationSubring : Set K) :=
  Valued.isClosed_valuationSubring K

/-- *Valuation subring is clopen*: combining the two preceding results, $\mathcal{O}_v$ is
both open and closed in $K$ (i.e. clopen). -/
theorem valuationRing_isClopen :
    IsClopen (hv.v.valuationSubring : Set K) :=
  ⟨valuationRing_isClosed K, valuationRing_isOpen K⟩


/-- *Maximal ideal of the valuation subring is open* in $K$: the set $\{x : v(x) < 1\}$ —
which corresponds to the maximal ideal $\mathfrak{m}_v$ of $\mathcal{O}_v$ — is open. -/
theorem maximalIdeal_isOpen :
    IsOpen (X := K)
      {x | Valued.v.restrict x < (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
  Valued.isOpen_ball K 1

/-- *Maximal ideal of the valuation subring is closed* in $K$: $\{x : v(x) < 1\}$ is closed
(another non-archimedean phenomenon — strict inequality balls are closed). -/
theorem maximalIdeal_isClosed :
    IsClosed (X := K)
      {x | Valued.v.restrict x < (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
  Valued.isClosed_ball K 1

/-- *Maximal ideal is clopen* in $K$: combining the two preceding results. -/
theorem maximalIdeal_isClopen :
    IsClopen (X := K)
      {x | Valued.v.restrict x < (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
  ⟨maximalIdeal_isClosed K, maximalIdeal_isOpen K⟩


/-- *The set of valuation units is open* in $K$: $\mathcal{O}_v^\times = \{x : v(x) = 1\}$
is open. -/
theorem valuationUnits_isOpen :
    IsOpen (X := K)
      {x | Valued.v.restrict x = (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
  Valued.isOpen_sphere K one_ne_zero

/-- *The set of valuation units is closed* in $K$: $\{x : v(x) = 1\}$ is also closed. -/
theorem valuationUnits_isClosed :
    IsClosed (X := K)
      {x | Valued.v.restrict x = (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
  Valued.isClosed_sphere K 1

/-- *Valuation units form a clopen subset* of $K$: combining the two preceding results. -/
theorem valuationUnits_isClopen :
    IsClopen (X := K)
      {x | Valued.v.restrict x = (1 : MonoidWithZeroHom.ValueGroup₀ hv.v)} :=
  ⟨valuationUnits_isClosed K, valuationUnits_isOpen K⟩

end ClopenSubsets


section HenselsLemma

/-- *One Newton iteration*: given $f \in R[X]$ and a current approximation $x$ at which
$f'(x)$ is a unit, return $x - f(x)/f'(x)$. The unit hypothesis lets us invert $f'(x)$. -/
noncomputable def newtonStep {R : Type*} [CommRing R] (f : R[X]) (x : R)
    (h_unit : IsUnit ((Polynomial.derivative f).eval x)) : R :=
  x - ↑h_unit.unit⁻¹ * f.eval x

/-- *Newton iteration sequence* starting from $x_0$: $c_0 = x_0$ and $c_{n+1} = c_n -
f(c_n) \cdot \text{Ring.inverse}(f'(c_n))$. We use `Ring.inverse` so that this is total in
$R$ — the value is meaningful when $f'(c_n)$ is a unit. -/
noncomputable def newtonSeq {R : Type*} [CommRing R] (f : R[X]) (x₀ : R) : ℕ → R :=
  fun n => Nat.recOn n x₀ fun _ b => b - f.eval b * Ring.inverse ((Polynomial.derivative f).eval b)

/-- *Hensel's lemma for non-monic polynomials over an adically complete ring*: if $R$ is
$I$-adically complete, $f \in R[X]$ has an approximate root $a_0$ with $f(a_0) \in I$ and
$f'(a_0)$ a unit mod $I$, then there is a true root $a \in R$ of $f$ with $a \equiv a_0
\pmod I$. The proof constructs Newton's sequence $c_{n+1} = c_n - f(c_n)/f'(c_n)$, shows it is
Cauchy in the $I$-adic topology, and takes its limit. -/
theorem hensel_nonmonic_adic (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f

  let c : ℕ → R := fun n =>
    Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b)
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) := by
    intro n; simp only [c]

  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁

  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)


  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using h₁
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i; rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_

      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _


      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _

  have cauchy : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => simp [SModEq.refl]
    | succ k ih =>
      rw [← Nat.add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [Nat.add_assoc]
      exact le_self_add

  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (cauchy _ _)
  refine ⟨a, ?_, ?_⟩

  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)

  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/-- *Hensel's lemma with an explicit Newton-sequence witness*: same hypotheses as
`hensel_nonmonic_adic`, but the conclusion also records that the Newton sequence converges to
$a$ in the $I$-adic topology, that $f(\text{newtonSeq}\,f\,a_0\,n) \in I^{n+1}$ for every $n$
(quadratic convergence!), and that $f'(\text{newtonSeq}\,f\,a_0\,n)$ is a unit at every step
(allowing the iteration to continue). This stronger form is what `IwahoriDecomp` consumes. -/
theorem hensel_nonmonic_adic_newton (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R,
      f.IsRoot a ∧
      a - a₀ ∈ I ∧

      (∀ n, newtonSeq f a₀ n ≡ a [SMOD (I ^ n • ⊤ : Ideal R)]) ∧

      (∀ n, f.eval (newtonSeq f a₀ n) ∈ I ^ (n + 1)) ∧

      (∀ n, IsUnit ((Polynomial.derivative f).eval (newtonSeq f a₀ n))) := by
  classical
  set c := newtonSeq f a₀ with hc_def
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse ((derivative f).eval (c n)) := by
    intro n; simp only [c, newtonSeq]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit ((derivative f).eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using h₁
    | succ n ih =>
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i; rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have cauchy : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => simp [SModEq.refl]
    | succ k ih =>
      rw [← Nat.add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [Nat.add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (cauchy _ _)
  refine ⟨a, ?_, ?_, ha, hfcI, hf'c⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

end HenselsLemma
