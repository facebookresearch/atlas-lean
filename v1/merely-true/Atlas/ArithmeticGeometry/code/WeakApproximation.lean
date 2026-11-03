/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Instances.Rat

noncomputable section

open Filter Topology

/-- The rational numbers are dense in $\mathbb{Q}_p$: the inclusion
$\mathbb{Q} \hookrightarrow \mathbb{Q}_p$ has dense range. -/
theorem rat_dense_in_padic (p : ℕ) [Fact (Nat.Prime p)] :
    DenseRange ((↑) : ℚ → ℚ_[p]) :=
  Padic.denseRange_ratCast p


/-- Density of the diagonal embedding $R \to \prod_i (R, v_i)$ given a finite family of pairwise
inequivalent nontrivial absolute values; this is the algebraic core of weak approximation. -/
theorem AbsoluteValue.denseRange_algebraMap_pi
    {R : Type*} [Field R] {ι : Type*} [Fintype ι]
    {v : ι → AbsoluteValue R ℝ}
    (hnt : ∀ i, (v i).IsNontrivial)
    (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j)) :
    DenseRange (algebraMap R ((i : ι) → WithAbs (v i))) := by
  set_option backward.isDefEq.respectTransparency false in
  classical
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using exists_one_lt_lt_one_pi_of_not_isEquiv hnt hne
  let y := fun n ↦ ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (v i) (z i)
  have : atTop.Tendsto
      (fun n (i : ι) ↦ (WithAbs.equiv (v i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finset_sum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have : (v u) (a u)⁻¹ < 1 := by simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (v i)) hw (z w)]
      have haw_pos : 0 < (v u) (a w) := by
        apply (v u).pos_iff.2
        intro ha
        have h1 : (v w) (a w) = 0 := by rw [ha]; simp
        linarith [(hx w).1]
      have hu : 1 < (v u) (a w)⁻¹ := by
        rw [map_inv₀]
        exact one_lt_inv_iff₀.mpr ⟨haw_pos, (hx w).2 u hw⟩
      have := (v u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (v u)).symm (WithAbs.equiv (v w) (z w)))
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 this r hr
  exact ⟨y N, dist_comm z (algebraMap R _ (y N)) ▸ h N le_rfl⟩

/-- Diagonal embedding into the product of completions has dense range: the image of $R$ is
dense in $\prod_i \widehat{R}_{v_i}$ for pairwise inequivalent nontrivial absolute values. -/
theorem AbsoluteValue.denseRange_coe_completion_pi
    {R : Type*} [Field R] {ι : Type*} [Fintype ι]
    {v : ι → AbsoluteValue R ℝ}
    (hnt : ∀ i, (v i).IsNontrivial)
    (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j)) :
    DenseRange (fun (x : R) (i : ι) =>
      (UniformSpace.Completion.coe' (WithAbs.toAbs (v i) x) : (v i).Completion)) :=
  (DenseRange.piMap (fun _ => UniformSpace.Completion.denseRange_coe)).comp
    (denseRange_algebraMap_pi hnt hne)
    (Continuous.piMap fun _ => UniformSpace.Completion.continuous_coe _)

/-- A *place of $\mathbb{Q}$* is either the archimedean (real) place or a $p$-adic place for some
prime $p$. -/
inductive PlaceQ where
  | finite (p : Nat.Primes) : PlaceQ
  | infinite : PlaceQ

/-- Decidable equality on places of $\mathbb{Q}$: two places are either both infinite, or finite
with the same prime. -/
instance : DecidableEq PlaceQ := by
  intro a b
  cases a with
  | finite p =>
    cases b with
    | finite q =>
      exact if h : p = q then isTrue (by rw [h]) else
        isFalse (by intro heq; exact h (PlaceQ.finite.inj heq))
    | infinite => exact isFalse PlaceQ.noConfusion
  | infinite =>
    cases b with
    | finite _ => exact isFalse PlaceQ.noConfusion
    | infinite => exact isTrue rfl

/-- The absolute value on $\mathbb{Q}$ associated to a place: the $p$-adic absolute value for a
finite place, and the real absolute value $|\cdot|_\infty$ for the infinite place. -/
def PlaceQ.absValue : PlaceQ → AbsoluteValue ℚ ℝ
  | .finite ⟨p, hp⟩ => @Rat.AbsoluteValue.padic p ⟨hp⟩
  | .infinite => Rat.AbsoluteValue.real

/-- The $p$-adic absolute value on $\mathbb{Q}$ is nontrivial: $|p|_p = 1/p < 1$. -/
lemma PlaceQ.absValue_isNontrivial_finite (p : Nat.Primes) :
    (PlaceQ.absValue (.finite p)).IsNontrivial := by
  obtain ⟨p, hp⟩ := p
  simp only [PlaceQ.absValue]
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  use p
  simp only [Rat.AbsoluteValue.padic_eq_padicNorm]
  rw [padicNorm.padicNorm_p hp.one_lt]
  push_cast
  exact ⟨Nat.cast_ne_zero.mpr hp.ne_zero,
    ne_of_lt (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr hp.one_lt))⟩

/-- The real (infinite) absolute value on $\mathbb{Q}$ is nontrivial: $|2|_\infty = 2 \ne 1$. -/
lemma PlaceQ.absValue_isNontrivial_infinite :
    (PlaceQ.absValue .infinite).IsNontrivial :=
  ⟨2, by simp [PlaceQ.absValue, Rat.AbsoluteValue.real_eq_abs]⟩

/-- Every place of $\mathbb{Q}$ yields a nontrivial absolute value. -/
lemma PlaceQ.absValue_isNontrivial (v : PlaceQ) :
    (PlaceQ.absValue v).IsNontrivial := by
  cases v with
  | finite p => exact absValue_isNontrivial_finite p
  | infinite => exact absValue_isNontrivial_infinite

/-- A $p$-adic absolute value is not equivalent to the real absolute value: any $p$ has
$|p|_p < 1$ while $|p|_\infty > 1$. -/
lemma PlaceQ.padic_not_equiv_real (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ¬(Rat.AbsoluteValue.padic p).IsEquiv Rat.AbsoluteValue.real := by
  intro h
  have h1 := (h p 1).mp
  simp only [Rat.AbsoluteValue.padic_eq_padicNorm, Rat.AbsoluteValue.real_eq_abs, map_one] at h1
  rw [padicNorm.padicNorm_p hp.out.one_lt] at h1
  push_cast at h1
  have hq_inv_le : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)
  have h2 := h1 hq_inv_le
  rw [abs_of_pos (by exact_mod_cast hp.out.pos : (0 : ℝ) < p)] at h2
  linarith [show (1 : ℝ) < p from by exact_mod_cast hp.out.one_lt]

/-- $p$-adic and $q$-adic absolute values are inequivalent whenever $p \ne q$. -/
lemma PlaceQ.padic_not_equiv_padic {p q : ℕ} [hp : Fact (Nat.Prime p)]
    [hq : Fact (Nat.Prime q)] (hpq : p ≠ q) :
    ¬(Rat.AbsoluteValue.padic p).IsEquiv (Rat.AbsoluteValue.padic q) := by
  intro h
  have h1 := (h q p).mpr
  simp only [Rat.AbsoluteValue.padic_eq_padicNorm] at h1
  rw [padicNorm.padicNorm_of_prime_of_ne hpq,
      padicNorm.padicNorm_p hp.out.one_lt,
      padicNorm.padicNorm_of_prime_of_ne hpq.symm,
      padicNorm.padicNorm_p hq.out.one_lt] at h1
  push_cast at h1
  have hq_inv_le : (q : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hq.out.one_lt.le)
  have h2 := h1 hq_inv_le
  have hp_inv_lt : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  linarith

/-- Pairwise inequivalence of distinct places: the absolute values from any two distinct
places of $\mathbb{Q}$ are not equivalent. -/
lemma PlaceQ.absValue_pairwise_not_equiv :
    ∀ (v w : PlaceQ), v ≠ w → ¬(PlaceQ.absValue v).IsEquiv (PlaceQ.absValue w) := by
  intro v w hvw
  cases v with
  | finite p =>
    cases w with
    | finite q =>
      simp only [PlaceQ.absValue]
      have hpq : p ≠ q := fun h => hvw (by rw [h])
      have hpq_val : p.val ≠ q.val := fun h => hpq (Subtype.val_injective h)
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      haveI : Fact (Nat.Prime q.val) := ⟨q.property⟩
      exact padic_not_equiv_padic hpq_val
    | infinite =>
      simp only [PlaceQ.absValue]
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      exact padic_not_equiv_real p.val
  | infinite =>
    cases w with
    | finite q =>
      simp only [PlaceQ.absValue]
      haveI : Fact (Nat.Prime q.val) := ⟨q.property⟩
      exact fun h => padic_not_equiv_real q.val h.symm
    | infinite => exact absurd rfl hvw

/-- Theorem 11.7 (Weak Approximation for $\mathbb{Q}$): the diagonal embedding
$\mathbb{Q} \to \prod_i \widehat{\mathbb{Q}}_{v_i}$ has dense range for any finite injective
family of places. Concretely, one can simultaneously approximate any tuple of elements in the
completions by a single rational number. -/
theorem weak_approximation_rationals {ι : Type*} [Fintype ι]
    (v : ι → PlaceQ) (hv : Function.Injective v) :
    DenseRange (fun (x : ℚ) (i : ι) =>
      (UniformSpace.Completion.coe' (WithAbs.toAbs (PlaceQ.absValue (v i)) x) :
        (PlaceQ.absValue (v i)).Completion)) := by
  apply AbsoluteValue.denseRange_coe_completion_pi
  · intro i
    exact PlaceQ.absValue_isNontrivial (v i)
  · intro i j hij
    exact PlaceQ.absValue_pairwise_not_equiv _ _ (fun h => hij (hv h))

/-- Theorem 11.8 (Strong Approximation for $\mathbb{Z}$): the diagonal embedding
$\mathbb{Z} \to \prod_i \mathbb{Z}_{p_i}$ has dense range for any finite injective family of
primes. The proof combines $p$-adic density with the Chinese Remainder Theorem. -/
theorem strong_approximation_integers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [hp : ∀ i, Fact (Nat.Prime (p i))]
    (hinj : Function.Injective p) :
    DenseRange (fun (z : ℤ) (i : ι) => (z : ℤ_[p i])) := by
  rw [Metric.denseRange_iff]
  intro x r hr

  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)

  have hne : ∀ i, NeZero (p i ^ n) := fun i => ⟨pow_ne_zero n (hp i).out.ne_zero⟩
  let a : ι → ℕ := fun i => ZMod.val (PadicInt.toZModPow n (x i))

  have hcoprime : (↑(Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun Nat.Coprime (fun i => p i ^ n)) := by
    intro i _ j _ hij
    exact Nat.coprime_pow_primes n n (hp i).out (hp j).out (fun h => hij (hinj h))
  have hne' : ∀ i ∈ (Finset.univ : Finset ι), (fun i => p i ^ n) i ≠ 0 :=
    fun i _ => pow_ne_zero n (hp i).out.ne_zero
  obtain ⟨z, hz⟩ := Nat.chineseRemainderOfFinset a (fun i => p i ^ n) Finset.univ hne' hcoprime

  refine ⟨(z : ℤ), ?_⟩
  rw [dist_pi_lt_iff hr]
  intro i

  have hzi := hz i (Finset.mem_univ i)

  have hzmod : (z : ZMod (p i ^ n)) = ((a i : ℕ) : ZMod (p i ^ n)) := by
    rwa [ZMod.natCast_eq_natCast_iff]

  have ha : ((a i : ℕ) : ZMod (p i ^ n)) = PadicInt.toZModPow n (x i) := by
    simp only [a, ZMod.natCast_val, ZMod.cast_id']
    rfl

  have hmod : PadicInt.toZModPow n ((z : ℤ) : ℤ_[p i]) = PadicInt.toZModPow n (x i) := by
    rw [map_intCast]
    push_cast
    rw [hzmod, ha]

  calc dist (x i) ((z : ℤ) : ℤ_[p i])
      ≤ (p i : ℝ) ^ (-(n : ℤ)) := by
        rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow]
        simp only [RingHom.mem_ker, map_sub]
        exact sub_eq_zero.mpr hmod.symm
    _ = ((p i : ℝ) ^ n)⁻¹ := by rw [zpow_neg, zpow_natCast]
    _ ≤ (2⁻¹ : ℝ) ^ n := by
        rw [← inv_pow]
        exact pow_le_pow_left₀ (by positivity)
          (inv_anti₀ (by positivity : (0 : ℝ) < 2) (by exact_mod_cast (hp i).out.two_le)) n
    _ = (1 / 2 : ℝ) ^ n := by rw [one_div]
    _ < r := hn

end
