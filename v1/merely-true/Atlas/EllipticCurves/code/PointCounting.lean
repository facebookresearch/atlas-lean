/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Exponent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Atlas.EllipticCurves.code.Isogenies

section Lemma71

variable {R : Type*} [Ring R] (IsInsep : R → Prop)

/-- Abstract axiomatization of the inseparability predicate on a ring $R$
(intended to be the endomorphism ring of an elliptic curve), specifying the structural
properties needed to prove Lemma 7.1. It posits a distinguished inseparable element
$\pi$ (Frobenius) through which every inseparable endomorphism factors, closure under
multiplication by $\pi$, and closure under negation. -/
structure InsepAxioms where
  /-- The distinguished inseparable element (Frobenius). -/
  π : R
  /-- The element $\pi$ is itself inseparable. -/
  π_insep : IsInsep π
  /-- Every inseparable element factors as $\gamma \cdot \pi$ for some $\gamma$. -/
  factor : ∀ α, IsInsep α → ∃ γ, α = γ * π
  /-- Any product $\gamma \cdot \pi$ is inseparable. -/
  mul_π_insep : ∀ γ, IsInsep (γ * π)
  /-- The set of inseparable elements is closed under negation. -/
  neg_insep : ∀ α, IsInsep α → IsInsep (-α)

variable {IsInsep}

/-- Lemma 7.1 (additive complement of inseparables): if $\alpha$ is inseparable, then
$\alpha + \beta$ is inseparable iff $\beta$ is. Both directions reduce to factoring
through $\pi$. -/
theorem inseparable_add_iff (ax : InsepAxioms IsInsep)
    {α β : R} (hα : IsInsep α) :
    IsInsep (α + β) ↔ IsInsep β := by
  constructor
  ·
    intro hαβ

    suffices h : IsInsep (-β) by
      have := ax.neg_insep (-β) h
      rwa [neg_neg] at this


    have h_neg_αβ : IsInsep (-(α + β)) := ax.neg_insep _ hαβ
    obtain ⟨γ₁, hγ₁⟩ := ax.factor _ h_neg_αβ
    obtain ⟨γ₂, hγ₂⟩ := ax.factor _ hα

    have key : -β = (γ₁ + γ₂) * ax.π := by
      have : -(α + β) + α = -β := by abel
      rw [← this, hγ₁, hγ₂, add_mul]
    rw [key]
    exact ax.mul_π_insep _
  ·
    intro hβ
    obtain ⟨γ₁, hγ₁⟩ := ax.factor _ hα
    obtain ⟨γ₂, hγ₂⟩ := ax.factor _ hβ
    have key : α + β = (γ₁ + γ₂) * ax.π := by
      rw [hγ₁, hγ₂, add_mul]
    rw [key]
    exact ax.mul_π_insep _

/-- Lemma 7.1 (contrapositive form): if $\alpha$ is inseparable, then $\alpha + \beta$ is
*separable* iff $\beta$ is separable. -/
theorem separable_add_iff (ax : InsepAxioms IsInsep)
    {α β : R} (hα : IsInsep α) :
    ¬ IsInsep (α + β) ↔ ¬ IsInsep β :=
  (inseparable_add_iff ax hα).not

end Lemma71

namespace PointCounting

variable {F : Type*} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}




end PointCounting

namespace Hasse

set_option maxHeartbeats 400000

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {W : WeierstrassCurve.Affine F}

/-- An equivalence between the points of a Weierstrass curve and `Option`-of-nonsingular
affine pairs: the point at infinity corresponds to `none` and each affine point $(x, y)$
to `some ⟨(x, y), h⟩`. -/
noncomputable def pointEquiv :
    W.Point ≃ Option { p : F × F // W.Nonsingular p.1 p.2 } where
  toFun P := P.rec Option.none (fun x y h => Option.some ⟨⟨x, y⟩, h⟩)
  invFun o := o.rec .zero (fun ⟨⟨x, y⟩, h⟩ => .some x y h)
  left_inv P := by cases P <;> rfl
  right_inv o := by
    cases o with
    | none => rfl
    | some val =>
      obtain ⟨⟨x, y⟩, h⟩ := val
      rfl

/-- The point set $W(F)$ of a Weierstrass curve over a finite field is itself finite,
transported across `pointEquiv` from the (finite) type of optional nonsingular affine
pairs. -/
noncomputable instance pointFintypeInst : Fintype W.Point := by
  classical
  exact Fintype.ofEquiv _ pointEquiv.symm

/-- The number $\#E(\mathbb{F}_q)$ of $\mathbb{F}_q$-rational points (including the point
at infinity) of a Weierstrass curve over a finite field. -/
noncomputable def numPoints (W : WeierstrassCurve.Affine F) : ℕ :=
  Fintype.card W.Point

/-- The trace of Frobenius $t = q + 1 - \#E(\mathbb{F}_q)$ for an elliptic curve $E$
over $\mathbb{F}_q$. By Hasse's theorem, $|t| \leq 2\sqrt{q}$. -/
noncomputable def traceFrobenius (W : WeierstrassCurve.Affine F) : ℤ :=
  (Fintype.card F : ℤ) + 1 - (numPoints W : ℤ)

/-- Rearrangement of the definition of the trace of Frobenius: $\#E(\mathbb{F}_q) = q + 1 - t$. -/
theorem numPoints_eq_card_sub_trace (W : WeierstrassCurve.Affine F) :
    (numPoints W : ℤ) = (Fintype.card F : ℤ) + 1 - traceFrobenius W := by
  simp [traceFrobenius]










end Hasse

namespace GroupExponent

variable (G : Type*) [Group G]

/-- The exponent of a group $G$: the least $n$ such that $g^n = 1$ for all $g \in G$
(equivalent to the LCM of orders of elements when $G$ is finite). -/
noncomputable def groupExponent : ℕ := Monoid.exponent G

end GroupExponent

section EulerProductInfra

/-- The completely multiplicative monoid-with-zero homomorphism $\mathbb{N} \to \mathbb{R}$
sending $n \mapsto 1/n^2$ (and $0 \mapsto 0$). Used to express $\zeta(2)$ as the Euler
product $\sum_n 1/n^2 = \prod_p (1 - p^{-2})^{-1}$. -/
noncomputable def oneOverSqHom : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else 1 / (n : ℝ) ^ 2
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [hm, hn, Nat.mul_eq_zero, or_self, ↓reduceIte, Nat.cast_mul]; field_simp

/-- The value of `oneOverSqHom` at $n$ is $1/n^2$ (which is $0$ when $n = 0$). -/
lemma oneOverSqHom_eq (n : ℕ) : oneOverSqHom n = 1 / (n : ℝ) ^ 2 := by
  unfold oneOverSqHom; simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]; split <;> simp_all

/-- Norm-summability of $\sum 1/n^2$: a prerequisite for invoking Mathlib's Euler product
machinery for $\zeta(2)$. -/
lemma oneOverSqHom_summable : Summable (fun n => ‖oneOverSqHom n‖) :=
  hasSum_zeta_two.summable.norm.congr (fun n => by rw [oneOverSqHom_eq])

/-- The Euler product for $\zeta(2)$: $\prod_p (1 - p^{-2})^{-1} = \pi^2 / 6$, the
Basel formula. This is the analytic input to Theorem 7.6. -/
lemma eulerProduct_zeta2 :
    HasProd (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
  have : ∑' (n : ℕ), oneOverSqHom n = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two.tsum_eq
    rw [show (fun n : ℕ => 1 / (n : ℝ) ^ 2) = oneOverSqHom from
      by ext; rw [oneOverSqHom_eq]] at h
    exact h
  rw [← this]
  convert EulerProduct.eulerProduct_completely_multiplicative_hasProd
    oneOverSqHom_summable using 2 with p
  rw [oneOverSqHom_eq]

/-- Each Euler factor $(1 - p^{-2})^{-1}$ is at least $1$ since the geometric series
expansion $\sum_k p^{-2k}$ starts with $1$. -/
lemma eulerFactor_ge_one (p : Nat.Primes) :
    1 ≤ (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ := by
  rw [one_le_inv_iff₀]
  have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp2 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ 2 := by positivity
  exact ⟨by rw [sub_pos, div_lt_one hp2]; nlinarith,
         by linarith [div_nonneg one_pos.le hp2.le]⟩

/-- Any finite partial product $\prod_{p \in s} (1 - p^{-2})^{-1}$ is bounded above by
the full Euler product $\pi^2 / 6$, since the partial products are monotonically
increasing toward the full product. -/
lemma partialInvProduct_le (s : Finset Nat.Primes) :
    ∏ p ∈ s, (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 :=
  (show Monotone (fun s : Finset Nat.Primes =>
      ∏ p ∈ s, (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹) from by
    intro s t hst; exact Finset.prod_le_prod_of_subset_of_one_le hst
      (fun p _ => le_of_lt (lt_of_lt_of_le zero_lt_one (eulerFactor_ge_one p)))
      (fun p _ _ => eulerFactor_ge_one p)
  ).ge_of_tendsto eulerProduct_zeta2 s

end EulerProductInfra

namespace GroupExponentBound

set_option maxHeartbeats 400000

open scoped Classical in
open Finset in
/-- The number of "good" pairs $(g_1, g_2) \in G \times G$ such that
$\mathrm{lcm}(\mathrm{ord}(g_1), \mathrm{ord}(g_2))$ equals the exponent of $G$. This
counts pairs that together generate a cyclic subgroup of order equal to the exponent. -/
noncomputable def numGoodPairs (G : Type*) [CommGroup G] [Fintype G] : ℕ :=
  (univ : Finset (G × G)).filter
    (fun p => Nat.lcm (orderOf p.1) (orderOf p.2) = Monoid.exponent G) |>.card

/-- The probability that two random elements of $G$ have orders whose LCM equals the
exponent of $G$: $|\text{good pairs}| / |G|^2$. -/
noncomputable def probLcmEqExponent (G : Type*) [CommGroup G] [Fintype G] : ℝ :=
  (numGoodPairs G : ℝ) / (Fintype.card G : ℝ) ^ 2

/-- For any group homomorphism $\varphi : G \to H$ and any two elements $\alpha, \beta \in G$,
$\mathrm{lcm}(\mathrm{ord}(\varphi \alpha), \mathrm{ord}(\varphi \beta))$ divides
$\mathrm{lcm}(\mathrm{ord}(\alpha), \mathrm{ord}(\beta))$, since each individual order
of an image divides the corresponding source order. -/
lemma lcm_orderOf_map_dvd {G H : Type*} [Group G] [Group H] (φ : G →* H) (α β : G) :
    Nat.lcm (orderOf (φ α)) (orderOf (φ β)) ∣ Nat.lcm (orderOf α) (orderOf β) :=
  Nat.lcm_dvd
    (dvd_trans (orderOf_map_dvd φ α) (Nat.dvd_lcm_left _ _))
    (dvd_trans (orderOf_map_dvd φ β) (Nat.dvd_lcm_right _ _))




/-- For any $n \geq 2$, the finite truncation $\prod_{p \mid n} (1 - p^{-2})$ strictly
exceeds $6/\pi^2 = 1/\zeta(2)$. This uses the existence of some prime $q$ not dividing
$n$ to produce a strict inequality when comparing the truncation to the full Euler product. -/
theorem finite_euler_product_gt (n : ℕ) (hn : 2 ≤ n) :
    6 / Real.pi ^ 2 < ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  classical
  have hpf : ∀ p ∈ n.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := by omega

  let f : ℕ → Nat.Primes := fun p =>
    if h : Nat.Prime p then ⟨p, h⟩ else ⟨2, by decide⟩
  have transfer : ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      ∏ p ∈ s, (1 - 1 / (p : ℝ) ^ 2)⁻¹ =
      ∏ p ∈ s.image f, (1 - 1 / ((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro s hs
    apply Finset.prod_nbij f
    · intro a ha; exact Finset.mem_image_of_mem f ha
    · intro a₁ ha₁ a₂ ha₂ h
      simp only [f, dif_pos (hs a₁ ha₁), dif_pos (hs a₂ ha₂)] at h
      exact Subtype.mk.inj h
    · rw [Set.SurjOn, Finset.coe_image]
    · intro a ha; simp only [f, dif_pos (hs a ha)]

  obtain ⟨q, hq, hq_ndvd⟩ : ∃ q, Nat.Prime q ∧ ¬ q ∣ n := by
    by_contra h; push_neg at h
    exact (Set.Finite.subset n.primeFactors.finite_toSet
      (fun p (hp : Nat.Prime p) => Nat.mem_primeFactors.mpr ⟨hp, h p hp, hn0⟩)).not_infinite
      Nat.infinite_setOf_prime
  have hq_notin : q ∉ n.primeFactors := by rw [Nat.mem_primeFactors]; tauto

  have hfq : 1 < (1 - 1 / (q : ℝ) ^ 2)⁻¹ := by
    rw [one_lt_inv_iff₀]
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
    have hq2pos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    exact ⟨by rw [sub_pos, div_lt_one hq2pos]; nlinarith,
           by linarith [div_pos one_pos hq2pos]⟩

  have hprod_pos : 0 < ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
    apply Finset.prod_pos
    intro p hp; exact lt_of_lt_of_le zero_lt_one (eulerFactor_ge_one ⟨p, hpf p hp⟩)

  have hall : ∀ p ∈ n.primeFactors ∪ {q}, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hpf p h
    · exact Finset.mem_singleton.mp h ▸ hq

  have hinv_lt : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ < Real.pi ^ 2 / 6 :=
    calc ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹
        < (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹) * (1 - 1 / (q : ℝ) ^ 2)⁻¹ :=
          lt_mul_of_one_lt_right hprod_pos hfq
      _ = ∏ p ∈ n.primeFactors ∪ {q}, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
          rw [Finset.prod_union (Finset.disjoint_singleton_right.mpr hq_notin),
              Finset.prod_singleton]
      _ ≤ Real.pi ^ 2 / 6 := by rw [transfer _ hall]; exact partialInvProduct_le _

  have hpf_pos : 0 < ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    apply Finset.prod_pos; intro p hp
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hpf p hp).two_le
    have : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    rw [sub_pos, div_lt_one this]; nlinarith
  rw [Finset.prod_inv_distrib] at hinv_lt
  rw [inv_lt_comm₀ hpf_pos (by positivity)] at hinv_lt
  linarith [show (Real.pi ^ 2 / 6)⁻¹ = 6 / Real.pi ^ 2 from inv_div _ _]

/-- Any nontrivial group has exponent at least $2$ (since a nontrivial element has
order $\geq 2$). -/
lemma exponent_ge_two_of_nontrivial (G : Type*) [CommGroup G] [Fintype G]
    (hG : 1 < Fintype.card G) : 2 ≤ Monoid.exponent G := by
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp hG
  exact Monoid.one_lt_exponent


/-- A trivial real-analytic fact used to handle the trivial-group edge case in
Theorem 7.6: $6/\pi^2 < 1$. -/
lemma six_div_pi_sq_lt_one : 6 / Real.pi ^ 2 < 1 := by
  rw [div_lt_one (by positivity : (0 : ℝ) < Real.pi ^ 2)]
  nlinarith [Real.pi_gt_three]


end GroupExponentBound

namespace BSGSOrder

variable {G : Type*} [AddGroup G] [DecidableEq G]

/-- If $q$ divides $a$ and $a$ divides $b$, then $a/q$ divides $b/q$. -/
theorem nat_div_dvd_div {q a b : ℕ} (hqa : q ∣ a) (hab : a ∣ b) : a / q ∣ b / q := by
  obtain ⟨c, rfl⟩ := hqa
  obtain ⟨d, rfl⟩ := hab
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · rw [Nat.mul_div_cancel_left _ hq, mul_assoc, Nat.mul_div_cancel_left _ hq]
    exact dvd_mul_right c d

/-- Iteratively divide $m$ by $p$ as long as the smaller multiple $m/p$ still
annihilates the point $P$. This is the key subroutine in Algorithm 7.4 (order
computation): given any annihilator $m$, it strips the prime $p$ to obtain a smaller
annihilator. -/
noncomputable def stripPrimeFactor (P : G) (p : ℕ) (hp : 1 < p) : ℕ → ℕ
  | m =>
    if hcond : 0 < m ∧ p ∣ m ∧ (m / p) • P = 0 then
      have : m / p < m := Nat.div_lt_self hcond.1 hp
      stripPrimeFactor P p hp (m / p)
    else m
termination_by m => m

/-- Algorithm 7.4: compute the order of a point $P$ in an additive group given a known
multiple $m$ and a list of primes containing all prime factors of the order. Strips each
prime in turn via `stripPrimeFactor`. -/
noncomputable def computeOrder (P : G) : List ℕ → ℕ → ℕ
  | [], m => m
  | p :: ps, m =>
    if hp : 1 < p then computeOrder P ps (stripPrimeFactor P p hp m)
    else computeOrder P ps m

/-- Soundness of `stripPrimeFactor`: the stripped value remains an annihilator of $P$. -/
theorem stripPrimeFactor_nsmul (P : G) (p : ℕ) (hp : 1 < p) (m : ℕ)
    (hm : m • P = 0) : (stripPrimeFactor P p hp m) • P = 0 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [stripPrimeFactor]
    split_ifs with h
    · exact ih _ (Nat.div_lt_self h.1 hp) h.2.2
    · exact hm

/-- The result of `stripPrimeFactor` divides the original $m$, since each iterative
step replaces $m$ by a divisor $m/p$. -/
theorem stripPrimeFactor_dvd (P : G) (p : ℕ) (hp : 1 < p) (m : ℕ) :
    stripPrimeFactor P p hp m ∣ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [stripPrimeFactor]
    split_ifs with h
    · exact dvd_trans (ih _ (Nat.div_lt_self h.1 hp)) (Nat.div_dvd_of_dvd h.2.1)
    · exact dvd_refl m

/-- After stripping, the result is "prime-stripped": if $p$ still divides
$\mathrm{strip}(m)$, then $\mathrm{strip}(m)/p$ no longer annihilates $P$ (otherwise we
would have continued stripping). -/
theorem stripPrimeFactor_prime_stripped (P : G) (p : ℕ) (hp : 1 < p) (m : ℕ)
    (hm_pos : 0 < m) (hm_ann : m • P = 0) :
    p ∣ stripPrimeFactor P p hp m → (stripPrimeFactor P p hp m / p) • P ≠ 0 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    rw [stripPrimeFactor]
    split_ifs with h
    · exact ih _ (Nat.div_lt_self h.1 hp)
        (Nat.div_pos (Nat.le_of_dvd hm_pos h.2.1) (by omega)) h.2.2
    · push Not at h
      exact fun hd => h hm_pos hd

/-- Soundness of `computeOrder`: the output still annihilates $P$. -/
theorem computeOrder_nsmul (P : G) (ps : List ℕ) (m : ℕ)
    (hm : m • P = 0) : (computeOrder P ps m) • P = 0 := by
  induction ps generalizing m with
  | nil => exact hm
  | cons p ps ih =>
    simp only [computeOrder]
    split_ifs with hp
    · exact ih _ (stripPrimeFactor_nsmul P p hp m hm)
    · exact ih _ hm

/-- The result of `computeOrder` always divides the input multiple $m$. -/
theorem computeOrder_dvd (P : G) (ps : List ℕ) (m : ℕ) :
    computeOrder P ps m ∣ m := by
  induction ps generalizing m with
  | nil => exact dvd_refl m
  | cons p ps ih =>
    unfold computeOrder
    split_ifs with hp
    · exact dvd_trans (ih _) (stripPrimeFactor_dvd P p hp m)
    · exact ih _

/-- Correctness lemma for `computeOrder`: if a prime $q$ divides the output, then
$\mathrm{output}/q$ does not annihilate $P$ (i.e. the output is the true order whenever
the prime list is complete). This is the inductive auxiliary used to prove that
`computeOrder` returns exactly $\mathrm{ord}(P)$. -/
theorem computeOrder_correct_aux (P : G) (ps : List ℕ)
    (hps : ∀ p ∈ ps, Nat.Prime p) (m : ℕ) (hm_pos : 0 < m) (hm_ann : m • P = 0)
    (q : ℕ) (hq_prime : Nat.Prime q) (hq_dvd : q ∣ computeOrder P ps m)
    (hq_src : q ∈ ps ∨ (m / q) • P ≠ 0) :
    (computeOrder P ps m / q) • P ≠ 0 := by
  induction ps generalizing m with
  | nil =>
    rcases hq_src with h | h
    · simp at h
    · exact h
  | cons p ps ih =>
    have hps_tail : ∀ r ∈ ps, Nat.Prime r := fun r hr => hps r (List.mem_cons_of_mem _ hr)
    simp only [computeOrder] at hq_dvd ⊢
    by_cases hp : 1 < p
    · simp only [hp, dite_true] at hq_dvd ⊢
      have hm'_ann := stripPrimeFactor_nsmul P p hp m hm_ann
      have hm'_dvd := stripPrimeFactor_dvd P p hp m
      have hm'_pos : 0 < stripPrimeFactor P p hp m := Nat.pos_of_ne_zero
        (fun h => by rw [h] at hm'_dvd; exact absurd (Nat.eq_zero_of_zero_dvd hm'_dvd) (by omega))
      have hsrc : q ∈ ps ∨ (stripPrimeFactor P p hp m / q) • P ≠ 0 := by
        rcases hq_src with hmem | hcond
        · rcases List.mem_cons.mp hmem with heq | htail
          · right; subst heq
            exact stripPrimeFactor_prime_stripped P q hp m hm_pos hm_ann
              (dvd_trans hq_dvd (computeOrder_dvd P ps _))
          · left; exact htail
        · right; intro h_ann; apply hcond
          exact addOrderOf_dvd_iff_nsmul_eq_zero.mp
            (dvd_trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h_ann)
              (nat_div_dvd_div (dvd_trans hq_dvd (computeOrder_dvd P ps _)) hm'_dvd))
      exact ih hps_tail _ hm'_pos hm'_ann hq_dvd hsrc
    · simp only [hp, dite_false] at hq_dvd ⊢
      have hsrc : q ∈ ps ∨ (m / q) • P ≠ 0 := by
        rcases hq_src with hmem | hcond
        · rcases List.mem_cons.mp hmem with heq | htail
          · subst heq; exact absurd hq_prime.one_lt hp
          · left; exact htail
        · right; exact hcond
      exact ih hps_tail m hm_pos hm_ann hq_dvd hsrc

end BSGSOrder

namespace QuadraticTwist

universe u

variable {F : Type u} [Field F]

/-- Two Weierstrass curves $E'$ and $E$ over $F$ are *twists* of each other if there is
a field extension $L/F$ over which they become isomorphic via a Weierstrass variable
change. -/
def IsTwistOf (E' E : WeierstrassCurve.Affine F) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra F L)
    (C : @WeierstrassCurve.VariableChange L _),
    C • (E.map (algebraMap F L)) = E'.map (algebraMap F L)

/-- The quadratic twist of a short Weierstrass curve $W : y^2 = x^3 + a_4 x + a_6$ by
$s \in F$: the curve $y^2 = x^3 + (s^2 a_4) x + (s^3 a_6)$. -/
noncomputable def quadraticTwistCurve (W : WeierstrassCurve.Affine F) (s : F) :
    WeierstrassCurve.Affine F :=
  ⟨0, 0, 0, s ^ 2 * W.a₄, s ^ 3 * W.a₆⟩

/-- The coefficient $a_1$ of a quadratic twist is $0$. -/
@[simp]
lemma quadraticTwistCurve_a₁ (W : WeierstrassCurve.Affine F) (s : F) :
    (quadraticTwistCurve W s).a₁ = 0 := rfl

/-- The coefficient $a_2$ of a quadratic twist is $0$. -/
@[simp]
lemma quadraticTwistCurve_a₂ (W : WeierstrassCurve.Affine F) (s : F) :
    (quadraticTwistCurve W s).a₂ = 0 := rfl

/-- The coefficient $a_3$ of a quadratic twist is $0$. -/
@[simp]
lemma quadraticTwistCurve_a₃ (W : WeierstrassCurve.Affine F) (s : F) :
    (quadraticTwistCurve W s).a₃ = 0 := rfl

/-- The coefficient $a_4$ of a quadratic twist by $s$ is $s^2 \cdot W.a_4$. -/
@[simp]
lemma quadraticTwistCurve_a₄ (W : WeierstrassCurve.Affine F) (s : F) :
    (quadraticTwistCurve W s).a₄ = s ^ 2 * W.a₄ := rfl

/-- The coefficient $a_6$ of a quadratic twist by $s$ is $s^3 \cdot W.a_6$. -/
@[simp]
lemma quadraticTwistCurve_a₆ (W : WeierstrassCurve.Affine F) (s : F) :
    (quadraticTwistCurve W s).a₆ = s ^ 3 * W.a₆ := rfl

/-- The number of points on the quadratic twist of $W$ over $\mathbb{F}_q$, defined via
the relation $\#E + \#E^{\mathrm{twist}} = 2q + 2$. -/
noncomputable def twistNumPoints {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : ℕ :=
  2 * Fintype.card F + 2 - Hasse.numPoints W

/-- The classical relation $\#E(\mathbb{F}_q) + \#E^{\mathrm{twist}}(\mathbb{F}_q) = 2q + 2$
between an elliptic curve and its quadratic twist. -/
theorem numPoints_add_twist {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (hW : Hasse.numPoints W ≤ 2 * Fintype.card F + 2) :
    Hasse.numPoints W + twistNumPoints W = 2 * Fintype.card F + 2 := by
  unfold twistNumPoints
  omega

end QuadraticTwist

namespace Mestre

set_option maxHeartbeats 800000

/-- The predicate "$N$ has a unique positive multiple in the closed interval
$[\mathit{lo}, \mathit{hi}]$": there is exactly one positive integer $k$ such that
$\mathit{lo} \leq k N \leq \mathit{hi}$. Mestre's theorem uses this to pin down the
number of points from a known annihilator. -/
def HasUniqueMultipleIn (N : ℕ) (lo hi : ℝ) : Prop :=
  ∃! k : ℕ, 0 < k ∧ lo ≤ (k * N : ℝ) ∧ (k * N : ℝ) ≤ hi

/-- Core algebraic inequality in Mestre's proof: given a bound $m^2 n^2 \leq 64 p$ and
suitable interval containment hypotheses, derive $16384 p^3 > (\sqrt{p} - 1)^8$. The
contradiction with `inequality_fails_large_p` produces the desired uniqueness for
large $p$. -/
lemma mestre_inequality_of_bounds
    (p m n M N : ℕ)
    (hp : 0 < p) (hm : 0 < m) (hn : 0 < n) (hM : 0 < M) (hN : 0 < N)
    (hbound : (m : ℤ) ^ 2 * (n : ℤ) ^ 2 ≤ 64 * (p : ℤ))
    (hMN_lt : (M : ℝ) * N < 16 * (p : ℝ))
    (hmnMN_ge : ((m : ℝ) * n) * (M * N) ≥ ((Real.sqrt p) - 1) ^ 4) :
    16384 * (p : ℝ) ^ 3 > (Real.sqrt p - 1) ^ 8 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hmn_pos : (0 : ℝ) < (m : ℝ) * n := by positivity
  have hMN_pos : (0 : ℝ) < (M : ℝ) * N := by positivity


  have hmn_lower : (m : ℝ) * n > (Real.sqrt p - 1) ^ 4 / (16 * p) := by
    rw [gt_iff_lt, div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * p)]
    calc (Real.sqrt ↑p - 1) ^ 4
        ≤ (↑m * ↑n) * (↑M * ↑N) := hmnMN_ge
      _ < (↑m * ↑n) * (16 * ↑p) := by nlinarith

  have hbound_real : (m : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ 64 * (p : ℝ) := by
    exact_mod_cast hbound


  have hmn_sq : (m : ℝ) ^ 2 * n ^ 2 > (Real.sqrt p - 1) ^ 8 / (256 * p ^ 2) := by
    have h1 : ((m : ℝ) * n) ^ 2 = (m : ℝ) ^ 2 * n ^ 2 := by ring
    have h2 : ((Real.sqrt p - 1) ^ 4 / (16 * p)) ^ 2 =
        (Real.sqrt p - 1) ^ 8 / (256 * p ^ 2) := by ring
    rw [← h1, ← h2]
    have hq : 0 ≤ (Real.sqrt p - 1) ^ 4 / (16 * p) := by positivity
    exact sq_lt_sq' (by nlinarith) hmn_lower


  calc (Real.sqrt ↑p - 1) ^ 8
      < (m : ℝ) ^ 2 * n ^ 2 * (256 * (p : ℝ) ^ 2) := by
        rwa [gt_iff_lt, div_lt_iff₀ (by positivity : (0 : ℝ) < 256 * (p : ℝ) ^ 2)] at hmn_sq
    _ ≤ 64 * (p : ℝ) * (256 * (p : ℝ) ^ 2) := by nlinarith
    _ = 16384 * (p : ℝ) ^ 3 := by ring

/-- For $s \geq 132$, the elementary polynomial inequality $(s - 1)^4 \geq 128 s^3$
holds. Used to verify that $(\sqrt{p} - 1)^8 \geq 16384 p^3$ when $p \geq 132^2 = 17424$. -/
lemma poly_bound_132 (s : ℝ) (hs : 132 ≤ s) : (s - 1) ^ 4 ≥ 128 * s ^ 3 := by
  nlinarith [mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ s by linarith) 3)
               (show (0 : ℝ) ≤ s - 132 by linarith),
             show (s - 1) ^ 4 - 128 * s ^ 3 =
               s ^ 3 * (s - 132) + (6 * s ^ 2 - 4 * s + 1) from by ring,
             sq_nonneg (s - 1)]

/-- For $p \geq 17424 = 132^2$, the inequality $(\sqrt{p} - 1)^8 \geq 16384 p^3$ holds,
established by squaring `poly_bound_132` and rewriting $(\sqrt p)^2 = p$. -/
lemma inequality_large_case (p : ℕ) (hp : 17424 ≤ p) :
    (Real.sqrt p - 1) ^ 8 ≥ 16384 * (p : ℝ) ^ 3 := by
  have hs : (132 : ℝ) ≤ Real.sqrt p := by
    rw [show (132 : ℝ) = Real.sqrt (17424 : ℝ) from by
      rw [show (17424 : ℝ) = 132 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 132)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp)
  have hsq : Real.sqrt (↑p) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have h4 := poly_bound_132 (Real.sqrt p) hs
  calc (Real.sqrt p - 1) ^ 8
      = ((Real.sqrt p - 1) ^ 4) ^ 2 := by ring
    _ ≥ (128 * (Real.sqrt p) ^ 3) ^ 2 := by
        apply sq_le_sq'
        · nlinarith [sq_nonneg (Real.sqrt p - 1)]
        · exact h4
    _ = 16384 * ((Real.sqrt p) ^ 2) ^ 3 := by ring
    _ = 16384 * (p : ℝ) ^ 3 := by rw [hsq]

/-- An integer-level inequality for $p$ in the narrow range $17413 \leq p \leq 17423$:
$(p - 263)^4 \geq 16384 p^3$. Verified by `nlinarith` from squared lower bounds. -/
lemma int_bound_small_range (p : ℕ) (h1 : 17413 ≤ p) (h2 : p ≤ 17423) :
    (p - 263 : ℤ) ^ 4 ≥ 16384 * (p : ℤ) ^ 3 := by
  have hp1 : (17413 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h1
  have hp2 : (p : ℤ) ≤ 17423 := by exact_mod_cast h2
  nlinarith [sq_nonneg ((p : ℤ) - 17413), sq_nonneg ((p : ℤ) - 17423),
             sq_nonneg ((p : ℤ) - 17418)]

/-- The boundary range $17413 \leq p < 17424$ where `inequality_large_case` does not yet
apply: handled by the integer arithmetic lemma `int_bound_small_range` lifted to the
reals via $(\sqrt p - 1)^2 > p - 263$. -/
lemma inequality_small_case (p : ℕ) (h1 : 17413 ≤ p) (h2 : p < 17424) :
    (Real.sqrt p - 1) ^ 8 ≥ 16384 * (p : ℝ) ^ 3 := by
  have hint := int_bound_small_range p h1 (by omega)
  have hint_real : ((p : ℝ) - 263) ^ 4 ≥ 16384 * (p : ℝ) ^ 3 := by
    have := Int.cast_le (R := ℝ).mpr hint; push_cast at this; linarith
  have hsq : Real.sqrt (↑p) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have h132 : Real.sqrt (↑p) < 132 := by
    rw [show (132 : ℝ) = Real.sqrt (17424 : ℝ) from by
      rw [show (17424 : ℝ) = 132 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 132)]]
    exact Real.sqrt_lt_sqrt (Nat.cast_nonneg p) (by exact_mod_cast h2)
  have hgt : (p : ℝ) - 263 < (Real.sqrt p - 1) ^ 2 := by
    rw [sub_sq, hsq, mul_one, one_pow]; linarith
  have h_nn : (0 : ℝ) ≤ (p : ℝ) - 263 :=
    sub_nonneg.mpr (by exact_mod_cast show 263 ≤ p by omega)
  calc (Real.sqrt ↑p - 1) ^ 8
      = ((Real.sqrt ↑p - 1) ^ 2) ^ 4 := by ring
    _ ≥ ((p : ℝ) - 263) ^ 4 := pow_le_pow_left₀ h_nn (le_of_lt hgt) 4
    _ ≥ 16384 * (p : ℝ) ^ 3 := hint_real

/-- For all $p \geq 17413$, $(\sqrt{p} - 1)^8 \geq 16384 p^3$, combining the small
range $17413 \leq p < 17424$ and the large range $p \geq 17424$. This rules out the
"non-unique multiple" case for sufficiently large $p$ in Mestre's argument. -/
theorem inequality_fails_large_p (p : ℕ) (hp : 17413 ≤ p) :
    (Real.sqrt p - 1) ^ 8 ≥ 16384 * (p : ℝ) ^ 3 := by
  by_cases h : 17424 ≤ p
  · exact inequality_large_case p h
  · exact inequality_small_case p hp (by omega)

/-- If $N$ has at least one positive multiple in the Hasse interval
$[(\sqrt p - 1)^2, (\sqrt p + 1)^2]$ but the multiple is not unique, then
$N < 4 \sqrt p$ (the width of the interval). The strict inequality uses the
irrationality of $\sqrt{p}$ for primes $p$. -/
theorem not_unique_implies_lt_width (N : ℕ) (p : ℕ)
    (hN_pos : 0 < N) (hp_prime : Nat.Prime p) (hp_gt4 : 4 < p)
    (h_has_multiple : ∃ k : ℕ, 0 < k ∧
      (Real.sqrt p - 1) ^ 2 ≤ (k * N : ℝ) ∧ (k * N : ℝ) ≤ (Real.sqrt p + 1) ^ 2)
    (h_not_unique : ¬ HasUniqueMultipleIn N ((Real.sqrt p - 1) ^ 2) ((Real.sqrt p + 1) ^ 2)) :
    (N : ℝ) < 4 * Real.sqrt p := by
  unfold HasUniqueMultipleIn at h_not_unique
  obtain ⟨k₁, hk₁_pos, hk₁_lo, hk₁_hi⟩ := h_has_multiple

  have h_not_all_eq : ¬ ∀ y : ℕ,
      (0 < y ∧ (Real.sqrt ↑p - 1) ^ 2 ≤ ↑y * ↑N ∧ ↑y * ↑N ≤ (Real.sqrt ↑p + 1) ^ 2) → y = k₁ := by
    intro huniq
    exact h_not_unique ⟨k₁, ⟨hk₁_pos, hk₁_lo, hk₁_hi⟩, huniq⟩
  simp only [not_forall] at h_not_all_eq
  obtain ⟨k₂, ⟨hk₂_pos, hk₂_lo, hk₂_hi⟩, hne⟩ := h_not_all_eq

  suffices hN_le : (↑N : ℝ) ≤ 4 * Real.sqrt ↑p by
    apply lt_of_le_of_ne hN_le
    intro heq
    have hirr : Irrational (4 * Real.sqrt (↑p : ℝ)) :=
      hp_prime.irrational_sqrt.natCast_mul (show (4 : ℕ) ≠ 0 by norm_num)
    rw [← heq] at hirr
    exact hirr ⟨↑N, by push_cast; ring⟩


  obtain hlt | rfl | hlt := lt_trichotomy k₁ k₂
  ·
    have h_gap : ↑k₁ * (↑N : ℝ) + ↑N ≤ ↑k₂ * ↑N := by
      have : (↑(k₁ + 1) : ℝ) ≤ (↑k₂ : ℝ) := by exact_mod_cast (hlt : k₁ + 1 ≤ k₂)
      have := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg N)
      push_cast at this ⊢; linarith
    linarith [show (Real.sqrt ↑p + 1) ^ 2 - (Real.sqrt ↑p - 1) ^ 2 = 4 * Real.sqrt ↑p from by ring]
  · exact absurd rfl hne
  ·
    have h_gap : ↑k₂ * (↑N : ℝ) + ↑N ≤ ↑k₁ * ↑N := by
      have : (↑(k₂ + 1) : ℝ) ≤ (↑k₁ : ℝ) := by exact_mod_cast (hlt : k₂ + 1 ≤ k₁)
      have := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg N)
      push_cast at this ⊢; linarith
    linarith [show (Real.sqrt ↑p + 1) ^ 2 - (Real.sqrt ↑p - 1) ^ 2 = 4 * Real.sqrt ↑p from by ring]






end Mestre
