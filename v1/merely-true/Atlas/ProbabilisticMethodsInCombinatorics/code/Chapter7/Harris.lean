/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.UpperLower.Basic

open Finset Fintype MeasureTheory Set

noncomputable section

namespace Harris

/-- Product weight for the Bernoulli product measure on $\{0,1\}^n$: assigns to a
configuration $\omega : \text{Fin } n \to \text{Bool}$ the weight
$\prod_i p_i^{\omega_i} (1 - p_i)^{1 - \omega_i}$. -/
def prodWeight (n : ℕ) (p : Fin n → ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, bif ω i then p i else 1 - p i

/-- Probability of an event $S \subseteq \{0,1\}^n$ under the Bernoulli product
measure with parameters $p$, defined as $\sum_\omega \text{prodWeight}(\omega) \cdot \mathbf{1}_S(\omega)$. -/
def P (n : ℕ) (p : Fin n → ℝ) (S : Set (Fin n → Bool)) : ℝ :=
  ∑ ω : Fin n → Bool, prodWeight n p ω * S.indicator (fun _ => (1 : ℝ)) ω

/-- The total mass of $\text{prodWeight}$ is one: $\sum_\omega \text{prodWeight}(\omega) = 1$. -/
lemma prodWeight_sum_eq_one (n : ℕ) (p : Fin n → ℝ) :
    ∑ ω : Fin n → Bool, prodWeight n p ω = 1 := by
  unfold prodWeight
  trans ∏ i : Fin n, ∑ b : Bool, (bif b then p i else 1 - p i)
  · rw [← Finset.sum_prod_piFinset]; congr 1
  · exact Finset.prod_eq_one (fun i _ => by rw [Fintype.sum_bool]; simp)

/-- When each $p_i \in [0,1]$ the product weight is nonnegative. -/
lemma prodWeight_nonneg {n : ℕ} {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Set.Icc 0 1)
    (ω : Fin n → Bool) : 0 ≤ prodWeight n p ω := by
  unfold prodWeight
  apply Finset.prod_nonneg
  intro i _
  have h0 : 0 ≤ p i := (hp i).1
  have h1 : p i ≤ 1 := (hp i).2
  cases ω i <;> simp <;> linarith

/-- Log-modularity (FKG condition) of the Bernoulli product weight:
$\mu(a)\mu(b) = \mu(a \wedge b)\mu(a \vee b)$. -/
lemma prodWeight_log_modular (n : ℕ) (p : Fin n → ℝ) (a b : Fin n → Bool) :
    prodWeight n p a * prodWeight n p b =
    prodWeight n p (a ⊓ b) * prodWeight n p (a ⊔ b) := by
  unfold prodWeight
  simp only [← Finset.prod_mul_distrib]
  congr 1; ext i; simp only [Pi.inf_apply, Pi.sup_apply]
  cases a i <;> cases b i <;> simp
  ring

/-- The indicator function of an upper set (increasing event) is monotone. -/
lemma indicator_upperSet_mono {n : ℕ} {A : Set (Fin n → Bool)} (hA : IsUpperSet A) :
    Monotone (A.indicator (fun _ => (1 : ℝ))) := by
  intro x y hxy
  simp only [Set.indicator]
  split_ifs with hxA hyA
  · exact le_refl _
  · exact absurd (hA hxy hxA) hyA
  · exact zero_le_one
  · exact le_refl _

/-- The indicator function of any set is pointwise nonnegative. -/
lemma indicator_nonneg_fun (n : ℕ) (A : Set (Fin n → Bool)) :
    (0 : (Fin n → Bool) → ℝ) ≤ A.indicator (fun _ => (1 : ℝ)) := by
  intro x; simp only [Pi.zero_apply, Set.indicator]; split_ifs <;> linarith

/-- The indicator of an intersection equals the product of indicators:
$\mathbf{1}_{A \cap B}(\omega) = \mathbf{1}_A(\omega) \cdot \mathbf{1}_B(\omega)$. -/
lemma indicator_inter_eq_mul {n : ℕ} (A B : Set (Fin n → Bool)) :
    (A ∩ B).indicator (fun _ => (1 : ℝ)) =
    fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
  funext ω
  simp only [Set.indicator, Set.mem_inter_iff]
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

/-- Theorem 7.1.1 (Harris 1960): For independent Boolean random variables with
parameters $p_i \in [0,1]$ and increasing events $A, B \subseteq \{0,1\}^n$,
$\mathbb{P}(A \cap B) \geq \mathbb{P}(A)\mathbb{P}(B)$. -/
theorem harris_inequality {n : ℕ} {p : Fin n → ℝ} (hp : ∀ i, p i ∈ Set.Icc 0 1)
    {A B : Set (Fin n → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    P n p (A ∩ B) ≥ P n p A * P n p B := by
  unfold P
  rw [show (∑ ω, prodWeight n p ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω) =
    ∑ ω, prodWeight n p ω *
      (A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω) from by
    congr 1; ext ω; rw [indicator_inter_eq_mul]]
  have hfkg := fkg (A.indicator (fun _ => (1 : ℝ))) (B.indicator (fun _ => (1 : ℝ)))
    (prodWeight n p)
    (fun ω => prodWeight_nonneg hp ω)
    (indicator_nonneg_fun n A)
    (indicator_nonneg_fun n B)
    (indicator_upperSet_mono hA)
    (indicator_upperSet_mono hB)
    (fun a b => le_of_eq (prodWeight_log_modular n p a b))
  rw [prodWeight_sum_eq_one, one_mul] at hfkg
  exact hfkg

/-- Corollary 7.1.6 (multiple-event Harris): For finitely many increasing events
$A_1, \dots, A_k$, $\mathbb{P}\!\left(\bigcap_i A_i\right) \geq \prod_i \mathbb{P}(A_i)$. -/
theorem harris_inequality_multiple_increasing {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ i, p i ∈ Set.Icc 0 1)
    {k : ℕ} {A : Fin k → Set (Fin n → Bool)} (hA : ∀ i, IsUpperSet (A i)) :
    P n p (⋂ i, A i) ≥ ∏ i : Fin k, P n p (A i) := by
  induction k with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    show P n p (⋂ i : Fin 0, A i) ≥ 1
    simp only [iInter_of_empty]
    unfold P
    simp only [Set.indicator_univ, mul_one]

    linarith [prodWeight_sum_eq_one n p]
  | succ k ih =>

    have hAk : IsUpperSet (A (Fin.last k)) := hA (Fin.last k)

    have hInter : IsUpperSet (⋂ i : Fin k, A (Fin.castSucc i)) := by
      apply isUpperSet_iInter
      intro i; exact hA (Fin.castSucc i)

    have hH := harris_inequality hp hInter hAk

    have hsplit : (⋂ i : Fin (k + 1), A i) =
        (⋂ i : Fin k, A (Fin.castSucc i)) ∩ A (Fin.last k) := by
      ext x; simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨fun i => h (Fin.castSucc i), h (Fin.last k)⟩
      · intro ⟨h1, h2⟩ i
        exact Fin.lastCases h2 h1 i
    rw [hsplit]

    have hih := ih (A := fun i => A (Fin.castSucc i)) (fun i => hA (Fin.castSucc i))

    have hprod : ∏ i : Fin (k + 1), P n p (A i) =
        (∏ i : Fin k, P n p (A (Fin.castSucc i))) * P n p (A (Fin.last k)) := by
      rw [Fin.prod_univ_castSucc]
    rw [hprod]

    have hP_nonneg : ∀ S : Set (Fin n → Bool), 0 ≤ P n p S := by
      intro S; unfold P
      apply Finset.sum_nonneg
      intro ω _
      apply mul_nonneg (prodWeight_nonneg hp ω)
      simp only [Set.indicator]; split_ifs <;> linarith
    calc P n p ((⋂ i : Fin k, A (Fin.castSucc i)) ∩ A (Fin.last k))
        ≥ P n p (⋂ i : Fin k, A (Fin.castSucc i)) * P n p (A (Fin.last k)) := hH
      _ ≥ (∏ i : Fin k, P n p (A (Fin.castSucc i))) * P n p (A (Fin.last k)) := by
          apply mul_le_mul_of_nonneg_right (GE.ge.le hih) (hP_nonneg _)

set_option maxHeartbeats 400000

/-- General product weight on $\alpha^n$ for a linearly ordered finite type $\alpha$:
$\mu(\omega) = \prod_i p_i(\omega_i)$. -/
def generalProdWeight (n : ℕ) (α : Type*) [LinearOrder α] [Fintype α]
    (p : Fin n → α → ℝ) (ω : Fin n → α) : ℝ :=
  ∏ i : Fin n, p i (ω i)

/-- General expectation operator: $\mathbb{E}[f] = \sum_\omega \mu(\omega) f(\omega)$
under the product weight on $\alpha^n$. -/
def generalE (n : ℕ) (α : Type*) [LinearOrder α] [Fintype α]
    (p : Fin n → α → ℝ) (f : (Fin n → α) → ℝ) : ℝ :=
  ∑ ω : Fin n → α, generalProdWeight n α p ω * f ω

/-- If each marginal $p_i$ sums to one, then $\sum_\omega \text{generalProdWeight}(\omega) = 1$. -/
lemma generalProdWeight_sum_eq_one (n : ℕ) (α : Type*) [LinearOrder α] [Fintype α]
    (p : Fin n → α → ℝ) (hp : ∀ i, ∑ x : α, p i x = 1) :
    ∑ ω : Fin n → α, generalProdWeight n α p ω = 1 := by
  unfold generalProdWeight
  trans ∏ i : Fin n, ∑ x : α, p i x
  · rw [← Finset.sum_prod_piFinset]; congr 1
  · simp [hp]

/-- Nonnegativity of the general product weight when each marginal is nonnegative. -/
lemma generalProdWeight_nonneg {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α]
    {p : Fin n → α → ℝ} (hp : ∀ i x, 0 ≤ p i x)
    (ω : Fin n → α) : 0 ≤ generalProdWeight n α p ω := by
  unfold generalProdWeight
  exact Finset.prod_nonneg (fun i _ => hp i (ω i))

/-- Log-modularity of the general product weight on the lattice $\alpha^n$. -/
lemma generalProdWeight_log_modular (n : ℕ) (α : Type*) [LinearOrder α] [Fintype α]
    (p : Fin n → α → ℝ) (a b : Fin n → α) :
    generalProdWeight n α p a * generalProdWeight n α p b =
    generalProdWeight n α p (a ⊓ b) * generalProdWeight n α p (a ⊔ b) := by
  unfold generalProdWeight
  simp only [← Finset.prod_mul_distrib]
  congr 1; ext i
  simp only [Pi.inf_apply, Pi.sup_apply]
  rcases le_total (a i) (b i) with h | h
  · rw [inf_eq_left.mpr h, sup_eq_right.mpr h]
  · rw [inf_eq_right.mpr h, sup_eq_left.mpr h]; ring

/-- Theorem 7.1.5 (Harris, general form): For monotone increasing real-valued
functions $f, g$ on $\alpha^n$ under a product probability measure,
$\mathbb{E}[fg] \geq \mathbb{E}[f]\mathbb{E}[g]$. -/
theorem harris_inequality_general {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    {p : Fin n → α → ℝ} (hp_nonneg : ∀ i x, 0 ≤ p i x) (hp_sum : ∀ i, ∑ x : α, p i x = 1)
    {f g : (Fin n → α) → ℝ} (hf : Monotone f) (hg : Monotone g) :
    generalE n α p (fun ω => f ω * g ω) ≥ generalE n α p f * generalE n α p g := by
  haveI : OrderBot α := Fintype.toOrderBot α

  have key : ∀ (f g : (Fin n → α) → ℝ), Monotone f → Monotone g →
      (∀ ω, 0 ≤ f ω) → (∀ ω, 0 ≤ g ω) →
      generalE n α p (fun ω => f ω * g ω) ≥ generalE n α p f * generalE n α p g := by
    intro f g hfm hgm hfnn hgnn
    unfold generalE
    have hfkg := fkg f g (generalProdWeight n α p)
      (fun ω => generalProdWeight_nonneg hp_nonneg ω)
      (fun ω => hfnn ω)
      (fun ω => hgnn ω)
      hfm hgm
      (fun a b => le_of_eq (generalProdWeight_log_modular n α p a b))
    rw [generalProdWeight_sum_eq_one n α p hp_sum, one_mul] at hfkg
    exact hfkg


  set c := f ⊥
  set d := g ⊥
  have hfc : ∀ ω, c ≤ f ω := fun ω => hf bot_le
  have hgd : ∀ ω, d ≤ g ω := fun ω => hg bot_le
  have hf'mono : Monotone (fun ω => f ω - c) := fun a b h => sub_le_sub_right (hf h) c
  have hg'mono : Monotone (fun ω => g ω - d) := fun a b h => sub_le_sub_right (hg h) d
  have hf'nn : ∀ ω, 0 ≤ f ω - c := fun ω => sub_nonneg.mpr (hfc ω)
  have hg'nn : ∀ ω, 0 ≤ g ω - d := fun ω => sub_nonneg.mpr (hgd ω)
  have hkey := key _ _ hf'mono hg'mono hf'nn hg'nn

  have hEfc : generalE n α p (fun ω => f ω - c) = generalE n α p f - c := by
    unfold generalE; simp only [mul_sub]; rw [Finset.sum_sub_distrib]
    congr 1; simp only [← Finset.sum_mul]
    rw [generalProdWeight_sum_eq_one n α p hp_sum, one_mul]
  have hEgd : generalE n α p (fun ω => g ω - d) = generalE n α p g - d := by
    unfold generalE; simp only [mul_sub]; rw [Finset.sum_sub_distrib]
    congr 1; simp only [← Finset.sum_mul]
    rw [generalProdWeight_sum_eq_one n α p hp_sum, one_mul]
  have hEfg : generalE n α p (fun ω => (f ω - c) * (g ω - d)) =
      generalE n α p (fun ω => f ω * g ω) - c * generalE n α p g -
      d * generalE n α p f + c * d := by
    unfold generalE
    have : ∀ ω, generalProdWeight n α p ω * ((f ω - c) * (g ω - d)) =
        generalProdWeight n α p ω * (f ω * g ω) - c * (generalProdWeight n α p ω * g ω) -
        d * (generalProdWeight n α p ω * f ω) + c * d * generalProdWeight n α p ω := by
      intro ω; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [show ∑ x, c * (generalProdWeight n α p x * g x) =
      c * ∑ x, generalProdWeight n α p x * g x from by rw [Finset.mul_sum]]
    rw [show ∑ x, d * (generalProdWeight n α p x * f x) =
      d * ∑ x, generalProdWeight n α p x * f x from by rw [Finset.mul_sum]]
    rw [show ∑ x : Fin n → α, c * d * generalProdWeight n α p x =
      c * d * ∑ x : Fin n → α, generalProdWeight n α p x from by rw [Finset.mul_sum]]
    rw [generalProdWeight_sum_eq_one n α p hp_sum, mul_one]
  rw [hEfc, hEgd, hEfg] at hkey
  linarith

end Harris
