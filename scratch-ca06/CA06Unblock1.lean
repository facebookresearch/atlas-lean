import Mathlib.Logic.Function.DependsOn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

-- ===== begin atlas-src/MathlibExt/Probability/FiniteWeight.lean =====
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



/-!
# Marginals and conditional independence for weights on finite configuration spaces

Variables indexed by a finite type `V` take values in a finite type `α`, so a configuration is a
function `x : V → α`, and a weight is a function `p : (V → α) → ℝ`. A nonnegative weight of
positive total mass is an unnormalized probability distribution; the definitions below are its
marginals and conditional independence. Marginals scale linearly with `p` and `CondIndep` is
unchanged when `p` is multiplied by a nonzero constant, so `p` need not be normalized. The
algebraic results hold for arbitrary real weights.

* `marginal p U x`: the total weight of the configurations that agree with `x` on `U`, the
  (unnormalized) marginal of `p` on the variables in `U` at `x`. `marginal_nonneg`,
  `marginal_anti`: for nonnegative weights marginals are nonnegative and decrease as more
  variables are fixed. `marginal_marginal`: marginalizing `p` to `W` and then to `U ⊆ W` gives the
  `U`-marginal of `p` up to the number of values of the variables outside `W`, so
  `condIndep_marginal_iff`: conditional independence among variables in `W` can be read off the
  `W`-marginal.
* `CondIndep p A B S`: `p(x_A, x_B, x_S) p(x_S) = p(x_A, x_S) p(x_B, x_S)` for every `x`.
  `CondIndep.cond_eq_mul` divides it into the conditional-probability form wherever
  `p(x_S) ≠ 0`; for a nonnegative weight, where `p(x_S) = 0` every marginal fixing `S` vanishes
  (`marginal_anti`) and the equation holds trivially. `condIndep_of_sdiff`: only the variables
  of `A` and `B` outside `S` matter.
* `marginal_mul`: if `f` depends only on the variables in `P` and `g` only on those in `Q`, with
  every variable in `P` or `Q` and `P ∩ Q ⊆ U`, the `U`-marginal of `f * g` is a product of a
  marginal of `f` and a marginal of `g`.
* `condIndep_of_dependsOn` (**factorization criterion**): if `p = f * g` with `f` depending only
  on `P` and `g` only on `Q`, and every variable is in `P` or `Q`, then variables `A` outside `Q`
  and `B` outside `P` are conditionally independent given `P ∩ Q`.

Mathlib's `ProbabilityTheory.CondIndepFun` states conditional independence of random variables
on a measure space through conditional expectations (`condExpKernel`); this file states the
atomwise identity for finite configuration spaces directly, in the form used by graphical models
(`CSLibExt/MachineLearning/GraphicalModels/MarkovRandomField.lean`). The equivalence of the two
for nonnegative weights is not formalized here.
-/

section

namespace MetaMathlibExt.FiniteWeight

open Finset

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]

open Classical in
/-- The (unnormalized) marginal of the weight `p` on the variables in `U`, at the values of `x`:
the total weight of the configurations that agree with `x` on `U`. -/
noncomputable def marginal (p : (V → α) → ℝ) (U : Set V) (x : V → α) : ℝ :=
  ∑ y ∈ univ.filter (fun y : V → α => ∀ v ∈ U, y v = x v), p y

theorem marginal_nonneg {p : (V → α) → ℝ} (hp : ∀ x, 0 ≤ p x) (U : Set V) (x : V → α) :
    0 ≤ marginal p U x := by
  classical
  exact sum_nonneg fun y _ => hp y

/-- For a nonnegative weight, fixing more variables decreases the marginal. -/
theorem marginal_anti {p : (V → α) → ℝ} (hp : ∀ x, 0 ≤ p x) {U U' : Set V} (h : U ⊆ U')
    (x : V → α) : marginal p U' x ≤ marginal p U x := by
  classical
  refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun y _ _ => hp y
  simp only [mem_filter, mem_univ, true_and] at hy ⊢
  exact fun v hv => hy v (h hv)

/-- The variables in `A` and in `B` are **conditionally independent given** those in `S` under
the weight `p`: `p(x_A, x_B, x_S) p(x_S) = p(x_A, x_S) p(x_B, x_S)` for every configuration,
where `p(x_U)` is `marginal p U x`. -/
def CondIndep (p : (V → α) → ℝ) (A B S : Set V) : Prop :=
  ∀ x, marginal p (A ∪ B ∪ S) x * marginal p S x = marginal p (A ∪ S) x * marginal p (B ∪ S) x

/-- Conditional independence in ratio form: where `p(x_S) ≠ 0`,
`p(x_A, x_B, x_S) / p(x_S) = (p(x_A, x_S) / p(x_S)) (p(x_B, x_S) / p(x_S))`. For a nonnegative
weight of positive total mass these ratios are the conditional probabilities of the normalized
distribution, so this is `P(x_A, x_B | x_S) = P(x_A | x_S) P(x_B | x_S)`. -/
theorem CondIndep.cond_eq_mul {p : (V → α) → ℝ} {A B S : Set V} (h : CondIndep p A B S)
    {x : V → α} (hx : marginal p S x ≠ 0) :
    marginal p (A ∪ B ∪ S) x / marginal p S x =
      (marginal p (A ∪ S) x / marginal p S x) * (marginal p (B ∪ S) x / marginal p S x) := by
  rw [div_mul_div_comm, ← h x, mul_div_mul_right _ _ hx]

/-- **Marginals of a product**: if `f` depends only on the variables in `P` and `g` only on those
in `Q`, with `P ∪ Q` everything and `P ∩ Q ⊆ U`, then summing `f * g` over the variables outside
`U` sums `f` and `g` separately: the free variables of `f` are those of `P` outside `U`, and the
free variables of `g` those of `Q` outside `U`. -/
theorem marginal_mul {f g : (V → α) → ℝ} {P Q U : Set V} (hf : DependsOn f P) (hg : DependsOn g Q)
    (hPQ : ∀ v, v ∈ P ∨ v ∈ Q) (hU : P ∩ Q ⊆ U) (x : V → α) :
    marginal (f * g) U x = marginal f (U ∪ Pᶜ) x * marginal g (U ∪ Qᶜ) x := by
  classical
  simp only [marginal]
  rw [sum_mul_sum, ← sum_product']
  refine sum_nbij' (fun y => (fun v => if v ∈ P then y v else x v,
      fun v => if v ∈ Q then y v else x v)) (fun z v => if v ∈ P then z.1 v else z.2 v)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    simp only [mem_product, mem_filter, mem_univ, true_and, Set.mem_union, Set.mem_compl_iff]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · by_cases hvP : v ∈ P
      · simp only [hvP, ↓reduceIte]
        exact hy v (hv.resolve_right (not_not.mpr hvP))
      · simp only [hvP, ↓reduceIte]
    · by_cases hvQ : v ∈ Q
      · simp only [hvQ, ↓reduceIte]
        exact hy v (hv.resolve_right (not_not.mpr hvQ))
      · simp only [hvQ, ↓reduceIte]
  · intro z hz
    simp only [mem_product, mem_filter, mem_univ, true_and, Set.mem_union,
      Set.mem_compl_iff] at hz
    simp only [mem_filter, mem_univ, true_and]
    intro v hv
    by_cases hvP : v ∈ P
    · simp only [hvP, ↓reduceIte]
      exact hz.1 v (Or.inl hv)
    · simp only [hvP, ↓reduceIte]
      exact hz.2 v (Or.inl hv)
  · intro y _
    funext v
    by_cases hvP : v ∈ P
    · simp [hvP]
    · simp [hvP, (hPQ v).resolve_left hvP]
  · intro z hz
    simp only [mem_product, mem_filter, mem_univ, true_and, Set.mem_union,
      Set.mem_compl_iff] at hz
    refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
    · by_cases hvP : v ∈ P
      · simp [hvP]
      · simp only [hvP, ↓reduceIte]
        exact (hz.1 v (Or.inr hvP)).symm
    · by_cases hvQ : v ∈ Q
      · by_cases hvP : v ∈ P
        · simp only [hvQ, hvP, ↓reduceIte]
          rw [hz.1 v (Or.inl (hU ⟨hvP, hvQ⟩)), hz.2 v (Or.inl (hU ⟨hvP, hvQ⟩))]
        · simp [hvQ, hvP]
      · simp only [hvQ, ↓reduceIte]
        exact (hz.2 v (Or.inr hvQ)).symm
  · intro y _
    simp only [Pi.mul_apply]
    congr 1
    · exact hf fun v hv => by simp [hv]
    · exact hg fun v hv => by simp [hv]

/-- **The factorization criterion for conditional independence**: if `p = f * g`, where `f`
depends only on the variables in `P`, `g` only on those in `Q`, and every variable is in `P` or
`Q`, then variables `A` outside `Q` and `B` outside `P` are conditionally independent given
`P ∩ Q`. -/
theorem condIndep_of_dependsOn {f g : (V → α) → ℝ} {P Q : Set V} (hf : DependsOn f P)
    (hg : DependsOn g Q) (hPQ : ∀ v, v ∈ P ∨ v ∈ Q) {A B : Set V} (hA : ∀ v ∈ A, v ∉ Q)
    (hB : ∀ v ∈ B, v ∉ P) : CondIndep (f * g) A B (P ∩ Q) := by
  intro x
  have hsub : ∀ U : Set V, P ∩ Q ⊆ U ∪ P ∩ Q := fun U => Set.subset_union_right
  rw [marginal_mul hf hg hPQ (hsub _) x, marginal_mul hf hg hPQ subset_rfl x,
    marginal_mul hf hg hPQ (hsub _) x, marginal_mul hf hg hPQ (hsub _) x]
  have e1 : A ∪ B ∪ P ∩ Q ∪ Pᶜ = A ∪ P ∩ Q ∪ Pᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hB v
    tauto
  have e2 : A ∪ B ∪ P ∩ Q ∪ Qᶜ = B ∪ P ∩ Q ∪ Qᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hA v
    tauto
  have e3 : P ∩ Q ∪ Pᶜ = B ∪ P ∩ Q ∪ Pᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hB v
    tauto
  have e4 : P ∩ Q ∪ Qᶜ = A ∪ P ∩ Q ∪ Qᶜ := by
    ext v
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    have := hA v
    tauto
  rw [e1, e2, e3, e4]
  ring

/-- Conditional independence given `S` only involves the variables of `A` and `B` outside `S`. -/
theorem condIndep_of_sdiff {p : (V → α) → ℝ} {A B S : Set V}
    (h : CondIndep p (A \ S) (B \ S) S) : CondIndep p A B S := by
  intro x
  have e1 : A ∪ B ∪ S = A \ S ∪ B \ S ∪ S := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  have e2 : A ∪ S = A \ S ∪ S := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  have e3 : B ∪ S = B \ S ∪ S := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  rw [e1, e2, e3]
  exact h x

open Classical in
/-- The number of configurations that agree with `x` on `W` does not depend on `x`. -/
theorem card_filter_agree (W : Set V) (x z : V → α) :
    (univ.filter fun y : V → α => ∀ v ∈ W, y v = z v).card =
      (univ.filter fun y : V → α => ∀ v ∈ W, y v = x v).card := by
  refine card_nbij' (fun y v => if v ∈ W then x v else y v) (fun y v => if v ∈ W then z v else y v)
    ?_ ?_ ?_ ?_
  · intro y _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    intro v hv
    simp [hv]
  · intro y _
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    intro v hv
    simp [hv]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
    funext v
    by_cases hv : v ∈ W <;> simp [hv, hy v]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
    funext v
    by_cases hv : v ∈ W <;> simp [hv, hy v]

open Classical in
/-- Marginalizing in two steps: for `U ⊆ W`, the `U`-marginal of the `W`-marginal of `p` is the
`U`-marginal of `p` times the number of configurations agreeing with `x` on `W` (the number of
values of the variables outside `W`). -/
theorem marginal_marginal (p : (V → α) → ℝ) {U W : Set V} (h : U ⊆ W) (x : V → α) :
    marginal (marginal p W) U x =
      (univ.filter fun y : V → α => ∀ v ∈ W, y v = x v).card * marginal p U x := by
  simp only [marginal]
  rw [sum_comm' (t' := univ.filter fun z : V → α => ∀ v ∈ U, z v = x v)
    (s' := fun z => univ.filter fun y : V → α => ∀ v ∈ W, y v = z v)]
  · rw [mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [sum_const, nsmul_eq_mul, card_filter_agree W x z]
  · intro y z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hy, hz⟩
      exact ⟨fun v hv => (hz v hv).symm, fun v hv => (hz v (h hv)).trans (hy v hv)⟩
    · rintro ⟨hy, hz⟩
      exact ⟨fun v hv => (hy v (h hv)).trans (hz v hv), fun v hv => (hy v hv).symm⟩

open Classical in
/-- Conditional independence among variables in `W` is the same for `p` and for its
`W`-marginal. -/
theorem condIndep_marginal_iff {p : (V → α) → ℝ} {A B S W : Set V} (hA : A ⊆ W) (hB : B ⊆ W)
    (hS : S ⊆ W) : CondIndep (marginal p W) A B S ↔ CondIndep p A B S := by
  have hpos : ∀ x : V → α,
      (0 : ℝ) < (univ.filter fun y : V → α => ∀ v ∈ W, y v = x v).card := fun x => by
    exact_mod_cast card_pos.mpr ⟨x, by simp⟩
  refine forall_congr' fun x => ?_
  rw [marginal_marginal p (Set.union_subset (Set.union_subset hA hB) hS),
    marginal_marginal p hS, marginal_marginal p (Set.union_subset hA hS),
    marginal_marginal p (Set.union_subset hB hS)]
  have h := (hpos x).ne'
  rw [mul_mul_mul_comm _ (marginal p (A ∪ B ∪ S) x), mul_mul_mul_comm _ (marginal p (A ∪ S) x),
    mul_right_inj' (mul_ne_zero h h)]

end MetaMathlibExt.FiniteWeight
end
-- ===== end atlas-src/MathlibExt/Probability/FiniteWeight.lean =====

-- ===== begin atlas-src/CSLibExt/MachineLearning/GraphicalModels/BayesianNetwork.lean =====
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



/-!
# Bayesian networks: the chain rule and factorization along a topological order

Random variables `X 0, …, X (n - 1)` take values in a finite type `α` and are listed in a
topological order of a directed acyclic graph. A `Chain` gives, for each `k`, the conditional
distribution of `X k` given the earlier variables `X 0, …, X (k - 1)` (a point of Mathlib's
standard simplex `Convexity.StdSimplex`). Its joint distribution is defined by the chain rule:
`joint (k + 1) (x₀, …, x_k) = joint k (x₀, …, x_{k-1}) * p_k (x_k | x₀, …, x_{k-1})`.

## Main results

* `sum_joint`: the joint is a probability distribution; `sum_joint_snoc`: summing out the last
  variable gives the joint of the earlier ones, so `joint k` is the marginal of the first `k`
  variables; `cond_eq_div`: the conditional of the joint is the given conditional distribution.
* `joint_eq_prod`: the joint is the product of the conditionals along the order.
* `exists_chain`: **the chain rule**: every probability distribution of `n` variables is the
  joint of a chain, that is, factorizes as a product of conditionals along any order.
* Bayesian networks: `BayesNet` gives each node `k` a set of parents among `0, …, k - 1` and a
  conditional probability table depending only on the parents. `BayesNet.joint_eq_prod`: its
  joint is `∏ k, p_k (x_k | x_{pa k})`; `BayesNet.sum_joint`: it is a probability distribution;
  `BayesNet.cond_eq_cpt`: the conditional distribution of each node given all earlier nodes (with
  positive probability) is its table, so it depends only on the parents (the ordered Markov
  property).

Sequential models with a hidden chain (hidden Markov models) are in
`CSLibExt/MachineLearning/Sequence/HiddenMarkov.lean`.
-/

section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*}

/-- Sums over `Fin (n + 1) → α` split into the first `n` coordinates and the last one. -/
theorem sum_snoc [Fintype α] {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → α) → M) :
    ∑ x, f x = ∑ y : Fin n → α, ∑ a, f (Fin.snoc y a) := by
  rw [← (Fin.snocEquiv fun _ => α).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- Conditional distributions of each variable given all earlier ones. -/
structure Chain (α : Type*) where
  /-- The distribution of variable `k` given the values of variables `0, …, k - 1`. -/
  cond : (k : ℕ) → (Fin k → α) → StdSimplex ℝ α

namespace Chain

variable (c : Chain α)

/-- The joint distribution of the first `n` variables, by the chain rule. -/
noncomputable def joint : (n : ℕ) → (Fin n → α) → ℝ
  | 0, _ => 1
  | n + 1, x => joint n (Fin.init x) * (c.cond n (Fin.init x)).weights (x (Fin.last n))

theorem joint_zero (x : Fin 0 → α) : c.joint 0 x = 1 :=
  rfl

theorem joint_snoc (n : ℕ) (y : Fin n → α) (a : α) :
    c.joint (n + 1) (Fin.snoc y a) = c.joint n y * (c.cond n y).weights a := by
  simp [joint, Fin.init_snoc, Fin.snoc_last]

theorem joint_nonneg : ∀ (n : ℕ) (x : Fin n → α), 0 ≤ c.joint n x
  | 0, _ => zero_le_one
  | n + 1, _ => mul_nonneg (joint_nonneg n _) ((c.cond n _).nonneg _)

/-- Summing out the last variable gives the joint of the earlier ones. -/
theorem sum_joint_snoc [Fintype α] (n : ℕ) (y : Fin n → α) :
    ∑ a, c.joint (n + 1) (Fin.snoc y a) = c.joint n y := by
  simp only [joint_snoc, ← mul_sum, (c.cond n y).total_of_fintype, mul_one]

/-- The joint is a probability distribution. -/
theorem sum_joint [Fintype α] : ∀ n : ℕ, ∑ x, c.joint n x = 1
  | 0 => by simp [joint]
  | n + 1 => by
    rw [sum_snoc]
    simp only [sum_joint_snoc]
    exact sum_joint n

/-- The conditional distribution of the last variable given the earlier ones, computed from the
joint, is the given conditional distribution. -/
theorem cond_eq_div {n : ℕ} {y : Fin n → α} (hy : c.joint n y ≠ 0) (a : α) :
    c.joint (n + 1) (Fin.snoc y a) / c.joint n y = (c.cond n y).weights a := by
  rw [joint_snoc, mul_div_cancel_left₀ _ hy]

/-- The joint is the product of the conditionals along the order. -/
theorem joint_eq_prod : ∀ (n : ℕ) (x : Fin n → α),
    c.joint n x = ∏ k : Fin n, (c.cond k fun j => x (Fin.castLE k.2.le j)).weights (x k)
  | 0, _ => by simp [joint]
  | n + 1, x => by
    rw [joint, joint_eq_prod n, Fin.prod_univ_castSucc]
    rfl

/-- Two chains that agree on the conditionals of the first `n` variables have the same joint
distribution of these variables. -/
theorem joint_congr {c' : Chain α} : ∀ {n : ℕ}, (∀ k < n, c.cond k = c'.cond k) →
    c.joint n = c'.joint n
  | 0, _ => rfl
  | n + 1, h => by
    funext x
    rw [joint, joint, joint_congr fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)]

/-- Replace the conditional distribution of variable `n`. -/
def update (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) : Chain α where
  cond k := if h : k = n then h ▸ f else c.cond k

theorem update_cond_self (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) :
    (c.update n f).cond n = f := by
  simp [update]

theorem update_cond_of_ne (n : ℕ) (f : (Fin n → α) → StdSimplex ℝ α) {k : ℕ} (hk : k ≠ n) :
    (c.update n f).cond k = c.cond k := by
  simp [update, hk]

end Chain

/-- **The chain rule**: every probability distribution of `n` variables is the joint of a chain
of conditional distributions. -/
theorem exists_chain [Fintype α] [Nonempty α] : ∀ (n : ℕ) (P : (Fin n → α) → ℝ),
    (∀ x, 0 ≤ P x) → ∑ x, P x = 1 → ∃ c : Chain α, ∀ x, P x = c.joint n x
  | 0, P, _, h1 => ⟨⟨fun _ _ => StdSimplex.single (Classical.arbitrary α)⟩, fun x => by
      rw [Fintype.sum_unique, Subsingleton.elim default x] at h1
      rw [h1, Chain.joint_zero]⟩
  | n + 1, P, h0, h1 => by
    classical
    set Q : (Fin n → α) → ℝ := fun y => ∑ a, P (Fin.snoc y a) with hQ
    have hQ0 : ∀ y, 0 ≤ Q y := fun y => sum_nonneg fun a _ => h0 _
    have hQ1 : ∑ y, Q y = 1 := by rw [← h1, sum_snoc]
    obtain ⟨c', hc'⟩ := exists_chain n Q hQ0 hQ1
    let f : (Fin n → α) → StdSimplex ℝ α := fun y =>
      if hy : Q y = 0 then StdSimplex.single (Classical.arbitrary α) else
        { weights := Finsupp.equivFunOnFinite.symm fun a => P (Fin.snoc y a) / Q y
          nonneg := fun a => by
            simpa using div_nonneg (h0 (Fin.snoc y a)) (hQ0 y)
          total := by
            rw [Finsupp.sum_fintype _ _ fun _ => rfl, ← div_self hy]
            simp [← sum_div, hQ] }
    refine ⟨c'.update n f, fun x => ?_⟩
    have hjoint : (c'.update n f).joint n = c'.joint n :=
      Chain.joint_congr _ fun k hk => Chain.update_cond_of_ne _ _ _ hk.ne
    rw [← Fin.snoc_init_self x, Chain.joint_snoc, hjoint, ← hc', Chain.update_cond_self]
    by_cases hy : Q (Fin.init x) = 0
    · have hzero : P (Fin.snoc (Fin.init x) (x (Fin.last n))) = 0 :=
        (sum_eq_zero_iff_of_nonneg fun a _ => h0 _).1 hy _ (mem_univ _)
      rw [hzero, hy, zero_mul]
    · simp [f, hy, mul_div_cancel₀ _ hy]

/-! ### Bayesian networks -/

/-- A Bayesian network on nodes `0, …, n - 1` in topological order: each node has parents among
the earlier nodes and a conditional probability table given the values of its parents. -/
structure BayesNet (α : Type*) (n : ℕ) where
  /-- The parents of node `k`, among the nodes `0, …, k - 1`. -/
  pa : (k : Fin n) → Finset (Fin k)
  /-- The distribution of node `k` given the values of its parents. -/
  cpt : (k : Fin n) → (pa k → α) → StdSimplex ℝ α

namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-- The network as a chain: the conditional of node `k` given the earlier nodes is its table
applied to the values of its parents. -/
noncomputable def toChain : Chain α where
  cond k y := if hk : k < n then b.cpt ⟨k, hk⟩ fun j => y j else
    StdSimplex.single (Classical.arbitrary α)

/-- The joint distribution of the network. -/
noncomputable def joint (x : Fin n → α) : ℝ :=
  b.toChain.joint n x

/-- **Factorization of a Bayesian network**: the joint is the product over nodes of the
probability of the node's value given the values of its parents. -/
theorem joint_eq_prod (x : Fin n → α) :
    b.joint x = ∏ k : Fin n, (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k) := by
  rw [joint, Chain.joint_eq_prod]
  refine prod_congr rfl fun k _ => ?_
  simp [toChain, k.2]

/-- The joint of a Bayesian network is a probability distribution. -/
theorem sum_joint [Fintype α] : ∑ x, b.joint x = 1 :=
  b.toChain.sum_joint n

/-- **The ordered Markov property**: the conditional distribution of node
`k` given all earlier nodes, computed from the joint of the first `k + 1` nodes, is the node's
table at its parents' values. In particular it depends only on the values of the parents. -/
theorem cond_eq_cpt {k : ℕ} (hk : k < n) {y : Fin k → α} (hy : b.toChain.joint k y ≠ 0)
    (a : α) :
    b.toChain.joint (k + 1) (Fin.snoc y a) / b.toChain.joint k y =
      (b.cpt ⟨k, hk⟩ fun j => y j).weights a := by
  rw [Chain.cond_eq_div _ hy]
  simp [toChain, hk]

end BayesNet

end Cslib.MachineLearning.GraphicalModels
end
-- ===== end atlas-src/CSLibExt/MachineLearning/GraphicalModels/BayesianNetwork.lean =====

-- ===== begin atlas-src/CSLibExt/MachineLearning/GraphicalModels/CausalBayesNet.lean =====
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



/-!
# Causal Bayesian networks: the do-operator and adjustment for the parents

A Bayesian network (`BayesNet`, nodes in a topological order) is read causally: each table
`p_k (x_k | x_{pa k})` is an autonomous mechanism. The intervention `do(X_k = a)` replaces the
mechanism of node `k` by the point mass at `a` and keeps all other mechanisms (Pearl 2009,
Definition 1.3.1 and §3.2.2).

## Main definitions

* `BayesNet.paVal b k x`: the values of the parents of node `k` in a full assignment `x`.
* `BayesNet.intervene b k a`: the network after the intervention `do(X_k = a)`.
* `BayesNet.Edge`, `BayesNet.IsDescendant`, `BayesNet.IsPath`, `BayesNet.PathBlocked`,
  `BayesNet.DSeparated`: the graph of a network, paths of its skeleton, blocking and
  d-separation (Pearl 2009, Definition 1.2.3).

## Main results

* `BayesNet.joint_intervene`: **the truncated factorization** (Pearl 2009, eq. (3.10)): the
  post-intervention joint is `∏_{j ≠ k} p_j (x_j | x_{pa j})` on assignments with `x_k = a`,
  and `0` elsewhere.
* `BayesNet.sum_paVal_intervene`: the intervention does not change the law of the parents of
  the intervened node; `BayesNet.sum_filter_joint_eq_cpt_mul`: the table of a node is its
  conditional law given its parents, `P(X_k = a, pa_k = z) = p_k (a | z) P(pa_k = z)`.
* `BayesNet.sum_intervene_joint_mul`: **adjustment for the direct causes** (Pearl 2009,
  Theorem 3.2.2; the case `Z = pa(X)` of the back-door adjustment, Pearl 1995 and Pearl 2009,
  Theorem 3.3.2): for every function `f` of the variables,
  `E[f | do(X_k = a)] = ∑_z P(pa_k = z) E[f | X_k = a, pa_k = z]`, under positivity of
  `P(X_k = a, pa_k = z)` wherever `P(pa_k = z) > 0`. With `f` the indicator of `{Y = y}` this is
  `P(y | do(x)) = ∑_z P(y | x, z) P(z)`. `BayesNet.sum_intervene_joint_mul_of_cpt_ne_zero`:
  the same when the table of node `k` gives `a` positive probability at every parent value.
* `BayesNet.sum_intervene_joint_mul_of_pred`: **back-door adjustment** (Pearl 2009,
  Theorem 3.3.2) for a set `Z` of nodes preceding the treatment in the topological order that
  contains its parents (such a `Z` meets the back-door criterion), with
  `BayesNet.sum_filter_restrict_joint_eq_cpt_mul` and
  `BayesNet.sum_intervene_joint_mul_of_pred_of_cpt_ne_zero`.
* `BayesNet.DSeparated.symm`: d-separation is symmetric.

The global Markov property (d-separation implies conditional independence) is in
`CSLibExt/MachineLearning/GraphicalModels/GlobalMarkov.lean`; the general back-door adjustment
(any `Z` meeting the back-door criterion, for example one containing nodes after the treatment
in the order) and the front-door adjustment are in
`CSLibExt/MachineLearning/GraphicalModels/CausalAdjustment.lean`; the do-calculus is not
covered.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §1.2–1.3, §3.2–3.3.
-/

section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*}

/-- Summing a function of the first `k` variables against the joint of `n ≥ k` variables gives
the sum against the joint of the first `k`. -/
private lemma chain_sum_mul_joint_castLE [Fintype α] (c : Chain α) {k : ℕ}
    (g : (Fin k → α) → ℝ) (n : ℕ) (h : k ≤ n) :
    ∑ x : Fin n → α, g (fun j => x (Fin.castLE h j)) * c.joint n x =
      ∑ y : Fin k → α, g y * c.joint k y := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [sum_snoc]
    have hc : ∀ (y : Fin n → α) (a : α),
        (fun j : Fin k => (Fin.snoc y a : Fin (n + 1) → α) (Fin.castLE (hkn.trans n.le_succ) j)) =
          fun j => y (Fin.castLE hkn j) := by
      intro y a; funext j
      have : Fin.castLE (hkn.trans n.le_succ) j = Fin.castSucc (Fin.castLE hkn j) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    simp_rw [hc, Chain.joint_snoc, ← mul_assoc, ← mul_sum, (c.cond n _).total_of_fintype,
      mul_one]
    exact ih
namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-- The values of the parents of node `k` in a full assignment `x`. -/
def paVal (k : Fin n) (x : Fin n → α) : b.pa k → α :=
  fun j => x (Fin.castLE k.2.le j)

/-- **The intervention `do(X_k = a)`**: the mechanism of node `k` is replaced by the point mass
at `a`, and all incoming arrows to `k` are deleted (its parent set becomes `∅`); every other
node keeps its parents and its table. (The new table of `k` is the point mass on the empty
parent set; the tables of the other nodes are transported along the equality of their
parent sets.) -/
noncomputable def intervene (k : Fin n) (a : α) : BayesNet α n where
  pa j := if j = k then ∅ else b.pa j
  cpt j z := if h : j = k then StdSimplex.single a
    else b.cpt j fun i => z ⟨i.1, by rw [if_neg h]; exact i.2⟩

/-- The parents of the intervened node are deleted. -/
theorem intervene_pa_self (k : Fin n) (a : α) : (b.intervene k a).pa k = ∅ := by
  simp [intervene]

/-- The parents of every other node are unchanged by the intervention. -/
theorem intervene_pa_of_ne {j k : Fin n} (hj : j ≠ k) (a : α) :
    (b.intervene k a).pa j = b.pa j := by
  simp [intervene, hj]

/-- **The truncated factorization** (Pearl 2009, eq. (3.10)): after `do(X_k = a)` the joint is
the product of the tables of all nodes other than `k` on assignments with `x_k = a`, and `0`
elsewhere. -/
theorem joint_intervene [DecidableEq α] (k : Fin n) (a : α) (x : Fin n → α) :
    (b.intervene k a).joint x =
      if x k = a then ∏ j ∈ univ.erase k, (b.cpt j (b.paVal j x)).weights (x j) else 0 := by
  rw [joint_eq_prod, ← Finset.mul_prod_erase _ _ (mem_univ k)]
  have hrest : ∏ j ∈ univ.erase k, ((b.intervene k a).cpt j
      fun i => x (Fin.castLE j.2.le i)).weights (x j) =
      ∏ j ∈ univ.erase k, (b.cpt j (b.paVal j x)).weights (x j) := by
    refine prod_congr rfl fun j hj => ?_
    simp [intervene, ne_of_mem_erase hj]
    rfl
  rw [hrest]
  simp only [intervene, dite_true]
  split_ifs with h
  · simp [StdSimplex.single, h]
  · simp [StdSimplex.single, Ne.symm h]

private lemma toChain_intervene_joint (k : Fin n) (a : α) :
    (b.intervene k a).toChain.joint k = b.toChain.joint k := by
  refine Chain.joint_congr _ fun j hj => ?_
  funext y
  have hjn : j < n := hj.trans k.2
  have hne : (⟨j, hjn⟩ : Fin n) ≠ k := fun h => (Fin.ext_iff.1 h ▸ hj).false
  simp [toChain, hjn, intervene, hne]

/-- The intervention `do(X_k = a)` does not change the law of the parents of node `k`. -/
theorem sum_paVal_intervene [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (z : b.pa k → α) :
    ∑ x with b.paVal k x = z, (b.intervene k a).joint x = ∑ x with b.paVal k x = z, b.joint x := by
  have hmarg : ∀ b' : BayesNet α n,
      ∑ x with b.paVal k x = z, b'.joint x =
        ∑ y : Fin k → α, (if (fun j : b.pa k => y j) = z then 1 else 0) * b'.toChain.joint k y := by
    intro b'
    rw [← chain_sum_mul_joint_castLE b'.toChain _ n k.2.le, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    change (if b.paVal k x = z then b'.joint x else 0) =
      (if b.paVal k x = z then 1 else 0) * b'.toChain.joint n x
    split_ifs <;> simp [joint]
  rw [hmarg (b.intervene k a), hmarg b, toChain_intervene_joint]

private lemma joint_eq_intervene_mul (k : Fin n) (a : α) {x : Fin n → α}
    (hx : x k = a) :
    b.joint x = (b.intervene k a).joint x * (b.cpt k (b.paVal k x)).weights a := by
  classical
  rw [joint_intervene]
  simp only [hx, ↓reduceIte]
  rw [joint_eq_prod, ← Finset.mul_prod_erase _ _ (mem_univ k),
    mul_comm, hx]
  rfl

private lemma sum_filter_joint_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (f : (Fin n → α) → ℝ) (z : b.pa k → α) :
    ∑ x with x k = a ∧ b.paVal k x = z, b.joint x * f x =
      (b.cpt k z).weights a * ∑ x with b.paVal k x = z, (b.intervene k a).joint x * f x := by
  rw [sum_filter, sum_filter, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases hk : x k = a
  · by_cases hz : b.paVal k x = z
    · simp only [hk, hz, and_self, ↓reduceIte]
      rw [joint_eq_intervene_mul b k a hk, hz]
      ring
    · simp [hz]
  · rw [joint_intervene]
    simp [hk]

/-- **Adjustment for the direct causes** (Pearl 2009, Theorem 3.2.2; the case `Z = pa(X)` of
the back-door adjustment): for every function `f` of the variables,
`E[f | do(X_k = a)] = ∑_z P(pa_k = z) E[f | X_k = a, pa_k = z]`, assuming
`P(X_k = a, pa_k = z) > 0` whenever `P(pa_k = z) > 0`. -/
theorem sum_intervene_joint_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (f : (Fin n → α) → ℝ)
    (hpos : ∀ z : b.pa k → α, ∑ x with b.paVal k x = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ b.paVal k x = z, b.joint x ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : b.pa k → α, (∑ x with b.paVal k x = z, b.joint x) *
        ((∑ x with x k = a ∧ b.paVal k x = z, b.joint x * f x) /
          ∑ x with x k = a ∧ b.paVal k x = z, b.joint x) := by
  rw [← sum_fiberwise univ (b.paVal k) fun x => (b.intervene k a).joint x * f x]
  refine sum_congr rfl fun z _ => ?_
  have hQ := sum_filter_joint_mul b k a (fun _ => 1) z
  simp only [mul_one] at hQ
  rw [sum_paVal_intervene] at hQ
  rw [sum_filter_joint_mul b k a f z, hQ]
  by_cases hP : ∑ x with b.paVal k x = z, b.joint x = 0
  · rw [hP, zero_mul]
    have hPdo : ∑ x with b.paVal k x = z, (b.intervene k a).joint x = 0 := by
      rw [sum_paVal_intervene, hP]
    rw [sum_eq_zero_iff_of_nonneg (f := fun x => (b.intervene k a).joint x)
      fun x _ => (b.intervene k a).toChain.joint_nonneg n x] at hPdo
    exact sum_eq_zero fun x hx => by
      change (b.intervene k a).joint x * f x = 0
      rw [hPdo x hx, zero_mul]
  · have hw : (b.cpt k z).weights a ≠ 0 := by
      intro hw; apply hpos z hP; rw [hQ, hw, zero_mul]
    field_simp

/-- The table of node `k` is the conditional law of `X_k` given its parents:
`P(X_k = a, pa_k = z) = p_k (a | z) P(pa_k = z)`. -/
theorem sum_filter_joint_eq_cpt_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (z : b.pa k → α) :
    ∑ x with x k = a ∧ b.paVal k x = z, b.joint x =
      (b.cpt k z).weights a * ∑ x with b.paVal k x = z, b.joint x := by
  have hQ := sum_filter_joint_mul b k a (fun _ => 1) z
  simp only [mul_one] at hQ
  rw [hQ, sum_paVal_intervene]

/-- Adjustment for the direct causes when the table of node `k` gives the value `a` positive
probability at every value of the parents. -/
theorem sum_intervene_joint_mul_of_cpt_ne_zero [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (f : (Fin n → α) → ℝ) (hpos : ∀ z, (b.cpt k z).weights a ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : b.pa k → α, (∑ x with b.paVal k x = z, b.joint x) *
        ((∑ x with x k = a ∧ b.paVal k x = z, b.joint x * f x) /
          ∑ x with x k = a ∧ b.paVal k x = z, b.joint x) :=
  b.sum_intervene_joint_mul k a f fun z hz => by
    rw [sum_filter_joint_eq_cpt_mul]
    exact mul_ne_zero (hpos z) hz

/-- The intervention `do(X_k = a)` does not change the law of any set `Z` of nodes preceding `k`
in the topological order. -/
private lemma sum_restrict_intervene [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k) (z : Z → α) :
    ∑ x with (fun i : Z => x i) = z, (b.intervene k a).joint x =
      ∑ x with (fun i : Z => x i) = z, b.joint x := by
  let g : (Fin k → α) → ℝ := fun y =>
    if (fun i : Z => y ⟨i.1.val, hZk i.1 i.2⟩) = z then 1 else 0
  have hmarg : ∀ b' : BayesNet α n,
      ∑ x with (fun i : Z => x i) = z, b'.joint x = ∑ y, g y * b'.toChain.joint k y := by
    intro b'
    rw [← chain_sum_mul_joint_castLE b'.toChain g n k.2.le, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    change (if (fun i : Z => x i) = z then b'.joint x else 0) =
      (if (fun i : Z => x i) = z then 1 else 0) * b'.toChain.joint n x
    split_ifs <;> simp [joint]
  rw [hmarg, hmarg, toChain_intervene_joint]

/-- **Back-door adjustment for a set of predecessors containing the parents**: let `Z` be a set
of nodes preceding `k` in the topological order (so `Z` contains no descendant of `k`) that
contains the parents of `k`. Then `Z` meets the back-door criterion for every outcome node
`y ∉ Z` (a path from `k` to `y` that starts with an arrow into `k` starts `k ← p` with
`p ∈ pa(k) ⊆ Z`, an interior non-collider, so it is blocked), and for every function `f` of the
variables
`E[f | do(X_k = a)] = ∑_z P(Z = z) E[f | X_k = a, Z = z]`, assuming `P(X_k = a, Z = z) > 0`
whenever `P(Z = z) > 0` (Pearl 2009, Theorem 3.3.2, in this case). -/
theorem sum_intervene_joint_mul_of_pred [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k)
    (hpaZ : ∀ j ∈ b.pa k, Fin.castLE k.2.le j ∈ Z) (f : (Fin n → α) → ℝ)
    (hpos : ∀ z : Z → α, ∑ x with (fun i : Z => x i) = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, b.joint x) *
        ((∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x * f x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x) := by
  -- the parents' values as a function of the values on `Z`
  let π : (Z → α) → (b.pa k → α) := fun z j => z ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩
  have hπ : ∀ x z, (fun i : Z => x i) = z → b.paVal k x = π z := by
    intro x z hz
    funext j
    exact congrFun hz ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩
  have hR : ∀ (g : (Fin n → α) → ℝ) (z : Z → α),
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x * g x =
        (b.cpt k (π z)).weights a *
          ∑ x with (fun i : Z => x i) = z, (b.intervene k a).joint x * g x := by
    intro g z
    rw [sum_filter, sum_filter, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    by_cases hk : x k = a
    · by_cases hz : (fun i : Z => x i) = z
      · simp only [hk, hz, and_self, ↓reduceIte]
        rw [joint_eq_intervene_mul b k a hk, hπ x z hz]
        ring
      · simp [hz]
    · rw [joint_intervene]
      simp [hk]
  rw [← sum_fiberwise univ (fun x : Fin n → α => fun i : Z => x i)
    fun x => (b.intervene k a).joint x * f x]
  refine sum_congr rfl fun z _ => ?_
  have hQ := hR (fun _ => 1) z
  simp only [mul_one] at hQ
  rw [sum_restrict_intervene b k a Z hZk] at hQ
  rw [hR f z, hQ]
  by_cases hP : ∑ x with (fun i : Z => x i) = z, b.joint x = 0
  · rw [hP, zero_mul]
    have hPdo : ∑ x with (fun i : Z => x i) = z, (b.intervene k a).joint x = 0 := by
      rw [sum_restrict_intervene b k a Z hZk, hP]
    rw [sum_eq_zero_iff_of_nonneg (f := fun x => (b.intervene k a).joint x)
      fun x _ => (b.intervene k a).toChain.joint_nonneg n x] at hPdo
    exact sum_eq_zero fun x hx => by
      change (b.intervene k a).joint x * f x = 0
      rw [hPdo x hx, zero_mul]
  · have hw : (b.cpt k (π z)).weights a ≠ 0 := by
      intro hw; apply hpos z hP; rw [hQ, hw, zero_mul]
    field_simp

/-- For a set `Z` of predecessors of `k` containing its parents, the table of `k` is its
conditional law given `Z`: `P(X_k = a, Z = z) = p_k (a | z_{pa k}) P(Z = z)`. -/
theorem sum_filter_restrict_joint_eq_cpt_mul [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k) (hpaZ : ∀ j ∈ b.pa k, Fin.castLE k.2.le j ∈ Z)
    (z : Z → α) :
    ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x =
      (b.cpt k fun j => z ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩).weights a *
        ∑ x with (fun i : Z => x i) = z, b.joint x := by
  rw [← sum_restrict_intervene b k a Z hZk, mul_sum, sum_filter, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hk : x k = a
  · by_cases hz : (fun i : Z => x i) = z
    · simp only [hk, hz, and_self, ↓reduceIte]
      rw [joint_eq_intervene_mul b k a hk, mul_comm,
        show b.paVal k x = fun j : b.pa k => z ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩ from
          funext fun j : b.pa k => congrFun hz ⟨Fin.castLE k.2.le j, hpaZ j j.2⟩]
    · simp [hz]
  · rw [joint_intervene]
    simp [hk]

/-- Back-door adjustment for a set of predecessors containing the parents, when the table of
node `k` gives the value `a` positive probability at every value of the parents. -/
theorem sum_intervene_joint_mul_of_pred_of_cpt_ne_zero [Fintype α] [DecidableEq α] (k : Fin n)
    (a : α) (Z : Finset (Fin n)) (hZk : ∀ i ∈ Z, i < k)
    (hpaZ : ∀ j ∈ b.pa k, Fin.castLE k.2.le j ∈ Z) (f : (Fin n → α) → ℝ)
    (hcpt : ∀ u, (b.cpt k u).weights a ≠ 0) :
    ∑ x, (b.intervene k a).joint x * f x =
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, b.joint x) *
        ((∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x * f x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x) :=
  b.sum_intervene_joint_mul_of_pred k a Z hZk hpaZ f fun z hz => by
    rw [sum_filter_restrict_joint_eq_cpt_mul b k a Z hZk hpaZ]
    exact mul_ne_zero (hcpt _) hz

end BayesNet

namespace BayesNet

variable {n : ℕ} (b : BayesNet α n)

/-! ### The graph of a network and d-separation -/

/-- The edge `i → j` of the network's graph: `i` is a parent of `j`. -/
def Edge (i j : Fin n) : Prop :=
  ∃ h : i.val < j.val, (⟨i.val, h⟩ : Fin j) ∈ b.pa j

/-- `j` is a descendant of `i` (every node is its own descendant). -/
def IsDescendant (i j : Fin n) : Prop :=
  Relation.ReflTransGen b.Edge i j

/-- `i` and `j` are adjacent in the skeleton of the graph. -/
def Adj (i j : Fin n) : Prop :=
  b.Edge i j ∨ b.Edge j i

/-- A path of the skeleton from `x` to `y`: a list of distinct nodes, consecutive ones
adjacent, starting at `x` and ending at `y`. -/
def IsPath (x y : Fin n) (p : List (Fin n)) : Prop :=
  p.Nodup ∧ p.IsChain b.Adj ∧ p.head? = some x ∧ p.getLast? = some y

/-- The consecutive nodes `u, m, w` of a path are blocked by `Z` (Pearl 2009, Definition
1.2.3): either `m` is a collider `u → m ← w` none of whose descendants is in `Z`, or `m` is not
a collider (a chain or a fork) and `m ∈ Z`. -/
def BlockedAt (Z : Set (Fin n)) (u m w : Fin n) : Prop :=
  (b.Edge u m ∧ b.Edge w m ∧ ∀ d, b.IsDescendant m d → d ∉ Z) ∨
    (¬(b.Edge u m ∧ b.Edge w m) ∧ m ∈ Z)

/-- A path is blocked by `Z` if some three consecutive nodes of it are. -/
def PathBlocked (Z : Set (Fin n)) (p : List (Fin n)) : Prop :=
  ∃ (i : ℕ) (h : i + 2 < p.length), b.BlockedAt Z p[i] p[i + 1] p[i + 2]

/-- **d-separation** (Pearl 1988; Pearl 2009, Definition 1.2.3): `Z` d-separates `X` from `Y`
if every path between a node of `X` and a node of `Y` is blocked by `Z`. -/
def DSeparated (X Y Z : Set (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ p, b.IsPath x y p → b.PathBlocked Z p

/-- Blocking at a node does not depend on the direction in which the path is read. -/
theorem blockedAt_comm {Z : Set (Fin n)} {u m w : Fin n} :
    b.BlockedAt Z u m w ↔ b.BlockedAt Z w m u := by
  unfold BlockedAt
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩

/-- The reverse of a path from `x` to `y` is a path from `y` to `x`. -/
theorem isPath_reverse {x y : Fin n} {p : List (Fin n)} (h : b.IsPath x y p) :
    b.IsPath y x p.reverse := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨List.nodup_reverse.2 h1, ?_, by simpa using h4, by simpa using h3⟩
  rw [List.isChain_reverse]
  exact h2.imp fun a b hab => hab.symm

/-- If a path is blocked by `Z`, so is its reverse. -/
theorem pathBlocked_reverse {Z : Set (Fin n)} {p : List (Fin n)} (h : b.PathBlocked Z p) :
    b.PathBlocked Z p.reverse := by
  obtain ⟨i, hi, hb⟩ := h
  refine ⟨p.length - 3 - i, by simp; omega, ?_⟩
  rw [blockedAt_comm]
  simp only [List.getElem_reverse]
  convert hb using 3 <;> omega

/-- d-separation is symmetric. -/
theorem DSeparated.symm {X Y Z : Set (Fin n)} (h : b.DSeparated X Y Z) : b.DSeparated Y X Z :=
  fun y hy x hx p hp => by
    simpa using b.pathBlocked_reverse (h x hx y hy p.reverse (b.isPath_reverse hp))

end BayesNet

end Cslib.MachineLearning.GraphicalModels
end
-- ===== end atlas-src/CSLibExt/MachineLearning/GraphicalModels/CausalBayesNet.lean =====

-- ===== begin atlas-src/CSLibExt/MachineLearning/GraphicalModels/GlobalMarkov.lean =====
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



/-!
# The global Markov property of Bayesian networks

For a Bayesian network (`BayesNet`, nodes in a topological order, finite state space), d-separation
in its graph implies conditional independence under its joint law: **the global Markov
property** (Geiger, Verma & Pearl 1990; Lauritzen, Dawid, Larsen & Leimer 1990; Pearl 2009,
Theorem 1.2.4). d-separation `BayesNet.DSeparated` is that of
`CSLibExt/MachineLearning/GraphicalModels/CausalBayesNet.lean`; marginals and conditional
independence are `MetaMathlibExt.FiniteWeight.marginal` and `MetaMathlibExt.FiniteWeight.CondIndep`
of `MathlibExt/Probability/FiniteWeight.lean`, applied to `Finset`s of nodes through the
coercion to `Set`.

## Main definitions

* `BayesNet.IsAncestral b A`: `A` contains the parents of each of its nodes.
* `BayesNet.ancProd b A`: the product of the tables of the nodes of `A`, with the uniform law on
  the other nodes.

## Main results

* `marginal_eq_sum_insert`, `marginal_le_of_subset`, and the semi-graphoid properties
  `condIndep_symm`, `condIndep_mono_left` (decomposition) and `condIndep_weak_union`.
* `BayesNet.marginal_joint_eq_ancProd`: the law of an ancestral set depends only on the tables
  of its nodes.
* `BayesNet.condIndep_of_dSeparated`: **the global Markov property**.

## Proof

By induction over ancestral sets `A`, removing the last node `s` of `A` (a sink of the subgraph
on `A`), for d-separation in the subgraph on `A`. When `s` is in the conditioning set, one of the
two sides absorbs all its parents outside the conditioning set; otherwise a path through `s`
gives an active walk, and active walks shorten to active paths. The probabilistic steps use
decomposition and weak union of `CondIndep`.

## References

* D. Geiger, T. Verma and J. Pearl, *Identifying independence in Bayesian networks*, Networks
  20(5) (1990), 507–534.
* S. L. Lauritzen, A. P. Dawid, B. N. Larsen and H.-G. Leimer, *Independence properties of
  directed Markov fields*, Networks 20(5) (1990), 491–505.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §1.2.
-/

section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity MetaMathlibExt.FiniteWeight

variable {α : Type*}

/-! ### Properties of `marginal` and `CondIndep` -/

section CondIndep

variable {n : ℕ} [Fintype α]

/-- `FiniteWeight.marginal` on a `Finset` of nodes, as a sum over a decidable filter. -/
theorem marginal_coe [DecidableEq α] (P : (Fin n → α) → ℝ) (S : Finset (Fin n)) (x' : Fin n → α) :
    marginal P ↑S x' = ∑ x with ∀ i ∈ S, x i = x' i, P x := by
  unfold marginal
  congr 1
  ext x
  simp

/-- `FiniteWeight.CondIndep` for `Finset`s of nodes, with the unions taken in `Finset`. -/
theorem condIndep_coe_iff {P : (Fin n → α) → ℝ} {X Y Z : Finset (Fin n)} :
    CondIndep P ↑X ↑Y ↑Z ↔ ∀ x', marginal P ↑(X ∪ Y ∪ Z) x' * marginal P ↑Z x' =
      marginal P ↑(X ∪ Z) x' * marginal P ↑(Y ∪ Z) x' := by
  simp only [CondIndep, coe_union]

/-- `marginal P S x'` depends only on the values of `x'` on `S`. -/
theorem marginal_congr_of_eqOn (P : (Fin n → α) → ℝ) (S : Finset (Fin n)) {x y : Fin n → α}
    (h : ∀ i ∈ S, x i = y i) : marginal P ↑S x = marginal P ↑S y := by
  classical
  simp only [marginal_coe]
  congr 1
  exact Finset.filter_congr fun z _ => forall₂_congr fun i hi => by rw [h i hi]

/-- Fixing more variables decreases the probability. -/
theorem marginal_le_of_subset {P : (Fin n → α) → ℝ} (hP : ∀ x, 0 ≤ P x)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (x' : Fin n → α) :
    marginal P ↑T x' ≤ marginal P ↑S x' :=
  marginal_anti hP (coe_subset.2 hST) x'

/-- Summing out one more variable `i ∉ S`. -/
theorem marginal_eq_sum_insert (P : (Fin n → α) → ℝ) {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) (x' : Fin n → α) :
    marginal P ↑S x' = ∑ a, marginal P ↑(insert i S) (Function.update x' i a) := by
  classical
  simp only [marginal_coe]
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => ∀ j ∈ S, x j = x' j)
    (fun x => x i)]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.filter_filter]
  refine sum_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
  simp only [Finset.mem_insert, forall_eq_or_imp, Function.update_self]
  have hne : ∀ j ∈ S, j ≠ i := fun j hj h => hi (h ▸ hj)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun j hj => by rw [h1 j hj, Function.update_of_ne (hne j hj)]⟩
  · rintro ⟨h2, h1⟩
    exact ⟨fun j hj => by rw [h1 j hj, Function.update_of_ne (hne j hj)], h2⟩

/-- Conditional independence is symmetric. -/
theorem condIndep_symm {P : (Fin n → α) → ℝ} {X Y Z : Finset (Fin n)}
    (h : CondIndep P ↑X ↑Y ↑Z) : CondIndep P ↑Y ↑X ↑Z := by
  classical
  rw [condIndep_coe_iff] at h ⊢
  intro x'
  have := h x'
  rw [Finset.union_comm Y X, mul_comm (marginal P ↑(Y ∪ Z) x')]
  exact this

/-- Removing one variable `i ∉ Y` from the first set preserves conditional independence. -/
private lemma condIndep_of_insert {P : (Fin n → α) → ℝ} {X Y Z : Finset (Fin n)} {i : Fin n}
    (hiY : i ∉ Y) (h : CondIndep P ↑(insert i X) ↑Y ↑Z) : CondIndep P ↑X ↑Y ↑Z := by
  classical
  rw [condIndep_coe_iff] at h ⊢
  by_cases hiX : i ∈ X
  · rwa [Finset.insert_eq_of_mem hiX] at h
  by_cases hiZ : i ∈ Z
  · intro x'
    have := h x'
    rwa [insert_union, insert_union, insert_eq_of_mem (mem_union_right _ hiZ), insert_union,
      insert_eq_of_mem (mem_union_right _ hiZ)] at this
  intro x'
  have hi1 : i ∉ X ∪ Y ∪ Z := by simp [hiX, hiY, hiZ]
  have hi2 : i ∉ X ∪ Z := by simp [hiX, hiZ]
  rw [marginal_eq_sum_insert P hi1, marginal_eq_sum_insert P hi2, sum_mul, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  have := h (Function.update x' i a)
  rw [insert_union, insert_union, insert_union] at this
  have hz : marginal P ↑Z (Function.update x' i a) = marginal P ↑Z x' :=
    marginal_congr_of_eqOn P Z fun j hj =>
      Function.update_of_ne (fun h => hiZ (by rwa [h] at hj)) _ _
  have hyz : marginal P ↑(Y ∪ Z) (Function.update x' i a) = marginal P ↑(Y ∪ Z) x' :=
    marginal_congr_of_eqOn P _ fun j hj => Function.update_of_ne (fun h => by
      subst h; rcases mem_union.1 hj with h | h <;> contradiction) _ _
  rw [← hz, ← hyz]
  exact this

/-- **Decomposition**: if `X ⫫ Y | Z` then `X' ⫫ Y | Z` for `X' ⊆ X`. -/
theorem condIndep_mono_left {P : (Fin n → α) → ℝ} {X X' Y Z : Finset (Fin n)}
    (h : CondIndep P ↑X ↑Y ↑Z) (hX' : X' ⊆ X) (hXY : Disjoint X Y) : CondIndep P ↑X' ↑Y ↑Z := by
  classical
  have key : ∀ (D X' : Finset (Fin n)), CondIndep P ↑(X' ∪ D) ↑Y ↑Z → Disjoint (X' ∪ D) Y →
      CondIndep P ↑X' ↑Y ↑Z := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro X' h _; simpa using h
    | insert i D hiD ih =>
      intro X' h hd
      rw [union_insert] at h
      have hiY : i ∉ Y := fun hy =>
        Finset.disjoint_left.1 hd (mem_union_right _ (mem_insert_self i D)) hy
      exact ih X' (condIndep_of_insert hiY h)
        (hd.mono_left (union_subset_union_right (subset_insert i D)))
  rw [← union_sdiff_of_subset hX'] at h hXY
  exact key _ _ h hXY

/-- **Weak union**: if `X ∪ W ⫫ Y | Z` then `X ⫫ Y | Z ∪ W` (for a nonnegative law). -/
theorem condIndep_weak_union {P : (Fin n → α) → ℝ} (hP : ∀ x, 0 ≤ P x)
    {X W Y Z : Finset (Fin n)} (h : CondIndep P ↑(X ∪ W) ↑Y ↑Z) (hXY : Disjoint (X ∪ W) Y) :
    CondIndep P ↑X ↑Y ↑(Z ∪ W) := by
  classical
  have hW : CondIndep P ↑W ↑Y ↑Z := condIndep_mono_left h subset_union_right hXY
  rw [condIndep_coe_iff] at h hW ⊢
  intro x'
  have e1 : X ∪ Y ∪ (Z ∪ W) = X ∪ W ∪ Y ∪ Z := by ext; simp only [mem_union]; tauto
  have e2 : X ∪ (Z ∪ W) = X ∪ W ∪ Z := by ext; simp only [mem_union]; tauto
  have e3 : Y ∪ (Z ∪ W) = W ∪ Y ∪ Z := by ext; simp only [mem_union]; tauto
  rw [e1, e2, e3, union_comm Z W]
  have h1 := h x'
  have h2 := hW x'
  by_cases hz : marginal P ↑Z x' = 0
  · have z1 : marginal P ↑(W ∪ Z) x' = 0 := le_antisymm
      (hz ▸ marginal_le_of_subset hP subset_union_right x') (marginal_nonneg hP _ _)
    have z2 : marginal P ↑(X ∪ W ∪ Z) x' = 0 := le_antisymm
      (hz ▸ marginal_le_of_subset hP subset_union_right x') (marginal_nonneg hP _ _)
    rw [z1, z2, mul_zero, zero_mul]
  · apply mul_left_cancel₀ hz
    linear_combination marginal P ↑(W ∪ Z) x' * h1 - marginal P ↑(X ∪ W ∪ Z) x' * h2

end CondIndep

section Split

variable {n : ℕ}

/-- Sums over assignments split at the coordinate `s`. -/
private lemma sum_split_at [Fintype α] (s : Fin n) (g : (Fin n → α) → ℝ) :
    ∑ x, g x = ∑ y : {j // j ≠ s} → α, ∑ a, g ((Equiv.funSplitAt s α).symm (a, y)) := by
  rw [← (Equiv.funSplitAt s α).symm.sum_comp, Fintype.sum_prod_type, sum_comm]

private lemma funSplitAt_symm_self (s : Fin n) (a : α) (y : {j // j ≠ s} → α) :
    (Equiv.funSplitAt s α).symm (a, y) s = a := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

private lemma funSplitAt_symm_of_ne (s : Fin n) (a : α) (y : {j // j ≠ s} → α)
    {j : Fin n} (h : j ≠ s) : (Equiv.funSplitAt s α).symm (a, y) j = y ⟨j, h⟩ := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

end Split

namespace BayesNet

section Graph

variable {n : ℕ} (b : BayesNet α n)

/-- A set of nodes is ancestral if it contains the parents of each of its nodes. -/
def IsAncestral (A : Finset (Fin n)) : Prop :=
  ∀ ⦃i j : Fin n⦄, b.Edge i j → j ∈ A → i ∈ A

/-! ### d-separation inside an ancestral set -/

/-- `j` is a descendant of `i` through nodes of `A`. -/
private def DescIn (A : Finset (Fin n)) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (fun u v => b.Edge u v ∧ v ∈ A) i j

/-- The consecutive nodes `u, m, w` are blocked by `Z` in the subgraph on `A`. -/
private def BlockedIn (A Z : Finset (Fin n)) (u m w : Fin n) : Prop :=
  (b.Edge u m ∧ b.Edge w m ∧ ∀ d, b.DescIn A m d → d ∉ Z) ∨
    (¬(b.Edge u m ∧ b.Edge w m) ∧ m ∈ Z)

/-- An active walk given `Z` in the subgraph on `A`: consecutive nodes adjacent, all nodes in
`A`, no three consecutive nodes blocked. Nodes may repeat. -/
private def ActiveIn (A Z : Finset (Fin n)) (p : List (Fin n)) : Prop :=
  p.IsChain b.Adj ∧ (∀ v ∈ p, v ∈ A) ∧
    ∀ (i : ℕ) (h : i + 2 < p.length), ¬b.BlockedIn A Z p[i] p[i + 1] p[i + 2]

/-- d-separation in the subgraph on `A`: no path from `X` to `Y` is active given `Z`. -/
private def DSepIn (A X Y Z : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ p, b.IsPath x y p → b.ActiveIn A Z p → False

private lemma descIn_mono {A A' : Finset (Fin n)} (hA : A' ⊆ A) {i j : Fin n}
    (h : b.DescIn A' i j) : b.DescIn A i j := by
  unfold DescIn at h ⊢
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail ⟨hst.1, hA hst.2⟩

private lemma blockedIn_comm {A Z : Finset (Fin n)} {u m w : Fin n} :
    b.BlockedIn A Z u m w ↔ b.BlockedIn A Z w m u := by
  unfold BlockedIn
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩

/-- Activity transfers to a larger subgraph and a conditioning set that agrees on the smaller
subgraph. -/
private lemma activeIn_mono {A A' Z Z' : Finset (Fin n)} (hA : A' ⊆ A) (hZ' : Z' ⊆ Z)
    (hZ : ∀ m ∈ A', m ∈ Z → m ∈ Z') {p : List (Fin n)} (h : b.ActiveIn A' Z' p) :
    b.ActiveIn A Z p := by
  refine ⟨h.1, fun v hv => hA (h.2.1 v hv), fun i hi hb => h.2.2 i hi ?_⟩
  have hm : p[i + 1] ∈ A' := h.2.1 _ (List.getElem_mem _)
  rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, fun d hd hdZ => h3 d (b.descIn_mono hA hd) (hZ' hdZ)⟩
  · exact Or.inr ⟨h1, hZ _ hm h2⟩

private lemma activeIn_tail {A Z : Finset (Fin n)} {v : Fin n} {l : List (Fin n)}
    (h : b.ActiveIn A Z (v :: l)) : b.ActiveIn A Z l :=
  ⟨h.1.tail, fun u hu => h.2.1 u (List.mem_cons_of_mem _ hu), fun i hi =>
    h.2.2 (i + 1) (by simp; omega)⟩

private lemma activeIn_cons {A Z : Finset (Fin n)} {v w : Fin n} {l : List (Fin n)}
    (h : b.ActiveIn A Z (w :: l)) (hv : v ∈ A) (hvw : b.Adj v w)
    (h0 : ∀ hl : 0 < l.length, ¬b.BlockedIn A Z v w l[0]) : b.ActiveIn A Z (v :: w :: l) := by
  refine ⟨List.IsChain.cons_cons hvw h.1, ?_, ?_⟩
  · intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    exacts [hv, h.2.1 u hu]
  · intro i hi
    cases i with
    | zero => exact h0 (by simp at hi; omega)
    | succ i => exact h.2.2 i (by simp at hi ⊢; omega)

private lemma activeIn_reverse {A Z : Finset (Fin n)} {p : List (Fin n)}
    (h : b.ActiveIn A Z p) : b.ActiveIn A Z p.reverse := by
  refine ⟨List.isChain_reverse.2 (h.1.imp fun a b hab => hab.symm),
    fun v hv => h.2.1 v (List.mem_reverse.1 hv), fun i hi hb => ?_⟩
  simp only [List.length_reverse] at hi
  refine h.2.2 (p.length - 3 - i) (by omega) ?_
  rw [blockedIn_comm]
  simp only [List.getElem_reverse] at hb
  have e0 : p.length - 1 - (i + 2) = p.length - 3 - i := by omega
  have e1 : p.length - 1 - (i + 1) = p.length - 3 - i + 1 := by omega
  have e2 : p.length - 1 - i = p.length - 3 - i + 2 := by omega
  simp only [e0, e1, e2] at hb
  exact hb

private lemma activeIn_append {A Z : Finset (Fin n)} {m : Fin n} {l₂ : List (Fin n)} :
    ∀ {l₁ : List (Fin n)}, b.ActiveIn A Z (l₁ ++ [m]) → b.ActiveIn A Z (m :: l₂) →
      (∀ u w, l₁.getLast? = some u → l₂.head? = some w → ¬b.BlockedIn A Z u m w) →
      b.ActiveIn A Z (l₁ ++ m :: l₂)
  | [], _, h2, _ => by simpa using h2
  | v :: l₁, h1, h2, hj => by
    have ih : b.ActiveIn A Z (l₁ ++ m :: l₂) :=
      activeIn_append (b.activeIn_tail h1) h2 fun u w hu hw => hj u w (by
        cases l₁ with
        | nil => simp at hu
        | cons a l => simpa [List.getLast?_cons_cons] using hu) hw
    have hv : v ∈ A := h1.2.1 v (by simp)
    cases l₁ with
    | nil =>
      refine b.activeIn_cons h2 hv (by simpa using h1.1) fun hl => ?_
      exact hj v l₂[0] (by simp) (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hl])
    | cons w l₁ =>
      refine b.activeIn_cons ih hv (List.isChain_cons_cons.1 (by simpa using h1.1)).1 fun hl => ?_
      have := h1.2.2 0 (by simp)
      cases l₁ <;> simpa using this

private lemma activeIn_forward {α : Type*} {n : ℕ} (b : BayesNet α n)
    {A Z : Finset (Fin n)} {p : List (Fin n)} (hp : b.ActiveIn A Z p)
    {i : ℕ} (hi : i + 1 < p.length) (he : b.Edge p[i] p[i + 1])
    (hz : ∀ d, b.DescIn A p[i] d → d ∉ Z) (k : ℕ) (hik : i ≤ k)
    (hk : k + 1 < p.length) : b.DescIn A p[i] p[k] ∧ b.Edge p[k] p[k + 1] := by
  induction k, hik using Nat.le_induction with
  | base => exact ⟨Relation.ReflTransGen.refl, he⟩
  | succ k hik ih =>
    obtain ⟨hd, he⟩ := ih (by omega)
    have hd' : b.DescIn A p[i] p[k + 1] :=
      hd.tail ⟨he, hp.2.1 _ (List.getElem_mem (by omega))⟩
    refine ⟨hd', ?_⟩
    obtain hforward | hback := List.isChain_iff_getElem.1 hp.1 (k + 1) hk
    · exact hforward
    · exact False.elim (hp.2.2 k (by omega)
        (Or.inl ⟨he, hback, fun d hd => hz d (hd'.trans hd)⟩))

private lemma activeIn_junction {α : Type*} {n : ℕ} (b : BayesNet α n)
    {A Z : Finset (Fin n)} {p : List (Fin n)} (hp : b.ActiveIn A Z p)
    {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j + 1 < p.length)
    (heq : p[i] = p[j]) : ¬b.BlockedIn A Z p[i - 1] p[j] p[j + 1] := by
  have hbi : ¬b.BlockedIn A Z p[i - 1] p[i] p[i + 1] := by
    simpa only [show i - 1 + 1 = i by omega, show i - 1 + 2 = i + 1 by omega]
      using hp.2.2 (i - 1) (by omega)
  have hbj : ¬b.BlockedIn A Z p[j - 1] p[j] p[j + 1] := by
    simpa only [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega]
      using hp.2.2 (j - 1) (by omega)
  rintro (⟨hl, hr, hz⟩ | ⟨hc, hz⟩)
  · have hz' : ∀ d, b.DescIn A p[i] d → d ∉ Z := by simpa only [heq] using hz
    have he : b.Edge p[i] p[i + 1] := by
      obtain he | he := List.isChain_iff_getElem.1 hp.1 i (by omega)
      · exact he
      · exact False.elim (hbi (Or.inl ⟨by simpa only [heq] using hl, he, hz'⟩))
    have hlast := (activeIn_forward b hp (by omega) he hz' (j - 1) (by omega)
      (by omega)).2
    have hlast' : b.Edge p[j - 1] p[j] := by
      simpa only [show j - 1 + 1 = j by omega] using hlast
    exact hbj (Or.inl ⟨hlast', hr, hz⟩)
  · have hci : b.Edge p[i - 1] p[i] ∧ b.Edge p[i + 1] p[i] := by
      by_contra h
      exact hbi (Or.inr ⟨h, by simpa only [heq] using hz⟩)
    have hcj : b.Edge p[j - 1] p[j] ∧ b.Edge p[j + 1] p[j] := by
      by_contra h
      exact hbj (Or.inr ⟨h, hz⟩)
    exact hc ⟨by simpa only [heq] using hci.1, hcj.2⟩

private lemma shortcut_get_left {β : Type*} (p : List β) {i j k : ℕ}
    (hi : i ≤ p.length) (hk : k < i)
    (h : k < (p.take i ++ p.drop j).length) : (p.take i ++ p.drop j)[k] = p[k] := by
  rw [List.getElem_append_left (by simpa [List.length_take, Nat.min_eq_left hi] using hk)]
  exact List.getElem_take

private lemma shortcut_get_right {β : Type*} (p : List β) {i j k : ℕ}
    (hi : i ≤ p.length) (hk : i ≤ k)
    (h : k < (p.take i ++ p.drop j).length) :
    (p.take i ++ p.drop j)[k] = p[j + (k - i)]'(by
      simp only [List.length_append, List.length_take, List.length_drop,
        Nat.min_eq_left hi] at h
      omega) := by
  rw [List.getElem_append_right (by simpa [List.length_take, Nat.min_eq_left hi] using hk)]
  simp only [List.getElem_drop, List.length_take, Nat.min_eq_left hi]

private lemma activeIn_shortcut {α : Type*} {n : ℕ} (b : BayesNet α n)
    {A Z : Finset (Fin n)} {p : List (Fin n)} (hp : b.ActiveIn A Z p)
    {i j : ℕ} (hij : i < j) (hj : j < p.length) (heq : p[i] = p[j]) :
    b.ActiveIn A Z (p.take i ++ p.drop j) := by
  have hi : i ≤ p.length := by omega
  have hlen : (p.take i ++ p.drop j).length = i + (p.length - j) := by
    simp [List.length_take, Nat.min_eq_left hi]
  refine ⟨List.isChain_iff_getElem.2 ?_, ?_, ?_⟩
  · intro k hk
    rw [hlen] at hk
    by_cases hki : k + 1 < i
    · rw [shortcut_get_left p hi (by omega), shortcut_get_left p hi hki]
      exact List.isChain_iff_getElem.1 hp.1 k (by omega)
    · by_cases hki' : k < i
      · have hnext : k + 1 = i := by omega
        rw [shortcut_get_left p hi hki', shortcut_get_right p hi (by omega)]
        simp only [hnext, Nat.sub_self, Nat.add_zero, ← heq]
        simpa only [hnext] using List.isChain_iff_getElem.1 hp.1 k (by omega)
      · rw [shortcut_get_right p hi (by omega), shortcut_get_right p hi (by omega)]
        simp only [show j + (k + 1 - i) = j + (k - i) + 1 by omega]
        exact List.isChain_iff_getElem.1 hp.1 (j + (k - i)) (by omega)
  · intro v hv
    apply hp.2.1 v
    obtain hv | hv := List.mem_append.1 hv
    · exact List.mem_of_mem_take hv
    · exact List.mem_of_mem_drop hv
  · intro k hk
    rw [hlen] at hk
    by_cases hki : k + 2 < i
    · rw [shortcut_get_left p hi (by omega), shortcut_get_left p hi (by omega),
        shortcut_get_left p hi hki]
      exact hp.2.2 k (by omega)
    · by_cases hki' : k + 1 < i
      · have hnext : k + 2 = i := by omega
        rw [shortcut_get_left p hi (by omega), shortcut_get_left p hi hki',
          shortcut_get_right p hi (by omega)]
        simp only [hnext, Nat.sub_self, Nat.add_zero, ← heq]
        simpa only [hnext] using hp.2.2 k (by omega)
      · by_cases hki'' : k < i
        · rw [shortcut_get_left p hi hki'', shortcut_get_right p hi (by omega),
            shortcut_get_right p hi (by omega)]
          simp only [show j + (k + 1 - i) = j by omega,
            show j + (k + 2 - i) = j + 1 by omega]
          simp only [show k = i - 1 by omega]
          exact activeIn_junction b hp (by omega) hij (by omega) heq
        · rw [shortcut_get_right p hi (by omega), shortcut_get_right p hi (by omega),
            shortcut_get_right p hi (by omega)]
          simp only [show j + (k + 1 - i) = j + (k - i) + 1 by omega,
            show j + (k + 2 - i) = j + (k - i) + 2 by omega]
          exact hp.2.2 (j + (k - i)) (by omega)

/-- An active walk from `x` to `y` can be shortened to an active path (no repeated node). -/
private theorem exists_path_of_activeIn {A Z : Finset (Fin n)} {p : List (Fin n)}
    {x y : Fin n} (hp : b.ActiveIn A Z p) (hx : p.head? = some x) (hy : p.getLast? = some y) :
    ∃ q, b.IsPath x y q ∧ b.ActiveIn A Z q := by
  classical
  induction hlen : p.length using Nat.strong_induction_on generalizing p with
  | h l ih =>
    by_cases hn : p.Nodup
    · exact ⟨p, ⟨hn, hp.1, hx, hy⟩, hp⟩
    · have hrepeated : ∃ i j : ℕ, ∃ hi : i < p.length, ∃ hj : j < p.length,
          i < j ∧ p[i] = p[j] := by
        rw [List.nodup_iff_injective_getElem] at hn
        simp only [Function.Injective, not_forall] at hn
        obtain ⟨i, j, heq, hne⟩ := hn
        have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
        obtain hij | hji := lt_or_gt_of_ne hne'
        · exact ⟨i.val, j.val, i.isLt, j.isLt, hij, heq⟩
        · exact ⟨j.val, i.val, j.isLt, i.isLt, hji, heq.symm⟩
      obtain ⟨i, j, hi, hj, hij, heq⟩ := hrepeated
      let q := p.take i ++ p.drop j
      have hq : b.ActiveIn A Z q := activeIn_shortcut b hp hij hj heq
      have hshort : q.length < l := by
        simp only [q, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hi.le]
        omega
      have hxq : q.head? = some x := by
        dsimp [q]
        by_cases hi0 : i = 0
        · subst i
          rw [List.take_zero, List.nil_append, List.head?_drop,
            List.getElem?_eq_getElem hj, ← heq]
          simpa only [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] using hx
        · rw [List.head?_append, List.head?_take, ite_eq_right hi0, hx]
          rfl
      have hyq : q.getLast? = some y := by
        dsimp [q]
        rw [List.getLast?_append, List.getLast?_drop, ite_eq_right (Nat.not_le_of_lt hj), hy]
        rfl
      exact ih q.length hshort hq hxq hyq rfl

private lemma dSepIn_mono {A A' X X' Y Y' Z Z' : Finset (Fin n)} (hA : A' ⊆ A) (hZ' : Z' ⊆ Z)
    (hZ : ∀ m ∈ A', m ∈ Z → m ∈ Z') (hX : X' ⊆ X) (hY : Y' ⊆ Y) (h : b.DSepIn A X Y Z) :
    b.DSepIn A' X' Y' Z' :=
  fun x hx y hy p hp ha => h x (hX hx) y (hY hy) p hp (b.activeIn_mono hA hZ' hZ ha)

private lemma dSepIn_symm {A X Y Z : Finset (Fin n)} (h : b.DSepIn A X Y Z) :
    b.DSepIn A Y X Z :=
  fun y hy x hx p hp ha => h x hx y hy p.reverse (b.isPath_reverse hp) (b.activeIn_reverse ha)

/-- d-separation forces disjointness: a node of `X ∩ Y` is a one-node active path. -/
private lemma dSepIn_disjoint {A X Y Z : Finset (Fin n)} (hX : X ⊆ A) (h : b.DSepIn A X Y Z) :
    Disjoint X Y :=
  Finset.disjoint_left.2 fun x hx hy => h x hx x hy [x]
    ⟨List.nodup_singleton x, List.isChain_singleton x, rfl, rfl⟩
    ⟨List.isChain_singleton x, fun v hv => by
      rw [List.mem_singleton] at hv; exact hv ▸ hX hx,
      fun i hi => by simp at hi⟩

/-- The step of the global Markov property removing a sink `s ∈ X`. -/
private lemma dSepIn_erase_of_mem {A X Y Z Ps : Finset (Fin n)} {s : Fin n} (hs : s ∈ A)
    (hch : ∀ j ∈ A, ¬b.Edge s j) (hsX : s ∈ X) (hPs : ∀ i ∈ Ps, b.Edge i s ∧ i ∉ Z)
    (h : b.DSepIn A X Y Z) : b.DSepIn (A.erase s) (X.erase s ∪ Ps) Y Z := by
  intro x hx y hy p hp ha
  have ha' := b.activeIn_mono (erase_subset s A) subset_rfl (fun _ _ h => h) ha
  rcases mem_union.1 hx with hx | hx
  · exact h x (mem_of_mem_erase hx) y hy p hp ha'
  obtain ⟨hxs, hxZ⟩ := hPs x hx
  obtain ⟨hnd, hch', hhead, hlast⟩ := hp
  cases p with
  | nil => simp at hhead
  | cons x0 rest =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hsp : s ∉ x0 :: rest := fun hm => by simpa using ha.2.1 s hm
    have hxA : x0 ∈ A := mem_of_mem_erase (ha.2.1 x0 (by simp))
    refine h s hsX y hy (s :: x0 :: rest) ⟨List.nodup_cons.2 ⟨hsp, hnd⟩,
      List.IsChain.cons_cons (Or.inr hxs) hch', rfl, by simpa using hlast⟩
      (b.activeIn_cons ha' hs (Or.inr hxs) fun _ hb => ?_)
    rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
    exacts [hch x0 hxA h1, hxZ h2]

/-- The step of the global Markov property removing a sink `s ∈ Z`: one side absorbs all the
parents of `s` outside `Z`. -/
private lemma dSepIn_erase_of_mem_cond {A X Y Z Ps : Finset (Fin n)} {s : Fin n} (hs : s ∈ A)
    (hch : ∀ j ∈ A, ¬b.Edge s j) (hsZ : s ∈ Z) (hPsA : Ps ⊆ A)
    (hPs : ∀ i ∈ Ps, b.Edge i s ∧ i ∉ Z) (h : b.DSepIn A X Y Z) :
    b.DSepIn (A.erase s) (X ∪ Ps) Y (Z.erase s) ∨
      b.DSepIn (A.erase s) X (Y ∪ Ps) (Z.erase s) := by
  have hmono : ∀ {p}, b.ActiveIn (A.erase s) (Z.erase s) p → b.ActiveIn A Z p := fun ha =>
    b.activeIn_mono (erase_subset s A) (erase_subset s Z)
      (fun m hm hmZ => mem_erase.2 ⟨ne_of_mem_erase hm, hmZ⟩) ha
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  simp only [DSepIn, not_forall] at h1 h2
  obtain ⟨u, hu, y, hy, π, hπ, hπa, -⟩ := h1
  rcases mem_union.1 hu with hu | hu
  · exact h u hu y hy π hπ (hmono hπa)
  obtain ⟨x, hx, w, hw, σ, hσ, hσa, -⟩ := h2
  rcases mem_union.1 hw with hw | hw
  · exact h x hx w hw σ hσ (hmono hσa)
  obtain ⟨hus, huZ⟩ := hPs u hu
  obtain ⟨hws, hwZ⟩ := hPs w hw
  have hσA := hmono hσa
  have hπA := hmono hπa
  obtain ⟨-, -, hσh, hσl⟩ := hσ
  obtain ⟨-, -, hπh, hπl⟩ := hπ
  -- the walk `σ ++ s :: π`
  have hrev : b.ActiveIn A Z (s :: σ.reverse) := by
    have hr : σ.reverse.head? = some w := by simpa using hσl
    have hσr := b.activeIn_reverse hσA
    cases hσ' : σ.reverse with
    | nil => simp [hσ'] at hr
    | cons w' t =>
      rw [hσ'] at hr hσr
      simp only [List.head?_cons, Option.some.injEq] at hr
      subst hr
      refine b.activeIn_cons hσr hs (Or.inr hws) fun _ hb => ?_
      rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
      exacts [hch w' (hPsA hw) h1, hwZ h2]
  have h1' : b.ActiveIn A Z (σ ++ [s]) := by simpa using b.activeIn_reverse hrev
  have h2' : b.ActiveIn A Z (s :: π) := by
    cases π with
    | nil => simp at hπh
    | cons u' t =>
      simp only [List.head?_cons, Option.some.injEq] at hπh
      subst hπh
      refine b.activeIn_cons hπA hs (Or.inr hus) fun _ hb => ?_
      rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
      exacts [hch u' (hPsA hu) h1, huZ h2]
  have hW := b.activeIn_append h1' h2' fun u' w' hu' hw' hb => by
    rw [hσl, Option.some.injEq] at hu'
    rw [hπh, Option.some.injEq] at hw'
    subst hu' hw'
    rcases hb with ⟨-, -, h3⟩ | ⟨h3, -⟩
    exacts [h3 s .refl hsZ, h3 ⟨hws, hus⟩]
  have hWh : (σ ++ s :: π).head? = some x := by
    cases σ with
    | nil => simp at hσh
    | cons a l => simpa using hσh
  have hWl : (σ ++ s :: π).getLast? = some y := by
    cases π with
    | nil => simp at hπl
    | cons a l => simpa [List.getLast?_append] using hπl
  obtain ⟨q, hq, hqa⟩ := b.exists_path_of_activeIn hW hWh hWl
  exact h x hx y hy q hq hqa

end Graph

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)


/-- The product of the tables of the nodes in `A`, with the uniform distribution on the other
nodes. For an ancestral `A` it has the same marginals on `A` as the joint
(`marginal_joint_eq_ancProd`). -/
noncomputable def ancProd [Fintype α] (A : Finset (Fin n)) (x : Fin n → α) : ℝ :=
  ∏ j, if j ∈ A then (b.cpt j (b.paVal j x)).weights (x j) else (Fintype.card α : ℝ)⁻¹

/-- On all nodes, `ancProd` is the joint. -/
theorem ancProd_univ [Fintype α] : b.ancProd univ = b.joint := by
  funext x
  rw [ancProd, joint_eq_prod]
  simp only [mem_univ, ite_true]
  rfl

/-- Removing from `B` a node `s` with no child in `B` does not change the marginals of `ancProd`
on sets not containing `s`: the factor of `s` sums to one either way. -/
private lemma marginal_ancProd_erase [Fintype α] {B : Finset (Fin n)}
    {s : Fin n} (hch : ∀ j ∈ B, ¬b.Edge s j) {S : Finset (Fin n)} (hsS : s ∉ S)
    (x' : Fin n → α) :
    marginal (b.ancProd B) ↑S x' = marginal (b.ancProd (B.erase s)) ↑S x' := by
  classical
  simp only [marginal_coe]
  rw [sum_filter, sum_filter, sum_split_at s, sum_split_at s]
  refine sum_congr rfl fun y _ => ?_
  set e := (Equiv.funSplitAt s α).symm with he
  have hcond : ∀ a a', (∀ i ∈ S, e (a, y) i = x' i) ↔ (∀ i ∈ S, e (a', y) i = x' i) := by
    intro a a'
    refine forall₂_congr fun i hi => ?_
    have hi' : i ≠ s := fun h => hsS (h ▸ hi)
    rw [he, funSplitAt_symm_of_ne s a y hi', funSplitAt_symm_of_ne s a' y hi']
  set c : ℝ := (Fintype.card α : ℝ)⁻¹
  have hfac : ∀ (C : Finset (Fin n)) (a : α), b.ancProd C (e (a, y)) =
      (if s ∈ C then (b.cpt s (b.paVal s (e (a, y)))).weights a else c) *
        ∏ j ∈ univ.erase s,
          (if j ∈ C then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c) := by
    intro C a
    rw [ancProd, ← mul_prod_erase univ _ (mem_univ s), he, funSplitAt_symm_self]
  have hrest : ∀ a a', (∏ j ∈ univ.erase s,
      (if j ∈ B then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c)) =
      ∏ j ∈ univ.erase s,
      (if j ∈ B.erase s then (b.cpt j (b.paVal j (e (a', y)))).weights (e (a', y) j) else c) := by
    intro a a'
    refine prod_congr rfl fun j hj => ?_
    have hjs := ne_of_mem_erase hj
    simp only [mem_erase, hjs, ne_eq, not_false_eq_true, true_and]
    split_ifs with hjB
    · have hpa : b.paVal j (e (a, y)) = b.paVal j (e (a', y)) := by
        funext i
        have hi : Fin.castLE j.2.le i ≠ s := by
          intro h
          have hv : (i : Fin j).val = s.val := by simpa using congrArg Fin.val h
          refine hch j hjB ⟨by rw [← hv]; exact i.1.2, ?_⟩
          convert i.2 using 1
          exact Fin.ext hv.symm
        simp only [paVal, he, funSplitAt_symm_of_ne s _ y hi]
      rw [hpa, he, funSplitAt_symm_of_ne s a y hjs, funSplitAt_symm_of_ne s a' y hjs]
    · rfl
  have hpas : ∀ a a', b.paVal s (e (a, y)) = b.paVal s (e (a', y)) := by
    intro a a'
    funext i
    have hi : Fin.castLE s.2.le i ≠ s := fun h => by
      have : (i : Fin s).val = s.val := by simpa using congrArg Fin.val h
      exact absurd this (Nat.ne_of_lt i.1.2)
    simp only [paVal, he, funSplitAt_symm_of_ne s _ y hi]
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  by_cases hc : ∀ i ∈ S, e (a₀, y) i = x' i
  · have hc' : ∀ a, ∀ i ∈ S, e (a, y) i = x' i := fun a => (hcond a a₀).2 hc
    rw [sum_congr rfl fun a _ => ite_eq_left (hc' a), sum_congr rfl fun a _ => ite_eq_left (hc' a)]
    simp_rw [hfac]
    have hsB : s ∉ B.erase s := by simp
    simp only [hsB, ite_false]
    by_cases hsB' : s ∈ B
    · simp only [hsB', ite_true]
      have hrest' : ∀ a, (∏ j ∈ univ.erase s,
          (if j ∈ B.erase s then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j)
            else c)) = ∏ j ∈ univ.erase s,
          (if j ∈ B.erase s then (b.cpt j (b.paVal j (e (a₀, y)))).weights (e (a₀, y) j)
            else c) := fun a => (hrest a₀ a).symm.trans (hrest a₀ a₀)
      simp_rw [hrest _ a₀, hpas _ a₀]
      rw [← sum_mul, (b.cpt s _).total_of_fintype, one_mul,
        sum_congr rfl fun a _ => congrArg (c * ·) (hrest' a), sum_const, card_univ, nsmul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]
    · have hBe : B.erase s = B := erase_eq_of_notMem hsB'
      simp only [hsB', ite_false, hBe]
  · have hc' : ∀ a, ¬∀ i ∈ S, e (a, y) i = x' i := fun a h => hc ((hcond a a₀).1 h)
    rw [sum_congr rfl fun a _ => ite_eq_right (hc' a),
      sum_congr rfl fun a _ => ite_eq_right (hc' a)]

/-- Fixing in addition the value of a node `s ∈ A` with no child in `A`, whose parents are in
`S`, multiplies the marginal by the table of `s`. -/
private lemma marginal_ancProd_insert [Fintype α] {A : Finset (Fin n)}
    {s : Fin n} (hs : s ∈ A) (hch : ∀ j ∈ A, ¬b.Edge s j) {S : Finset (Fin n)} (hsS : s ∉ S)
    (hpa : ∀ i, b.Edge i s → i ∈ S) (x' : Fin n → α) :
    marginal (b.ancProd A) ↑(insert s S) x' =
      (b.cpt s (b.paVal s x')).weights (x' s) * marginal (b.ancProd (A.erase s)) ↑S x' := by
  classical
  simp only [marginal_coe]
  rw [sum_filter, sum_filter, sum_split_at s, sum_split_at s, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  set e := (Equiv.funSplitAt s α).symm with he
  have hcond : ∀ a a', (∀ i ∈ S, e (a, y) i = x' i) ↔ (∀ i ∈ S, e (a', y) i = x' i) := by
    intro a a'
    refine forall₂_congr fun i hi => ?_
    have hi' : i ≠ s := fun h => hsS (h ▸ hi)
    rw [he, funSplitAt_symm_of_ne s a y hi', funSplitAt_symm_of_ne s a' y hi']
  set c : ℝ := (Fintype.card α : ℝ)⁻¹
  have hfac : ∀ (C : Finset (Fin n)) (a : α), b.ancProd C (e (a, y)) =
      (if s ∈ C then (b.cpt s (b.paVal s (e (a, y)))).weights a else c) *
        ∏ j ∈ univ.erase s,
          (if j ∈ C then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c) := by
    intro C a
    rw [ancProd, ← mul_prod_erase univ _ (mem_univ s), he, funSplitAt_symm_self]
  have hrest : ∀ a a', (∏ j ∈ univ.erase s,
      (if j ∈ A then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c)) =
      ∏ j ∈ univ.erase s,
      (if j ∈ A.erase s then (b.cpt j (b.paVal j (e (a', y)))).weights (e (a', y) j) else c) := by
    intro a a'
    refine prod_congr rfl fun j hj => ?_
    have hjs := ne_of_mem_erase hj
    simp only [mem_erase, hjs, ne_eq, not_false_eq_true, true_and]
    split_ifs with hjB
    · have hpa : b.paVal j (e (a, y)) = b.paVal j (e (a', y)) := by
        funext i
        have hi : Fin.castLE j.2.le i ≠ s := by
          intro h
          have hv : (i : Fin j).val = s.val := by simpa using congrArg Fin.val h
          refine hch j hjB ⟨by rw [← hv]; exact i.1.2, ?_⟩
          convert i.2 using 1
          exact Fin.ext hv.symm
        simp only [paVal, he, funSplitAt_symm_of_ne s _ y hi]
      rw [hpa, he, funSplitAt_symm_of_ne s a y hjs, funSplitAt_symm_of_ne s a' y hjs]
    · rfl
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  have hrest' : ∀ a, (∏ j ∈ univ.erase s,
      (if j ∈ A.erase s then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j)
        else c)) = ∏ j ∈ univ.erase s,
      (if j ∈ A.erase s then (b.cpt j (b.paVal j (e (a₀, y)))).weights (e (a₀, y) j)
        else c) := fun a => (hrest a₀ a).symm.trans (hrest a₀ a₀)
  by_cases hc : ∀ i ∈ S, e (a₀, y) i = x' i
  · have hc' : ∀ a, ∀ i ∈ S, e (a, y) i = x' i := fun a => (hcond a a₀).2 hc
    have hins : ∀ a, (∀ i ∈ insert s S, e (a, y) i = x' i) ↔ a = x' s := by
      intro a
      rw [forall_mem_insert, he, funSplitAt_symm_self]
      exact ⟨fun h => h.1, fun h => ⟨h, hc' a⟩⟩
    simp_rw [hins]
    rw [sum_ite_eq' univ (x' s), ite_eq_left (mem_univ _)]
    rw [sum_congr rfl fun a _ => ite_eq_left (hc' a)]
    simp_rw [hfac]
    have hsA : s ∉ A.erase s := by simp
    simp only [hs, hsA, ite_true, ite_false]
    have hpas : b.paVal s (e (x' s, y)) = b.paVal s x' := by
      funext i
      have hi : Fin.castLE s.2.le i ∈ S := hpa _ ⟨by simp, by simp⟩
      exact hc' (x' s) _ hi
    rw [hpas, hrest (x' s) a₀,
      sum_congr rfl fun a _ => congrArg (c * ·) (hrest' a), sum_const, card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [← mul_assoc (Fintype.card α : ℝ) c,
      mul_inv_cancel₀ hcard, one_mul]
  · have hc' : ∀ a, ¬∀ i ∈ S, e (a, y) i = x' i := fun a h => hc ((hcond a a₀).1 h)
    have hins : ∀ a, ¬∀ i ∈ insert s S, e (a, y) i = x' i := fun a h =>
      hc' a fun i hi => h i (mem_insert_of_mem hi)
    rw [sum_congr rfl fun a _ => ite_eq_right (hins a),
      sum_congr rfl fun a _ => ite_eq_right (hc' a)]
    simp

/-- One-node step of the global Markov property: if `B ⫫ Y | Z` for the tables on `A.erase s`
and the parents of `s` lie in `B ∪ Z`, then `insert s B ⫫ Y | Z` for the tables on `A`. -/
private lemma condIndep_ancProd_insert [Fintype α] {A : Finset (Fin n)}
    {s : Fin n} (hs : s ∈ A) (hch : ∀ j ∈ A, ¬b.Edge s j) {B Y Z : Finset (Fin n)}
    (hsB : s ∉ B) (hsY : s ∉ Y) (hsZ : s ∉ Z) (hpa : ∀ i, b.Edge i s → i ∈ B ∪ Z)
    (h : CondIndep (b.ancProd (A.erase s)) ↑B ↑Y ↑Z) :
    CondIndep (b.ancProd A) ↑(insert s B) ↑Y ↑Z := by
  classical
  rw [condIndep_coe_iff] at h ⊢
  intro x'
  have h1 : s ∉ B ∪ Y ∪ Z := by simp [hsB, hsY, hsZ]
  have h2 : s ∉ B ∪ Z := by simp [hsB, hsZ]
  have h3 : s ∉ Y ∪ Z := by simp [hsY, hsZ]
  rw [insert_union, insert_union, insert_union,
    marginal_ancProd_insert b hs hch h1 (fun i hi => by
      rcases mem_union.1 (hpa i hi) with h | h <;> simp [h]) x',
    marginal_ancProd_insert b hs hch h2 hpa x',
    marginal_ancProd_erase b hch hsZ x', marginal_ancProd_erase b hch h3 x']
  have := h x'
  linear_combination (b.cpt s (b.paVal s x')).weights (x' s) * this

/-- **The law of an ancestral set depends only on its tables**: for an ancestral set `A` and
`S ⊆ A`, the marginals of the joint on `S` are those of `ancProd A`. -/
theorem marginal_joint_eq_ancProd [Fintype α] {A : Finset (Fin n)}
    (hA : b.IsAncestral A) {S : Finset (Fin n)} (hS : S ⊆ A) (x' : Fin n → α) :
    marginal b.joint ↑S x' = marginal (b.ancProd A) ↑S x' := by
  classical
  have key : ∀ m : ℕ, ∀ B : Finset (Fin n), A ⊆ B → (B \ A).card = m →
      marginal (b.ancProd B) ↑S x' = marginal (b.ancProd A) ↑S x' := by
    intro m
    induction m with
    | zero =>
      intro B hAB hc
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hc
      rw [subset_antisymm hc hAB]
    | succ m ih =>
      intro B hAB hc
      have hne : (B \ A).Nonempty := by rw [← card_pos, hc]; omega
      have hsBA : (B \ A).max' hne ∈ B \ A := max'_mem _ _
      set s := (B \ A).max' hne
      have hsA : s ∉ A := (mem_sdiff.1 hsBA).2
      have hch : ∀ j ∈ B, ¬b.Edge s j := by
        intro j hj hE
        by_cases hjA : j ∈ A
        · exact hsA (hA hE hjA)
        · have h1 : j ≤ s := le_max' _ j (mem_sdiff.2 ⟨hj, hjA⟩)
          obtain ⟨hlt, _⟩ := hE
          exact absurd h1 (not_le.2 hlt)
      rw [marginal_ancProd_erase b hch (fun h => hsA (hS h)) x']
      refine ih (B.erase s) (fun i hi => mem_erase.2 ⟨fun h => hsA (h ▸ hi), hAB hi⟩) ?_
      rw [erase_sdiff_comm, card_erase_of_mem hsBA, hc]
      rfl
  rw [← b.ancProd_univ]
  exact key _ univ (subset_univ A) rfl

/-- The global Markov property for the product of the tables on an ancestral set. -/
private theorem condIndep_ancProd [Fintype α] (A : Finset (Fin n))
    (hA : b.IsAncestral A) (X Y Z : Finset (Fin n)) (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (h : b.DSepIn A X Y Z) : CondIndep (b.ancProd A) ↑X ↑Y ↑Z := by
  classical
  suffices key : ∀ (m : ℕ) (A : Finset (Fin n)), A.card = m → b.IsAncestral A →
      ∀ X Y Z : Finset (Fin n), X ⊆ A → Y ⊆ A → Z ⊆ A → Disjoint X Z → Disjoint Y Z →
        b.DSepIn A X Y Z → CondIndep (b.ancProd A) ↑X ↑Y ↑Z by
    have hc := key _ A rfl hA (X \ Z) (Y \ Z) Z (sdiff_subset.trans hX) (sdiff_subset.trans hY)
      hZ disjoint_sdiff_self_left disjoint_sdiff_self_left
      (b.dSepIn_mono subset_rfl subset_rfl (fun _ _ h => h) sdiff_subset sdiff_subset h)
    rw [condIndep_coe_iff] at hc ⊢
    intro x'
    have e1 : X \ Z ∪ Y \ Z ∪ Z = X ∪ Y ∪ Z := by
      ext i; simp only [mem_union, mem_sdiff]; tauto
    have := hc x'
    rwa [e1, sdiff_union_self_eq_union, sdiff_union_self_eq_union] at this
  intro m
  induction m with
  | zero =>
    intro A hcard _ X Y Z hX hY hZ _ _ _
    rw [card_eq_zero] at hcard
    subst hcard
    rw [subset_empty] at hX hY hZ
    subst hX hY hZ
    intro x'
    simp
  | succ m ih =>
    intro A hcard hA X Y Z hX hY hZ hXZ hYZ h
    classical
    have hne : A.Nonempty := by rw [← card_pos, hcard]; omega
    have hs : A.max' hne ∈ A := max'_mem A hne
    set s := A.max' hne
    have hch : ∀ j ∈ A, ¬b.Edge s j := fun j hj hE =>
      absurd (le_max' A j hj) (not_le.2 (Fin.lt_def.2 hE.1))
    have hA' : b.IsAncestral (A.erase s) := fun i j hE hj =>
      mem_erase.2 ⟨fun hi => hch j (mem_of_mem_erase hj) (hi ▸ hE), hA hE (mem_of_mem_erase hj)⟩
    have hcard' : (A.erase s).card = m := by rw [card_erase_of_mem hs, hcard]; rfl
    have IH := ih (A.erase s) hcard' hA'
    have hsub : ∀ T ⊆ A, s ∉ T → T ⊆ A.erase s := fun T hT hsT i hi =>
      mem_erase.2 ⟨fun h => hsT (h ▸ hi), hT hi⟩
    have hnn : ∀ x, 0 ≤ b.ancProd A x := fun x => prod_nonneg fun j _ => by
      split_ifs
      · exact (b.cpt j _).nonneg _
      · positivity
    have hss : ¬b.Edge s s := fun hE => lt_irrefl _ hE.1
    set Ps := univ.filter fun i => b.Edge i s ∧ i ∉ Z with hPsdef
    have hPs : ∀ i ∈ Ps, b.Edge i s ∧ i ∉ Z := fun i hi => (mem_filter.1 hi).2
    have hPsA : Ps ⊆ A.erase s := fun i hi => mem_erase.2
      ⟨fun h => hss (h ▸ (hPs i hi).1), hA (hPs i hi).1 hs⟩
    have hsPs : s ∉ Ps := fun h => hss (hPs s h).1
    have hpa : ∀ i, b.Edge i s → i ∈ Ps ∪ Z := fun i hi => by
      by_cases hiZ : i ∈ Z
      · exact mem_union_right _ hiZ
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hi, hiZ⟩)
    -- the case of a sink in the first set
    have caseX : ∀ X Y : Finset (Fin n), X ⊆ A → Y ⊆ A → Disjoint X Z → Disjoint Y Z →
        b.DSepIn A X Y Z → s ∈ X → CondIndep (b.ancProd A) ↑X ↑Y ↑Z := by
      intro X Y hX hY hXZ hYZ h hsX
      have hsZ : s ∉ Z := disjoint_left.1 hXZ hsX
      have hsY : s ∉ Y := disjoint_left.1 (b.dSepIn_disjoint hX h) hsX
      have hB : b.DSepIn (A.erase s) (X.erase s ∪ Ps) Y Z :=
        b.dSepIn_erase_of_mem hs hch hsX hPs h
      have hBA : X.erase s ∪ Ps ⊆ A.erase s := union_subset (erase_subset_erase s hX) hPsA
      have hBZ : Disjoint (X.erase s ∪ Ps) Z := disjoint_union_left.2
        ⟨hXZ.mono_left (erase_subset s X), disjoint_left.2 fun i hi hiZ => (hPs i hi).2 hiZ⟩
      have hci := IH _ Y Z hBA (hsub Y hY hsY) (hsub Z hZ hsZ) hBZ hYZ hB
      have hsB : s ∉ X.erase s ∪ Ps := by simp [hsPs]
      have h2 := b.condIndep_ancProd_insert hs hch hsB hsY hsZ (fun i hi => by
        rcases mem_union.1 (hpa i hi) with h' | h'
        · exact mem_union_left _ (mem_union_right _ h')
        · exact mem_union_right _ h') hci
      refine condIndep_mono_left h2 (fun i hi => ?_)
        (disjoint_insert_left.2 ⟨hsY, b.dSepIn_disjoint hBA hB⟩)
      by_cases his : i = s
      · exact his ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (mem_erase.2 ⟨his, hi⟩))
    by_cases hsX : s ∈ X
    · exact caseX X Y hX hY hXZ hYZ h hsX
    by_cases hsY : s ∈ Y
    · exact condIndep_symm (caseX Y X hY hX hYZ hXZ (b.dSepIn_symm h) hsY)
    by_cases hsZ : s ∈ Z
    · have caseZ : ∀ X Y : Finset (Fin n), X ⊆ A → Y ⊆ A → s ∉ X → s ∉ Y → Disjoint X Z →
          Disjoint Y Z → b.DSepIn (A.erase s) (X ∪ Ps) Y (Z.erase s) →
          CondIndep (b.ancProd A) ↑X ↑Y ↑Z := by
        intro X Y hX hY hsX hsY hXZ hYZ hd
        have hXPA : X ∪ Ps ⊆ A.erase s := union_subset (hsub X hX hsX) hPsA
        have hXPZ : Disjoint (X ∪ Ps) (Z.erase s) := by
          refine disjoint_left.2 fun i hi hiZ => ?_
          rcases mem_union.1 hi with hi | hi
          · exact disjoint_left.1 hXZ hi (mem_of_mem_erase hiZ)
          · exact (hPs i hi).2 (mem_of_mem_erase hiZ)
        have hci := IH (X ∪ Ps) Y (Z.erase s) hXPA (hsub Y hY hsY) (erase_subset_erase s hZ) hXPZ
          (hYZ.mono_right (erase_subset s Z)) hd
        have hsXP : s ∉ X ∪ Ps := by simp [hsX, hsPs]
        have h2 := b.condIndep_ancProd_insert hs hch hsXP hsY (by simp) (fun i hi => by
          rcases mem_union.1 (hpa i hi) with h' | h'
          · exact mem_union_left _ (mem_union_right _ h')
          · exact mem_union_right _ (mem_erase.2 ⟨fun h => hss (h ▸ hi), h'⟩)) hci
        have hdXY : Disjoint (insert s (X ∪ Ps)) Y :=
          disjoint_insert_left.2 ⟨hsY, b.dSepIn_disjoint hXPA hd⟩
        have hsub' : X ∪ {s} ⊆ insert s (X ∪ Ps) := fun i hi => by
          rcases mem_union.1 hi with hi | hi
          · exact mem_insert_of_mem (mem_union_left _ hi)
          · rw [mem_singleton.1 hi]; exact mem_insert_self _ _
        have h4 := condIndep_weak_union hnn (condIndep_mono_left h2 hsub' hdXY)
          (hdXY.mono_left hsub')
        have hZe : Z.erase s ∪ {s} = Z := by
          ext i
          by_cases his : i = s
          · subst his; simp [hsZ]
          · simp [his]
        rwa [hZe] at h4
      rcases b.dSepIn_erase_of_mem_cond hs hch hsZ (hPsA.trans (erase_subset s A)) hPs h with
        hd | hd
      · exact caseZ X Y hX hY hsX hsY hXZ hYZ hd
      · exact condIndep_symm (caseZ Y X hY hX hsY hsX hYZ hXZ (b.dSepIn_symm hd))
    · have hci := IH X Y Z (hsub X hX hsX) (hsub Y hY hsY) (hsub Z hZ hsZ) hXZ hYZ
        (b.dSepIn_mono (erase_subset s A) subset_rfl (fun _ _ h => h) subset_rfl subset_rfl h)
      rw [condIndep_coe_iff] at hci ⊢
      intro x'
      have h1 : s ∉ X ∪ Y ∪ Z := by simp [hsX, hsY, hsZ]
      have h2 : s ∉ X ∪ Z := by simp [hsX, hsZ]
      have h3 : s ∉ Y ∪ Z := by simp [hsY, hsZ]
      rw [marginal_ancProd_erase b hch h1, marginal_ancProd_erase b hch h2,
        marginal_ancProd_erase b hch h3, marginal_ancProd_erase b hch hsZ]
      exact hci x'

/-- The global Markov property for `Finset`s of nodes; `condIndep_of_dSeparated` is the
statement for arbitrary sets of nodes. -/
theorem condIndep_of_dSeparated_finset [Fintype α] {X Y Z : Finset (Fin n)}
    (h : b.DSeparated (X : Set (Fin n)) (Y : Set (Fin n)) (Z : Set (Fin n))) :
    CondIndep b.joint ↑X ↑Y ↑Z := by
  classical
  have hdesc : ∀ {i j : Fin n}, b.DescIn univ i j → b.IsDescendant i j := by
    intro i j hij
    unfold DescIn at hij
    induction hij with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail hst.1
  have hd : b.DSepIn univ X Y Z := fun x hx y hy p hp ha => by
    obtain ⟨i, hi, hb⟩ := h x hx y hy p hp
    refine ha.2.2 i hi ?_
    rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, fun d hd hdZ => h3 d (hdesc hd) (mem_coe.2 hdZ)⟩
    · exact Or.inr ⟨h1, mem_coe.1 h2⟩
  rw [← b.ancProd_univ]
  exact b.condIndep_ancProd univ (fun _ _ _ _ => mem_univ _) X Y Z (subset_univ _)
    (subset_univ _) (subset_univ _) hd

/-- **The global Markov property** (soundness of d-separation: Geiger, Verma & Pearl 1990;
Lauritzen, Dawid, Larsen & Leimer 1990): if `Z` d-separates `X` from `Y` in the graph of a
Bayesian network, then `X` and `Y` are conditionally independent given `Z` under its joint
law. No disjointness of `X`, `Y`, `Z` is needed. -/
theorem condIndep_of_dSeparated [Fintype α] {X Y Z : Set (Fin n)} (h : b.DSeparated X Y Z) :
    CondIndep b.joint X Y Z := by
  classical
  have := b.condIndep_of_dSeparated_finset (X := X.toFinset) (Y := Y.toFinset)
    (Z := Z.toFinset) (by simpa only [Set.coe_toFinset] using h)
  simpa only [Set.coe_toFinset] using this

end BayesNet

end Cslib.MachineLearning.GraphicalModels
end
-- ===== end atlas-src/CSLibExt/MachineLearning/GraphicalModels/GlobalMarkov.lean =====

-- ===== begin atlas-src/CSLibExt/MachineLearning/GraphicalModels/CausalAdjustment.lean =====
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



/-!
# Back-door and front-door adjustment

Graphical identification of causal effects in a causal Bayesian network (`BayesNet`, nodes in a
topological order, finite state space; the intervention `do(X_k = a)` is `BayesNet.intervene`).
The proofs combine the truncated factorization with the global Markov property
(`BayesNet.condIndep_of_dSeparated`) applied to networks with the arrows into the intervened
nodes removed.

## Main definitions

* `BayesNet.mutilateSet b W w`: the network of the intervention `do(X_W = w)` on a set `W` of
  nodes, with the arrows into `W` removed.

## Main results

* `BayesNet.joint_mutilateSet`: the truncated factorization for a set of nodes.
* `BayesNet.marginal_intervene_of_not_isDescendant`: an intervention does not change the law of the
  non-descendants of the intervened node.
* `BayesNet.backdoor_adjustment`: **the back-door adjustment** (Pearl 1995; Pearl 2009,
  Theorem 3.3.2): if `Z` contains no descendant of `k` and blocks every path from `k` to `y`
  that begins with an arrow into `k`, then
  `P(X_y = v | do(X_k = a)) = ∑_z P(Z = z) P(X_y = v | X_k = a, Z = z)`, assuming
  `P(X_k = a, Z = z) > 0` whenever `P(Z = z) > 0`. The adjustment set may contain nodes after
  `k` in the topological order.
* `BayesNet.frontdoor_adjustment`: **the front-door adjustment** (Pearl 1995; Pearl 2009,
  Theorem 3.3.4): if `M` intercepts every directed path from `k` to `y`, every path from `k` to
  a node of `M` beginning with an arrow into `k` is blocked by `∅`, and every path from a node
  of `M` to `y` beginning with an arrow into that node is blocked by `{k}`, then
  `P(X_y = v | do(X_k = a))` equals
  `∑_m P(M = m | X_k = a) ∑_{a'} P(X_y = v | X_k = a', M = m) P(X_k = a')`, assuming
  `P(X_k = a', M = m) > 0` for all `a'` and `m`.

Both formulas are stated for a single outcome node. The three rules of the do-calculus (Pearl
1995; Pearl 2009, Theorem 3.4.1) are not covered.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §3.2–3.3.
-/

section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity MetaMathlibExt.FiniteWeight

variable {α : Type*}

/-- The assignment equal to `t` on `T` and to `x'` elsewhere. -/
private def fill {n : ℕ} (T : Finset (Fin n)) (x' : Fin n → α) (t : T → α) : Fin n → α :=
  fun i => if h : i ∈ T then t ⟨i, h⟩ else x' i

/-- Splitting a sum against `P` by the values `t` of the variables in `T` (disjoint from the
fixed set `S`), for a weight `g` depending only on the variables in `T ∪ S`. -/
private lemma sum_filter_mul_eq_sum_marginal {n : ℕ} [Fintype α] [DecidableEq α]
    (P : (Fin n → α) → ℝ) {S T : Finset (Fin n)} (hTS : Disjoint T S) (x' : Fin n → α)
    (g : (Fin n → α) → ℝ) (hg : ∀ x y, (∀ i ∈ T ∪ S, x i = y i) → g x = g y) :
    ∑ x with ∀ i ∈ S, x i = x' i, P x * g x =
      ∑ t : T → α, g (fill T x' t) * marginal P ↑(T ∪ S) (fill T x' t) := by
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => ∀ i ∈ S, x i = x' i)
    (fun x => fun i : T => x i)]
  refine sum_congr rfl fun t _ => ?_
  rw [filter_filter, marginal_coe, mul_sum]
  have hiff : ∀ x : Fin n → α, ((∀ i ∈ S, x i = x' i) ∧ (fun i : T => x i) = t) ↔
      ∀ i ∈ T ∪ S, x i = fill T x' t i := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hiT : i ∈ T
      · simp only [fill, hiT, dite_true]
        exact congrFun h2 ⟨i, hiT⟩
      · simp only [fill, hiT, dite_false]
        exact h1 i ((mem_union.1 hi).resolve_left hiT)
    · intro h
      refine ⟨fun i hi => ?_, funext fun i => ?_⟩
      · have hiT : i ∉ T := fun hiT => disjoint_left.1 hTS hiT hi
        rw [h i (mem_union_right _ hi)]
        simp [fill, hiT]
      · rw [h i (mem_union_left _ i.2)]
        simp [fill]
  refine sum_congr (filter_congr fun x _ => hiff x) fun x hx => ?_
  rw [mul_comm, hg x (fill T x' t) (mem_filter.1 hx).2]

namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-! ### Interventions on a set of nodes -/

/-- The network of the intervention `do(X_W = w)` with the arrows into `W` removed: every node
`j ∈ W` has no parents and the point mass at `w j` as its table. -/
noncomputable def mutilateSet (W : Finset (Fin n)) (w : Fin n → α) : BayesNet α n where
  pa j := if j ∈ W then ∅ else b.pa j
  cpt j z := if h : j ∈ W then StdSimplex.single (w j) else
    b.cpt j fun i => z ⟨i, by simp [h]⟩

/-- **The truncated factorization for a set of nodes**: after `do(X_W = w)`, the joint is the
product of the tables of the nodes outside `W` on assignments agreeing with `w` on `W`. -/
theorem joint_mutilateSet [DecidableEq α] (W : Finset (Fin n)) (w x : Fin n → α) :
    (b.mutilateSet W w).joint x = ∏ j, if j ∈ W then (if x j = w j then 1 else 0)
      else (b.cpt j (b.paVal j x)).weights (x j) := by
  rw [joint_eq_prod]
  refine prod_congr rfl fun j _ => ?_
  by_cases h : j ∈ W
  · simp only [mutilateSet, h, dite_true, ite_true]
    by_cases hx : x j = w j
    · simp [StdSimplex.single, hx]
    · simp [StdSimplex.single, hx]
  · simp only [mutilateSet, h, dite_false, ite_false]
    rfl

omit [Nonempty α] in
/-- The arrows of `b.mutilateSet W w` are those of `b` not pointing into `W`. -/
theorem edge_mutilateSet_iff (W : Finset (Fin n)) (w : Fin n → α) {i j : Fin n} :
    (b.mutilateSet W w).Edge i j ↔ b.Edge i j ∧ j ∉ W := by
  by_cases h : j ∈ W
  · simp [Edge, mutilateSet, h]
  · simp [Edge, mutilateSet, h]

omit [Nonempty α] in
/-- A descendant after removing the arrows into `W` is a descendant in `b`. -/
theorem IsDescendant.of_mutilateSet {W : Finset (Fin n)} {w : Fin n → α} {i j : Fin n}
    (h : (b.mutilateSet W w).IsDescendant i j) : b.IsDescendant i j := by
  unfold IsDescendant at h ⊢
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail ((b.edge_mutilateSet_iff W w).1 hst).1

omit [Nonempty α] in
/-- After removing the arrows into `W`, a node of `W` is a descendant only of itself. -/
theorem eq_of_isDescendant_mutilateSet {W : Finset (Fin n)} {w : Fin n → α} {i j : Fin n}
    (h : (b.mutilateSet W w).IsDescendant i j) (hj : j ∈ W) : i = j := by
  unfold IsDescendant at h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, hc⟩
  · exact h.symm
  · exact absurd hj ((b.edge_mutilateSet_iff W w).1 hc).2

/-- Two networks whose tables agree on an ancestral set (for both graphs) have the same law on
that set. -/
private lemma marginal_eq_of_tables [Fintype α] (b' : BayesNet α n)
    {N : Finset (Fin n)} (hN : b.IsAncestral N) (hN' : b'.IsAncestral N)
    (htab : ∀ j ∈ N, ∀ x, (b.cpt j (b.paVal j x)).weights (x j) =
      (b'.cpt j (b'.paVal j x)).weights (x j))
    {S : Finset (Fin n)} (hS : S ⊆ N) (x' : Fin n → α) :
    marginal b.joint ↑S x' = marginal b'.joint ↑S x' := by
  classical
  rw [marginal_joint_eq_ancProd b hN hS, marginal_joint_eq_ancProd b' hN' hS]
  congr 1
  funext x
  refine prod_congr rfl fun j _ => ?_
  split_ifs with hj
  · exact htab j hj x
  · rfl

omit [Nonempty α] in
/-- d-separation in a network with the arrows into `W` removed, from back-door blocking in
`b`: parents of nodes of `W` are d-separated from `Ys` by `C`. -/
private lemma dSeparated_mutilateSet {W C Zb Ys Ps : Finset (Fin n)} (w : Fin n → α)
    (hWC : W ⊆ C) (hZC : Zb ⊆ C) (hCWZ : C ⊆ W ∪ Zb) (hYW : ∀ y ∈ Ys, y ∉ W)
    (hPs : ∀ p ∈ Ps, p ∉ C ∧ ∃ r ∈ W, b.Edge p r ∧ ∀ y ∈ Ys, ∀ l, b.IsPath r y l →
      (∃ h : 1 < l.length, b.Edge l[1] r) → b.PathBlocked (Zb : Set (Fin n)) l) :
    (b.mutilateSet W w).DSeparated (Ps : Set (Fin n)) (Ys : Set (Fin n)) (C : Set (Fin n)) := by
  intro p hp y hy π hπ
  rw [mem_coe] at hp hy
  obtain ⟨hpC, r, hrW, hpr, hbl⟩ := hPs p hp
  obtain ⟨hnd, hch, hh, hl⟩ := hπ
  cases π with
  | nil => simp at hh
  | cons q rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    by_cases hmeet : ∃ c ∈ q :: rest, c ∈ W
    · obtain ⟨c, hc, hcW⟩ := hmeet
      obtain ⟨t, ht, htc⟩ := List.mem_iff_getElem.1 hc
      cases t with
      | zero =>
        simp only [List.getElem_cons_zero] at htc
        subst htc
        exact absurd (hWC hcW) hpC
      | succ t =>
        have hlast : t + 1 ≠ (q :: rest).length - 1 := by
          intro h
          rw [List.getLast?_eq_getElem?] at hl
          simp only [← h, List.getElem?_eq_getElem ht, Option.some.injEq] at hl
          exact hYW y hy (hl ▸ htc ▸ hcW)
        refine ⟨t, by omega, Or.inr ⟨fun hc' => ?_, ?_⟩⟩
        · exact ((b.edge_mutilateSet_iff W w).1 hc'.1).2 (htc ▸ hcW)
        · rw [mem_coe]
          exact hWC (htc ▸ hcW)
    · simp only [not_exists, not_and] at hmeet
      have hrπ : r ∉ q :: rest := fun h => hmeet r h hrW
      have hpath : b.IsPath r y (r :: q :: rest) := by
        refine ⟨List.nodup_cons.2 ⟨hrπ, hnd⟩, List.IsChain.cons_cons (Or.inr hpr) ?_, rfl, ?_⟩
        · exact hch.imp fun u v huv => huv.imp
            (fun h => ((b.edge_mutilateSet_iff W w).1 h).1)
            (fun h => ((b.edge_mutilateSet_iff W w).1 h).1)
        · simpa using hl
      obtain ⟨i, hi, hb⟩ := hbl y hy _ hpath ⟨by simp, hpr⟩
      cases i with
      | zero =>
        rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
        · exact absurd (h1.1.trans hpr.1) (lt_irrefl _)
        · exact (hpC (hZC (mem_coe.1 h2))).elim
      | succ i =>
        simp only [List.getElem_cons_succ] at hb
        have hm : (q :: rest)[i + 1]'(by simp at hi ⊢; omega) ∉ W :=
          hmeet _ (List.getElem_mem _)
        refine ⟨i, by simp at hi ⊢; omega, ?_⟩
        rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨(b.edge_mutilateSet_iff W w).2 ⟨h1, hm⟩,
            (b.edge_mutilateSet_iff W w).2 ⟨h2, hm⟩, fun d hd hdC => ?_⟩
          rcases mem_union.1 (hCWZ (mem_coe.1 hdC)) with hdW | hdZ
          · exact hm (b.eq_of_isDescendant_mutilateSet hd hdW ▸ hdW)
          · exact h3 d (hd.of_mutilateSet b) (mem_coe.2 hdZ)
        · refine Or.inr ⟨fun hc => h1 ⟨((b.edge_mutilateSet_iff W w).1 hc.1).1,
            ((b.edge_mutilateSet_iff W w).1 hc.2).1⟩, ?_⟩
          rw [mem_coe] at h2 ⊢
          exact hZC h2

omit [Nonempty α] in
/-- Reweighting: if `L = L' · h` on the assignments fixing `C`, with `h` a function of the
variables in `T ∪ C` and `T ⫫ Ys | C` under `L'`, then
`L(Ys, C) L'(C) = L(C) L'(Ys, C)`. -/
private lemma marginal_reweight [Fintype α] {L L' : (Fin n → α) → ℝ}
    {T Ys C : Finset (Fin n)} (hTY : Disjoint T Ys) (hTC : Disjoint T C) (xb : Fin n → α)
    (h : (Fin n → α) → ℝ) (hh : ∀ x y, (∀ i ∈ T ∪ C, x i = y i) → h x = h y)
    (hL : ∀ x, (∀ i ∈ C, x i = xb i) → L x = L' x * h x) (hci : CondIndep L' ↑T ↑Ys ↑C) :
    marginal L ↑(Ys ∪ C) xb * marginal L' ↑C xb = marginal L ↑C xb * marginal L' ↑(Ys ∪ C) xb := by
  classical
  have e : ∀ S, C ⊆ S → Disjoint T S →
      marginal L ↑S xb = ∑ t : T → α, h (fill T xb t) * marginal L' ↑(T ∪ S) (fill T xb t) := by
    intro S hCS hTS
    rw [← sum_filter_mul_eq_sum_marginal L' hTS xb h fun x y hxy => hh x y fun i hi => hxy i
      (by rcases mem_union.1 hi with hi | hi
          · exact mem_union_left _ hi
          · exact mem_union_right _ (hCS hi))]
    simp only [marginal_coe]
    exact sum_congr rfl fun x hx => hL x fun i hi => (mem_filter.1 hx).2 i (hCS hi)
  have agree : ∀ S, Disjoint T S → ∀ t, marginal L' ↑S (fill T xb t) = marginal L' ↑S xb :=
    fun S hS t => marginal_congr_of_eqOn L' S fun i hi => by
      have hi' : i ∉ T := fun h => disjoint_left.1 hS h hi
      simp [fill, hi']
  have hTYC : Disjoint T (Ys ∪ C) := disjoint_union_right.2 ⟨hTY, hTC⟩
  rw [e (Ys ∪ C) subset_union_right hTYC, e C subset_rfl hTC, sum_mul, sum_mul]
  refine sum_congr rfl fun t _ => ?_
  have := condIndep_coe_iff.1 hci (fill T xb t)
  rw [agree C hTC t, agree (Ys ∪ C) hTYC t, union_assoc] at this
  rw [mul_assoc, this, mul_assoc]

omit [Nonempty α] in
private lemma exists_isChain_of_reflTransGen {r : Fin n → Fin n → Prop} {a c : Fin n}
    (h : Relation.ReflTransGen r a c) :
    ∃ l : List (Fin n), (a :: l).IsChain r ∧ (a :: l).getLast? = some c ∧
      ∀ x ∈ l, ∃ u, r u x := by
  induction h with
  | refl => exact ⟨[], .singleton _, rfl, fun x hx => by cases hx⟩
  | @tail b' c' _ hbc ih =>
    obtain ⟨l, h1, h2, h3⟩ := ih
    refine ⟨l ++ [c'], ?_, ?_, ?_⟩
    · rw [← List.cons_append]
      refine h1.append (.singleton _) fun x hx y hy => ?_
      rw [h2] at hx
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
      subst hx hy
      exact hbc
    · rw [show a :: (l ++ [c']) = (a :: l) ++ [c'] from rfl, List.getLast?_append]
      simp
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h3 x hx
      · rw [List.mem_singleton] at hx
        exact ⟨b', hx ▸ hbc⟩

omit [Nonempty α] in
/-- If every directed path from `k` to `y` meets `M`, then `y` is not a descendant of `k` once
the arrows into `M` are removed. -/
private lemma not_isDescendant_mutilateSet {k y : Fin n} {M : Finset (Fin n)} (w : Fin n → α)
    (hkM : k ∉ M)
    (hdir : ∀ p : List (Fin n), p.IsChain b.Edge → p.head? = some k → p.getLast? = some y →
      ∃ m ∈ M, m ∈ p) :
    ¬(b.mutilateSet M w).IsDescendant k y := by
  intro h
  obtain ⟨l, h1, h2, h3⟩ := exists_isChain_of_reflTransGen h
  obtain ⟨m, hm, hml⟩ :=
    hdir (k :: l) (h1.imp fun u v huv => ((b.edge_mutilateSet_iff M w).1 huv).1) rfl h2
  rcases List.mem_cons.1 hml with rfl | hml
  · exact hkM hm
  · obtain ⟨u, hu⟩ := h3 m hml
    exact ((b.edge_mutilateSet_iff M w).1 hu).2 hm

omit [Nonempty α] in
/-- If every path from `k` to `m` beginning with an arrow into `k` is blocked by `∅`, then `k` is
not a descendant of `m`. -/
private lemma not_isDescendant_of_blocked {k m : Fin n} (hkm' : m ≠ k)
    (hkm : ∀ p, b.IsPath k m p → (∃ h : 1 < p.length, b.Edge p[1] k) → b.PathBlocked ∅ p) :
    ¬b.IsDescendant m k := by
  intro h
  obtain ⟨l, h1, h2, -⟩ := exists_isChain_of_reflTransGen h
  have hlt : (m :: l).IsChain (· < ·) := h1.imp fun u v huv => Fin.lt_def.2 huv.1
  have hnd : (m :: l).Nodup := (List.isChain_iff_pairwise.1 hlt).imp ne_of_lt
  have hq : (m :: l).reverse.IsChain fun u v => b.Edge v u := List.isChain_reverse.2 h1
  have hl : l ≠ [] := by
    rintro rfl
    simp only [List.getLast?_singleton, Option.some.injEq] at h2
    exact hkm' h2
  have hlen : 1 < (m :: l).reverse.length := by
    simp only [List.length_reverse, List.length_cons]
    have := List.length_pos_of_ne_nil hl
    omega
  have hhead : (m :: l).reverse.head? = some k := by rw [List.head?_reverse]; exact h2
  have h0 : (m :: l).reverse[0]'(by omega) = k := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some.inj hhead
  have hpath : b.IsPath k m (m :: l).reverse :=
    ⟨List.nodup_reverse.2 hnd, hq.imp fun u v huv => Or.inr huv, hhead,
      by rw [List.getLast?_reverse]; rfl⟩
  have he : b.Edge (m :: l).reverse[1] k := by
    have := List.isChain_iff_getElem.1 hq 0 hlen
    simpa only [h0] using this
  obtain ⟨i, hi, hb⟩ := hkm _ hpath ⟨hlen, he⟩
  rcases hb with ⟨h1', -, -⟩ | ⟨-, h2'⟩
  · have := List.isChain_iff_getElem.1 hq i (by omega)
    exact absurd (h1'.1.trans this.1) (lt_irrefl _)
  · exact h2'

/-- Relating two interventions `do(X_W = w)` and `do(X_{W'} = w)` for `W ⊆ W'` on assignments
agreeing with `w` on `W'`: the larger one drops the tables of `W' \ W`. -/
private lemma joint_mutilateSet_mul {W W' : Finset (Fin n)} (hWW' : W ⊆ W')
    (w : Fin n → α) {x : Fin n → α} (hx : ∀ j ∈ W', x j = w j) :
    (b.mutilateSet W w).joint x = (b.mutilateSet W' w).joint x *
      ∏ j ∈ W' \ W, (b.cpt j (b.paVal j x)).weights (x j) := by
  classical
  rw [joint_mutilateSet, joint_mutilateSet, ← univ_inter (W' \ W), ← prod_ite_mem univ (W' \ W),
    ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ W
  · simp [hj, hWW' hj, hx j (hWW' hj)]
  · by_cases hj' : j ∈ W'
    · simp [hj, hj', hx j hj']
    · simp [hj, hj']

/-- Without intervened nodes, the joint is that of `b`. -/
private lemma joint_mutilateSet_empty (w : Fin n → α) :
    (b.mutilateSet ∅ w).joint = b.joint := by
  classical
  funext x
  rw [joint_mutilateSet, joint_eq_prod]
  simp only [notMem_empty, ite_false]
  rfl

/-- `do(X_k = a)` as an intervention on the set `{k}`. -/
private lemma joint_mutilateSet_singleton {k : Fin n} {w : Fin n → α} {a : α}
    (hw : w k = a) : (b.mutilateSet {k} w).joint = (b.intervene k a).joint := by
  classical
  funext x
  rw [joint_mutilateSet, joint_intervene, ← mul_prod_erase univ _ (mem_univ k)]
  have hrest : ∏ j ∈ univ.erase k, (if j ∈ ({k} : Finset (Fin n)) then
      (if x j = w j then (1 : ℝ) else 0) else (b.cpt j (b.paVal j x)).weights (x j)) =
      ∏ j ∈ univ.erase k, (b.cpt j (b.paVal j x)).weights (x j) :=
    prod_congr rfl fun j hj => by simp [ne_of_mem_erase hj]
  rw [hrest, hw]
  by_cases hx : x k = a <;> simp [hx]

/-- After `do(X_W = w)`, fixing in addition the nodes of `W` at their values `w` does not change
the probability. -/
private lemma marginal_mutilateSet_union [Fintype α] (W : Finset (Fin n))
    (w : Fin n → α) (S : Finset (Fin n)) {x' : Fin n → α} (hx' : ∀ j ∈ W, x' j = w j) :
    marginal (b.mutilateSet W w).joint ↑(S ∪ W) x' = marginal (b.mutilateSet W w).joint ↑S x' := by
  classical
  simp only [marginal_coe]
  symm
  rw [← sum_filter_of_ne (p := fun x => ∀ j ∈ W, x j = w j), filter_filter]
  · refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    simp only [mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact (h2 i hi).trans (hx' i hi).symm
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun j hj => (h j (Or.inr hj)).trans (hx' j hj)⟩
  · intro x _ hx j hj
    by_contra hne
    apply hx
    rw [joint_mutilateSet]
    exact prod_eq_zero (mem_univ j) (by simp [hj, hne])

/-- The joint of `do(X_W = w)` is a probability distribution concentrated on `W = w`. -/
private lemma marginal_mutilateSet_self [Fintype α] (W : Finset (Fin n))
    (w : Fin n → α) {x' : Fin n → α} (hx' : ∀ j ∈ W, x' j = w j) :
    marginal (b.mutilateSet W w).joint ↑W x' = 1 := by
  classical
  have := b.marginal_mutilateSet_union W w ∅ hx'
  rw [empty_union] at this
  rw [this]
  simp only [marginal_coe]
  simp only [notMem_empty, IsEmpty.forall_iff, implies_true, filter_true_of_mem]
  exact (b.mutilateSet W w).sum_joint

/-! ### Interventions on one node -/

/-- After `do(X_k = a)`, assignments with `x k ≠ a` have probability `0`. -/
theorem joint_intervene_eq_zero {k : Fin n} {a : α} {x : Fin n → α}
    (hx : x k ≠ a) : (b.intervene k a).joint x = 0 := by
  classical
  rw [joint_intervene, ite_eq_right hx]

/-- For `x k = a`, `P(x) = P(x | do(X_k = a)) · p_k(a | x_{pa k})`. -/
theorem joint_eq_intervene_mul_cpt {k : Fin n} {a : α} {x : Fin n → α}
    (hx : x k = a) :
    b.joint x = (b.intervene k a).joint x * (b.cpt k (b.paVal k x)).weights a := by
  classical
  rw [joint_intervene, ite_eq_left hx, joint_eq_prod, ← Finset.mul_prod_erase _ _ (mem_univ k),
    mul_comm, hx]
  rfl

/-- **The intervention `do(X_k = a)` does not change the law of the non-descendants of `k`.** -/
theorem marginal_intervene_of_not_isDescendant [Fintype α] (k : Fin n) (a : α)
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, ¬b.IsDescendant k i) (x' : Fin n → α) :
    marginal (b.intervene k a).joint ↑S x' = marginal b.joint ↑S x' := by
  classical
  set N := univ.filter fun j => ¬b.IsDescendant k j
  have hN : b.IsAncestral N := by
    intro i j hE hj
    simp only [N, mem_filter, mem_univ, true_and] at hj ⊢
    exact fun hi => hj (Relation.ReflTransGen.tail hi hE)
  have hN' : (b.intervene k a).IsAncestral N := by
    intro i j hE hj
    refine hN ?_ hj
    obtain ⟨hlt, hm⟩ := hE
    by_cases hjk : j = k
    · subst hjk
      simp [intervene_pa_self] at hm
    · exact ⟨hlt, by rwa [b.intervene_pa_of_ne hjk a] at hm⟩
  refine marginal_eq_of_tables (b.intervene k a) b hN' hN (fun j hj x => ?_)
    (fun i hi => mem_filter.2 ⟨mem_univ _, hS i hi⟩) x'
  have hjk : j ≠ k := fun h => (mem_filter.1 hj).2 (h ▸ .refl)
  simp [intervene, hjk]
  rfl

/-- **The back-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.2): if the
set `Z` contains no descendant of the treatment node `k` and blocks every path between `k` and
the outcome node `y` that begins with an arrow into `k`, then
`P(X_y = v | do(X_k = a)) = ∑_z P(Z = z) P(X_y = v | X_k = a, Z = z)`, assuming
`P(X_k = a, Z = z) > 0` whenever `P(Z = z) > 0`. -/
theorem backdoor_adjustment [Fintype α] [DecidableEq α] (k y : Fin n) (Z : Finset (Fin n))
    (a v : α) (hky : k ≠ y) (hyZ : y ∉ Z) (hdesc : ∀ z ∈ Z, ¬b.IsDescendant k z)
    (hblock : ∀ p, b.IsPath k y p → (∃ h : 1 < p.length, b.Edge p[1] k) →
      b.PathBlocked (Z : Set (Fin n)) p)
    (hpos : ∀ z : Z → α, ∑ x with (fun i : Z => x i) = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x ≠ 0) :
    ∑ x with x y = v, (b.intervene k a).joint x =
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, b.joint x) *
        ((∑ x with x k = a ∧ x y = v ∧ (fun i : Z => x i) = z, b.joint x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x) := by
  classical
  set P := b.joint
  set Q := (b.intervene k a).joint
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => (b.intervene k a).toChain.joint_nonneg n x
  have hkZ : k ∉ Z := fun h => hdesc k h .refl
  set Pk := univ.filter fun i => b.Edge i k ∧ i ∉ Z with hPkdef
  have hPk : ∀ i ∈ Pk, b.Edge i k ∧ i ∉ Z := fun i hi => (mem_filter.1 hi).2
  have hyPk : y ∉ Pk := by
    intro hy
    obtain ⟨i, hi, hb⟩ : b.PathBlocked (Z : Set (Fin n)) [k, y] :=
      hblock [k, y] ⟨by simp [hky], List.IsChain.cons_cons (Or.inr (hPk y hy).1) (.singleton _),
        rfl, rfl⟩ ⟨by simp, (hPk y hy).1⟩
    simp at hi
  have hPkC : Disjoint Pk (insert k Z) := disjoint_left.2 fun p hp hpC => by
    rcases mem_insert.1 hpC with h | h
    · exact lt_irrefl _ (h ▸ (hPk p hp).1).1
    · exact (hPk p hp).2 h
  -- conditional independence once the arrows into `k` are removed
  have hJ : (b.mutilateSet {k} fun _ => a).joint = Q := b.joint_mutilateSet_singleton rfl
  have hci : CondIndep Q ↑Pk ↑({y} : Finset (Fin n)) ↑(insert k Z) := by
    have := (b.mutilateSet {k} fun _ => a).condIndep_of_dSeparated_finset
      (b.dSeparated_mutilateSet (fun _ => a) (W := {k}) (C := insert k Z) (Zb := Z) (Ys := {y})
        (Ps := Pk) (singleton_subset_iff.2 (mem_insert_self _ _)) (subset_insert _ _)
        (insert_eq k Z).subset
        (fun y' hy' h => hky ((mem_singleton.1 h).symm.trans (mem_singleton.1 hy')))
        fun p hp => ⟨disjoint_left.1 hPkC hp, k, mem_singleton_self k, (hPk p hp).1,
          fun y' hy' l hl hE => by rw [mem_singleton] at hy'; subst hy'; exact hblock l hl hE⟩)
    rwa [hJ] at this
  -- sum over the values of `Z`
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => x y = v)
    (fun x => fun i : Z => x i)]
  refine sum_congr rfl fun z _ => ?_
  rw [filter_filter]
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  set xb : Fin n → α := fill Z (Function.update (Function.update (fun _ => a₀) y v) k a) z
    with hxb
  have hxk : xb k = a := by simp [hxb, fill, hkZ]
  have hxy : xb y = v := by simp [hxb, fill, hyZ, Ne.symm hky]
  have hres : ∀ x : Fin n → α, (fun i : Z => x i) = z ↔ ∀ i ∈ Z, x i = xb i := by
    intro x
    constructor
    · rintro h i hi
      have := congrFun h ⟨i, hi⟩
      simp only at this
      rw [this]
      simp [hxb, fill, hi]
    · intro h
      funext i
      rw [h i i.2]
      simp [hxb, fill]
  have c1 : ∑ x with x y = v ∧ (fun i : Z => x i) = z, Q x = marginal Q ↑(insert y Z) xb := by
    simp only [marginal_coe]
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, hxy, hres]
  have c2 : ∑ x with (fun i : Z => x i) = z, P x = marginal P ↑Z xb := by
    simp only [marginal_coe]
    exact sum_congr (filter_congr fun x _ => hres x) fun _ _ => rfl
  have c3 : ∑ x with x k = a ∧ x y = v ∧ (fun i : Z => x i) = z, P x =
      marginal P ↑(insert k (insert y Z)) xb := by
    simp only [marginal_coe]
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, forall_mem_insert, hxk, hxy, hres]
  have c4 : ∑ x with x k = a ∧ (fun i : Z => x i) = z, P x = marginal P ↑(insert k Z) xb := by
    simp only [marginal_coe]
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, hxk, hres]
  have hpos' : marginal P ↑Z xb ≠ 0 → marginal P ↑(insert k Z) xb ≠ 0 := by
    rw [← c2, ← c4]; exact hpos z
  rw [c1, c2, c3, c4]
  -- reweighting by the table of `k`
  have hkey := marginal_reweight (L := P) (L' := Q) (disjoint_singleton_right.2 hyPk) hPkC xb
    (fun x => (b.cpt k (b.paVal k x)).weights a)
    (fun x x' hxx' => by
      rw [show b.paVal k x = b.paVal k x' from funext fun j => hxx' _ ?_]
      by_cases hj : Fin.castLE k.2.le j ∈ Z
      · exact mem_union_right _ (mem_insert_of_mem hj)
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, ⟨by simp, by simp⟩, hj⟩))
    (fun x hx => b.joint_eq_intervene_mul_cpt ((hx k (mem_insert_self k Z)).trans hxk)) hci
  have hxk' : ∀ j ∈ ({k} : Finset (Fin n)), xb j = a := fun j hj => by
    rw [mem_singleton] at hj; rw [hj, hxk]
  have hQZ : marginal Q ↑(insert k Z) xb = marginal Q ↑Z xb := by
    rw [← hJ, insert_eq, union_comm]
    exact b.marginal_mutilateSet_union {k} _ Z hxk'
  have hQyZ : marginal Q ↑({y} ∪ insert k Z) xb = marginal Q ↑(insert y Z) xb := by
    rw [← hJ, show ({y} : Finset (Fin n)) ∪ insert k Z = insert y Z ∪ {k} by
      ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto]
    exact b.marginal_mutilateSet_union {k} _ _ hxk'
  have hPyZ : marginal P ↑({y} ∪ insert k Z) xb = marginal P ↑(insert k (insert y Z)) xb := by
    rw [show ({y} ∪ insert k Z : Finset (Fin n)) = insert k (insert y Z) by
      ext i; simp only [mem_union, mem_insert, mem_singleton]; exact or_left_comm]
  -- the law of `Z` is unchanged by the intervention
  have hZ : marginal Q ↑Z xb = marginal P ↑Z xb :=
    b.marginal_intervene_of_not_isDescendant k a (fun i hi => hdesc i hi) xb
  rw [hQZ, hQyZ, hPyZ, hZ] at hkey
  by_cases hP0 : marginal P ↑Z xb = 0
  · have hA : marginal Q ↑(insert y Z) xb = 0 := le_antisymm
      (hP0 ▸ hZ ▸ marginal_le_of_subset hQ0 (subset_insert y Z) xb) (marginal_nonneg hQ0 _ _)
    rw [hA, hP0, zero_mul]
  · have hD0 := hpos' hP0
    field_simp
    linarith [hkey]

/-- **The front-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.4): if the
set `M` intercepts every directed path from the treatment node `k` to the outcome node `y`, no
path from `k` to a node of `M` that begins with an arrow into `k` is open (blocked by `∅`), and
every path from a node of `M` to `y` that begins with an arrow into that node is blocked by
`{k}`, then
`P(X_y = v | do(X_k = a)) = ∑_m P(M = m | X_k = a) ∑_{a'} P(X_y = v | X_k = a', M = m) P(X_k = a')`,
assuming `P(X_k = a', M = m) > 0` for all `a'` and `m`. -/
theorem frontdoor_adjustment [Fintype α] [DecidableEq α] (k y : Fin n) (M : Finset (Fin n))
    (a v : α) (hky : k ≠ y) (hkM : k ∉ M) (hyM : y ∉ M)
    (hdir : ∀ p : List (Fin n), p.IsChain b.Edge → p.head? = some k → p.getLast? = some y →
      ∃ m ∈ M, m ∈ p)
    (hkm : ∀ m ∈ M, ∀ p, b.IsPath k m p → (∃ h : 1 < p.length, b.Edge p[1] k) →
      b.PathBlocked ∅ p)
    (hmy : ∀ m ∈ M, ∀ p, b.IsPath m y p → (∃ h : 1 < p.length, b.Edge p[1] m) →
      b.PathBlocked {k} p)
    (hpos : ∀ (a' : α) (m : M → α), ∑ x with x k = a' ∧ (fun i : M => x i) = m, b.joint x ≠ 0) :
    ∑ x with x y = v, (b.intervene k a).joint x =
      ∑ m : M → α,
        ((∑ x with x k = a ∧ (fun i : M => x i) = m, b.joint x) /
            ∑ x with x k = a, b.joint x) *
          ∑ a' : α,
            ((∑ x with x k = a' ∧ x y = v ∧ (fun i : M => x i) = m, b.joint x) /
                ∑ x with x k = a' ∧ (fun i : M => x i) = m, b.joint x) *
              ∑ x with x k = a', b.joint x := by
  classical
  set P := b.joint with hPdef
  set Q := (b.intervene k a).joint with hQdef
  have hP0 : ∀ x, 0 ≤ P x := fun x => b.toChain.joint_nonneg n x
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  set Pk := univ.filter fun i => b.Edge i k with hPkdef
  set PaM := univ.filter fun i => i ∉ M ∧ i ≠ k ∧ ∃ j ∈ M, b.Edge i j with hPaMdef
  have hPkM : Disjoint Pk M := disjoint_left.2 fun p hp hpM => by
    have hE := (mem_filter.1 hp).2
    have hkp : k ≠ p := fun h => hkM (h ▸ hpM)
    obtain ⟨i, hi, -⟩ := hkm p hpM [k, p] ⟨by simp [hkp],
      List.IsChain.cons_cons (Or.inr hE) (.singleton _), rfl, rfl⟩ ⟨by simp, hE⟩
    simp at hi
  have hPkk : Disjoint Pk {k} := disjoint_singleton_right.2 fun h =>
    lt_irrefl _ (mem_filter.1 h).2.1
  have hyPaM : y ∉ PaM := by
    intro hy
    obtain ⟨-, -, m0, hm0, hE⟩ := (mem_filter.1 hy).2
    have hm0y : m0 ≠ y := fun h => hyM (h ▸ hm0)
    obtain ⟨i, hi, -⟩ := hmy m0 hm0 [m0, y] ⟨by simp [hm0y],
      List.IsChain.cons_cons (Or.inr hE) (.singleton _), rfl, rfl⟩ ⟨by simp, hE⟩
    simp at hi
  have hPaMC : Disjoint PaM (insert k M) := disjoint_left.2 fun p hp hpC => by
    obtain ⟨h1, h2, -⟩ := (mem_filter.1 hp).2
    rcases mem_insert.1 hpC with h | h
    · exact h2 h
    · exact h1 h
  have hPaMy : Disjoint PaM {y} := disjoint_singleton_right.2 hyPaM
  have hPaMs : ∀ (W : Finset (Fin n)), M ⊆ W → ∀ p ∈ PaM, p ∉ insert k M ∧ ∃ r ∈ W,
      b.Edge p r ∧ ∀ y' ∈ ({y} : Finset (Fin n)), ∀ l, b.IsPath r y' l →
        (∃ h : 1 < l.length, b.Edge l[1] r) →
          b.PathBlocked (({k} : Finset (Fin n)) : Set (Fin n)) l := by
    intro W hMW p hp
    obtain ⟨h1, h2, m0, hm0, hE⟩ := (mem_filter.1 hp).2
    refine ⟨by simp [h1, h2], m0, hMW hm0, hE, fun y' hy' l hl hb => ?_⟩
    rw [mem_singleton] at hy'
    subst hy'
    rw [coe_singleton]
    exact hmy m0 hm0 l hl hb
  -- the weight of the tables of `M`, a function of the variables in `PaM ∪ insert k M`
  set hM : (Fin n → α) → ℝ := fun x => ∏ j ∈ M, (b.cpt j (b.paVal j x)).weights (x j)
  have hhM : ∀ x x' : Fin n → α, (∀ i ∈ PaM ∪ insert k M, x i = x' i) → hM x = hM x' := by
    intro x x' hxx'
    refine prod_congr rfl fun j hj => ?_
    have hpa : b.paVal j x = b.paVal j x' := by
      funext i
      apply hxx'
      by_cases hiM : Fin.castLE j.2.le i ∈ M
      · exact mem_union_right _ (mem_insert_of_mem hiM)
      by_cases hik : Fin.castLE j.2.le i = k
      · exact mem_union_right _ (hik ▸ mem_insert_self _ _)
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hiM, hik, j, hj,
          ⟨by simp, by simp⟩⟩)
    rw [hpa, hxx' j (mem_union_right _ (mem_insert_of_mem hj))]
  have hsd : insert k M \ {k} = M := by
    ext i
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
    · intro h
      exact ⟨Or.inr h, fun h' => hkM (h' ▸ h)⟩
  -- sum over the values of `M`
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => x y = v)
    (fun x => fun i : M => x i)]
  refine sum_congr rfl fun m _ => ?_
  rw [filter_filter]
  set xb : Fin n → α := fill M (Function.update (Function.update (fun _ => a₀) y v) k a) m
    with hxb
  have hxk : xb k = a := by simp [hxb, fill, hkM]
  have hxy : xb y = v := by simp [hxb, fill, hyM, Ne.symm hky]
  have hxa : Function.update xb k a = xb := by rw [← hxk, Function.update_eq_self]
  have hres : ∀ x : Fin n → α, (fun i : M => x i) = m ↔ ∀ i ∈ M, x i = xb i := by
    intro x
    constructor
    · rintro h i hi
      have := congrFun h ⟨i, hi⟩
      simp only at this
      rw [this]
      simp [hxb, fill, hi]
    · intro h
      funext i
      rw [h i i.2]
      simp [hxb, fill]
  have hxaM : ∀ a', ∀ i ∈ M, Function.update xb k a' i = xb i := fun a' i hi =>
    Function.update_of_ne (fun h => hkM (by rw [← h]; exact hi)) _ _
  have hresa : ∀ a' (x : Fin n → α), (fun i : M => x i) = m ↔
      ∀ i ∈ M, x i = Function.update xb k a' i := by
    intro a' x
    rw [hres]
    exact forall₂_congr fun i hi => by rw [hxaM a' i hi]
  have c1 : ∑ x with x y = v ∧ (fun i : M => x i) = m, Q x = marginal Q ↑(insert y M) xb := by
    simp only [marginal_coe]
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, hxy, hres]
  have c2 : ∀ a', ∑ x with x k = a' ∧ (fun i : M => x i) = m, P x =
      marginal P ↑(insert k M) (Function.update xb k a') := by
    intro a'
    simp only [marginal_coe]
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, Function.update_self, hresa a']
  have c3 : ∀ a', ∑ x with x k = a', P x =
      marginal P ↑({k} : Finset (Fin n)) (Function.update xb k a') := by
    intro a'
    simp only [marginal_coe]
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    simp
  have c4 : ∀ a', ∑ x with x k = a' ∧ x y = v ∧ (fun i : M => x i) = m, P x =
      marginal P ↑(insert k (insert y M)) (Function.update xb k a') := by
    intro a'
    simp only [marginal_coe]
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, forall_mem_insert, Function.update_self,
      Function.update_of_ne (Ne.symm hky), hxy, hresa a']
  rw [c1, c2 a, c3 a, hxa]
  rw [sum_congr rfl fun a' _ => by rw [c4 a', c2 a', c3 a']]
  -- step B: `P(M = m | do(a)) = P(M = m | a)`
  have hJ1 : (b.mutilateSet {k} xb).joint = Q := b.joint_mutilateSet_singleton hxk
  have hciB : CondIndep Q ↑Pk ↑M ↑({k} : Finset (Fin n)) := by
    have := (b.mutilateSet {k} xb).condIndep_of_dSeparated_finset
      (b.dSeparated_mutilateSet xb (W := {k}) (C := {k}) (Zb := ∅) (Ys := M) (Ps := Pk)
        subset_rfl (empty_subset _) (by simp)
        (fun y' hy' h => hkM (by rw [mem_singleton] at h; rwa [h] at hy'))
        fun p hp => ⟨fun h => by
          rw [mem_singleton] at h
          subst h
          exact lt_irrefl _ (mem_filter.1 hp).2.1, k, mem_singleton_self k,
          (mem_filter.1 hp).2, fun y' hy' l hl hE => by rw [coe_empty]; exact hkm y' hy' l hl hE⟩)
    rwa [hJ1] at this
  have hB := marginal_reweight (L := P) (L' := Q) hPkM hPkk xb
    (fun x => (b.cpt k (b.paVal k x)).weights a)
    (fun x x' hxx' => by
      rw [show b.paVal k x = b.paVal k x' from funext fun i => hxx' _
        (mem_union_left _ (mem_filter.2 ⟨mem_univ _, by simp, by simp⟩))])
    (fun x hx => b.joint_eq_intervene_mul_cpt ((hx k (mem_singleton_self k)).trans hxk)) hciB
  have hMk : M ∪ {k} = insert k M := by rw [union_comm, ← insert_eq]
  have hQk : marginal Q ↑({k} : Finset (Fin n)) xb = 1 := by
    rw [← hJ1]; exact b.marginal_mutilateSet_self {k} xb fun _ _ => rfl
  have hQMk : marginal Q ↑(M ∪ {k}) xb = marginal Q ↑M xb := by
    rw [← hJ1]; exact b.marginal_mutilateSet_union {k} xb M fun _ _ => rfl
  rw [hQk, hQMk, hMk, mul_one] at hB
  -- step C: `P(y | do(a), M = m) = P(y | do(a, M = m))`
  set R' := (b.mutilateSet (insert k M) xb).joint with hR'def
  have hciC : CondIndep R' ↑PaM ↑({y} : Finset (Fin n)) ↑(insert k M) :=
    (b.mutilateSet (insert k M) xb).condIndep_of_dSeparated_finset
      (b.dSeparated_mutilateSet xb (W := insert k M) (C := insert k M) (Zb := {k}) (Ys := {y})
        (Ps := PaM) subset_rfl (singleton_subset_iff.2 (mem_insert_self _ _)) subset_union_left
        (fun y' hy' => by
          rw [mem_singleton] at hy'
          subst hy'
          simp [Ne.symm hky, hyM])
        (hPaMs (insert k M) (subset_insert _ _)))
  have hC := marginal_reweight (L := Q) (L' := R') hPaMy hPaMC xb hM hhM (fun x hx => by
      rw [← hJ1, b.joint_mutilateSet_mul (singleton_subset_iff.2 (mem_insert_self k M)) xb hx,
        hsd]) hciC
  have hR'1 : marginal R' ↑(insert k M) xb = 1 := b.marginal_mutilateSet_self _ xb fun _ _ => rfl
  have hR'y : marginal R' ↑({y} ∪ insert k M) xb = marginal R' ↑({y} : Finset (Fin n)) xb :=
    b.marginal_mutilateSet_union _ xb {y} fun _ _ => rfl
  have hQy : marginal Q ↑({y} ∪ insert k M) xb = marginal Q ↑(insert y M) xb := by
    rw [← hJ1, show ({y} : Finset (Fin n)) ∪ insert k M = insert y M ∪ {k} by
      ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto]
    exact b.marginal_mutilateSet_union {k} xb _ fun _ _ => rfl
  have hQkM : marginal Q ↑(insert k M) xb = marginal Q ↑M xb := by rw [← hMk, hQMk]
  rw [hR'1, hR'y, hQy, hQkM, mul_one] at hC
  -- step D: `do(a)` has no effect once `M` is fixed
  set R := (b.mutilateSet M xb).joint with hRdef
  have hD : marginal R' ↑({y} : Finset (Fin n)) xb = marginal R ↑({y} : Finset (Fin n)) xb := by
    set N := univ.filter fun j => ¬(b.mutilateSet M xb).IsDescendant k j with hNdef
    have hN2 : (b.mutilateSet M xb).IsAncestral N := by
      intro i j hE hj
      simp only [N, mem_filter, mem_univ, true_and] at hj ⊢
      exact fun hi => hj (Relation.ReflTransGen.tail hi hE)
    have hN1 : (b.mutilateSet (insert k M) xb).IsAncestral N := by
      intro i j hE hj
      obtain ⟨hE', hj'⟩ := (b.edge_mutilateSet_iff _ _).1 hE
      exact hN2 ((b.edge_mutilateSet_iff _ _).2 ⟨hE', fun h => hj' (mem_insert_of_mem h)⟩) hj
    refine marginal_eq_of_tables (b.mutilateSet (insert k M) xb) (b.mutilateSet M xb) hN1 hN2
      (fun j hj x => ?_) (singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ _,
        b.not_isDescendant_mutilateSet xb hkM hdir⟩)) xb
    have hjk : j ≠ k := fun h => (mem_filter.1 hj).2 (h ▸ .refl)
    by_cases hjM : j ∈ M
    · simp [mutilateSet, hjM]
    · simp [mutilateSet, hjM, hjk]
      rfl
  -- step E: adjusting for `k` after fixing `M`
  have hciE : CondIndep R ↑PaM ↑({y} : Finset (Fin n)) ↑(insert k M) :=
    (b.mutilateSet M xb).condIndep_of_dSeparated_finset
      (b.dSeparated_mutilateSet xb (W := M) (C := insert k M) (Zb := {k}) (Ys := {y})
        (Ps := PaM) (subset_insert _ _) (singleton_subset_iff.2 (mem_insert_self _ _))
        (by rw [← hMk])
        (fun y' hy' => by rw [mem_singleton] at hy'; subst hy'; exact hyM)
        (hPaMs M subset_rfl))
  have hkN : ∀ a', marginal R ↑({k} : Finset (Fin n)) (Function.update xb k a') =
      marginal P ↑({k} : Finset (Fin n)) (Function.update xb k a') := by
    intro a'
    set N := univ.filter fun j => ∀ m' ∈ M, ¬b.IsDescendant m' j with hNdef
    have hNb : b.IsAncestral N := by
      intro i j hE hj
      simp only [N, mem_filter, mem_univ, true_and] at hj ⊢
      exact fun m' hm' hi => hj m' hm' (Relation.ReflTransGen.tail hi hE)
    have hNM : (b.mutilateSet M xb).IsAncestral N := fun i j hE hj =>
      hNb ((b.edge_mutilateSet_iff _ _).1 hE).1 hj
    refine marginal_eq_of_tables (b.mutilateSet M xb) b hNM hNb (fun j hj x => ?_)
      (singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ _, fun m' hm' =>
        b.not_isDescendant_of_blocked (fun h => hkM (by rw [← h]; exact hm')) (hkm m' hm')⟩)) _
    have hjM : j ∉ M := fun h => (mem_filter.1 hj).2 j h .refl
    simp [mutilateSet, hjM]
    rfl
  have hE : ∀ a', marginal R ↑(insert k ({y} : Finset (Fin n))) (Function.update xb k a') =
      marginal P ↑(insert k (insert y M)) (Function.update xb k a') /
        marginal P ↑(insert k M) (Function.update xb k a') *
          marginal P ↑({k} : Finset (Fin n)) (Function.update xb k a') := by
    intro a'
    set xa := Function.update xb k a'
    have hxaM' : ∀ j ∈ M, xa j = xb j := hxaM a'
    have h2 := marginal_reweight (L := P) (L' := R) hPaMy hPaMC xa hM hhM (fun x hx => by
        change b.joint x = _
        rw [← b.joint_mutilateSet_empty xb, b.joint_mutilateSet_mul (empty_subset M) xb
          (fun j hj => (hx j (mem_insert_of_mem hj)).trans (hxaM' j hj)), sdiff_empty]) hciE
    have hRk : marginal R ↑(insert k M) xa = marginal P ↑({k} : Finset (Fin n)) xa := by
      rw [← hMk, union_comm, ← hkN a']
      exact b.marginal_mutilateSet_union M xb {k} hxaM'
    have hRky : marginal R ↑({y} ∪ insert k M) xa =
        marginal R ↑(insert k ({y} : Finset (Fin n))) xa := by
      rw [show ({y} : Finset (Fin n)) ∪ insert k M = insert k ({y} : Finset (Fin n)) ∪ M by
        ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto]
      exact b.marginal_mutilateSet_union M xb _ hxaM'
    have hPy : marginal P ↑({y} ∪ insert k M) xa = marginal P ↑(insert k (insert y M)) xa := by
      rw [show ({y} ∪ insert k M : Finset (Fin n)) = insert k (insert y M) by
        ext i; simp only [mem_union, mem_insert, mem_singleton]; exact or_left_comm]
    rw [hRk, hRky, hPy] at h2
    have hne : marginal P ↑(insert k M) xa ≠ 0 := by
      have := hpos a' m
      rwa [c2 a'] at this
    field_simp
    linarith [h2]
  have hsumE : marginal R ↑({y} : Finset (Fin n)) xb =
      ∑ a' : α, marginal R ↑(insert k ({y} : Finset (Fin n))) (Function.update xb k a') :=
    marginal_eq_sum_insert R (by simp [hky]) xb
  have hPk0 : marginal P ↑({k} : Finset (Fin n)) xb ≠ 0 := by
    have h1 := hpos a m
    rw [c2 a, hxa] at h1
    exact (lt_of_lt_of_le (lt_of_le_of_ne (marginal_nonneg hP0 _ _) (Ne.symm h1))
      (marginal_le_of_subset hP0 (singleton_subset_iff.2 (mem_insert_self k M)) xb)).ne'
  rw [hC, hD, hsumE, sum_congr rfl fun a' _ => hE a', hB]
  field_simp

end BayesNet

end Cslib.MachineLearning.GraphicalModels
end
-- ===== end atlas-src/CSLibExt/MachineLearning/GraphicalModels/CausalAdjustment.lean =====

-- ===== CA06.T02: the three rules of the do-calculus (pinned statements) =====

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight

namespace BayesNet

/-- The network with **the arrows out of `Z` removed** (the graph `G_{underline Z}` of Pearl
2009, §3.4): every parent of a node that lies in `Z` is dropped from its parent set, and the
node's table reads that parent at the fixed value `z`. Only the graph of this network enters
the do-calculus (`edge_cutOut_iff`); the tables are a concrete choice that keeps it a
`BayesNet`. -/
noncomputable def cutOut {α : Type*} {n : ℕ} (b : BayesNet α n) (Z : Finset (Fin n))
    (z : Fin n → α) : BayesNet α n where
  pa j := (b.pa j).filter fun i => Fin.castLE j.2.le i ∉ Z
  cpt j u := b.cpt j fun i =>
    if h : Fin.castLE j.2.le i.1 ∈ Z then z (Fin.castLE j.2.le i.1)
    else u ⟨i.1, Finset.mem_filter.2 ⟨i.2, h⟩⟩

/-- Absorption of the intervened set (copy of the prelude's private
`marginal_mutilateSet_union`, which is not visible at integration time): under `do(X_W = w)`,
the marginal over `S ∪ W` at an assignment agreeing with `w` on `W` equals the marginal over
`S`. -/
lemma marginal_mutilateSet_union_absorb {α : Type*} {n : ℕ} [Fintype α] [Nonempty α]
    (b : BayesNet α n)
    (W : Finset (Fin n)) (w : Fin n → α) (S : Finset (Fin n)) {x' : Fin n → α}
    (hx' : ∀ j ∈ W, x' j = w j) :
    marginal (b.mutilateSet W w).joint ((S ∪ W : Finset (Fin n)) : Set (Fin n)) x' =
      marginal (b.mutilateSet W w).joint (S : Set (Fin n)) x' := by
  classical
  simp only [marginal_coe]
  symm
  rw [← sum_filter_of_ne (p := fun x => ∀ j ∈ W, x j = w j), filter_filter]
  · refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    simp only [mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact (h2 i hi).trans (hx' i hi).symm
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun j hj => (h j (Or.inr hj)).trans (hx' j hj)⟩
  · intro x _ hx j hj
    by_contra hne
    apply hx
    rw [joint_mutilateSet]
    exact prod_eq_zero (mem_univ j) (by simp [hj, hne])

/-- Ratio form of conditional independence with the intervened set absorbed: from
`Y ⫫ Z | T ∪ W'` and absorption of `T`, `P(y | z, w') = P(y | w')`. -/
theorem condRatio_of_condIndep {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    {P : (Fin n → α) → ℝ} {Y Z W' T : Finset (Fin n)} {x : Fin n → α}
    (hCI : CondIndep P (Y : Set (Fin n)) (Z : Set (Fin n))
      ((T ∪ W' : Finset (Fin n)) : Set (Fin n)))
    (habs : ∀ S : Finset (Fin n),
      marginal P ((S ∪ T : Finset (Fin n)) : Set (Fin n)) x = marginal P (S : Set (Fin n)) x)
    (hzw : marginal P ((Z ∪ W' : Finset (Fin n)) : Set (Fin n)) x ≠ 0)
    (hw : marginal P (W' : Set (Fin n)) x ≠ 0) :
    marginal P ((Y ∪ Z ∪ W' : Finset (Fin n)) : Set (Fin n)) x /
        marginal P ((Z ∪ W' : Finset (Fin n)) : Set (Fin n)) x =
      marginal P ((Y ∪ W' : Finset (Fin n)) : Set (Fin n)) x /
        marginal P (W' : Set (Fin n)) x := by
  have h := hCI x
  have e1 : ((Y : Set (Fin n)) ∪ (Z : Set (Fin n)) ∪ ((T ∪ W' : Finset (Fin n)) : Set (Fin n))) =
      ((((Y ∪ Z ∪ W') ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    ext i
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_union]
    tauto
  have e2 : (((T ∪ W' : Finset (Fin n))) : Set (Fin n)) =
      (((W' ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    rw [Finset.union_comm T W']
  have e3 : ((Y : Set (Fin n)) ∪ ((T ∪ W' : Finset (Fin n)) : Set (Fin n))) =
      ((((Y ∪ W') ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    ext i
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_union]
    tauto
  have e4 : ((Z : Set (Fin n)) ∪ ((T ∪ W' : Finset (Fin n)) : Set (Fin n))) =
      ((((Z ∪ W') ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    ext i
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_union]
    tauto
  rw [e1, e3, e4, e2] at h
  simp only [habs] at h
  rw [div_eq_div_iff hzw hw]
  exact h

/-- For `v` agreeing with `z` on `Z`, the `cutOut` network has the same joint as the original
(children of `Z` read `x` there anyway). -/
theorem joint_cutOut_eq_of_agree {α : Type*} {n : ℕ} [Fintype α] [Nonempty α]
    (M : BayesNet α n) (Z : Finset (Fin n)) (z v : Fin n → α)
    (hv : ∀ j ∈ Z, v j = z j) : (M.cutOut Z z).joint v = M.joint v := by
  simp only [joint_eq_prod]
  refine prod_congr rfl fun j _ => ?_
  have hfun : (fun i : M.pa j =>
        if h : Fin.castLE j.2.le i.1 ∈ Z then z (Fin.castLE j.2.le i.1)
        else v (Fin.castLE j.2.le i.1)) =
      (fun i : M.pa j => v (Fin.castLE j.2.le i)) := by
    funext i
    by_cases h : Fin.castLE j.2.le i.1 ∈ Z
    · simp only [dif_pos h]
      exact (hv _ h).symm
    · simp only [dif_neg h]
  simp only [cutOut, hfun]

/-- The `cutOut` marginal over a set containing `Z` equals the original marginal. -/
theorem margCutOut_eq_of_superset {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α] [Nonempty α]
    (M : BayesNet α n) (Z : Finset (Fin n)) (z : Fin n → α) (T : Finset (Fin n))
    (hTZ : Z ⊆ T) (x : Fin n → α) (hx : ∀ j ∈ Z, x j = z j) :
    marginal (M.cutOut Z z).joint (T : Set (Fin n)) x =
      marginal M.joint (T : Set (Fin n)) x := by
  simp only [marginal_coe]
  refine sum_congr rfl fun v hv => ?_
  simp only [mem_filter, mem_univ, true_and] at hv
  exact joint_cutOut_eq_of_agree M Z z v (fun j hj => (hv j (hTZ hj)).trans (hx j hj))

/-- The `cutOut` table at `j ∉ X` in a mutilated network: `Z`-parents read at `x`. -/
theorem cpt_cutOut_mutilate {α : Type*} {n : ℕ} [Fintype α] [Nonempty α] (b : BayesNet α n)
    (X Z : Finset (Fin n)) (x : Fin n → α) (j : Fin n) (hjX : j ∉ X)
    (w : Fin n → α) :
    ((b.mutilateSet X x).cutOut Z x).cpt j (fun j' => w (Fin.castLE j.2.le j')) =
      b.cpt j (fun i : b.pa j => if _ : Fin.castLE j.2.le i.1 ∈ Z then x (Fin.castLE j.2.le i.1)
        else w (Fin.castLE j.2.le i.1)) := by
  simp only [cutOut, mutilateSet, dif_neg hjX]

/-- The `cutOut` table at `j ∈ X` in a mutilated network is the point mass. -/
theorem cpt_cutOut_mutilate_mem {α : Type*} {n : ℕ} [Fintype α] [Nonempty α] (b : BayesNet α n)
    (X Z : Finset (Fin n)) (x : Fin n → α) (j : Fin n) (hjX : j ∈ X)
    (u : ((b.mutilateSet X x).cutOut Z x).pa j → α) :
    ((b.mutilateSet X x).cutOut Z x).cpt j u = Convexity.StdSimplex.single (x j) := by
  simp only [cutOut, mutilateSet, dif_pos hjX]

/-- Summing the `Z`-coordinates against fixed tables gives `1`. -/
theorem fiber_sum_eq_one {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (Z : Finset (Fin n))
    (D : Fin n → Convexity.StdSimplex ℝ α) :
    ∑ p ∈ Z.pi (fun _ => (Finset.univ : Finset α)),
      ∏ x ∈ Z.attach, (D x.1).weights (p x.1 x.2) = 1 := by
  have htot : ∀ j ∈ Z, (∑ a ∈ (Finset.univ : Finset α), (D j).weights a) = 1 :=
    fun j _ => Convexity.StdSimplex.total_of_fintype (D j)
  have hps := Finset.prod_sum Z (fun _ => (Finset.univ : Finset α))
    (fun j a => (D j).weights a)
  have hprod : (∏ j ∈ Z, ∑ a ∈ (Finset.univ : Finset α), (D j).weights a) = 1 :=
    Finset.prod_eq_one htot
  calc ∑ p ∈ Z.pi (fun _ => (Finset.univ : Finset α)),
          ∏ x ∈ Z.attach, (D x.1).weights (p x.1 x.2)
      = (∏ j ∈ Z, ∑ a ∈ (Finset.univ : Finset α), (D j).weights a) := hps.symm
    _ = 1 := hprod

/-- Absorption of the intervened set in a `cutOut` network: under `do(X)`, further fixing `X`
does not change the marginal, since the `X`-nodes keep their point-mass tables. -/
theorem marginal_cutOut_mutilate_absorb {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : BayesNet α n) (X Z : Finset (Fin n)) (x : Fin n → α)
    (S : Finset (Fin n)) :
    marginal ((b.mutilateSet X x).cutOut Z x).joint ((S ∪ X : Finset (Fin n)) : Set (Fin n)) x =
      marginal ((b.mutilateSet X x).cutOut Z x).joint (S : Set (Fin n)) x := by
  classical
  simp only [marginal_coe]
  symm
  rw [← sum_filter_of_ne (p := fun x' => ∀ j ∈ X, x' j = x j), filter_filter]
  · refine sum_congr (filter_congr fun x' _ => ?_) fun _ _ => rfl
    simp only [mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact h2 i hi
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun j hj => h j (Or.inr hj)⟩
  · intro x' _ hx j hj
    by_contra hne
    apply hx
    rw [joint_eq_prod]
    refine prod_eq_zero (mem_univ j) ?_
    have hcpt : ((b.mutilateSet X x).cutOut Z x).cpt j (fun i => x' (Fin.castLE j.2.le i)) =
        Convexity.StdSimplex.single (x j) :=
      cpt_cutOut_mutilate_mem b X Z x j hj _
    rw [hcpt]
    simp [Convexity.StdSimplex.single, hne]

/-- The fiber sum over `(Z → α)`: summing a product of per-node weights over all `Z`-values
gives `1`, since each table sums to `1`. `F` agrees with the fiber coordinate on `Z`. -/
theorem fiber_sum_univ {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α] [Nonempty α]
    (Z : Finset (Fin n)) (D : Fin n → Convexity.StdSimplex ℝ α)
    (F : (Z → α) → Fin n → α) (hF : ∀ δ j (hj : j ∈ Z), F δ j = δ ⟨j, hj⟩) :
    ∑ δ ∈ (univ : Finset (Z → α)), ∏ j ∈ Z, (D j).weights (F δ j) = 1 := by
  classical
  revert hF; revert F; revert D
  induction Z using Finset.induction_on with
  | empty =>
    intro D F hF
    have hU : (univ : Finset ((∅ : Finset (Fin n)) → α)) = {fun _ => Classical.arbitrary α} := by
      ext δ
      simp only [mem_univ, mem_singleton]
      exact ⟨fun _ => funext fun z => (notMem_empty z.1 z.2).elim, fun _ => trivial⟩
    rw [hU, Finset.sum_singleton]
    show ∏ j ∈ (∅ : Finset (Fin n)), (D j).weights (F (fun _ => Classical.arbitrary α) j) = 1
    exact Finset.prod_empty
  | insert z Z' hz ih =>
    intro D F hF
    set e' : α × (Z' → α) → (↥(insert z Z') → α) :=
      fun p w => if h : w.1 = z then p.1 else p.2 ⟨w.1, (mem_insert.1 w.2).resolve_left h⟩ with he'
    have he'_pos : ∀ p w (h : w.1 = z), e' p w = p.1 := fun p w h => dif_pos h
    have he'_neg : ∀ p w (h : w.1 ≠ z),
        e' p w = p.2 ⟨w.1, (mem_insert.1 w.2).resolve_left h⟩ :=
      fun p w h => dif_neg h
    have himg' : (univ : Finset (↥(insert z Z') → α)) =
        (univ : Finset (α × (Z' → α))).image e' := by
      ext δ
      simp only [mem_image]
      constructor
      · intro _
        refine ⟨(δ ⟨z, mem_insert_self z Z'⟩, fun w : Z' => δ ⟨w.1, mem_insert_of_mem w.2⟩),
          mem_univ _, ?_⟩
        funext w
        by_cases h : w.1 = z
        · have hwz : w = ⟨z, mem_insert_self z Z'⟩ := Subtype.ext h
          rw [he'_pos _ _ h]
          show δ ⟨z, mem_insert_self z Z'⟩ = δ w
          rw [hwz]
        · exact (he'_neg _ _ h).trans rfl
      · intro _
        exact mem_univ δ
    have hinj' : ∀ p₁ ∈ (univ : Finset (α × (Z' → α))), ∀ p₂ ∈ (univ : Finset (α × (Z' → α))),
        e' p₁ = e' p₂ → p₁ = p₂ := by
      intro p₁ _ p₂ _ h
      obtain ⟨a₁, d₁⟩ := p₁; obtain ⟨a₂, d₂⟩ := p₂
      have h1 : a₁ = a₂ := by
        have hcon := congrFun h ⟨z, mem_insert_self z Z'⟩
        rw [he'_pos _ ⟨z, mem_insert_self z Z'⟩ rfl,
          he'_pos _ ⟨z, mem_insert_self z Z'⟩ rfl] at hcon
        exact hcon
      have h2 : d₁ = d₂ := by
        funext w
        have hne : w.1 ≠ z := fun he => hz (he ▸ w.2)
        have hcon := congrFun h ⟨w.1, mem_insert_of_mem w.2⟩
        rw [he'_neg _ _ hne, he'_neg _ _ hne] at hcon
        exact hcon
      rw [h1, h2]
    rw [himg', Finset.sum_image hinj']
    simp only [Fintype.sum_prod_type]
    have hsplit2 : ∀ a d, ∏ j ∈ insert z Z', (D j).weights (F (e' (a, d)) j) =
        (D z).weights a * ∏ j ∈ Z', (D j).weights (F (e' (a, d)) j) := by
      intro a d
      simp only [prod_insert hz]
      congr 1
      congr 1
      rw [hF _ _ (mem_insert_self z Z')]
      exact he'_pos (a, d) ⟨z, mem_insert_self z Z'⟩ rfl
    have hF' : ∀ a d j (hj : j ∈ Z'), (fun d j => F (e' (a, d)) j) d j = d ⟨j, hj⟩ := by
      intro a d j hj
      show F (e' (a, d)) j = d ⟨j, hj⟩
      rw [hF _ _ (mem_insert_of_mem hj)]
      have hne : j ≠ z := fun he => hz (he ▸ hj)
      exact (he'_neg _ _ hne).trans rfl
    have hIH : ∀ a, ∑ d ∈ univ, ∏ j ∈ Z', (D j).weights (F (e' (a, d)) j) = 1 :=
      fun a => ih D (fun d j => F (e' (a, d)) j) (hF' a)
    simp only [hsplit2, ← mul_sum, hIH, mul_one]
    exact Convexity.StdSimplex.total_of_fintype (D z)

/-- Summing out the `Z`-coordinates of the `cutOut` joint gives the `do(X ∪ Z)` marginal on
sets disjoint from `Z`: the `Z`-factors sum to `1` and the rest match the intervened tables. -/
theorem marginal_cutOut_eq_mutilate {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : BayesNet α n) {X Z : Finset (Fin n)} (x : Fin n → α)
    (hXZ : Disjoint X Z) {S : Finset (Fin n)} (hSZ : Disjoint S Z) :
    marginal ((b.mutilateSet X x).cutOut Z x).joint (S : Set (Fin n)) x =
      marginal (b.mutilateSet (X ∪ Z) x).joint (S : Set (Fin n)) x := by
  classical
  rw [← marginal_cutOut_mutilate_absorb b X Z x S]
  rw [← marginal_mutilateSet_union_absorb b (X ∪ Z) x S (fun _ _ => rfl)]
  simp only [marginal_coe]
  set M : BayesNet α n := b.mutilateSet X x with hM
  set N : BayesNet α n := M.cutOut Z x with hN
  set P : BayesNet α n := b.mutilateSet (X ∪ Z) x with hP
  set g : (Fin n → α) → (Fin n → α) := fun v j => if j ∈ Z then x j else v j with hg
  have hg_pos : ∀ v j (hj : j ∈ Z), g v j = x j := fun v j hj => dif_pos hj
  have hg_neg : ∀ v j (hj : j ∉ Z), g v j = v j := fun v j hj => dif_neg hj
  have hSXZ : ∀ j ∈ S ∪ X, j ∉ Z := fun j hj hJZ => (mem_union.1 hj).elim
    (fun hjS => disjoint_left.1 hSZ hjS hJZ) (fun hjX => disjoint_left.1 hXZ hjX hJZ)
  have hmemSX : ∀ j ∈ S ∪ X, j ∈ S ∪ (X ∪ Z) := fun j hj => (mem_union.1 hj).elim
    (fun hjS => mem_union_left _ hjS) (fun hjX => mem_union_right _ (mem_union_left _ hjX))
  have himg : (univ.filter (fun v : Fin n → α => ∀ i ∈ S ∪ X, v i = x i)).image g =
      univ.filter (fun v₀ : Fin n → α => ∀ i ∈ S ∪ (X ∪ Z), v₀ i = x i) := by
    ext v₀
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨v, ⟨-, hv⟩, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      intro j hj
      by_cases hjZ : j ∈ Z
      · rw [hg_pos _ _ hjZ]
      · rw [hg_neg _ _ hjZ]
        exact hv j ((mem_union.1 hj).elim (fun hjS => mem_union_left _ hjS)
          (fun hjXZ => (mem_union.1 hjXZ).elim (fun hjX => mem_union_right _ hjX)
            (fun hjZ' => absurd hjZ' hjZ)))
    · intro hmem
      obtain ⟨-, hag⟩ := hmem
      refine ⟨v₀, ⟨mem_univ _, fun j hj => hag j (hmemSX j hj)⟩, ?_⟩
      funext j
      by_cases hjZ : j ∈ Z
      · rw [hg_pos _ _ hjZ]
        exact (hag j (mem_union_right _ (mem_union_right _ hjZ))).symm
      · rw [hg_neg _ _ hjZ]
  have hmaps : ∀ v ∈ univ.filter (fun v : Fin n → α => ∀ i ∈ S ∪ X, v i = x i),
      g v ∈ univ.filter (fun v₀ : Fin n → α => ∀ i ∈ S ∪ (X ∪ Z), v₀ i = x i) := by
    intro v hv
    rw [← himg]
    exact Finset.mem_image_of_mem g hv
  rw [← Finset.sum_fiberwise_of_maps_to hmaps N.joint]
  refine sum_congr rfl fun v₀ hv₀ => ?_
  have hv₀agree : ∀ i ∈ S ∪ (X ∪ Z), v₀ i = x i := (mem_filter.1 hv₀).2
  have hv₀SX : ∀ j ∈ S ∪ X, v₀ j = x j := fun j hj => hv₀agree j (hmemSX j hj)
  have hv₀Z : ∀ j ∈ Z, v₀ j = x j :=
    fun j hjZ => hv₀agree j (mem_union_right _ (mem_union_right _ hjZ))
  set e : (Z → α) → (Fin n → α) := fun δ j => if h : j ∈ Z then δ ⟨j, h⟩ else v₀ j with he
  have he_pos : ∀ δ j (hj : j ∈ Z), e δ j = δ ⟨j, hj⟩ := fun δ j hj => dif_pos hj
  have he_neg : ∀ δ j (hj : j ∉ Z), e δ j = v₀ j := fun δ j hj => dif_neg hj
  simp only [filter_filter]
  have hfibeq : univ.filter (fun v : Fin n → α => (∀ i ∈ S ∪ X, v i = x i) ∧ g v = v₀) =
      univ.image e := by
    ext v
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨-, hag, hpr⟩
      refine ⟨fun z : Z => v z.1, mem_univ _, ?_⟩
      funext j
      by_cases hjZ : j ∈ Z
      · exact (he_pos (fun z : Z => v z.1) j hjZ).trans rfl
      · rw [he_neg (fun z : Z => v z.1) j hjZ]
        have hprj : v j = v₀ j := by
          rw [← hg_neg v j hjZ]
          exact congrFun hpr j
        exact hprj.symm
    · rintro ⟨δ, _, rfl⟩
      refine ⟨mem_univ _, ?_, ?_⟩
      · intro j hjSX
        rw [he_neg _ _ (hSXZ j hjSX)]
        exact hv₀SX j hjSX
      · funext j
        by_cases hjZ : j ∈ Z
        · rw [hg_pos _ _ hjZ]
          exact (hv₀Z j hjZ).symm
        · rw [hg_neg _ _ hjZ, he_neg _ _ hjZ]
  have hinj : ∀ d₁ ∈ (univ : Finset (Z → α)), ∀ d₂ ∈ (univ : Finset (Z → α)),
      e d₁ = e d₂ → d₁ = d₂ := by
    intro δ₁ _ δ₂ _ h
    funext z
    have h12 := congrFun h z.1
    rw [he_pos _ _ z.2, he_pos _ _ z.2] at h12
    exact h12
  rw [hfibeq, Finset.sum_image hinj]
  conv_lhs => arg 2; ext x; rw [N.joint_eq_prod (e x)]
  have hpaE : ∀ δ k, (fun j : N.pa k => (e δ) (Fin.castLE k.2.le j)) = N.paVal k v₀ := by
    intro δ k
    funext i
    have hflt : i.1 ∈ (M.pa k).filter (fun i => Fin.castLE k.2.le i ∉ Z) := i.2
    have hmem : Fin.castLE k.2.le i.1 ∉ Z := (mem_filter.1 hflt).2
    show (e δ) (Fin.castLE k.2.le i.1) = v₀ (Fin.castLE k.2.le i.1)
    rw [he_neg _ _ hmem]
  have hsum : (∑ δ ∈ univ, ∏ k, (N.cpt k
      (fun j : N.pa k => (e δ) (Fin.castLE k.2.le j))).weights ((e δ) k)) =
      (∑ δ ∈ univ, ∏ k, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) :=
    Finset.sum_congr rfl fun δ _ => Finset.prod_congr rfl fun k _ => by rw [hpaE δ k]
  rw [hsum]
  have hunion : Z ∪ (univ \ Z) = univ := by
    ext j
    simp only [mem_union, mem_sdiff, mem_univ, true_and, iff_true_intro (em (j ∈ Z))]
  have hdisj : Disjoint Z (univ \ Z) :=
    disjoint_left.2 fun j hjZ hjSD => (mem_sdiff.1 hjSD).2 hjZ
  have hsplit : ∀ K : Fin n → ℝ, (∏ k ∈ univ, K k) =
      (∏ k ∈ Z, K k) * (∏ k ∈ univ \ Z, K k) := by
    intro K
    conv_lhs => rw [← hunion]
    rw [prod_union hdisj]
  simp only [hsplit]
  have hnonZ : ∀ δ k (hk : k ∉ Z),
      (N.cpt k (N.paVal k v₀)).weights ((e δ) k) =
        (N.cpt k (N.paVal k v₀)).weights (v₀ k) := fun δ k hk => by rw [he_neg δ k hk]
  have hδfree : ∀ δ, (∏ k ∈ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) *
      (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) =
      (∏ k ∈ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) *
      (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights (v₀ k)) := by
    intro δ
    congr 1
    exact prod_congr rfl fun k hk => hnonZ δ k (mem_sdiff.1 hk).2
  simp only [hδfree]
  rw [← sum_mul]
  have hfib : ∑ δ ∈ univ, ∏ k ∈ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k) = 1 :=
    fiber_sum_univ Z (fun k => N.cpt k (N.paVal k v₀)) e (fun δ k hk => he_pos δ k hk)
  rw [hfib, one_mul]
  have htable : ∀ k (hk : k ∉ X ∪ Z),
      N.cpt k (N.paVal k v₀) = b.cpt k (b.paVal k v₀) := by
    intro k hkXZ
    have hkX : k ∉ X := fun hX => hkXZ (mem_union_left _ hX)
    have hpa : N.paVal k v₀ = (fun j' : N.pa k => v₀ (Fin.castLE k.2.le j')) := rfl
    have hN' : N.cpt k (fun j' : N.pa k => v₀ (Fin.castLE k.2.le j')) =
        b.cpt k (fun i => if _ : Fin.castLE k.2.le i.1 ∈ Z then x (Fin.castLE k.2.le i.1)
          else v₀ (Fin.castLE k.2.le i.1)) :=
      cpt_cutOut_mutilate b X Z x k hkX v₀
    have hfun : (fun i => if _ : Fin.castLE k.2.le i.1 ∈ Z then x (Fin.castLE k.2.le i.1)
          else v₀ (Fin.castLE k.2.le i.1)) = b.paVal k v₀ := by
      funext i
      by_cases h : Fin.castLE k.2.le i.1 ∈ Z
      · simp only [dif_pos h]; exact (hv₀Z _ h).symm
      · simp only [dif_neg h]; exact rfl
    rw [hpa, hN', hfun]
  have hFG : ∀ k (hk : k ∉ X ∪ Z),
      (N.cpt k (N.paVal k v₀)).weights (v₀ k) =
        (b.cpt k (b.paVal k v₀)).weights (v₀ k) := fun k hk => by rw [htable k hk]
  have hNC : (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights (v₀ k)) =
      ∏ k ∈ univ.filter (fun k => k ∉ X ∪ Z),
        (N.cpt k (N.paVal k v₀)).weights (v₀ k) := by
    symm
    refine Finset.prod_subset ?_ ?_
    · intro k hk
      exact mem_sdiff.2 ⟨mem_univ k, fun hZ => (mem_filter.1 hk).2 (mem_union_right _ hZ)⟩
    · intro k hkUD hnf
      have hkXZ : k ∈ X ∪ Z := by
        by_contra hC
        exact hnf (mem_filter.2 ⟨mem_univ k, hC⟩)
      have hkX : k ∈ X := (mem_union.1 hkXZ).resolve_right (mem_sdiff.1 hkUD).2
      have hcpt1 : N.cpt k (N.paVal k v₀) = Convexity.StdSimplex.single (x k) :=
        cpt_cutOut_mutilate_mem b X Z x k hkX _
      rw [hcpt1]
      have hag : v₀ k = x k := hv₀SX k (mem_union_right _ hkX)
      rw [hag]
      simp [Convexity.StdSimplex.single]
  have hPJ : P.joint v₀ = ∏ j, (if j ∈ X ∪ Z then (if v₀ j = x j then 1 else 0)
      else (b.cpt j (b.paVal j v₀)).weights (v₀ j)) :=
    joint_mutilateSet b (X ∪ Z) x v₀
  have hPside : P.joint v₀ = ∏ k ∈ univ.filter (fun k => k ∉ X ∪ Z),
      (b.cpt k (b.paVal k v₀)).weights (v₀ k) := by
    rw [hPJ]
    have hsubP : univ.filter (fun k => k ∉ X ∪ Z) ⊆ univ := subset_univ _
    have hfP : ∀ j ∈ univ, j ∉ univ.filter (fun k => k ∉ X ∪ Z) →
        (if j ∈ X ∪ Z then (if v₀ j = x j then 1 else 0)
          else (b.cpt j (b.paVal j v₀)).weights (v₀ j)) = 1 := by
      intro j _ hnf
      have hjXZ : j ∈ X ∪ Z := by
        by_contra hC
        exact hnf (mem_filter.2 ⟨mem_univ j, hC⟩)
      have hag : v₀ j = x j := hv₀agree j (mem_union_right _ hjXZ)
      simp only [if_pos hjXZ, if_pos hag]
    rw [(Finset.prod_subset hsubP hfP).symm]
    refine prod_congr rfl fun j hj => ?_
    rw [if_neg (mem_filter.1 hj).2]
  have hNZ : (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights (v₀ k)) = P.joint v₀ := by
    rw [hNC]
    exact (prod_congr rfl fun k hk => hFG k (mem_filter.1 hk).2).trans hPside.symm
  exact hNZ

/-- The arrows of `b.cutOut Z z` are those of `b` not leaving `Z`. -/
theorem edge_cutOut_iff {α : Type*} {n : ℕ} (b : BayesNet α n) (Z : Finset (Fin n))
    (z : Fin n → α) {i j : Fin n} :
    (b.cutOut Z z).Edge i j ↔ b.Edge i j ∧ i ∉ Z := by
  have hcast : ∀ h : i.val < j.val, Fin.castLE j.2.le (⟨i.val, h⟩ : Fin j) = i :=
    fun h => Fin.ext rfl
  simp only [Edge, cutOut, Finset.mem_filter]
  constructor
  · rintro ⟨h, hmem, hnot⟩
    have hnot' : Fin.castLE j.2.le (⟨i.val, h⟩ : Fin j) ∉ Z := hnot
    rw [hcast h] at hnot'
    exact ⟨⟨h, hmem⟩, hnot'⟩
  · rintro ⟨⟨h, hmem⟩, hiZ⟩
    refine ⟨h, hmem, ?_⟩
    show Fin.castLE j.2.le (⟨i.val, h⟩ : Fin j) ∉ Z
    rw [hcast h]
    exact hiZ

/-- **Rule 1 of the do-calculus** (insertion/deletion of observations; Pearl 1995, Theorem 3;
Pearl 2009, Theorem 3.4.1): if `Y` and `Z` are d-separated by `X ∪ W` in `G_{bar X}` (the
graph of `b.mutilateSet X x`), then `P(y | do(x), z, w) = P(y | do(x), w)`, wherever both
conditional probabilities are defined. All values are read off the single assignment `x`. -/
theorem doCalculus_rule1 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y Z W : Finset (Fin n)} (x : Fin n → α)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hYW : Disjoint Y W) (hZW : Disjoint Z W)
    (hd : (b.mutilateSet X x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)))
    (hzw : marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x ≠ 0)
    (hw : marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x ≠ 0) :
    marginal (b.mutilateSet X x).joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal (b.mutilateSet X x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x := by
  have hCI : CondIndep (b.mutilateSet X x).joint (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)) :=
    (b.mutilateSet X x).condIndep_of_dSeparated_finset hd
  have habs : ∀ S : Finset (Fin n),
      marginal (b.mutilateSet X x).joint ((S ∪ X : Finset (Fin n)) : Set (Fin n)) x =
        marginal (b.mutilateSet X x).joint (S : Set (Fin n)) x :=
    fun S => marginal_mutilateSet_union_absorb b X x S (fun _ _ => rfl)
  exact condRatio_of_condIndep hCI habs hzw hw

/-- **Rule 2 of the do-calculus** (action/observation exchange; Pearl 1995, Theorem 3; Pearl
2009, Theorem 3.4.1): if `Y` and `Z` are d-separated by `X ∪ W` in `G_{bar X underline Z}`
(the graph of `(b.mutilateSet X x).cutOut Z x`), then
`P(y | do(x), do(z), w) = P(y | do(x), z, w)`, wherever both conditional probabilities are
defined. -/
theorem doCalculus_rule2 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y Z W : Finset (Fin n)} (x : Fin n → α)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hYW : Disjoint Y W) (hZW : Disjoint Z W)
    (hd : ((b.mutilateSet X x).cutOut Z x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)))
    (hw : marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x ≠ 0)
    (hzw : marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x ≠ 0) :
    marginal (b.mutilateSet (X ∪ Z) x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x =
      marginal (b.mutilateSet X x).joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x := by
  classical
  set M : BayesNet α n := b.mutilateSet X x with hM
  set N : BayesNet α n := M.cutOut Z x with hN
  set P : BayesNet α n := b.mutilateSet (X ∪ Z) x with hP
  have hCI : CondIndep N.joint (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)) :=
    N.condIndep_of_dSeparated_finset hd
  have habs : ∀ S : Finset (Fin n),
      marginal N.joint ((S ∪ X : Finset (Fin n)) : Set (Fin n)) x =
        marginal N.joint (S : Set (Fin n)) x :=
    fun S => marginal_cutOut_mutilate_absorb b X Z x S
  have hYWZ : Disjoint (Y ∪ W) Z :=
    disjoint_left.2 fun a ha haZ => (mem_union.1 ha).elim
      (fun haY => disjoint_left.1 hYZ haY haZ) (fun haW => disjoint_left.1 hZW haZ haW)
  have c1 : marginal N.joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal M.joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x :=
    margCutOut_eq_of_superset M Z x (Y ∪ Z ∪ W)
      (fun j hj => mem_union_left _ (mem_union_right _ hj)) x (fun _ _ => rfl)
  have c2 : marginal N.joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal M.joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x :=
    margCutOut_eq_of_superset M Z x (Z ∪ W)
      (fun j hj => mem_union_left _ hj) x (fun _ _ => rfl)
  have c3 : marginal N.joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal P.joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x :=
    marginal_cutOut_eq_mutilate b x hXZ hYWZ
  have c4 : marginal N.joint (W : Set (Fin n)) x =
      marginal P.joint (W : Set (Fin n)) x :=
    marginal_cutOut_eq_mutilate b x hXZ hZW.symm
  have hzw' : marginal N.joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x ≠ 0 := by
    rw [c2]; exact hzw
  have hw' : marginal N.joint (W : Set (Fin n)) x ≠ 0 := by
    rw [c4]; exact hw
  rw [← c3, ← c4, ← c1, ← c2]
  exact (condRatio_of_condIndep hCI habs hzw' hw').symm

/-! ### Rule 3 helpers (skeleton: every `sorry` below is to be replaced by Muse) -/

/-- Copy of the private prelude lemma `exists_isChain_of_reflTransGen`, strengthened: every
node after the first has an incoming `r`-edge and is reachable from `a`. -/
private lemma exists_isChain_of_reflTransGen_r3 {n : ℕ} {r : Fin n → Fin n → Prop}
    {a c : Fin n} (h : Relation.ReflTransGen r a c) :
    ∃ l : List (Fin n), (a :: l).IsChain r ∧ (a :: l).getLast? = some c ∧
      ∀ y ∈ l, (∃ u, r u y) ∧ Relation.ReflTransGen r a y := by
  sorry

/-- A directed path whose nodes after the first avoid `C` is a path not blocked by `C`. -/
private lemma exists_path_not_blocked_r3 {α : Type*} {n : ℕ} (B : BayesNet α n)
    {C : Set (Fin n)} {z t : Fin n} (h : B.IsDescendant z t)
    (hC : ∀ d, B.IsDescendant z d → d ≠ z → d ∉ C) :
    ∃ p, B.IsPath z t p ∧ ¬B.PathBlocked C p := by
  sorry

/-- Step 1 of rule 3: no node of `ZW` is an ancestor, in `G_{bar X}`, of a node of `Y ∪ W`. -/
private lemma not_isDescendant_rule3_r3 {α : Type*} [Nonempty α] {n : ℕ} (b : BayesNet α n)
    {X Y Z W ZW : Finset (Fin n)} (x : Fin n → α)
    (hZWdef : ∀ z, z ∈ ZW ↔ z ∈ Z ∧ ∀ w ∈ W, ¬(b.mutilateSet X x).IsDescendant z w)
    (hd : (b.mutilateSet (X ∪ ZW) x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n))) :
    ∀ z ∈ ZW, ∀ t ∈ Y ∪ W, ¬(b.mutilateSet X x).IsDescendant z t := by
  sorry

/-- Copy of the private prelude lemma `marginal_eq_of_tables`. -/
private lemma marginal_eq_of_tables_r3 {α : Type*} [Nonempty α] [Fintype α] {n : ℕ}
    (b b' : BayesNet α n) {N : Finset (Fin n)} (hN : b.IsAncestral N)
    (hN' : b'.IsAncestral N)
    (htab : ∀ j ∈ N, ∀ x, (b.cpt j (b.paVal j x)).weights (x j) =
      (b'.cpt j (b'.paVal j x)).weights (x j))
    {S : Finset (Fin n)} (hS : S ⊆ N) (x' : Fin n → α) :
    marginal b.joint ↑S x' = marginal b'.joint ↑S x' := by
  sorry

/-- Intervening on `T` does not change the law of a set `S` containing no descendant of `T`. -/
private lemma marginal_mutilateSet_of_not_isDescendant_r3 {α : Type*} [Nonempty α]
    [Fintype α] {n : ℕ} (B : BayesNet α n) (T S : Finset (Fin n)) (w : Fin n → α)
    (hS : ∀ t ∈ T, ∀ s ∈ S, ¬B.IsDescendant t s) (x' : Fin n → α) :
    marginal (B.mutilateSet T w).joint ↑S x' = marginal B.joint ↑S x' := by
  sorry

/-- Two interventions with the same values compose. -/
private lemma joint_mutilateSet_mutilateSet_r3 {α : Type*} [Nonempty α] {n : ℕ}
    (B : BayesNet α n) (A A' : Finset (Fin n)) (w : Fin n → α) :
    ((B.mutilateSet A w).mutilateSet A' w).joint = (B.mutilateSet (A ∪ A') w).joint := by
  sorry

/-- A list of nonzero elements of `Fin (n + 1)` is the image of a list under `Fin.succ`. -/
private lemma exists_eq_map_succ_r3 {n : ℕ} (l : List (Fin (n + 1))) (h : ∀ v ∈ l, v ≠ 0) :
    ∃ L : List (Fin n), l = L.map Fin.succ := by
  sorry

/-- Prior of the intervention switch: weight `1/2` on `a` and weight `1/2` on `c`. -/
private noncomputable def switchPrior_r3 {α : Type*} (a c : α) :
    Convexity.StdSimplex ℝ α :=
  sorry

private lemma switchPrior_r3_weights_left_pos {α : Type*} (a c : α) :
    0 < (switchPrior_r3 a c).weights a := by
  sorry

private lemma switchPrior_r3_weights_right_pos {α : Type*} (a c : α) :
    0 < (switchPrior_r3 a c).weights c := by
  sorry

/-- Parents in the switch network on `n + 1` nodes: node `0` is the switch (no parents); node
`j.succ` has the parents of `j` in `B` shifted by one, plus node `0` when `j ∈ T`. -/
private def switchPa_r3 {α : Type*} {n : ℕ} (B : BayesNet α n) (T : Finset (Fin n)) :
    (k : Fin (n + 1)) → Finset (Fin k) :=
  sorry

/-- The switch network: node `0` has table `switchPrior_r3 a c`; node `j.succ` with `j ∈ T` has
the point mass at `x j` when node `0` equals `a` and the table of `j` in `B` otherwise; every
other node `j.succ` has the table of `j` in `B`. -/
private noncomputable def switchNet_r3 {α : Type*} [DecidableEq α] {n : ℕ} (B : BayesNet α n)
    (T : Finset (Fin n)) (x : Fin n → α) (a c : α) : BayesNet α (n + 1) :=
  sorry

private lemma switchNet_r3_factor_zero {α : Type*} [DecidableEq α] {n : ℕ} (B : BayesNet α n)
    (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (v : Fin (n + 1) → α) :
    ((switchNet_r3 B T x a c).cpt 0 fun i => v (Fin.castLE (0 : Fin (n + 1)).2.le i)).weights
        (v 0) = (switchPrior_r3 a c).weights (v 0) := by
  sorry

private lemma switchNet_r3_factor_succ {α : Type*} [DecidableEq α] [Nonempty α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (v : Fin (n + 1) → α)
    (j : Fin n) :
    ((switchNet_r3 B T x a c).cpt j.succ fun i => v (Fin.castLE j.succ.2.le i)).weights
        (v j.succ) =
      if j ∈ T ∧ v 0 = a then (if v j.succ = x j then 1 else 0)
      else (B.cpt j (B.paVal j (Fin.tail v))).weights (v j.succ) := by
  sorry

private lemma switchNet_r3_edge_succ_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {i j : Fin n} :
    (switchNet_r3 B T x a c).Edge i.succ j.succ ↔ B.Edge i j := by
  sorry

private lemma switchNet_r3_edge_zero_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {j : Fin n} :
    (switchNet_r3 B T x a c).Edge 0 j.succ ↔ j ∈ T := by
  sorry

private lemma switchNet_r3_not_edge_zero {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (i : Fin (n + 1)) :
    ¬(switchNet_r3 B T x a c).Edge i 0 := by
  sorry

private lemma switchNet_r3_isDescendant_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {i : Fin n}
    {d : Fin (n + 1)} (h : (switchNet_r3 B T x a c).IsDescendant i.succ d) :
    ∃ d₀ : Fin n, d = d₀.succ ∧ B.IsDescendant i d₀ := by
  sorry

private lemma switchNet_r3_adj_succ_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {i j : Fin n} :
    (switchNet_r3 B T x a c).Adj i.succ j.succ ↔ B.Adj i j := by
  sorry

private lemma switchNet_r3_isPath_map {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {t y : Fin n}
    {L : List (Fin n)} (hp : (switchNet_r3 B T x a c).IsPath t.succ y.succ (L.map Fin.succ)) :
    B.IsPath t y L := by
  sorry

private lemma switchNet_r3_blockedAt_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T C : Finset (Fin n)) (x : Fin n → α) (a c : α) {u m w : Fin n}
    (h : B.BlockedAt (C : Set (Fin n)) u m w) :
    (switchNet_r3 B T x a c).BlockedAt
      ((C.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1))) u.succ m.succ
      w.succ := by
  sorry

private lemma switchNet_r3_dSeparated {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) {T Y C : Finset (Fin n)} (x : Fin n → α) (a c : α)
    (hd : B.DSeparated (T : Set (Fin n)) (Y : Set (Fin n)) (C : Set (Fin n))) :
    (switchNet_r3 B T x a c).DSeparated (({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((Y.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((C.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
  sorry

private lemma switchNet_r3_joint_cons {α : Type*} [DecidableEq α] [Nonempty α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (f : α)
    (v : Fin n → α) :
    (switchNet_r3 B T x a c).joint (Fin.cons f v) =
      (switchPrior_r3 a c).weights f *
        (if f = a then (B.mutilateSet T x).joint v else B.joint v) := by
  sorry

private lemma switchNet_r3_marginal_cons {α : Type*} [DecidableEq α] [Nonempty α] [Fintype α]
    {n : ℕ} (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α)
    (S : Finset (Fin n)) (f : α) (v : Fin n → α) :
    marginal (switchNet_r3 B T x a c).joint
        ((insert 0 (S.map (Fin.succEmb n)) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
        (Fin.cons f v) =
      (switchPrior_r3 a c).weights f *
        (if f = a then marginal (B.mutilateSet T x).joint ↑S v
          else marginal B.joint ↑S v) := by
  sorry

/-- Core of rule 3, with no positivity hypothesis: if `T` and `Y` are d-separated by `C` in
`B`, then `P(y, c | do(t)) P(c) = P(y, c) P(c | do(t))` at the values of `x`. -/
private lemma marginal_mutilateSet_mul_of_dSeparated_r3 {α : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] {n : ℕ} (B : BayesNet α n) {T Y C : Finset (Fin n)}
    (x : Fin n → α)
    (hd : B.DSeparated (T : Set (Fin n)) (Y : Set (Fin n)) (C : Set (Fin n))) :
    marginal (B.mutilateSet T x).joint ↑(Y ∪ C) x * marginal B.joint ↑C x =
      marginal B.joint ↑(Y ∪ C) x * marginal (B.mutilateSet T x).joint ↑C x := by
  sorry

/-- **Rule 3 of the do-calculus** (insertion/deletion of actions; Pearl 1995, Theorem 3; Pearl
2009, Theorem 3.4.1): let `ZW` be the nodes of `Z` that are not ancestors of any node of `W`
in `G_{bar X}` (Pearl's `Z(W)`). If `Y` and `Z` are d-separated by `X ∪ W` in
`G_{bar X overline{Z(W)}}` (the graph of `b.mutilateSet (X ∪ ZW) x`), then
`P(y | do(x), do(z), w) = P(y | do(x), w)`, wherever both conditional probabilities are
defined. -/
theorem doCalculus_rule3 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y Z W : Finset (Fin n)} (x : Fin n → α)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hYW : Disjoint Y W) (hZW : Disjoint Z W) (ZW : Finset (Fin n))
    (hZWdef : ∀ z, z ∈ ZW ↔ z ∈ Z ∧ ∀ w ∈ W, ¬(b.mutilateSet X x).IsDescendant z w)
    (hd : (b.mutilateSet (X ∪ ZW) x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)))
    (hwz : marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x ≠ 0)
    (hw : marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x ≠ 0) :
    marginal (b.mutilateSet (X ∪ Z) x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x =
      marginal (b.mutilateSet X x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x := by
  sorry

/-- The two-node network `0 → 1` with constant-`true` tables, for the examples below. -/
noncomputable def chain2 : BayesNet Bool 2 where
  pa k := Finset.univ.filter fun i : Fin k => i.val + 1 = k.val
  cpt _ _ := Convexity.StdSimplex.single true

/-- Rule 2 on the two-node network `0 → 1`, with `Z = ∅` so `hd` holds vacuously. -/
example : marginal (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint
      ((({1} ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) /
      marginal (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint
      ((∅ : Finset (Fin 2)) : Set (Fin 2)) (fun _ => true) =
    marginal (chain2.mutilateSet ∅ (fun _ => true)).joint
      ((({1} ∪ ∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) /
      marginal (chain2.mutilateSet ∅ (fun _ => true)).joint
      (((∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) := by
  have dXY : Disjoint (∅ : Finset (Fin 2)) ({1} : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have dXZ : Disjoint (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have dXW : Disjoint (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have dYZ : Disjoint ({1} : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a _ haE => (notMem_empty a haE).elim
  have dYW : Disjoint ({1} : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a _ haE => (notMem_empty a haE).elim
  have dZW : Disjoint (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) :=
    disjoint_left.2 fun a ha _ => (notMem_empty a ha).elim
  have hd : ((chain2.mutilateSet ∅ (fun _ => true)).cutOut ∅ (fun _ => true)).DSeparated
      (({1} : Finset (Fin 2)) : Set (Fin 2)) ((∅ : Finset (Fin 2)) : Set (Fin 2))
      (((∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) :=
    fun x _ y hy p _ => (notMem_empty y (mem_coe.1 hy)).elim
  have hpos : ∀ (P : (Fin 2 → Bool) → ℝ) (S : Finset (Fin 2)), (∀ v, 0 ≤ P v) →
      P (fun _ => true) = 1 → marginal P (S : Set (Fin 2)) (fun _ => true) ≠ 0 := by
    intro P S hnn h1
    simp only [marginal_coe]
    have ha : (fun _ => true) ∈
        univ.filter (fun v : Fin 2 → Bool => ∀ i ∈ S, v i = (fun _ => true) i) :=
      mem_filter.2 ⟨mem_univ _, fun _ _ => rfl⟩
    have hle : (1 : ℝ) ≤
        ∑ v ∈ univ.filter (fun v : Fin 2 → Bool => ∀ i ∈ S, v i = (fun _ => true) i), P v := by
      rw [← h1]
      exact Finset.single_le_sum (fun v _ => hnn v) ha
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hle)
  have hcpt : ∀ (j : Fin 2) (u : chain2.pa j → Bool),
      chain2.cpt j u = Convexity.StdSimplex.single true :=
    fun j u => rfl
  have hj1 : (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint (fun _ => true) = 1 := by
    rw [joint_mutilateSet]
    refine prod_eq_one fun j _ => ?_
    by_cases hj : j ∈ (∅ ∪ ∅ : Finset (Fin 2))
    · rcases mem_union.1 hj with h | h <;> exact (notMem_empty j h).elim
    · simp only [if_neg hj]
      rw [hcpt]
      simp [Convexity.StdSimplex.single]
  have hj0 : (chain2.mutilateSet ∅ (fun _ => true)).joint (fun _ => true) = 1 := by
    rw [joint_mutilateSet]
    refine prod_eq_one fun j _ => ?_
    by_cases hj : j ∈ (∅ : Finset (Fin 2))
    · exact (notMem_empty j hj).elim
    · simp only [if_neg hj]
      rw [hcpt]
      simp [Convexity.StdSimplex.single]
  have hnn1 : ∀ v, 0 ≤ (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint v :=
    fun v => (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).toChain.joint_nonneg 2 v
  have hnn0 : ∀ v, 0 ≤ (chain2.mutilateSet ∅ (fun _ => true)).joint v :=
    fun v => (chain2.mutilateSet ∅ (fun _ => true)).toChain.joint_nonneg 2 v
  have hw : marginal (chain2.mutilateSet (∅ ∪ ∅) (fun _ => true)).joint
      ((∅ : Finset (Fin 2)) : Set (Fin 2)) (fun _ => true) ≠ 0 :=
    hpos _ _ hnn1 hj1
  have hzw : marginal (chain2.mutilateSet ∅ (fun _ => true)).joint
      (((∅ ∪ ∅ : Finset (Fin 2))) : Set (Fin 2)) (fun _ => true) ≠ 0 :=
    hpos _ _ hnn0 hj0
  exact doCalculus_rule2 chain2 (fun _ => true) dXY dXZ dXW dYZ dYW dZW hd hw hzw

/-- `cutOut` removes the arrows out of the cut set, so no arrow leaves it. -/
example {α : Type*} {n : ℕ} (b : BayesNet α n) (z : Fin n → α) {i j : Fin n} :
    ¬ (b.cutOut {i} z).Edge i j := by
  simp [edge_cutOut_iff]

end BayesNet

end Cslib.MachineLearning.GraphicalModels
