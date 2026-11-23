/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.FiniteMarkovChain

open MeasureTheory ProbabilityTheory Finset BigOperators

namespace StochasticMatrix

variable {M : ℕ}

/-- The `n`-th matrix power of a stochastic transition matrix `P`. Entry `(i,j)` represents
the probability of moving from state `i` to state `j` in exactly `n` steps. -/
def matPow (P : StochasticMatrix M) : ℕ → (Fin (M + 1) → Fin (M + 1) → ℝ)
  | 0 => fun i j => if i = j then 1 else 0
  | n + 1 => fun i j => ∑ k, P.prob i k * P.matPow n k j

/-- A stochastic matrix `P` is **irreducible** if for every pair of states `i, j` there is some
positive number of steps `n` such that `P^n i j > 0`; i.e., every state is reachable from every
other state in finitely many steps. -/
def IsIrreducible (P : StochasticMatrix M) : Prop :=
  ∀ i j : Fin (M + 1), ∃ n : ℕ, 0 < n ∧ 0 < P.matPow n i j

/-- A **probability distribution** on the finite state space `Fin (M + 1)`: a function
`val : Fin (M + 1) → ℝ` whose values are nonnegative and sum to `1`. -/
structure Distribution (M : ℕ) where
  val : Fin (M + 1) → ℝ
  nonneg : ∀ i, 0 ≤ val i
  sum_one : ∑ i, val i = 1

/-- A distribution `π` is **stationary** for the transition matrix `P` if `π P = π`, i.e.,
`∑ᵢ π(i) P(i, j) = π(j)` for every state `j`. -/
def IsStationary (P : StochasticMatrix M) (π : Distribution M) : Prop :=
  ∀ j, ∑ i, π.val i * P.prob i j = π.val j

/-- The **detailed balance** (reversibility) equations between `P` and `π`:
`π(i) P(i,j) = π(j) P(j,i)` for all states `i, j`. -/
def DetailedBalance (P : StochasticMatrix M) (π : Distribution M) : Prop :=
  ∀ i j : Fin (M + 1), π.val i * P.prob i j = π.val j * P.prob j i

/-- A transition matrix `P` is **reversible** if there exists a distribution `π` that is
both stationary and satisfies the detailed balance equations with `P`. -/
def IsReversible (P : StochasticMatrix M) : Prop :=
  ∃ π : Distribution M, P.IsStationary π ∧ P.DetailedBalance π

/-- If `π` satisfies detailed balance with `P`, then `π` is stationary for `P`. Detailed
balance is a strictly stronger condition than stationarity. -/
theorem detailedBalance_isStationary (P : StochasticMatrix M) (π : Distribution M)
    (hdb : P.DetailedBalance π) : P.IsStationary π := by
  intro j
  calc ∑ i, π.val i * P.prob i j
      = ∑ i, π.val j * P.prob j i := by congr 1; ext i; exact hdb i j
    _ = π.val j * ∑ i, P.prob j i := by rw [← Finset.mul_sum]
    _ = π.val j * 1 := by rw [P.row_sum j]
    _ = π.val j := mul_one _

/-- The product of transition probabilities along a path: for a list of states
`[x₀, x₁, …, x_k]`, returns `∏ᵢ P(xᵢ, xᵢ₊₁)`. Empty and singleton lists give `1`. -/
def pathProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => P.prob a b * P.pathProduct (b :: rest)

/-- **Kolmogorov's cycle condition** on a stochastic matrix `P`:
(1) `symm_support`: `P(x, y) > 0` implies `P(y, x) > 0`; and
(2) `cycle_prod`: for any loop `x₀, x₁, …, xₙ = x₀` whose reverse path has positive
probability, the product of forward transition probabilities along the loop equals the
product of backward transition probabilities. This is the necessary and sufficient
condition for the existence of a reversible measure for an irreducible chain. -/
structure KolmogorovCycleCondition (P : StochasticMatrix M) : Prop where
  symm_support : ∀ x y : Fin (M + 1), P.prob x y > 0 → P.prob y x > 0
  cycle_prod : ∀ (n : ℕ) (c : Fin (n + 1) → Fin (M + 1)), c 0 = c (Fin.last n) →
    (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc)) > 0 →
    (∏ i : Fin n, P.prob (c i.castSucc) (c i.succ)) =
      (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc))

/-- Every entry of every power of a stochastic matrix is nonnegative. -/
lemma matPow_nonneg (P : StochasticMatrix M) : ∀ (n : ℕ) (i j : Fin (M + 1)),
    0 ≤ P.matPow n i j := by
  intro n
  induction n with
  | zero => intro i j; simp only [matPow]; split_ifs <;> linarith
  | succ k ih =>
    intro i j
    simp only [matPow]
    exact Finset.sum_nonneg (fun c _ => mul_nonneg (P.nonneg i c) (ih c j))

/-- For an irreducible chain `P`, any distribution `π` satisfying detailed balance
must assign strictly positive mass to every state. -/
lemma distribution_pos_of_irreducible_detailedBalance
    (P : StochasticMatrix M) (π : Distribution M)
    (hirr : P.IsIrreducible) (hdb : P.DetailedBalance π) :
    ∀ i, 0 < π.val i := by

  have hsome : ∃ j, 0 < π.val j := by
    by_contra h
    push Not at h
    have hzero : ∀ j, π.val j = 0 := fun j => le_antisymm (h j) (π.nonneg j)
    have hsum : ∑ i : Fin (M + 1), π.val i = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hzero i
    linarith [π.sum_one]
  obtain ⟨j₀, hj₀⟩ := hsome

  have step : ∀ a c, 0 < π.val a → 0 < P.prob a c → 0 < π.val c := by
    intro a c ha hPac
    have hdb_ac := hdb a c

    have hLHS : 0 < π.val a * P.prob a c := mul_pos ha hPac
    rw [hdb_ac] at hLHS

    exact pos_of_mul_pos_left hLHS (P.nonneg c a)

  have key : ∀ (m : ℕ), ∀ a b, 0 < π.val a → 0 < P.matPow m a b → 0 < π.val b := by
    intro m
    induction m with
    | zero =>
      intro a b ha hm
      simp only [matPow] at hm
      split_ifs at hm with heq
      · exact heq ▸ ha
      · linarith
    | succ k ih =>
      intro a b ha hm
      simp only [matPow] at hm

      rw [Finset.sum_pos_iff_of_nonneg
        (fun c _ => mul_nonneg (P.nonneg a c) (matPow_nonneg P k c b))] at hm
      obtain ⟨c, _, hc⟩ := hm
      have hPac : 0 < P.prob a c := pos_of_mul_pos_left hc (matPow_nonneg P k c b)
      have hPkb : 0 < P.matPow k c b := pos_of_mul_pos_right hc (P.nonneg a c)
      exact ih c b (step a c ha hPac) hPkb

  intro i
  obtain ⟨n, _, hn⟩ := hirr j₀ i
  exact key n j₀ i hj₀ hn

/-- Helper lemma: along a loop `c : Fin (n + 1) → Fin (M + 1)` with `c 0 = c (Fin.last n)`,
the product `∏ i, f (c (i.castSucc))` equals the shifted product `∏ i, f (c (i.succ))`.
This is a telescoping/cyclic rearrangement of products. -/
lemma prod_castSucc_eq_prod_succ {n : ℕ} {M : ℕ}
    (f : Fin (M + 1) → ℝ) (c : Fin (n + 1) → Fin (M + 1))
    (hcycle : c 0 = c (Fin.last n)) :
    ∏ i : Fin n, f (c i.castSucc) = ∏ i : Fin n, f (c i.succ) := by


  have h1 : ∏ i : Fin (n + 1), f (c i) =
      (∏ i : Fin n, f (c i.castSucc)) * f (c (Fin.last n)) :=
    Fin.prod_univ_castSucc (fun i => f (c i))
  have h2 : ∏ i : Fin (n + 1), f (c i) =
      f (c 0) * (∏ i : Fin n, f (c i.succ)) :=
    Fin.prod_univ_succ (fun i => f (c i))


  cases n with
  | zero => simp
  | succ k =>


    have heq := h1.symm.trans h2

    rw [← hcycle] at heq

    rw [mul_comm] at heq

    by_cases hfc : f (c 0) = 0
    ·
      have hL : ∏ i : Fin (k + 1), f (c i.castSucc) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k + 1)))
        show f (c ((0 : Fin (k + 1)).castSucc)) = 0
        have : ((0 : Fin (k + 1)).castSucc : Fin (k + 2)) = (0 : Fin (k + 2)) := by
          ext; simp [Fin.castSucc]
        rw [this]; exact hfc
      have hR : ∏ i : Fin (k + 1), f (c i.succ) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last k))
        show f (c ((Fin.last k).succ)) = 0
        have : ((Fin.last k).succ : Fin (k + 2)) = Fin.last (k + 1) := by
          ext; simp [Fin.last]
        rw [this, ← hcycle, hfc]
      rw [hL, hR]
    · exact mul_left_cancel₀ hfc heq

/-- `NNReal`-valued version of `pathProduct`: the product of forward transition probabilities
along the path, packaged as a nonnegative real. -/
noncomputable def listPathProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → NNReal
  | [] => 1
  | [_] => 1
  | a :: b :: rest => ⟨P.prob a b, P.nonneg a b⟩ * listPathProduct P (b :: rest)

/-- The product of ratios `P(xᵢ, xᵢ₊₁) / P(xᵢ₊₁, xᵢ)` along a path. This is the quantity
that defines the "cycle weight" used to construct a reversible measure from Kolmogorov's
cycle condition. -/
noncomputable def listRatioProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → NNReal
  | [] => 1
  | [_] => 1
  | a :: b :: rest =>
    (⟨P.prob a b, P.nonneg a b⟩ / ⟨P.prob b a, P.nonneg b a⟩) * listRatioProduct P (b :: rest)

/-- If the forward `listPathProduct` along a path is positive and the transition probabilities
have symmetric support, then the corresponding `listRatioProduct` is also positive. -/
lemma listRatioProduct_pos_of_listPathProduct_pos (P : StochasticMatrix M)
    (hsymm : ∀ x y : Fin (M + 1), P.prob x y > 0 → P.prob y x > 0)
    (path : List (Fin (M + 1))) (h : 0 < listPathProduct P path) :
    0 < listRatioProduct P path := by
  induction path with
  | nil => simp [listRatioProduct]
  | cons a tail ih =>
    cases tail with
    | nil => simp [listRatioProduct]
    | cons b rest =>
      simp only [listRatioProduct, listPathProduct] at *
      have hPab : (0 : NNReal) < ⟨P.prob a b, P.nonneg a b⟩ :=
        pos_of_mul_pos_left h (by positivity)
      have hPba_pos : P.prob b a > 0 := hsymm a b (NNReal.coe_pos.mpr hPab)
      have hPba : (0 : NNReal) < ⟨P.prob b a, P.nonneg b a⟩ := NNReal.coe_pos.mp hPba_pos
      have h_tail : 0 < listPathProduct P (b :: rest) :=
        pos_of_mul_pos_right h (by positivity)
      exact mul_pos (div_pos hPab hPba) (ih h_tail)


/-- If `P.matPow n i j > 0`, then there is an actual path from `i` to `j` (a list of states
starting at `i` and ending at `j`) along which the product of transition probabilities is
positive. -/
lemma exists_path_of_matPow_pos (P : StochasticMatrix M) :
    ∀ (n : ℕ) (i j : Fin (M + 1)), 0 < n → 0 < P.matPow n i j →
    ∃ path : List (Fin (M + 1)),
      path.head? = some i ∧ path.getLast? = some j ∧ 0 < listPathProduct P path := by
  intro n
  induction n with
  | zero => intro i j hn; omega
  | succ k ih =>
    intro i j _ hpos
    simp only [matPow] at hpos
    rw [Finset.sum_pos_iff_of_nonneg
      (fun m _ => mul_nonneg (P.nonneg i m) (matPow_nonneg P k m j))] at hpos
    obtain ⟨m, _, hm⟩ := hpos
    have hPim : 0 < P.prob i m := pos_of_mul_pos_left hm (matPow_nonneg P k m j)
    have hPkj : 0 < P.matPow k m j := pos_of_mul_pos_right hm (P.nonneg i m)
    by_cases hk : k = 0
    · subst hk
      simp only [matPow] at hPkj
      split_ifs at hPkj with heq
      · subst heq
        refine ⟨[i, m], by simp, by simp, ?_⟩
        simp only [listPathProduct]
        rw [mul_one]
        exact NNReal.coe_pos.mp hPim
      · linarith
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      obtain ⟨path, hhead, hlast, hprod⟩ := ih m j hk_pos hPkj
      cases path with
      | nil => simp at hhead
      | cons a tail =>
        simp at hhead
        subst hhead
        refine ⟨i :: a :: tail, by simp, ?_, ?_⟩
        · simp only [List.getLast?]
          simp only [List.getLast?] at hlast
          exact hlast
        · simp only [listPathProduct]
          exact mul_pos (NNReal.coe_pos.mp hPim) hprod

/-- For an irreducible chain, between any two states `i, j` there exists a finite path
from `i` to `j` along which the product of transition probabilities is strictly positive. -/
theorem IsIrreducible.exists_path {P : StochasticMatrix M} (hirr : P.IsIrreducible)
    (i j : Fin (M + 1)) :
    ∃ path : List (Fin (M + 1)),
      path.head? = some i ∧ path.getLast? = some j ∧ 0 < listPathProduct P path := by
  obtain ⟨n, hn_pos, hn⟩ := hirr i j
  exact exists_path_of_matPow_pos P n i j hn_pos hn

/-- Variant of `IsIrreducible.exists_path`: under symmetric support, there also exists a path
from `i` to `j` along which the `listRatioProduct` is positive. -/
theorem IsIrreducible.exists_path_ratio {P : StochasticMatrix M} (hirr : P.IsIrreducible)
    (hsymm : ∀ x y : Fin (M + 1), P.prob x y > 0 → P.prob y x > 0)
    (i j : Fin (M + 1)) :
    ∃ path : List (Fin (M + 1)),
      path.head? = some i ∧ path.getLast? = some j ∧ 0 < listRatioProduct P path := by
  obtain ⟨path, hhead, hlast, hprod⟩ := hirr.exists_path i j
  exact ⟨path, hhead, hlast, listRatioProduct_pos_of_listPathProduct_pos P hsymm path hprod⟩

/-- Unfolding of `listRatioProduct` on a list of the form `c 0 :: List.ofFn (c ∘ Fin.succ)`. -/
lemma listRatioProduct_cons_ofFn (P : StochasticMatrix M) (n : ℕ)
    (c : Fin (n + 2) → Fin (M + 1)) :
    listRatioProduct P (c 0 :: List.ofFn (fun i : Fin (n + 1) => c i.succ)) =
    (⟨P.prob (c 0) (c 1), P.nonneg _ _⟩ / ⟨P.prob (c 1) (c 0), P.nonneg _ _⟩) *
    listRatioProduct P (List.ofFn (fun i : Fin (n + 1) => c i.succ)) := by
  rw [show List.ofFn (fun i : Fin (n + 1) => c i.succ) =
         c (Fin.succ 0) :: List.ofFn (fun i : Fin n => c i.succ.succ) from List.ofFn_succ,
      show (1 : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) from rfl]; rfl

/-- `listRatioProduct` along `List.ofFn c` is the finite product of ratios
`P(c iₖ, c iₖ₊₁) / P(c iₖ₊₁, c iₖ)` indexed by `i : Fin n`. -/
lemma listRatioProduct_ofFn (P : StochasticMatrix M) :
    ∀ (n : ℕ) (c : Fin (n + 1) → Fin (M + 1)),
    listRatioProduct P (List.ofFn c) =
    ∏ i : Fin n, (⟨P.prob (c i.castSucc) (c i.succ), P.nonneg _ _⟩ /
                   ⟨P.prob (c i.succ) (c i.castSucc), P.nonneg _ _⟩ : NNReal) := by
  intro n; induction n with
  | zero => intro c; simp [List.ofFn_succ, List.ofFn_zero, listRatioProduct]
  | succ k ih =>
    intro c
    rw [show List.ofFn c = c 0 :: List.ofFn (fun i : Fin (k + 1) => c i.succ) from List.ofFn_succ,
        listRatioProduct_cons_ofFn, ih (fun i => c i.succ), Fin.prod_univ_succ]; rfl

/-- Under Kolmogorov's cycle condition, the ratio product along any closed loop (a path whose
first and last elements coincide and whose reverse edges all have positive probability) is
equal to `1`. -/
lemma listRatioProduct_cycle_eq_one (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition)
    (path : List (Fin (M + 1))) (hlen : 2 ≤ path.length) (hne : path ≠ [])
    (hloop : path.head hne = path.getLast hne)
    (hpos : ∀ i : Fin (path.length - 1),
      0 < P.prob (path.get ⟨i + 1, by omega⟩) (path.get ⟨i, by omega⟩)) :
    listRatioProduct P path = 1 := by
  set n := path.length - 1
  have hlen_eq : path.length = n + 1 := by omega
  set c : Fin (n + 1) → Fin (M + 1) := fun i => path.get (i.cast hlen_eq.symm)
  have path_eq : path = List.ofFn c := by
    conv_lhs => rw [← List.ofFn_get (l := path)]
    rw [List.ofFn_congr hlen_eq]
  have hc0 : c 0 = path.head hne := by
    simp only [c]; cases path with | nil => contradiction | cons a t => rfl
  have hclast : c (Fin.last n) = path.getLast hne := by
    simp only [c]
    have hcast : (Fin.last n).cast hlen_eq.symm = ⟨path.length - 1, by omega⟩ := by
      ext; simp [Fin.last, Fin.cast]; omega
    rw [hcast]; exact List.get_length_sub_one _
  have hloop_fin : c 0 = c (Fin.last n) := by rw [hc0, hclast, hloop]
  have hbwd_pos : ∏ i : Fin n, P.prob (c i.succ) (c i.castSucc) > 0 := by
    apply Finset.prod_pos; intro i _
    have := hpos ⟨i.val, by omega⟩
    simp only [c, Fin.succ, Fin.castSucc, Fin.cast] at *
    convert this using 2 <;> congr 1 <;> omega
  have hfwd_eq := hcycle.cycle_prod n c hloop_fin hbwd_pos
  rw [path_eq, listRatioProduct_ofFn]
  have : (↑(∏ i : Fin n, (⟨P.prob (c i.castSucc) (c i.succ), P.nonneg _ _⟩ /
      ⟨P.prob (c i.succ) (c i.castSucc), P.nonneg _ _⟩ : NNReal)) : ℝ) = 1 := by
    push_cast; rw [Finset.prod_div_distrib, hfwd_eq]
    exact div_self (ne_of_gt hbwd_pos)
  exact_mod_cast this

/-- The **cycle weight** of state `j` relative to a reference state `i₀`: defined as the
`listRatioProduct` along some (classically chosen) positive-probability path from `i₀` to `j`.
For chains satisfying Kolmogorov's cycle condition this value is path-independent
(`cycleWeight_path_independent`) and yields the unique-up-to-scaling reversible measure. -/
noncomputable def cycleWeight (P : StochasticMatrix M) (hirr : P.IsIrreducible)
    (i₀ : Fin (M + 1)) (j : Fin (M + 1)) : NNReal :=
  listRatioProduct P (Classical.choose (hirr.exists_path i₀ j))

/-- `listRatioProduct` is multiplicative when concatenating two paths that share an endpoint:
joining `l1` with `l2.tail` (so the join point isn't duplicated) gives the product of the
ratio products of `l1` and `l2`. -/
lemma listRatioProduct_append (P : StochasticMatrix M) :
    ∀ (l1 l2 : List (Fin (M + 1))) (hne1 : l1 ≠ []) (hne2 : l2 ≠ []),
    l1.getLast hne1 = l2.head hne2 →
    listRatioProduct P (l1 ++ l2.tail) =
      listRatioProduct P l1 * listRatioProduct P l2 := by
  intro l1
  induction l1 with
  | nil => intro _ hne1; exact absurd rfl hne1
  | cons a t ih =>
    intro l2 _ hne2 hjoin
    cases t with
    | nil =>
      simp only [listRatioProduct, List.singleton_append, one_mul,
                 List.getLast_singleton] at *
      cases l2 with
      | nil => exact absurd rfl hne2
      | cons b rest =>
        simp only [List.head] at hjoin
        subst hjoin
        simp only [List.tail]
    | cons b rest =>
      have htne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
      have hjoin' : (b :: rest).getLast htne = l2.head hne2 := by
        simp only [List.getLast_cons htne] at hjoin; exact hjoin
      have ih_eq := ih l2 htne hne2 hjoin'
      show (⟨P.prob a b, P.nonneg a b⟩ / ⟨P.prob b a, P.nonneg b a⟩) *
            listRatioProduct P ((b :: rest) ++ l2.tail) =
          (⟨P.prob a b, P.nonneg a b⟩ / ⟨P.prob b a, P.nonneg b a⟩) *
            listRatioProduct P (b :: rest) * listRatioProduct P l2
      rw [ih_eq, mul_assoc]

/-- If the path product along a list `l` is positive, then every consecutive transition
probability `P(l[i], l[i+1])` along `l` is positive. -/
lemma listPathProduct_pos_implies_transitions (P : StochasticMatrix M)
    (l : List (Fin (M + 1))) (hpos : 0 < listPathProduct P l)
    (i : ℕ) (hi : i + 1 < l.length) :
    0 < P.prob (l.get ⟨i, by omega⟩) (l.get ⟨i + 1, hi⟩) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases t with
    | nil => simp at hi
    | cons b rest =>
      simp only [listPathProduct] at hpos
      have hPab : (0 : NNReal) < ⟨P.prob a b, P.nonneg a b⟩ :=
        pos_of_mul_pos_left hpos (by positivity)
      have h_tail : 0 < listPathProduct P (b :: rest) :=
        pos_of_mul_pos_right hpos (by positivity)
      cases i with
      | zero => exact NNReal.coe_pos.mpr hPab
      | succ i => exact ih h_tail i (by simp only [List.length] at hi ⊢; omega)

/-- If two paths `l1, l2` each have positive path product and share an endpoint, then their
join `l1 ++ l2.tail` also has positive path product. -/
lemma listPathProduct_append_pos (P : StochasticMatrix M)
    (l1 l2 : List (Fin (M + 1))) (hne1 : l1 ≠ []) (hne2 : l2 ≠ [])
    (hjoin : l1.getLast hne1 = l2.head hne2)
    (h1 : 0 < listPathProduct P l1) (h2 : 0 < listPathProduct P l2) :
    0 < listPathProduct P (l1 ++ l2.tail) := by
  induction l1 with
  | nil => exact absurd rfl hne1
  | cons a t ih =>
    match t with
    | [] =>
      simp only [List.singleton_append, List.getLast_singleton] at hjoin ⊢
      cases l2 with
      | nil => exact absurd rfl hne2
      | cons b rest =>
        simp only [List.head] at hjoin
        subst hjoin
        simp only [List.tail]
        cases rest with
        | nil => simp [listPathProduct]
        | cons c rest' => simp only [listPathProduct] at h2 ⊢; exact h2
    | b :: rest =>
      have htne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
      have hjoin' : (b :: rest).getLast htne = l2.head hne2 := by
        simp only [List.getLast_cons htne] at hjoin; exact hjoin
      simp only [listPathProduct] at h1 ⊢
      have hPab : (0 : NNReal) < ⟨P.prob a b, P.nonneg a b⟩ :=
        pos_of_mul_pos_left h1 (by positivity : (0 : NNReal) ≤ listPathProduct P (b :: rest))
      have h_tail : 0 < listPathProduct P (b :: rest) :=
        pos_of_mul_pos_right h1 (by positivity : (0 : NNReal) ≤ ⟨P.prob a b, P.nonneg a b⟩)
      exact mul_pos hPab (ih htne hjoin' h_tail)

/-- **Path independence of cycle weight.** Under Kolmogorov's cycle condition, any two
positive-probability paths from `i₀` to `j` yield the same `listRatioProduct`. This is the
key step that makes `cycleWeight` well-defined and ultimately produces a reversible measure. -/
theorem cycleWeight_path_independent (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition) (hirr : P.IsIrreducible) (i₀ j : Fin (M + 1))
    (path1 path2 : List (Fin (M + 1)))
    (h1 : path1.head? = some i₀) (h1' : path1.getLast? = some j)
    (h2 : path2.head? = some i₀) (h2' : path2.getLast? = some j)
    (hp1 : 0 < listPathProduct P path1) (hp2 : 0 < listPathProduct P path2) :
    listRatioProduct P path1 = listRatioProduct P path2 := by

  obtain ⟨p3, hp3_head, hp3_last, hp3_pos⟩ := hirr.exists_path j i₀

  have hne1 : path1 ≠ [] := by intro h; simp [h] at h1
  have hne2 : path2 ≠ [] := by intro h; simp [h] at h2
  have hne3 : p3 ≠ [] := by intro h; simp [h] at hp3_head

  have hlast1 : path1.getLast hne1 = j := by
    have := List.getLast?_eq_some_getLast hne1; rw [this] at h1'; exact Option.some_injective _ h1'
  have hhead1 : path1.head hne1 = i₀ := by
    have := List.head?_eq_some_head hne1; rw [this] at h1; exact Option.some_injective _ h1
  have hlast2 : path2.getLast hne2 = j := by
    have := List.getLast?_eq_some_getLast hne2; rw [this] at h2'; exact Option.some_injective _ h2'
  have hhead2 : path2.head hne2 = i₀ := by
    have := List.head?_eq_some_head hne2; rw [this] at h2; exact Option.some_injective _ h2
  have hlast3 : p3.getLast hne3 = i₀ := by
    have := List.getLast?_eq_some_getLast hne3; rw [this] at hp3_last; exact Option.some_injective _ hp3_last
  have hhead3 : p3.head hne3 = j := by
    have := List.head?_eq_some_head hne3; rw [this] at hp3_head; exact Option.some_injective _ hp3_head

  have hjoin1 : path1.getLast hne1 = p3.head hne3 := by rw [hlast1, hhead3]
  have hjoin2 : path2.getLast hne2 = p3.head hne3 := by rw [hlast2, hhead3]

  set c1 := path1 ++ p3.tail with hc1_def
  set c2 := path2 ++ p3.tail with hc2_def

  have hne_c1 : c1 ≠ [] := List.append_ne_nil_of_left_ne_nil hne1 _
  have hne_c2 : c2 ≠ [] := List.append_ne_nil_of_left_ne_nil hne2 _

  have happ1 := listRatioProduct_append P path1 p3 hne1 hne3 hjoin1
  have happ2 := listRatioProduct_append P path2 p3 hne2 hne3 hjoin2

  have hc1_pos := listPathProduct_append_pos P path1 p3 hne1 hne3 hjoin1 hp1 hp3_pos
  have hc2_pos := listPathProduct_append_pos P path2 p3 hne2 hne3 hjoin2 hp2 hp3_pos

  have hp3_rpos := listRatioProduct_pos_of_listPathProduct_pos P hcycle.symm_support p3 hp3_pos

  have hji_of_ptail_nil : p3.tail = [] → j = i₀ := by
    intro htnil
    cases p3 with | nil => contradiction | cons x t =>
      simp only [List.tail] at htnil; subst htnil

      simp [List.getLast_singleton] at hlast3
      simp at hhead3
      rw [← hhead3, hlast3]

  have hc1_head : c1.head hne_c1 = i₀ := by
    show (path1 ++ p3.tail).head _ = i₀
    rw [List.head_append_of_ne_nil hne1]; exact hhead1
  have hc2_head : c2.head hne_c2 = i₀ := by
    show (path2 ++ p3.tail).head _ = i₀
    rw [List.head_append_of_ne_nil hne2]; exact hhead2

  have hc1_last : c1.getLast hne_c1 = i₀ := by
    show (path1 ++ p3.tail).getLast _ = i₀
    by_cases htail_ne : p3.tail = []
    · simp only [htail_ne, List.append_nil]
      exact hlast1.trans (hji_of_ptail_nil htail_ne)
    · rw [List.getLast_append_of_ne_nil _ htail_ne, List.getLast_tail htail_ne, hlast3]
  have hc2_last : c2.getLast hne_c2 = i₀ := by
    show (path2 ++ p3.tail).getLast _ = i₀
    by_cases htail_ne : p3.tail = []
    · simp only [htail_ne, List.append_nil]
      exact hlast2.trans (hji_of_ptail_nil htail_ne)
    · rw [List.getLast_append_of_ne_nil _ htail_ne, List.getLast_tail htail_ne, hlast3]

  have hc1_loop : c1.head hne_c1 = c1.getLast hne_c1 := by rw [hc1_head, hc1_last]
  have hc2_loop : c2.head hne_c2 = c2.getLast hne_c2 := by rw [hc2_head, hc2_last]


  suffices h_suffices : ∀ (p : List (Fin (M + 1))),
      p.head? = some i₀ → p.getLast? = some j → 0 < listPathProduct P p →
      listRatioProduct P p * listRatioProduct P p3 = 1 by
    have h1eq := h_suffices path1 h1 h1' hp1
    have h2eq := h_suffices path2 h2 h2' hp2
    exact mul_right_cancel₀ (ne_of_gt hp3_rpos) (h1eq.trans h2eq.symm)
  intro p hp_head hp_last hp_pos
  have hne_p : p ≠ [] := by intro h; simp [h] at hp_head
  have hlast_p : p.getLast hne_p = j := by
    have := List.getLast?_eq_some_getLast hne_p; rw [this] at hp_last
    exact Option.some_injective _ hp_last
  have hhead_p : p.head hne_p = i₀ := by
    have := List.head?_eq_some_head hne_p; rw [this] at hp_head
    exact Option.some_injective _ hp_head
  have hjoin_p : p.getLast hne_p = p3.head hne3 := by rw [hlast_p, hhead3]
  have happ_p := listRatioProduct_append P p p3 hne_p hne3 hjoin_p

  set cp := p ++ p3.tail
  have hne_cp : cp ≠ [] := List.append_ne_nil_of_left_ne_nil hne_p _
  have hcp_pos := listPathProduct_append_pos P p p3 hne_p hne3 hjoin_p hp_pos hp3_pos

  by_cases hcp_len : 2 ≤ cp.length
  ·
    have hcp_head : cp.head hne_cp = i₀ := by
      show (p ++ p3.tail).head _ = i₀
      rw [List.head_append_of_ne_nil hne_p]; exact hhead_p
    have hcp_last : cp.getLast hne_cp = i₀ := by
      show (p ++ p3.tail).getLast _ = i₀
      by_cases htail_ne : p3.tail = []
      · simp only [htail_ne, List.append_nil]
        exact hlast_p.trans (hji_of_ptail_nil htail_ne)
      · rw [List.getLast_append_of_ne_nil _ htail_ne, List.getLast_tail htail_ne, hlast3]
    have hcp_loop : cp.head hne_cp = cp.getLast hne_cp := by rw [hcp_head, hcp_last]
    have hcp_bwd : ∀ i : Fin (cp.length - 1),
        0 < P.prob (cp.get ⟨i + 1, by omega⟩) (cp.get ⟨i, by omega⟩) := by
      intro ⟨i, hi⟩
      exact hcycle.symm_support _ _
        (listPathProduct_pos_implies_transitions P cp hcp_pos i (by omega))
    have heq_cp : listRatioProduct P cp = 1 :=
      listRatioProduct_cycle_eq_one P hcycle cp hcp_len hne_cp hcp_loop hcp_bwd
    rw [happ_p] at heq_cp; exact heq_cp
  ·
    push Not at hcp_len
    have hcp_len1 : cp.length = 1 := by
      have : 1 ≤ cp.length := List.length_pos_of_ne_nil hne_cp; omega

    have hptail : p3.tail = [] := by
      have hlen : p.length + p3.tail.length = 1 := by
        have : (p ++ p3.tail).length = 1 := hcp_len1
        rwa [List.length_append] at this
      have : 1 ≤ p.length := List.length_pos_of_ne_nil hne_p
      have : p3.tail.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this


    have hji : j = i₀ := hji_of_ptail_nil hptail


    have hp_single : p.length = 1 := by
      have hlen : p.length + p3.tail.length = 1 := by
        have : (p ++ p3.tail).length = 1 := hcp_len1
        rwa [List.length_append] at this
      simp [hptail] at hlen; exact hlen

    have hp_ratio : listRatioProduct P p = 1 := by
      cases p with
      | nil => contradiction
      | cons a t =>
        cases t with
        | nil => simp [listRatioProduct]
        | cons b rest => simp at hp_single

    have hp3_ratio : listRatioProduct P p3 = 1 := by
      cases p3 with
      | nil => contradiction
      | cons a t =>
        simp only [List.tail] at hptail; subst hptail
        simp [listRatioProduct]
    rw [hp_ratio, hp3_ratio, mul_one]

/-- Recursion for `listRatioProduct` when appending a single state `j` at the end of a
nonempty path: the new ratio product equals the old one times the ratio for the new edge. -/
lemma listRatioProduct_snoc (P : StochasticMatrix M) :
    ∀ (path : List (Fin (M + 1))) (j : Fin (M + 1)) (hne : path ≠ []),
    listRatioProduct P (path ++ [j]) =
      listRatioProduct P path *
        (⟨P.prob (path.getLast hne) j, P.nonneg _ j⟩ /
          ⟨P.prob j (path.getLast hne), P.nonneg j _⟩) := by
  intro path
  induction path with
  | nil => intro j hne; contradiction
  | cons a tail ih =>
    intro j hne
    cases tail with
    | nil =>
      simp only [listRatioProduct, List.singleton_append, List.getLast_singleton]
      ring
    | cons b rest =>


      have htail_ne : b :: rest ≠ [] := List.cons_ne_nil b rest
      have ih_eq := ih j htail_ne

      have lhs_eq : listRatioProduct P ((a :: b :: rest) ++ [j]) =
          (⟨P.prob a b, P.nonneg a b⟩ / ⟨P.prob b a, P.nonneg b a⟩) *
            listRatioProduct P ((b :: rest) ++ [j]) := by
        show listRatioProduct P (a :: (b :: rest) ++ [j]) = _
        rfl

      have rhs_eq : listRatioProduct P (a :: b :: rest) =
          (⟨P.prob a b, P.nonneg a b⟩ / ⟨P.prob b a, P.nonneg b a⟩) *
            listRatioProduct P (b :: rest) := rfl
      rw [lhs_eq, ih_eq, rhs_eq]
      simp only [List.getLast_cons htail_ne]
      ring

/-- Extending the path by one positive-probability transition `i → j` multiplies the cycle
weight by `P(i,j) / P(j,i)`. Equivalently, `cycleWeight i₀ j = cycleWeight i₀ i · P(i,j)/P(j,i)`
whenever `P(i,j) > 0`. -/
lemma cycleWeight_extend (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition) (hirr : P.IsIrreducible)
    (i₀ i j : Fin (M + 1)) (hPij : 0 < P.prob i j) :
    cycleWeight P hirr i₀ i *
      (⟨P.prob i j, P.nonneg i j⟩ / ⟨P.prob j i, P.nonneg j i⟩) =
      cycleWeight P hirr i₀ j := by

  let path_i := Classical.choose (hirr.exists_path i₀ i)
  have hspec_i := Classical.choose_spec (hirr.exists_path i₀ i)
  have hhead_i : path_i.head? = some i₀ := hspec_i.1
  have hlast_i : path_i.getLast? = some i := hspec_i.2.1

  have hne_i : path_i ≠ [] := by intro heq; simp [heq] at hhead_i

  have hlast_eq : path_i.getLast hne_i = i := by
    rw [List.getLast?_eq_some_getLast hne_i] at hlast_i
    exact Option.some_injective _ hlast_i

  have hw_i : cycleWeight P hirr i₀ i = listRatioProduct P path_i := rfl

  let ext_path := path_i ++ [j]

  have hsnoc : listRatioProduct P ext_path =
      listRatioProduct P path_i *
        (⟨P.prob (path_i.getLast hne_i) j, P.nonneg _ j⟩ /
          ⟨P.prob j (path_i.getLast hne_i), P.nonneg j _⟩) :=
    listRatioProduct_snoc P path_i j hne_i

  rw [hlast_eq] at hsnoc

  rw [hw_i]
  rw [← hsnoc]


  let path_j := Classical.choose (hirr.exists_path i₀ j)
  have hspec_j := Classical.choose_spec (hirr.exists_path i₀ j)
  have hhead_j : path_j.head? = some i₀ := hspec_j.1
  have hlast_j : path_j.getLast? = some j := hspec_j.2.1

  show listRatioProduct P ext_path = listRatioProduct P path_j

  have hhead_ext : ext_path.head? = some i₀ := by
    show (path_i ++ [j]).head? = some i₀
    rw [List.head?_append_of_ne_nil _ hne_i, hhead_i]
  have hlast_ext : ext_path.getLast? = some j := by
    show (path_i ++ [j]).getLast? = some j
    simp

  have hprod_j : 0 < listPathProduct P path_j := hspec_j.2.2
  have hprod_ext : 0 < listPathProduct P ext_path := by


    have hne_ij : ([i, j] : List _) ≠ [] := List.cons_ne_nil _ _
    have hlast_eq_i : path_i.getLast hne_i = i := hlast_eq
    have hhead_ij : ([i, j] : List _).head hne_ij = i := rfl
    have hjoin_ij : path_i.getLast hne_i = ([i, j] : List _).head hne_ij := by
      rw [hlast_eq_i, hhead_ij]
    have hprod_ij : 0 < listPathProduct P [i, j] := by
      simp only [listPathProduct]; rw [mul_one]; exact NNReal.coe_pos.mp hPij
    have hprod_i := hspec_i.2.2
    have := listPathProduct_append_pos P path_i [i, j] hne_i hne_ij hjoin_ij hprod_i hprod_ij

    simp only [List.tail] at this; exact this
  exact cycleWeight_path_independent P hcycle hirr i₀ j ext_path path_j
    hhead_ext hlast_ext hhead_j hlast_j hprod_ext hprod_j

/-- The cycle weights satisfy the **detailed balance** equations with `P`:
`cycleWeight(i) · P(i,j) = cycleWeight(j) · P(j,i)` for all states `i, j`. -/
theorem cycleWeight_detailed_balance (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition) (hirr : P.IsIrreducible)
    (i₀ i j : Fin (M + 1)) :
    (cycleWeight P hirr i₀ i : ℝ) * P.prob i j =
    (cycleWeight P hirr i₀ j : ℝ) * P.prob j i := by
  by_cases hPij0 : P.prob i j = 0
  ·
    have hPji0 : P.prob j i = 0 := by
      by_contra h; push Not at h
      exact absurd (hcycle.symm_support j i (lt_of_le_of_ne (P.nonneg j i) (Ne.symm h))) (by linarith)
    rw [hPij0, hPji0, mul_zero, mul_zero]
  ·
    have hPij_pos : 0 < P.prob i j := lt_of_le_of_ne (P.nonneg i j) (Ne.symm hPij0)

    have hPji_pos : 0 < P.prob j i := hcycle.symm_support i j hPij_pos
    have hPji_ne : P.prob j i ≠ 0 := ne_of_gt hPji_pos
    have h_ij := cycleWeight_extend P hcycle hirr i₀ i j hPij_pos
    have h_ij_real : (cycleWeight P hirr i₀ i : ℝ) * (P.prob i j / P.prob j i) =
        (cycleWeight P hirr i₀ j : ℝ) := by
      have h := h_ij
      apply_fun (fun x => (x : ℝ)) at h
      simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_mk] at h
      exact h


    field_simp at h_ij_real
    linarith

/-- **Kolmogorov's cycle theorem.** For an irreducible finite Markov chain with transition
matrix `P`, there exists a reversible measure (i.e., `P.IsReversible`) if and only if `P`
satisfies the Kolmogorov cycle condition:
(1) `P(x,y) > 0` implies `P(y,x) > 0`; and
(2) for any loop `x₀, x₁, …, xₙ` with `∏ P(xᵢ, xᵢ₋₁) > 0`, we have
`∏ (P(xᵢ₋₁, xᵢ) / P(xᵢ, xᵢ₋₁)) = 1`. -/
theorem kolmogorov_cycle_theorem {M : ℕ} (P : StochasticMatrix M) (hirr : P.IsIrreducible) :
    P.IsReversible ↔ P.KolmogorovCycleCondition := by
  constructor
  ·
    intro ⟨π, _, hdb⟩
    have hπ := distribution_pos_of_irreducible_detailedBalance P π hirr hdb
    constructor
    ·
      intro x y hxy
      have h := hdb x y
      have hLHS : 0 < π.val x * P.prob x y := mul_pos (hπ x) hxy
      rw [h] at hLHS
      exact pos_of_mul_pos_right hLHS (π.nonneg y)
    ·
      intro n c hcycle hback


      have hdb_prod : (∏ i : Fin n, π.val (c i.castSucc)) *
          (∏ i : Fin n, P.prob (c i.castSucc) (c i.succ)) =
          (∏ i : Fin n, π.val (c i.succ)) *
          (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc)) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        congr 1; ext i; exact hdb (c i.castSucc) (c i.succ)

      have hprod_eq : ∏ i : Fin n, π.val (c i.castSucc) =
          ∏ i : Fin n, π.val (c i.succ) :=
        prod_castSucc_eq_prod_succ π.val c hcycle

      have hpi_pos : 0 < ∏ i : Fin n, π.val (c i.castSucc) :=
        Finset.prod_pos (fun i _ => hπ (c i.castSucc))
      rw [hprod_eq] at hdb_prod
      have hpi_ne : (∏ i : Fin n, π.val (c i.succ)) ≠ 0 := by
        rw [← hprod_eq]; exact ne_of_gt hpi_pos
      exact mul_left_cancel₀ hpi_ne hdb_prod
  ·
    intro hcycle

    let i₀ : Fin (M + 1) := ⟨0, Nat.zero_lt_succ M⟩

    let w : Fin (M + 1) → ℝ := fun j => (cycleWeight P hirr i₀ j : ℝ)

    have hw_pos : ∀ j, 0 ≤ w j := fun j => (cycleWeight P hirr i₀ j).coe_nonneg

    have hw_i₀_pos : 0 < w i₀ := by
      simp only [w, cycleWeight]
      have hspec := (Classical.choose_spec (hirr.exists_path i₀ i₀))
      have hprod_pos := hspec.2.2
      exact_mod_cast listRatioProduct_pos_of_listPathProduct_pos P hcycle.symm_support _ hprod_pos

    let S : ℝ := ∑ j, w j
    have hS_pos : 0 < S := by
      apply Finset.sum_pos'
      · intro j _; exact hw_pos j
      · exact ⟨i₀, Finset.mem_univ _, hw_i₀_pos⟩
    have hS_ne : S ≠ 0 := ne_of_gt hS_pos

    let π : Distribution M :=
      { val := fun j => w j / S
        nonneg := fun j => div_nonneg (hw_pos j) (le_of_lt hS_pos)
        sum_one := by
          rw [← Finset.sum_div]
          exact div_self hS_ne }

    have hdb : P.DetailedBalance π := by
      intro i j
      show w i / S * P.prob i j = w j / S * P.prob j i
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      congr 1
      exact cycleWeight_detailed_balance P hcycle hirr i₀ i j

    have hstat : P.IsStationary π := detailedBalance_isStationary P π hdb
    exact ⟨π, hstat, hdb⟩

end StochasticMatrix
