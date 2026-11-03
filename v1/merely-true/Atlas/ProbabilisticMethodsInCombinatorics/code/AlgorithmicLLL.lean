/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace AlgorithmicLLL

variable {Clause : Type*} {State : Type*}

/-- A `FixSystem` abstracts the structure underlying Moser's algorithm. It consists of
clauses and states, a predicate `satisfied` saying when a clause holds in a state, a `fix`
operation that repairs a clause, the guarantee that `fix c` makes `c` satisfied, and the
invariant that `fix c` preserves all currently satisfied clauses. -/
structure FixSystem (Clause : Type*) (State : Type*) where
  satisfied : Clause → State → Prop
  fix : Clause → State → State
  fix_makes_satisfied : ∀ (c : Clause) (s : State), satisfied c (fix c s)
  fix_preserves_satisfied : ∀ (c d : Clause) (s : State), satisfied d s → satisfied d (fix c s)

variable {sys : FixSystem Clause State}

/-- `IsValidOuterLoop sys cs s` says that the list of clauses `cs` is a valid execution
trace of the outer loop of Moser's algorithm starting from state `s`: each successive
clause is unsatisfied at the moment it is visited and then fixed. -/
def IsValidOuterLoop (sys : FixSystem Clause State) :
    List Clause → State → Prop
  | [], _ => True
  | c :: cs, s => ¬sys.satisfied c s ∧ IsValidOuterLoop sys cs (sys.fix c s)

/-- Any valid outer-loop trace contains each clause at most once: once a clause is fixed it
remains satisfied, so it can never be the unsatisfied clause selected at a later step. -/
theorem outer_loop_nodup (sys : FixSystem Clause State) [DecidableEq Clause]
    (cs : List Clause) (s : State) (h : IsValidOuterLoop sys cs s) :
    cs.Nodup := by
  induction cs generalizing s with
  | nil => exact List.nodup_nil
  | cons c cs ih =>
    obtain ⟨hc_violated, hrest⟩ := h
    refine List.nodup_cons.mpr ⟨?_, ih (sys.fix c s) hrest⟩


    intro hc_mem

    have hc_sat : sys.satisfied c (sys.fix c s) := sys.fix_makes_satisfied c s


    suffices h_contra : ∀ (ds : List Clause) (s' : State),
        sys.satisfied c s' → IsValidOuterLoop sys ds s' → c ∉ ds by
      exact h_contra cs (sys.fix c s) hc_sat hrest hc_mem
    intro ds
    induction ds with
    | nil => intro _ _ _; exact List.not_mem_nil
    | cons d ds ih_ds =>
      intro s' hc_sat' ⟨hd_violated, hrest'⟩ hc_mem'
      cases List.mem_cons.mp hc_mem' with
      | inl heq =>

        rw [heq] at hc_sat'
        exact hd_violated hc_sat'
      | inr hc_in_ds =>

        have hc_sat'' : sys.satisfied c (sys.fix d s') :=
          sys.fix_preserves_satisfied d c s' hc_sat'
        exact ih_ds (sys.fix d s') hc_sat'' hrest' hc_in_ds

noncomputable section

/-- A `KCNF` instance: $k$-CNF formula data with `numVars` Boolean variables, `numClauses`
clauses each of width $k \ge 3$, and `maxShared` bounding the number of clauses sharing a
variable with a given clause. -/
structure KCNF where
  numVars : ℕ
  numClauses : ℕ
  k : ℕ
  maxShared : ℕ
  hk : 3 ≤ k
  hn : 0 < numVars

/-- A `MoserKCNF` is a `KCNF` satisfying Moser's sharing condition $\text{maxShared} \le 2^{k-3}$,
the hypothesis under which Moser's algorithm provably finds a satisfying assignment. -/
structure MoserKCNF extends KCNF where
  hshared : maxShared ≤ 2 ^ (k - 3)

/-- The number $2^n$ of Boolean assignments on $n$ variables. -/
def numAssignments (n : ℕ) : ℕ := 2 ^ n

/-- Upper bound $2^{\ell(k-1)+1}$ on the number of execution traces of Moser's algorithm of
length $\ell$ on a $k$-CNF formula, used in the entropy-compression argument. -/
def numExecutionTraces (k ℓ : ℕ) : ℕ := 2 ^ (ℓ * (k - 1) + 1)

/-- Combined failure bound $2^n \cdot 2^{\ell(k-1)+1}$ from entropy compression: the count
of (assignment, trace) pairs available to encode failing executions. -/
def failureBound (n k ℓ : ℕ) : ℕ := numAssignments n * numExecutionTraces k ℓ

/-- Rewrites `failureBound n k ℓ` as a single power of $2$: $2^{n + \ell(k-1) + 1}$. -/
lemma failureBound_eq_pow (n k ℓ : ℕ) :
    failureBound n k ℓ = 2 ^ (n + (ℓ * (k - 1) + 1)) := by
  unfold failureBound numAssignments numExecutionTraces
  rw [← pow_add]

/-- Arithmetic identity used to compare exponents in the failure-probability bound:
$n + \ell(k-1) + 1 + \ell = k\ell + n + 1$, valid whenever $k \ge 1$. -/
lemma exponent_identity (n k ℓ : ℕ) (hk : 1 ≤ k) :
    n + (ℓ * (k - 1) + 1) + ℓ = k * ℓ + (n + 1) := by
  have h : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  nlinarith [Nat.sub_le k 1]


/-- Natural-number version of the failure-probability bound:
$\text{numFailing} \cdot 2^\ell \le 2^{k\ell} \cdot 2^{n+1}$ whenever the failing count is
bounded by `failureBound n k ℓ`. -/
lemma failure_prob_bound_nat (n k ℓ : ℕ) (numFailing : ℕ)
    (h_inj : numFailing ≤ failureBound n k ℓ)
    (hk : 1 ≤ k) :
    numFailing * 2 ^ ℓ ≤ 2 ^ (k * ℓ) * 2 ^ (n + 1) := by
  have h_bound : numFailing ≤ 2 ^ (n + (ℓ * (k - 1) + 1)) := by
    rw [← failureBound_eq_pow]; exact h_inj
  calc numFailing * 2 ^ ℓ
      ≤ 2 ^ (n + (ℓ * (k - 1) + 1)) * 2 ^ ℓ := Nat.mul_le_mul_right _ h_bound
    _ = 2 ^ (n + (ℓ * (k - 1) + 1) + ℓ) := (pow_add 2 _ ℓ).symm
    _ = 2 ^ (k * ℓ + (n + 1)) := by
        congr 1
        exact exponent_identity n k ℓ hk
    _ = 2 ^ (k * ℓ) * 2 ^ (n + 1) := pow_add 2 _ _


end

end AlgorithmicLLL
