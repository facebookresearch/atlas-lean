/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
open Finset BigOperators

namespace UnbalancingLights

/-- Conversion from booleans to signs $\{-1, +1\}$: `true ↦ 1`, `false ↦ -1`. -/
def boolToSign (b : Bool) : ℤ := if b then 1 else -1

/-- A vector $v : \mathrm{Fin}\,n \to \mathbb{Z}$ is a sign vector if every entry is
$\pm 1$. -/
def IsSignVec {n : ℕ} (v : Fin n → ℤ) : Prop := ∀ i, v i = 1 ∨ v i = -1

/-- A matrix $a : \mathrm{Fin}\,m \times \mathrm{Fin}\,n \to \mathbb{Z}$ is a sign matrix
if every entry is $\pm 1$. -/
def IsSignMatrix {m n : ℕ} (a : Fin m → Fin n → ℤ) : Prop := ∀ i j, a i j = 1 ∨ a i j = -1

/-- Total Rademacher absolute expectation: $\sum_{y \in \{-1,+1\}^n} \left|
\sum_j y_j \right|$, i.e., the (unnormalized) expected absolute value of a
$\pm 1$ random walk of length $n$. -/
def rademacherAbsExpect (n : ℕ) : ℤ :=
  ∑ y : Fin n → Bool, |∑ j : Fin n, boolToSign (y j)|

/-- The image of `boolToSign` lies in $\{-1, +1\}$. -/
lemma boolToSign_isSign (b : Bool) : boolToSign b = 1 ∨ boolToSign b = -1 := by
  cases b <;> simp [boolToSign]

/-- Mapping a boolean vector pointwise through `boolToSign` yields a sign vector. -/
lemma isSignVec_boolToSign {n : ℕ} (f : Fin n → Bool) :
    IsSignVec (fun j => boolToSign (f j)) :=
  fun _ => boolToSign_isSign _

/-- Averaging principle: for any function $f : \iota \to \mathbb{Z}$ on a finite
nonempty type there exists $x \in \iota$ whose value, multiplied by $|\iota|$, exceeds
the total sum $\sum_y f(y)$. -/
lemma exists_ge_sum_div {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℤ) :
    ∃ x : ι, (Fintype.card ι : ℤ) * f x ≥ ∑ y : ι, f y := by
  by_contra h
  push Not at h
  have h1 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun x (_ : x ∈ Finset.univ) => h x)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [← Finset.mul_sum] at h1
  exact lt_irrefl _ h1

/-- Rewriting the bilinear form $\sum_{i,j} a_{ij} x_i y_j$ as a row-by-row dot product
$\sum_i (\sum_j a_{ij} y_j) x_i$. -/
lemma bilinear_eq_row_sum {m n : ℕ} (a : Fin m → Fin n → ℤ) (x : Fin m → ℤ) (y : Fin n → ℤ) :
    ∑ i : Fin m, ∑ j : Fin n, a i j * x i * y j =
    ∑ i : Fin m, (∑ j : Fin n, a i j * y j) * x i := by
  congr 1; ext i; rw [Finset.sum_mul]; congr 1; ext j; ring

/-- For every integer $z$, there is a sign $s \in \{-1, +1\}$ with $s \cdot z = |z|$. -/
lemma exists_sign_mul_eq_abs (z : ℤ) : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ s * z = |z| := by
  by_cases h : 0 ≤ z
  · exact ⟨1, Or.inl rfl, by simp [abs_of_nonneg h]⟩
  · push Not at h
    exact ⟨-1, Or.inr rfl, by simp [abs_of_neg h]⟩

/-- Greedy row selection: given a matrix $a$ and a vector $y$, choose for each row $i$ a
sign $x_i \in \{-1, +1\}$ to align with the row-sum, so that
$\sum_{i,j} a_{ij} x_i y_j = \sum_i \left|\sum_j a_{ij} y_j\right|$. -/
theorem greedy_row_selection {m n : ℕ} (a : Fin m → Fin n → ℤ) (y : Fin n → ℤ) :
    ∃ x : Fin m → ℤ, IsSignVec x ∧
      ∑ i : Fin m, ∑ j : Fin n, a i j * x i * y j =
      ∑ i : Fin m, |∑ j : Fin n, a i j * y j| := by
  choose x hx using fun i => exists_sign_mul_eq_abs (∑ j, a i j * y j)
  refine ⟨x, fun i => (hx i).1, ?_⟩
  rw [bilinear_eq_row_sum]
  congr 1; ext i; rw [mul_comm]; exact (hx i).2

/-- Coordinate-wise sign flip on Boolean vectors: flip $y_j$ exactly when $a_j = -1$. -/
def signFlip {n : ℕ} (a : Fin n → ℤ) (y : Fin n → Bool) : Fin n → Bool :=
  fun j => decide (a j = -1) ^^ y j

/-- The sign flip operation is its own inverse. -/
lemma signFlip_involutive {n : ℕ} (a : Fin n → ℤ) :
    Function.Involutive (signFlip a) := by
  intro y; ext j; simp [signFlip]

/-- The sign-flip operation packaged as an `Equiv` on Boolean vectors, used to
relabel sums over $\{-1, +1\}^n$. -/
def signFlipEquiv {n : ℕ} (a : Fin n → ℤ) : (Fin n → Bool) ≃ (Fin n → Bool) :=
  (signFlip_involutive a).toPerm (signFlip a)

/-- Compatibility: multiplying a sign $a \in \{-1, +1\}$ by `boolToSign b` is the same
as `boolToSign` applied to the XOR-flipped bit. -/
lemma sign_mul_boolToSign (a : ℤ) (ha : a = 1 ∨ a = -1) (b : Bool) :
    a * boolToSign b = boolToSign (decide (a = -1) ^^ b) := by
  rcases ha with rfl | rfl
  · simp [boolToSign]
  · simp [boolToSign]; cases b <;> simp

/-- Sign-symmetry of the Rademacher-row sum: for any sign row $a$,
$\sum_y |\sum_j a_j y_j|$ over $y \in \{-1,+1\}^n$ equals $\sum_y |\sum_j y_j|$,
since the sign flip is a bijection on $\{-1,+1\}^n$. -/
lemma sum_abs_row_eq {n : ℕ} (a : Fin n → ℤ) (ha : ∀ j, a j = 1 ∨ a j = -1) :
    ∑ y : Fin n → Bool, (|∑ j, a j * boolToSign (y j)| : ℤ) =
    ∑ y : Fin n → Bool, |∑ j, boolToSign (y j)| := by
  have key : ∀ y : Fin n → Bool,
      |∑ j, a j * boolToSign (y j)| = |∑ j, boolToSign ((signFlipEquiv a) y j)| := by
    intro y; congr 1; congr 1; ext j
    rw [sign_mul_boolToSign (a j) (ha j)]
    simp [signFlipEquiv, signFlip, Function.Involutive.toPerm]
  simp_rw [key]
  exact Fintype.sum_equiv (signFlipEquiv a) _ _ (fun y => rfl)

/-- Total sum identity used in the unbalancing-lights proof: for a sign matrix $a$,
$\sum_y \sum_i |\sum_j a_{ij} y_j| = n \cdot \mathbb{E}_{\mathrm{Rad}}(n)$, where the
right-hand side is the (unnormalized) Rademacher walk expectation. -/
lemma total_sum_eq {n : ℕ} (a : Fin n → Fin n → ℤ) (ha : IsSignMatrix a) :
    ∑ y : Fin n → Bool, ∑ i : Fin n, |∑ j : Fin n, a i j * boolToSign (y j)| =
    (n : ℤ) * rademacherAbsExpect n := by
  rw [Finset.sum_comm]
  simp_rw [sum_abs_row_eq _ (fun j => ha _ j)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, rademacherAbsExpect,
    nsmul_eq_mul]

/-- **Unbalancing lights (Theorem 2.5.1, integer form).** For any sign matrix
$a \in \{-1, +1\}^{n \times n}$, there exist sign vectors $x, y \in \{-1, +1\}^n$ such
that $2^n \cdot \sum_{i,j} a_{ij} x_i y_j \geq n \cdot \mathbb{E}_{\mathrm{Rad}}(n)$.
This gives the asymptotic bound $\sum_{i,j} a_{ij} x_i y_j \geq
(\sqrt{2/\pi} + o(1)) n^{3/2}$. -/
theorem unbalancing_lights {n : ℕ} (a : Fin n → Fin n → ℤ) (ha : IsSignMatrix a) :
    ∃ x y : Fin n → ℤ, IsSignVec x ∧ IsSignVec y ∧
      (Fintype.card (Fin n → Bool) : ℤ) *
        ∑ i : Fin n, ∑ j : Fin n, a i j * x i * y j ≥
      (n : ℤ) * rademacherAbsExpect n := by

  obtain ⟨y₀, hy₀⟩ := exists_ge_sum_div (fun y : Fin n → Bool =>
    ∑ i : Fin n, |∑ j : Fin n, a i j * boolToSign (y j)|)

  let y_vec : Fin n → ℤ := fun j => boolToSign (y₀ j)
  obtain ⟨x, hx_sign, hx_eq⟩ := greedy_row_selection a y_vec
  refine ⟨x, y_vec, hx_sign, isSignVec_boolToSign y₀, ?_⟩

  rw [hx_eq]
  calc (Fintype.card (Fin n → Bool) : ℤ) * ∑ i, |∑ j, a i j * y_vec j|
      = (Fintype.card (Fin n → Bool) : ℤ) *
        ∑ i, |∑ j, a i j * boolToSign (y₀ j)| := rfl
    _ ≥ ∑ y : Fin n → Bool, ∑ i, |∑ j, a i j * boolToSign (y j)| := hy₀
    _ = (n : ℤ) * rademacherAbsExpect n := total_sum_eq a ha

/-- A "cross edge" in the $k$-partite hypergraph on $\mathrm{Fin}\,k \times \mathrm{Fin}\,n$:
a $k$-element set $e$ that picks exactly one vertex from each "part"
$\{i\} \times \mathrm{Fin}\,n$. -/
def IsCrossEdge {k n : ℕ} (e : Finset (Fin k × Fin n)) : Prop :=
  e.card = k ∧ ∀ i : Fin k, (e.filter (fun p => p.1 = i)).card = 1

/-- Discrepancy of a coloring on $k$-subsets of $S$: the signed sum
$\sum_{e \in \binom{S}{k}} \mathrm{color}(e)$ viewed as a real number. -/
noncomputable def discrepancy {k n : ℕ} (color : Finset (Fin k × Fin n) → ℤ)
    (S : Finset (Fin k × Fin n)) : ℝ :=
  ∑ e ∈ Finset.powersetCard k S, (color e : ℝ)


end UnbalancingLights
