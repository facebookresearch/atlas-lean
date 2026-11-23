/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.DirectSum.Internal

noncomputable section

open DirectSum BigOperators

/-- The `n`-th piece `m^n / m^{n+1}` of the associated graded ring of `A` with respect to
an ideal `m`. -/
abbrev AssocGradedPiece {A : Type*} [CommRing A] (m : Ideal A) (n : ℕ) : Type _ :=
  (m ^ n : Submodule A A) ⧸ Submodule.comap (m ^ n).subtype (m ^ (n + 1))

/-- The associated graded ring `gr_m(A) = ⨁_n m^n/m^{n+1}` of `A` with respect to `m`. -/
def AssocGraded {A : Type*} [CommRing A] (m : Ideal A) : Type _ :=
  ⨁ n, AssocGradedPiece m n

/-- The image (initial form in degree `p`) of an element `a ∈ m^p` inside the graded piece
`m^p/m^{p+1}`. -/
def imageInGradedPiece {A : Type*} [CommRing A] (m : Ideal A)
    (a : A) (p : ℕ) (ha : a ∈ m ^ p) : AssocGradedPiece m p :=
  Submodule.Quotient.mk ⟨a, ha⟩

/-- Include a single graded piece `m^p/m^{p+1}` into the associated graded ring. -/
def gradedPieceToAssocGraded {A : Type*} [CommRing A] (m : Ideal A)
    (p : ℕ) (x : AssocGradedPiece m p) : AssocGraded m :=
  DirectSum.of (AssocGradedPiece m) p x

/-- The image in the associated graded ring of an element `a ∈ m^p`, placed in degree `p`. -/
def imageInAssocGraded {A : Type*} [CommRing A] (m : Ideal A)
    (a : A) (p : ℕ) (ha : a ∈ m ^ p) : AssocGraded m :=
  gradedPieceToAssocGraded m p (imageInGradedPiece m a p ha)

/-- The image of an ideal `m` in the quotient ring `A / (a)`. -/
def quotientIdeal {A : Type*} [CommRing A] (m : Ideal A) (a : A) :
    Ideal (A ⧸ Ideal.span {a}) :=
  m.map (Ideal.Quotient.mk (Ideal.span {a}))

/-- The hypothesis used in Lemma 31/32 expressing that the initial form of `a` (an element of
`m^p`) is a non-zero-divisor in the associated graded ring: if `ax ∈ m^{k+p+1}` and
`x ∈ m^k`, then already `x ∈ m^{k+1}`. -/
def InitialFormNonZeroDivisor {A : Type*} [CommRing A] (m : Ideal A)
    (a : A) (p : ℕ) : Prop :=
  ∀ (k : ℕ) (x : A), x ∈ m ^ k → a * x ∈ m ^ (k + p + 1) → x ∈ m ^ (k + 1)

/-- Iterated form of the non-zero-divisor hypothesis: if the initial form of `a` is regular
in degree `p`, then `a · c ∈ m^n` (with `n ≥ p`) forces `c ∈ m^{n-p}`. -/
theorem initialForm_nonZeroDivisor_intersection
    {A : Type*} [CommRing A] (m : Ideal A) (a : A) (p : ℕ)
    (hnd : InitialFormNonZeroDivisor m a p)
    (n : ℕ) (hn : p ≤ n) (c : A) (hac : a * c ∈ m ^ n) :
    c ∈ m ^ (n - p) := by
  suffices h : ∀ j : ℕ, j ≤ n - p → c ∈ m ^ j from h (n - p) le_rfl
  intro j hj
  induction j with
  | zero => simp [Ideal.one_eq_top]
  | succ j ih =>
    have hj' : j ≤ n - p := Nat.le_of_succ_le hj
    have hcj := ih hj'
    have hjpn : j + p + 1 ≤ n := by omega
    have hacjp1 : a * c ∈ m ^ (j + p + 1) := Ideal.pow_le_pow_right hjpn hac
    exact hnd j c hcj hacjp1

/-- Lemma 32 (Lecture 19). If the initial form of `a ∈ m^p` is a non-zero-divisor in the
associated graded ring, then for `n ≥ p` one has `(a) ∩ m^n = (a) · m^{n-p}`. -/
theorem lemma32_graded_quotient
    {A : Type*} [CommRing A]
    (m : Ideal A) (a : A) (p : ℕ)
    (ha : a ∈ m ^ p)
    (hnd : InitialFormNonZeroDivisor m a p)
    (n : ℕ) (hn : p ≤ n) :
    Ideal.span {a} ⊓ m ^ n = Ideal.span {a} * m ^ (n - p) := by
  ext x
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton]
  rw [Ideal.mem_span_singleton_mul]
  constructor
  ·

    rintro ⟨⟨c, rfl⟩, hx⟩
    exact ⟨c, initialForm_nonZeroDivisor_intersection m a p hnd n hn c hx, rfl⟩
  ·

    rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, ?_⟩
    have hpow : m ^ p * m ^ (n - p) ≤ m ^ n := by
      rw [← pow_add]; exact le_of_eq (by congr 1; omega)
    exact hpow (Ideal.mul_mem_mul ha hc)

end
