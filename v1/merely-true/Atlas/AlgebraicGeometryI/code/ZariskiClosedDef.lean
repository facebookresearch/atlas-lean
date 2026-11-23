/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

open MvPolynomial

/-- The affine zero locus `V(S) ⊆ k^n` of a set `S` of polynomials: points
at which every `f ∈ S` vanishes. -/
def AffineZeroLocus {n : ℕ} (k : Type*) [CommRing k]
    (S : Set (MvPolynomial (Fin n) k)) : Set (Fin n → k) :=
  {p : Fin n → k | ∀ f ∈ S, MvPolynomial.aeval p f = 0}

/-- Zariski-closed subset of `k^n` (Def 1, Lec 1): a set defined as the
common zero locus of some collection of polynomials. -/
def IsAffineZariskiClosed {n : ℕ} {k : Type*} [CommRing k]
    (V : Set (Fin n → k)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) k), V = AffineZeroLocus k S

/-- Membership in the affine zero locus unfolds to vanishing of every
polynomial in `S`. -/
@[simp]
theorem mem_affineZeroLocus {n : ℕ} {k : Type*} [CommRing k]
    (S : Set (MvPolynomial (Fin n) k)) (p : Fin n → k) :
    p ∈ AffineZeroLocus k S ↔ ∀ f ∈ S, MvPolynomial.aeval p f = 0 :=
  Iff.rfl

/-- The affine zero locus is order-reversing in the polynomial set: a larger
set of equations cuts out a smaller closed subset. -/
theorem affineZeroLocus_mono {n : ℕ} {k : Type*} [CommRing k]
    {S T : Set (MvPolynomial (Fin n) k)} (h : S ⊆ T) :
    AffineZeroLocus k T ⊆ AffineZeroLocus k S := by
  intro p hp f hf
  exact hp f (h hf)
