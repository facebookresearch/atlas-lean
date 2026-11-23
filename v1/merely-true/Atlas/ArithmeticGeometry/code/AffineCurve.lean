/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

open scoped Cardinal
open MvPolynomial Algebra

variable (k : Type) [Field k]

/-- Affine $n$-space $\mathbb{A}^n_k$ has dimension $n$: the transcendence degree of $k[x_1, \dots, x_n]$ over $k$ is $n$. -/
theorem dim_affine_space (n : ℕ) :
    Algebra.trdeg k (MvPolynomial (Fin n) k) = ↑n := by
  simp [MvPolynomial.trdeg_of_isDomain]


/-- The coordinate ring of a point $p \in \mathbb{A}^n_k$, i.e. $k[x_1, \dots, x_n] / \ker(\mathrm{eval}_p)$, is an algebraic extension of $k$ (in fact isomorphic to $k$). -/
theorem quotient_eval_ker_isAlgebraic {n : ℕ} (p : Fin n → k) :
    Algebra.IsAlgebraic k
      (MvPolynomial (Fin n) k ⧸ RingHom.ker (MvPolynomial.eval p)) := by
  constructor
  intro x
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective x
  rw [isAlgebraic_iff_isIntegral, ← hf]
  have : (Ideal.Quotient.mk (RingHom.ker (MvPolynomial.eval p))) f =
      algebraMap k _ (MvPolynomial.eval p f) := by
    show _ = (Ideal.Quotient.mk _) (MvPolynomial.C (MvPolynomial.eval p f))
    rw [Ideal.Quotient.eq]
    simp [RingHom.mem_ker, map_sub, MvPolynomial.eval_C]
  rw [this]
  exact isIntegral_algebraMap


end
