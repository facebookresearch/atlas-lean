/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open ZMod Finset Complex
open scoped ZMod

noncomputable section

namespace ProjectionTheory

/-- The projection $\pi_p f : \mathbb{Z}_p \to \mathbb{C}$ of a function $f : [N] \to \mathbb{C}$
to the discrete subgroup $\mathbb{Z}_p$: for each residue $a \in \mathbb{Z}_p$, sum the values
of $f$ over all $n \in [N]$ with $n \equiv a \pmod p$. -/
def discreteProjection (p : ℕ) [NeZero p] {N : ℕ} (f : Fin N → ℂ) : ZMod p → ℂ :=
  fun a => ∑ n ∈ Finset.univ.filter (fun n : Fin N => (n.val : ZMod p) = a), f n

/-- Fourier dictionary for the discrete projection: the discrete Fourier transform of
$\pi_p f$ at $\alpha \in \mathbb{Z}_p$ equals $\sum_n e(-n\alpha/p)\, f(n)$, matching
$\widehat{\pi_p f}(\alpha) = \hat f(\alpha/p)$. -/
theorem dft_discreteProjection (p : ℕ) [NeZero p] {N : ℕ} (f : Fin N → ℂ) (α : ZMod p) :
    ZMod.dft (discreteProjection p f) α =
    ∑ n : Fin N, (stdAddChar (-((n.val : ZMod p) * α)) : ℂ) * f n := by
  simp only [ZMod.dft_apply, discreteProjection, smul_eq_mul]
  simp_rw [Finset.mul_sum]

  have key : ∀ a : ZMod p,
      ∑ n ∈ Finset.univ.filter (fun n : Fin N => (n.val : ZMod p) = a),
        (stdAddChar (-(a * α)) : ℂ) * f n =
      ∑ n ∈ Finset.univ.filter (fun n : Fin N => (n.val : ZMod p) = a),
        (stdAddChar (-((n.val : ZMod p) * α)) : ℂ) * f n := by
    intro a
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
    rw [hn]
  simp_rw [key]

  rw [← Finset.sum_fiberwise Finset.univ (fun n : Fin N => (n.val : ZMod p))
    (fun n => (stdAddChar (-((n.val : ZMod p) * α)) : ℂ) * f n)]

end ProjectionTheory
