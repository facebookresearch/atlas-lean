/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.WithVal

noncomputable section

open scoped Padic

variable (p : ℕ) [hp : Fact p.Prime]


/-- Canonical ring homomorphism from $\mathbb{Q}$ into the uniform-space completion with respect to
the $p$-adic valuation, obtained by composing the `WithVal` identification with the completion's
coercion ring hom. -/
def ratEmbedPadicCompletion : ℚ →+* (Rat.padicValuation p).Completion :=
  (UniformSpace.Completion.coeRingHom).comp (WithVal.equiv (Rat.padicValuation p)).symm.toRingHom

/-- Compatibility: applying the canonical ring isomorphism `Padic.withValRingEquiv` to the image of
a rational number $q$ under `ratEmbedPadicCompletion` recovers the usual coercion of $q$ into
$\mathbb{Q}_p$. -/
lemma padic_withValRingEquiv_ratEmbed (q : ℚ) :
    (Padic.withValRingEquiv (p := p)) (ratEmbedPadicCompletion p q) = (q : ℚ_[p]) := by
  show (Padic.withValRingEquiv (p := p))
    (↑((WithVal.equiv (Rat.padicValuation p)).symm q) : (Rat.padicValuation p).Completion) =
    (q : ℚ_[p])
  have heq : ∀ x : (Rat.padicValuation p).Completion,
      Padic.withValUniformEquiv x = Padic.withValRingEquiv x := by
    intro x
    exact congr_fun (congrArg Equiv.toFun
      (Padic.toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv (p := p))) x
  rw [← heq, Padic.withValUniformEquiv_cast_apply]
  simp

/-- Theorem 8.1: there is a ring isomorphism between the uniform-space completion of $\mathbb{Q}$
under the $p$-adic valuation and Mathlib's $\mathbb{Q}_p$, which is an isometry on the image of
$\mathbb{Q}$, i.e. the norm of $\pi(q)$ equals $|q|_p$ for every rational $q$. -/
theorem thm_8_1_padic_completion :
    ∃ (π : (Rat.padicValuation p).Completion ≃+* ℚ_[p]),
      ∀ (q : ℚ), ‖π (ratEmbedPadicCompletion p q)‖ = padicNorm p q :=
  ⟨Padic.withValRingEquiv, fun q => by
    rw [padic_withValRingEquiv_ratEmbed]; exact Padic.eq_padicNorm q⟩

/-- Ring isomorphism between the uniform completion of $\mathbb{Q}$ under the $p$-adic valuation and
Mathlib's $\mathbb{Q}_p$. -/
def padic_completion_ringEquiv :
    (Rat.padicValuation p).Completion ≃+* ℚ_[p] :=
  Padic.withValRingEquiv

/-- Uniform-space isomorphism between the uniform completion of $\mathbb{Q}$ under the $p$-adic
valuation and Mathlib's $\mathbb{Q}_p$, witnessing that the two completions agree as uniform
spaces. -/
def padic_completion_uniformEquiv :
    (Rat.padicValuation p).Completion ≃ᵤ ℚ_[p] :=
  Padic.withValUniformEquiv


end
