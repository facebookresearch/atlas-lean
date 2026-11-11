/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

set_option maxHeartbeats 400000

open MvPolynomial

namespace MvPolynomial

variable {σ : Type*} {k : Type*} [CommRing k]

/-- Translate a polynomial by `p`, sending `X i` to `X i + C (p i)`. -/
noncomputable def translate (p : σ → k) (f : MvPolynomial σ k) : MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => X i + C (p i)) f

/-- The minimum total degree among monomials appearing in `f` (Def 12). -/
noncomputable def minTotalDegree (f : MvPolynomial σ k) : ℕ := by
  classical
  exact if h : f.support.Nonempty then
    (f.support.image (fun s => Finsupp.sum s fun _ e => e)).min' (h.image _)
  else 0

/-- The multiplicity of `f` at the point `p` is the minimum total degree of the
translated polynomial `f(X + p)` (Def 12, 13). -/
noncomputable def multiplicityAt (f : MvPolynomial σ k) (p : σ → k) : ℕ :=
  (f.translate p).minTotalDegree

/-- Unfolding lemma for `translate`. -/
@[simp]
lemma translate_def (p : σ → k) (f : MvPolynomial σ k) :
    f.translate p = MvPolynomial.aeval (fun i => X i + C (p i)) f := rfl

/-- The minimum total degree of the zero polynomial is `0` (by convention). -/
@[simp]
lemma minTotalDegree_zero : (0 : MvPolynomial σ k).minTotalDegree = 0 := by
  classical
  simp [minTotalDegree, support_zero]

/-- The minimum total degree is bounded by the (maximum) total degree. -/
lemma minTotalDegree_le_totalDegree (f : MvPolynomial σ k) :
    f.minTotalDegree ≤ f.totalDegree := by
  classical
  unfold minTotalDegree
  split_ifs with h
  · set img := f.support.image (fun s => Finsupp.sum s fun _ e => e)
    have hmin_mem : img.min' (h.image _) ∈ img := Finset.min'_mem _ _
    rw [Finset.mem_image] at hmin_mem
    obtain ⟨s, hs, heq⟩ := hmin_mem
    rw [← heq]
    exact le_totalDegree hs
  · exact Nat.zero_le _

/-- Translating by the zero point is the identity. -/
@[simp]
lemma translate_zero (f : MvPolynomial σ k) :
    f.translate 0 = f := by
  simp only [translate, Pi.zero_apply, map_zero, add_zero]
  change (aeval X) f = f
  rw [aeval_X_left]
  rfl

/-- Translation by `p` packaged as a `k`-algebra homomorphism. -/
noncomputable def translateAlgHom (p : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => X i + C (p i))

/-- Translation is additive. -/
@[simp]
lemma translate_add (p : σ → k) (f g : MvPolynomial σ k) :
    (f + g).translate p = f.translate p + g.translate p := by
  simp [translate]

/-- Translation is multiplicative. -/
@[simp]
lemma translate_mul (p : σ → k) (f g : MvPolynomial σ k) :
    (f * g).translate p = f.translate p * g.translate p := by
  simp [translate]

end MvPolynomial
