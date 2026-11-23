/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

namespace WeakMordellWeil

open scoped Classical

/-- Affine equation of the elliptic curve $E : y^2 = x(x^2 + ax + b)$, used
in the descent step of the Mordell-Weil theorem (Chapter 25). -/
def onCurveE (a b x y : ℚ) : Prop :=
  y ^ 2 = x * (x ^ 2 + a * x + b)

/-- Affine equation of the 2-isogenous curve
$E' : Y^2 = X(X^2 - 2aX + (a^2 - 4b))$ used as the target of the 2-isogeny
$\varphi : E \to E'$. -/
def onCurveE' (a b X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X ^ 2 + (-2 * a) * X + (a ^ 2 - 4 * b))

/-- A point $(X, Y) \in E'(\mathbb{Q})$ lies in the image of the 2-isogeny
$\varphi : E \to E'$ if there exists $(x, y) \in E(\mathbb{Q})$ with $x \neq 0$,
$X = x + a + b/x$ and $Y = y(1 - b/x^2)$. -/
def inImageOfPhi (a b X Y : ℚ) : Prop :=
  ∃ x y : ℚ, onCurveE a b x y ∧ x ≠ 0 ∧
    X = x + a + b / x ∧ Y = y * (1 - b / x ^ 2)


/-- Membership predicate $X \in \mathbb{Q}^{\times 2}$: the rational $X$ is
nonzero and a square. -/
def mem_QxSq (X : ℚ) : Prop :=
  X ≠ 0 ∧ IsSquare X

/-- Lemma 25.3 (image of the 2-isogeny). Assuming $b \neq 0$ and
$a^2 - 4b \neq 0$, a point $(X, Y) \in E'(\mathbb{Q})$ lies in
$\varphi(E(\mathbb{Q}))$ if and only if either $X$ is a nonzero square in
$\mathbb{Q}$, or $X = 0$ and $a^2 - 4b$ is a nonzero square. -/
theorem lemma_25_3 (a b X Y : ℚ) (hb : b ≠ 0) (hdisc : a ^ 2 - 4 * b ≠ 0)
    (hE' : onCurveE' a b X Y) :
    inImageOfPhi a b X Y ↔
      (mem_QxSq X ∨ (X = 0 ∧ mem_QxSq (a ^ 2 - 4 * b))) := by
  constructor
  ·
    rintro ⟨x, y, hE, hx, hXeq, hYeq⟩
    unfold onCurveE at hE
    by_cases hXne : X ≠ 0
    ·

      left
      refine ⟨hXne, y / x, ?_⟩
      rw [hXeq]
      have : (y / x) * (y / x) = y ^ 2 / x ^ 2 := by ring
      rw [this, hE]; field_simp
    ·
      simp only [not_not] at hXne
      right
      refine ⟨hXne, hdisc, a + 2 * x, ?_⟩
      have hX0 : x + a + b / x = 0 := by linarith [hXeq]
      have h_quad : x ^ 2 + a * x + b = 0 := by field_simp at hX0; nlinarith
      nlinarith
  ·
    rintro (⟨hXne, r, hrs⟩ | ⟨hX0, _, d, hds⟩)
    ·

      have hr : r ≠ 0 := by
        intro hr; rw [hr, mul_zero] at hrs; exact hXne hrs

      have hE'_sub : Y ^ 2 = r * r * ((r * r) ^ 2 + (-2 * a) * (r * r) + (a ^ 2 - 4 * b)) := by
        unfold onCurveE' at hE'; rwa [hrs] at hE'
      have hE'r : Y ^ 2 = r ^ 2 * (r ^ 4 - 2 * a * r ^ 2 + a ^ 2 - 4 * b) := by
        nlinarith [hE'_sub]

      set x := (r * r - a + Y / r) / 2 with hx_def

      have key : Y ^ 2 / r ^ 2 = r ^ 4 - 2 * a * r ^ 2 + a ^ 2 - 4 * b := by
        field_simp; linarith [hE'r]

      have h_quad : x ^ 2 + (a - r * r) * x + b = 0 := by
        have step : 4 * (x ^ 2 + (a - r * r) * x + b) =
          Y ^ 2 / r ^ 2 - r ^ 4 + 2 * a * r ^ 2 - a ^ 2 + 4 * b := by
          simp only [hx_def]; field_simp; ring
        linarith [step, key]

      have hxne : x ≠ 0 := by
        intro hx0; simp [hx0] at h_quad; exact hb h_quad

      have h_curve_rw : x ^ 2 + a * x + b = r * r * x := by nlinarith
      refine ⟨x, r * x, ?_, hxne, ?_, ?_⟩
      ·
        unfold onCurveE; rw [h_curve_rw]; ring
      ·
        rw [hrs]; field_simp; nlinarith
      ·
        have hb_eq : b = r * r * x - x ^ 2 - a * x := by nlinarith
        have h1 : r * x * (1 - b / x ^ 2) = r * (x ^ 2 - b) / x := by field_simp
        rw [h1]
        have h2x_eq : 2 * x + a - r * r = Y / r := by
          have : 2 * x * r = (r * r - a) * r + Y := by
            field_simp at hx_def; linarith
          field_simp; linarith
        have h_xsqb : x ^ 2 - b = x * (2 * x + a - r * r) := by nlinarith [hb_eq]
        rw [h_xsqb, h2x_eq]; field_simp
    ·


      have hY0 : Y = 0 := by
        unfold onCurveE' at hE'
        exact sq_eq_zero_iff.mp (by subst hX0; linarith [hE'])
      set x := (-a + d) / 2 with hx_def

      have h_quad : x ^ 2 + a * x + b = 0 := by
        have : 4 * (x ^ 2 + a * x + b) = d * d - (a ^ 2 - 4 * b) := by
          simp only [hx_def]; ring
        linarith [hds]
      have hxne : x ≠ 0 := by
        intro hx0; simp [hx0] at h_quad; exact hb h_quad

      have hXval : x + a + b / x = 0 := by
        field_simp; nlinarith [h_quad]
      refine ⟨x, 0, ?_, hxne, ?_, ?_⟩
      ·
        unfold onCurveE; rw [h_quad]; simp
      ·
        linarith [hXval, hX0]
      ·
        rw [hY0]; ring

section DescentFiniteness


/-- Finiteness ingredient for the descent: the set of squarefree integer
divisors of any nonzero $B \in \mathbb{Z}$ is finite. -/
theorem sqfree_divisors_finite (B : ℤ) (hB : B ≠ 0) :
    Set.Finite {r : ℤ | Squarefree r ∧ r ∣ B} := by
  apply Set.Finite.subset
  · show Set.Finite {r : ℤ | r ∣ B}
    letI := UniqueFactorizationMonoid.fintypeSubtypeDvd B hB
    show Finite {x : ℤ // x ∣ B}
    infer_instance
  · intro x ⟨_, hd⟩; exact hd


end DescentFiniteness

section Corollary256

/-- Corollary 25.6 (finiteness for descent). The sets of squarefree divisors of
$a^2 - 4b$ and of $16 b$ are both finite, providing the finite quotient
$E(\mathbb{Q}) / 2 E(\mathbb{Q})$ needed in the Mordell-Weil theorem. -/
theorem corollary_25_6 (a b : ℤ) (hb : b ≠ 0) (hdisc : a ^ 2 - 4 * b ≠ 0) :

    Set.Finite {r : ℤ | Squarefree r ∧ r ∣ (a ^ 2 - 4 * b)} ∧

    Set.Finite {r : ℤ | Squarefree r ∧ r ∣ (16 * b)} :=
  ⟨sqfree_divisors_finite _ hdisc, sqfree_divisors_finite _ (by omega)⟩

end Corollary256

end WeakMordellWeil
