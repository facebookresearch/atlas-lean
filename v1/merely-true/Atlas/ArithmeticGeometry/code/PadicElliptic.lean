/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic

noncomputable section

open scoped Padic


attribute [local instance] Classical.dec

namespace PadicElliptic

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The group of $\mathbb{Q}_p$-points of a Weierstrass curve $W$ defined over $\mathbb{Q}$,
obtained by base-changing to $\mathbb{Q}_p$ and taking the affine point set. -/
abbrev PadicPointGroup (W : WeierstrassCurve ℚ) : Type :=
  (W.baseChange ℚ_[p]).toAffine.Point

/-- Membership predicate for the $n$-th piece $E_n(\mathbb{Q}_p)$ of the $p$-adic filtration:
a point is either the identity, or has $y \ne 0$ and $v_p(x) - v_p(y) \ge n$. -/
def InPadicFiltration (W : WeierstrassCurve ℚ) (n : ℕ)
    (P : PadicPointGroup W (p := p)) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y

/-- The $p$-adic filtration is monotone in the level: $E_{n+1}(\mathbb{Q}_p) \subseteq
E_n(\mathbb{Q}_p)$. -/
theorem inPadicFiltration_mono {W : WeierstrassCurve ℚ} {n : ℕ}
    {P : PadicPointGroup W (p := p)}
    (h : InPadicFiltration W (n + 1) P) : InPadicFiltration W n P := by
  match P with
  | .zero => exact trivial
  | .some x y h' =>
    simp only [InPadicFiltration] at h ⊢
    exact ⟨h.1, le_trans (by omega) h.2⟩

/-- The $p$-adic valuation on $\mathbb{Q}_p$ is invariant under negation: $v_p(-y) = v_p(y)$. -/
lemma padic_valuation_neg (y : ℚ_[p]) : (-y).valuation = y.valuation := by
  by_cases hy : y = 0
  · simp [hy]
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    have hnorm : ‖(-y)‖ = ‖y‖ := norm_neg y
    rw [Padic.norm_eq_zpow_neg_valuation hny, Padic.norm_eq_zpow_neg_valuation hy] at hnorm
    have hp1 : (1 : ℝ) < p := by exact_mod_cast Nat.Prime.one_lt hp.out
    have hp_pos : (0 : ℝ) < p := lt_trans zero_lt_one hp1
    have hp_ne_one : (p : ℝ) ≠ 1 := ne_of_gt hp1
    have := zpow_right_injective₀ hp_pos hp_ne_one hnorm
    linarith

/-- For a Weierstrass curve in short form ($a_1 = a_3 = 0$), the negation of a point $(x, y)$ on
$W_{\mathbb{Q}_p}$ has $y$-coordinate $-y$. -/
lemma negY_short_weierstrass (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) (x y : ℚ_[p]) :
    (W.baseChange ℚ_[p]).toAffine.negY x y = -y := by
  unfold WeierstrassCurve.baseChange WeierstrassCurve.toAffine WeierstrassCurve.Affine.negY
  simp [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, ha1, ha3]

/-- Negation preserves the $p$-adic filtration: if $P \in E_n(\mathbb{Q}_p)$ then so is $-P$.
This uses that negation only flips the sign of $y$ in short form, and $v_p$ is sign-invariant. -/
theorem negation_preserves_filtration (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) (n : ℕ)
    (P : PadicPointGroup W (p := p)) :
    InPadicFiltration W n P → InPadicFiltration W n (-P) := by
  match P with
  | .zero =>
    intro _
    show InPadicFiltration W n (-(0 : PadicPointGroup W))
    rw [neg_zero]
    trivial
  | .some x y h =>
    intro ⟨hy, hval⟩
    rw [WeierstrassCurve.Affine.Point.neg_some]
    have hNegY : (W.baseChange ℚ_[p]).toAffine.negY x y = -y :=
      negY_short_weierstrass W ha1 ha3 x y
    show (W.baseChange ℚ_[p]).toAffine.negY x y ≠ 0 ∧
         (n : ℤ) ≤ Padic.valuation x -
           Padic.valuation ((W.baseChange ℚ_[p]).toAffine.negY x y)
    rw [hNegY]
    exact ⟨neg_ne_zero.mpr hy, by rw [padic_valuation_neg]; exact hval⟩











/-- If $H$ is the kernel of a surjective additive group homomorphism $G \to \mathbb{Z}/p\mathbb{Z}$,
then $[G : H] = p$. -/
theorem index_eq_p_of_surjective_hom_to_zmod {G : Type*} [AddGroup G]
    (H : AddSubgroup G)
    (f : G →+ ZMod p) (hf : Function.Surjective f) (hker : f.ker = H) :
    H.index = p := by
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
      AddSubgroup.card_top, Nat.card_eq_fintype_card, ZMod.card]










/-- A point that lies in every filtration piece $E_n(\mathbb{Q}_p)$ is the identity: the only
element with infinite valuation difference is $0$. -/
lemma inPadicFiltration_all_eq_zero {W : WeierstrassCurve ℚ}
    {P : PadicPointGroup W (p := p)}
    (h : ∀ n : ℕ, InPadicFiltration W n P) : P = 0 := by
  match P with
  | .zero => rfl
  | .some x y hns =>
    exfalso
    have : ∀ n : ℕ, (n : ℤ) ≤ Padic.valuation x - Padic.valuation y := fun n => (h n).2
    have := this (Int.toNat (Padic.valuation x - Padic.valuation y) + 1)
    omega






end PadicElliptic

end
