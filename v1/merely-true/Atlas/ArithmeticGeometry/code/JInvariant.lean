/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.TateShafarevich

noncomputable section

universe u

open WeierstrassCurve

/-- The Weierstrass curve in *short form* $y^2 = x^3 + a_4 x + a_6$, obtained by
setting $a_1 = a_2 = a_3 = 0$. -/
def shortWeierstrassCurve {R : Type*} [CommRing R] (a₄ a₆ : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a₄, a₆⟩

namespace shortWeierstrassCurve

variable {R : Type*} [CommRing R] (a₄ a₆ : R)

/-- Coefficient $a_1$ of the short Weierstrass curve is $0$. -/
@[simp] lemma a₁_eq : (shortWeierstrassCurve a₄ a₆).a₁ = 0 := rfl
/-- Coefficient $a_2$ of the short Weierstrass curve is $0$. -/
@[simp] lemma a₂_eq : (shortWeierstrassCurve a₄ a₆).a₂ = 0 := rfl
/-- Coefficient $a_3$ of the short Weierstrass curve is $0$. -/
@[simp] lemma a₃_eq : (shortWeierstrassCurve a₄ a₆).a₃ = 0 := rfl
/-- Coefficient $a_4$ of the short Weierstrass curve is $a_4$. -/
@[simp] lemma a₄_eq : (shortWeierstrassCurve a₄ a₆).a₄ = a₄ := rfl
/-- Coefficient $a_6$ of the short Weierstrass curve is $a_6$. -/
@[simp] lemma a₆_eq : (shortWeierstrassCurve a₄ a₆).a₆ = a₆ := rfl

/-- For a short Weierstrass curve, the auxiliary invariant $c_4 = -48 a_4$. -/
lemma c₄_eq : (shortWeierstrassCurve a₄ a₆).c₄ = -48 * a₄ := by
  simp only [shortWeierstrassCurve, c₄, b₂, b₄]; ring

/-- For a short Weierstrass curve, the auxiliary invariant $c_6 = -864 a_6$. -/
lemma c₆_eq : (shortWeierstrassCurve a₄ a₆).c₆ = -864 * a₆ := by
  simp only [shortWeierstrassCurve, c₆, b₂, b₄, b₆]; ring

/-- The discriminant of the short Weierstrass curve:
$\Delta = -16(4 a_4^3 + 27 a_6^2)$. -/
lemma Δ_eq : (shortWeierstrassCurve a₄ a₆).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
  simp only [shortWeierstrassCurve, Δ, b₂, b₄, b₆, b₈]; ring

end shortWeierstrassCurve

/-- The defining relation $j \cdot \Delta = c_4^3$ for the $j$-invariant of an
elliptic Weierstrass curve. -/
lemma WeierstrassCurve.j_mul_Δ_eq_c₄_cube {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  simp only [j]
  have h : (↑W.Δ'⁻¹ : R) * W.Δ = 1 := Units.inv_mul W.Δ'
  calc ↑W.Δ'⁻¹ * W.c₄ ^ 3 * W.Δ
      = W.c₄ ^ 3 * (↑W.Δ'⁻¹ * W.Δ) := by ring
    _ = W.c₄ ^ 3 * 1 := by rw [h]
    _ = W.c₄ ^ 3 := mul_one _

section JInvariantFormula

variable {F : Type*} [Field F]

/-- Over a field, if the short Weierstrass curve $y^2 = x^3 + a_4 x + a_6$ is
elliptic, then $16 \neq 0$ (i.e. the characteristic is not $2$). -/
lemma shortWeierstrassCurve.sixteen_ne_zero (a₄ a₆ : F)
    [(shortWeierstrassCurve a₄ a₆).IsElliptic] :
    (16 : F) ≠ 0 := by
  intro h16
  exact (shortWeierstrassCurve a₄ a₆).isUnit_Δ.ne_zero (by
    rw [shortWeierstrassCurve.Δ_eq]
    rw [show (-16 : F) = -(16 : F) from by norm_num, h16, neg_zero, zero_mul])

/-- For an elliptic short Weierstrass curve, the quantity
$4 a_4^3 + 27 a_6^2 \neq 0$ (it is essentially the discriminant up to a unit). -/
lemma shortWeierstrassCurve.denominator_ne_zero (a₄ a₆ : F)
    [(shortWeierstrassCurve a₄ a₆).IsElliptic] :
    4 * a₄ ^ 3 + 27 * a₆ ^ 2 ≠ 0 := by
  intro heq
  exact (shortWeierstrassCurve a₄ a₆).isUnit_Δ.ne_zero (by
    rw [shortWeierstrassCurve.Δ_eq, heq, mul_zero])

/-- Closed form for the $j$-invariant of a short Weierstrass curve:
$j = 1728 \cdot \dfrac{4 a_4^3}{4 a_4^3 + 27 a_6^2}$. -/
theorem j_invariant_short_weierstrass_eq (a₄ a₆ : F)
    [(shortWeierstrassCurve a₄ a₆).IsElliptic] :
    (shortWeierstrassCurve a₄ a₆).j =
      1728 * (4 * a₄ ^ 3) / (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
  rw [eq_div_iff (shortWeierstrassCurve.denominator_ne_zero a₄ a₆)]
  have h_jΔ := WeierstrassCurve.j_mul_Δ_eq_c₄_cube (shortWeierstrassCurve a₄ a₆)
  rw [shortWeierstrassCurve.Δ_eq, shortWeierstrassCurve.c₄_eq] at h_jΔ
  apply mul_left_cancel₀
    (neg_ne_zero.mpr (shortWeierstrassCurve.sixteen_ne_zero a₄ a₆) : (-16 : F) ≠ 0)
  linear_combination h_jΔ

end JInvariantFormula

/-- **Definition 26.1.** The $j$-invariant of an elliptic curve $E$ over a field
$k$, extracted from its underlying Weierstrass curve. -/
def EllipticCurveOver.jInvariant {k : Type*} [Field k] (E : EllipticCurveOver k) : k :=
  @WeierstrassCurve.j _ _ E.curve E.isElliptic

/-- **Theorem 26.3 (surjectivity).** Over any field $k$, every value $j \in k$
arises as the $j$-invariant of some elliptic curve over $k$. -/
theorem j_invariant_surjective {k : Type*} [Field k] (j : k) :
    ∃ E : EllipticCurveOver k, E.jInvariant = j := by
  classical
  exact ⟨⟨WeierstrassCurve.ofJ j⟩, WeierstrassCurve.ofJ_j j⟩

/-- A choice of elliptic curve over $k$ whose $j$-invariant equals $j$, witnessing
the surjectivity of the $j$-invariant. -/
noncomputable def ellipticCurveOfJ {k : Type*} [Field k] (j : k) : EllipticCurveOver k :=
  (j_invariant_surjective j).choose

/-- The chosen curve `ellipticCurveOfJ j` indeed has $j$-invariant $j$. -/
lemma ellipticCurveOfJ_jInvariant {k : Type*} [Field k] (j : k) :
    (ellipticCurveOfJ j).jInvariant = j :=
  (j_invariant_surjective j).choose_spec

/-- Surjectivity of the $j$-invariant function $E \mapsto j(E)$ on elliptic
curves over $k$, restated as `Function.Surjective`. -/
theorem j_invariant_surjective_fun {k : Type*} [Field k] :
    Function.Surjective (EllipticCurveOver.jInvariant (k := k)) :=
  j_invariant_surjective

section Jacobian

variable {k : Type*} [Field k]

/-- The Jacobian of a genus-one curve $C$, viewed as an elliptic curve over $k$. -/
def GenusOneCurve.jacobian (C : GenusOneCurve k) : EllipticCurveOver k :=
  C.Jacobian





/-- The group of $k$-rational points $E(k)$ of an elliptic curve $E$ over $k$,
defined as the affine points of its underlying Weierstrass curve. -/
def EllipticCurveOver.RationalPoints (E : EllipticCurveOver k) :=
  E.curve.toAffine.Point

/-- Definitional unfolding: $E(k)$ is the affine points of the underlying
Weierstrass curve. -/
theorem EllipticCurveOver.RationalPoints_def (E : EllipticCurveOver k) :
    E.RationalPoints = E.curve.toAffine.Point := rfl

/-- The Mordell–Weil abelian group structure on $E(k)$. -/
noncomputable instance EllipticCurveOver.RationalPoints.instAddCommGroup (E : EllipticCurveOver k) :
    AddCommGroup (E.RationalPoints) := by
  unfold EllipticCurveOver.RationalPoints
  classical
  exact inferInstance

end Jacobian


variable {k : Type u} [Field k] [NumberField k]










/-- The set of $\bar k$-rational points of the Jacobian of $C$, used as base
points for the elliptic-curve structure of $C \otimes_k \bar k$. -/
def GenusOneCurve.PointOverAlgClosure {k : Type u} [Field k]
    (C : GenusOneCurve k) : Type u :=
  (C.Jacobian.curve.baseChange (AlgebraicClosure k)).toAffine.Point

/-- The set of $\bar k$-rational points of the Jacobian is nonempty, witnessed
by the identity element. -/
theorem GenusOneCurve.PointOverAlgClosure.nonempty {k : Type u} [Field k]
    (C : GenusOneCurve k) : Nonempty (C.PointOverAlgClosure) :=
  ⟨(0 : (C.Jacobian.curve.baseChange (AlgebraicClosure k)).toAffine.Point)⟩

/-- Given a $\bar k$-point $O$ of $C$, the associated elliptic curve over
$\bar k$ obtained by translating the Weierstrass model so that $O$ becomes the
identity. -/
noncomputable def GenusOneCurve.ellipticCurveAtBasePoint {k : Type u} [Field k]
    (C : GenusOneCurve k) (O : C.PointOverAlgClosure) :
    EllipticCurveOver (AlgebraicClosure k) :=
  haveI : C.Jacobian.curve.IsElliptic := C.Jacobian.isElliptic
  { curve := (C.weierstrassModel O) • (C.Jacobian.curve.baseChange (AlgebraicClosure k)) }

/-- An elliptic curve bundles an `IsElliptic` instance on its underlying
Weierstrass curve, registered for typeclass search. -/
instance EllipticCurveOver.instIsElliptic {k : Type*} [Field k] (E : EllipticCurveOver k) :
    E.curve.IsElliptic := E.isElliptic

/-- Changing the base point $O \mapsto O'$ on a genus-one curve $C$ yields an
isomorphism of the associated elliptic curves over $\bar k$ via an explicit
Weierstrass variable change. -/
theorem GenusOneCurve.translationIsomorphism {k : Type u} [Field k]
    (C : GenusOneCurve k) (O O' : C.PointOverAlgClosure) :
    ∃ σ : WeierstrassCurve.VariableChange (AlgebraicClosure k),
      (C.ellipticCurveAtBasePoint O').curve = σ • (C.ellipticCurveAtBasePoint O).curve :=
  ⟨C.weierstrassModel O' * (C.weierstrassModel O)⁻¹,
    by simp only [ellipticCurveAtBasePoint, mul_smul, inv_smul_smul]⟩

/-- The $j$-invariant of the elliptic curve $C_O$ associated to $C$ at a base
point $O$ is independent of the choice of base point. -/
theorem GenusOneCurve.jInvariant_eq_of_basePoints
    {k : Type u} [Field k] (C : GenusOneCurve k)
    (O O' : C.PointOverAlgClosure) :
    (C.ellipticCurveAtBasePoint O).jInvariant =
      (C.ellipticCurveAtBasePoint O').jInvariant := by


  simp only [EllipticCurveOver.jInvariant, ellipticCurveAtBasePoint, variableChange_j]

/-- The $j$-invariant $j(C) \in k$ of a genus-one curve $C$, defined as the
$j$-invariant of its Jacobian. -/
def GenusOneCurve.jInvariant {k : Type u} [Field k] (C : GenusOneCurve k) : k :=
  C.Jacobian.jInvariant

/-- Definitional unfolding: $j(C) = j(\mathrm{Jac}(C))$. -/
@[simp]
theorem GenusOneCurve.jInvariant_eq_jacobian_jInvariant
    {k : Type u} [Field k] (C : GenusOneCurve k) :
    C.jInvariant = C.Jacobian.jInvariant :=
  rfl

/-- **Theorem 26.4 ($\Rightarrow$).** If $W_1$ and $W_2$ become isomorphic over
the algebraic closure $\bar k$, then they have the same $j$-invariant. -/
theorem j_eq_of_isomorphic_over_closure
    {k : Type*} [Field k]
    (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic]
    (h : ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure k)),
      C • (W₁.baseChange (AlgebraicClosure k)) =
      W₂.baseChange (AlgebraicClosure k)) :
    W₁.j = W₂.j := by
  obtain ⟨C, hC⟩ := h
  have h1 := W₁.map_j (algebraMap k (AlgebraicClosure k))
  have h2 := W₂.map_j (algebraMap k (AlgebraicClosure k))
  have h3 := variableChange_j (W₁.baseChange (AlgebraicClosure k)) C
  have h4 : (C • W₁.baseChange (AlgebraicClosure k)).j =
    (W₂.baseChange (AlgebraicClosure k)).j := by simp only [hC]
  have h5 : (W₁.baseChange (AlgebraicClosure k)).j =
    (W₂.baseChange (AlgebraicClosure k)).j := h3.symm.trans h4
  change (W₁.map (algebraMap k (AlgebraicClosure k))).j =
    (W₂.map (algebraMap k (AlgebraicClosure k))).j at h5
  rw [h1, h2] at h5
  exact (algebraMap k (AlgebraicClosure k)).injective h5

/-- **Theorem 26.4 ($\Leftarrow$).** If two elliptic Weierstrass curves over
$k$ share the same $j$-invariant, they become isomorphic after base change to
$\bar k$. -/
theorem isomorphic_over_closure_of_j_eq
    {k : Type*} [Field k]
    (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic]
    (hj : W₁.j = W₂.j) :
    ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure k)),
      C • (W₁.baseChange (AlgebraicClosure k)) =
      W₂.baseChange (AlgebraicClosure k) := by
  have h1 := W₁.map_j (algebraMap k (AlgebraicClosure k))
  have h2 := W₂.map_j (algebraMap k (AlgebraicClosure k))
  have hj' : (W₁.baseChange (AlgebraicClosure k)).j =
      (W₂.baseChange (AlgebraicClosure k)).j := by
    change (W₁.map (algebraMap k (AlgebraicClosure k))).j =
      (W₂.map (algebraMap k (AlgebraicClosure k))).j
    rw [h1, h2, hj]
  exact exists_variableChange_of_j_eq _ _ hj'

/-- **Theorem 26.4.** Two elliptic Weierstrass curves over $k$ have equal
$j$-invariant if and only if they become isomorphic over the algebraic closure
$\bar k$. -/
theorem j_invariant_iff_isomorphic_over_closure
    {k : Type*} [Field k]
    (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic] :
    W₁.j = W₂.j ↔
    ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure k)),
      C • (W₁.baseChange (AlgebraicClosure k)) =
      W₂.baseChange (AlgebraicClosure k) :=
  ⟨isomorphic_over_closure_of_j_eq W₁ W₂, j_eq_of_isomorphic_over_closure W₁ W₂⟩

end
