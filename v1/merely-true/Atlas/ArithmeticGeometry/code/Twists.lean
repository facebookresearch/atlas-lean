/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Atlas.ArithmeticGeometry.code.JInvariant

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ArithmeticGeometry

/-- The affine scheme $\mathrm{Spec}\, R$ for a commutative ring $R$. -/
noncomputable abbrev specOf (R : Type u) [CommRing R] : Scheme.{u} := Spec (.of R)

variable (k : Type u) [Field k]

/-- The morphism of schemes $\mathrm{Spec}\, \overline{k} \to \mathrm{Spec}\, k$
induced by the algebraic closure inclusion $k \hookrightarrow \overline{k}$. -/
noncomputable def specAlgClosureToSpec :
    specOf (AlgebraicClosure k) ⟶ specOf k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- Base change of a $k$-scheme $X$ along the algebraic closure, producing the
$\overline{k}$-scheme $X_{\overline{k}} := X \times_{\mathrm{Spec}\, k} \mathrm{Spec}\, \overline{k}$. -/
noncomputable def baseChangeToAlgClosure (X : Scheme.{u}) [X.Over (specOf k)] : Scheme.{u} :=
  pullback (X ↘ specOf k) (specAlgClosureToSpec k)

/-- The base change $X_{\overline{k}}$ is canonically a scheme over
$\mathrm{Spec}\, \overline{k}$. -/
noncomputable instance baseChangeToAlgClosure_over (X : Scheme.{u}) [X.Over (specOf k)] :
    (baseChangeToAlgClosure k X).Over (specOf (AlgebraicClosure k)) :=
  Scheme.canonicallyOverPullback.toOverClass

/-- **Definition 26.1.** Two $k$-schemes $X$ and $Y$ are *twists* of each other
if they become isomorphic over the algebraic closure: $X_{\overline{k}} \cong
Y_{\overline{k}}$ as $\overline{k}$-schemes. -/
def AreTwists (X Y : Scheme.{u}) [X.Over (specOf k)] [Y.Over (specOf k)] : Prop :=
  Nonempty (
    Scheme.asOver (baseChangeToAlgClosure k X) (specOf (AlgebraicClosure k)) ≅
    Scheme.asOver (baseChangeToAlgClosure k Y) (specOf (AlgebraicClosure k)))

variable {k}

/-- Reflexivity of the twist relation: every scheme is a twist of itself. -/
theorem AreTwists.refl (X : Scheme.{u}) [X.Over (specOf k)] : AreTwists k X X :=
  ⟨Iso.refl _⟩

/-- Symmetry of the twist relation: if $X$ and $Y$ are twists, then so are
$Y$ and $X$. -/
theorem AreTwists.symm {X Y : Scheme.{u}} [X.Over (specOf k)] [Y.Over (specOf k)]
    (h : AreTwists k X Y) : AreTwists k Y X :=
  h.map Iso.symm

/-- Transitivity of the twist relation: if $X$ is a twist of $Y$ and $Y$ is a
twist of $Z$, then $X$ is a twist of $Z$. -/
theorem AreTwists.trans {X Y Z : Scheme.{u}} [X.Over (specOf k)] [Y.Over (specOf k)]
    [Z.Over (specOf k)] (hXY : AreTwists k X Y) (hYZ : AreTwists k Y Z) :
    AreTwists k X Z := by
  obtain ⟨f⟩ := hXY
  obtain ⟨g⟩ := hYZ
  exact ⟨f ≪≫ g⟩

end ArithmeticGeometry

section GenusOneTwist

universe v

variable {k : Type v} [Field k]

/-- A genus-one curve $C$ is a *twist* of an elliptic curve $E$ if its Jacobian
becomes isomorphic to $E$ over the algebraic closure $\overline{k}$, via a
Weierstrass variable change. -/
def GenusOneCurve.IsTwistOfEllipticCurve {k : Type v} [Field k]
    (C : GenusOneCurve k) (E : EllipticCurveOver k) : Prop :=
  ∃ (σ : WeierstrassCurve.VariableChange (AlgebraicClosure k)),
    σ • (C.Jacobian.curve.baseChange (AlgebraicClosure k)) =
    E.curve.baseChange (AlgebraicClosure k)


/-- **Theorem 26.3 (existence of an elliptic curve with prescribed
$j$-invariant).** Every genus-one curve $C$ over $k$ is a twist of some
elliptic curve $E$ over $k$ sharing the same $j$-invariant. -/
theorem GenusOneCurve.exists_ellipticCurve_twist {k : Type v} [Field k]
    (C : GenusOneCurve k) :
    ∃ E : EllipticCurveOver k, C.IsTwistOfEllipticCurve E := by


  obtain ⟨E, hE⟩ := j_invariant_surjective C.jInvariant

  refine ⟨E, ?_⟩
  rw [IsTwistOfEllipticCurve]


  haveI := C.Jacobian.isElliptic
  haveI := E.isElliptic
  exact isomorphic_over_closure_of_j_eq C.Jacobian.curve E.curve hE.symm

/-- Two elliptic curves over $k$ are *isomorphic over $k$* if there exists a
Weierstrass variable change defined over $k$ taking one to the other. -/
def EllipticCurveOver.IsIsomorphicOverK {k : Type v} [Field k]
    (E₁ E₂ : EllipticCurveOver k) : Prop :=
  ∃ σ : WeierstrassCurve.VariableChange k, E₁.curve = σ • E₂.curve

/-- No rational number satisfies $q^4 = 4$; equivalently, $\sqrt[4]{4}$ is
irrational. Used to exhibit nontrivial twists over $\mathbb{Q}$. -/
lemma Rat.no_fourth_root_of_four : ∀ q : ℚ, q ^ 4 ≠ 4 := by
  intro q hq
  have hcop : Int.gcd q.num q.den = 1 := q.reduced
  have h1 : (q.num : ℚ) ^ 4 = 4 * (q.den : ℚ) ^ 4 := by
    have : q = q.num / q.den := (Rat.num_div_den q).symm
    rw [this] at hq; field_simp at hq; linarith
  have h2 : q.num ^ 4 = 4 * (q.den : ℤ) ^ 4 := by exact_mod_cast h1
  have h_2_num : (2 : ℤ) ∣ q.num := by
    have hdvd : (2 : ℤ) ∣ q.num ^ (4 : ℕ) := ⟨2 * (q.den : ℤ) ^ 4, by linarith⟩
    exact Prime.dvd_of_dvd_pow Int.prime_two hdvd
  have h_2_den : (2 : ℤ) ∣ (q.den : ℤ) := by
    obtain ⟨m, hm⟩ := h_2_num
    have hd4 : (q.den : ℤ) ^ (4 : ℕ) = 4 * m ^ (4 : ℕ) := by have := hm ▸ h2; nlinarith
    have hdvd : (2 : ℤ) ∣ (q.den : ℤ) ^ (4 : ℕ) := ⟨2 * m ^ (4 : ℕ), by linarith [hd4]⟩
    exact Prime.dvd_of_dvd_pow Int.prime_two hdvd
  have : (2 : ℕ) ∣ Int.gcd q.num q.den := by exact_mod_cast Int.dvd_gcd h_2_num h_2_den
  rw [hcop] at this; omega

/-- The elliptic curves $y^2 = x^3 - x$ and $y^2 = x^3 - 4x$ over $\mathbb{Q}$
are *not* isomorphic over $\mathbb{Q}$, even though they have the same
$j$-invariant. Concrete witness that nontrivial twists exist over $\mathbb{Q}$. -/
lemma not_iso_y2x3mx_y2x3m4x :
    ¬∃ σ : WeierstrassCurve.VariableChange ℚ,
      (WeierstrassCurve.mk 0 0 0 (-1) 0 : WeierstrassCurve ℚ) =
      σ • (WeierstrassCurve.mk 0 0 0 (-4) 0 : WeierstrassCurve ℚ) := by
  rintro ⟨σ, h⟩
  have ha₁ := congr_arg WeierstrassCurve.a₁ h
  have ha₂ := congr_arg WeierstrassCurve.a₂ h
  have ha₃ := congr_arg WeierstrassCurve.a₃ h
  have ha₄ := congr_arg WeierstrassCurve.a₄ h
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄] at ha₁ ha₂ ha₃ ha₄
  have hu_inv_ne : (σ.u⁻¹ : ℚˣ).val ≠ 0 := σ.u⁻¹.ne_zero

  have hs : σ.s = 0 := by
    have : (↑σ.u⁻¹ : ℚ) * (0 + 2 * σ.s) = 0 := by linarith
    cases mul_eq_zero.mp this with
    | inl h => exact absurd h hu_inv_ne
    | inr h => linarith

  have ht : σ.t = 0 := by
    have : (↑σ.u⁻¹ : ℚ) ^ 3 * (2 * σ.t) = 0 := by ring_nf; ring_nf at ha₃; linarith
    cases mul_eq_zero.mp this with
    | inl h => exact absurd (pow_eq_zero_iff (n := 3) (by omega) |>.mp h) hu_inv_ne
    | inr h => linarith

  have hr : σ.r = 0 := by
    have : (↑σ.u⁻¹ : ℚ) ^ 2 * (3 * σ.r - σ.s ^ 2) = 0 := by
      ring_nf; ring_nf at ha₂; linarith
    cases mul_eq_zero.mp this with
    | inl h => exact absurd (pow_eq_zero_iff (n := 2) (by omega) |>.mp h) hu_inv_ne
    | inr h => nlinarith [hs]

  exact Rat.no_fourth_root_of_four (↑σ.u) (by
    simp only [hs, ht, hr] at ha₄
    have : (↑σ.u⁻¹ : ℚ) ^ 4 * 4 = 1 := by nlinarith
    rw [Units.val_inv_eq_inv_val, inv_pow] at this
    field_simp at this; linarith)

/-- The ring homomorphism $\mathrm{ULift}\, \mathbb{Q} \to \mathbb{Q}$ coming
from the canonical equivalence. A universe-polymorphism utility. -/
noncomputable abbrev uliftQToQ : ULift.{v, 0} ℚ →+* ℚ :=
  (ULift.ringEquiv (R := ℚ)).toRingHom


end GenusOneTwist
