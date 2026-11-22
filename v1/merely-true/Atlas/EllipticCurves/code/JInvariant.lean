/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

variable {k : Type*} [Field k]

/-- The short Weierstrass curve $y^2 = x^3 + Ax + B$, represented as the
`WeierstrassCurve` with $a_1 = a_2 = a_3 = 0$, $a_4 = A$, and $a_6 = B$. Over fields
of characteristic $\neq 2, 3$ every elliptic curve is isomorphic to one in this form. -/
def shortWeierstrassCurve (A B : k) : WeierstrassCurve k :=
  ⟨0, 0, 0, A, B⟩

/-- The $j$-invariant of a short Weierstrass curve $y^2 = x^3 + Ax + B$
(Definition 13.11): $j(A, B) = 1728 \cdot 4A^3 / (4A^3 + 27B^2)$. -/
def jInvariant (A B : k) : k :=
  1728 * (4 * A ^ 3) / (4 * A ^ 3 + 27 * B ^ 2)

/-- For a short Weierstrass curve, the invariant $c_4$ simplifies to $-48 A$. -/
@[simp]
lemma shortWeierstrassCurve_c₄ (A B : k) :
    (shortWeierstrassCurve A B).c₄ = -48 * A := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

/-- For a short Weierstrass curve, the discriminant simplifies to
$\Delta = -16(4A^3 + 27B^2)$. -/
@[simp]
lemma shortWeierstrassCurve_Δ (A B : k) :
    (shortWeierstrassCurve A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [shortWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- In a field where $2 \neq 0$, we also have $4 = 2^2 \neq 0$. -/
lemma four_ne_zero_of_two_ne_zero (h2 : (2 : k) ≠ 0) : (4 : k) ≠ 0 := by
  have : (4 : k) = 2 ^ 2 := by norm_num
  rw [this]; exact pow_ne_zero 2 h2

/-- In a field where $2 \neq 0$, we also have $16 = 2^4 \neq 0$. -/
lemma sixteen_ne_zero_of_two_ne_zero (h2 : (2 : k) ≠ 0) : (16 : k) ≠ 0 := by
  have : (16 : k) = 2 ^ 4 := by norm_num
  rw [this]; exact pow_ne_zero 4 h2

/-- A short Weierstrass curve $y^2 = x^3 + Ax + B$ defines an elliptic curve provided
$2 \neq 0$ and the discriminant condition $4A^3 + 27B^2 \neq 0$ holds. -/
lemma shortWeierstrassCurve_isElliptic (A B : k)
    (h2 : (2 : k) ≠ 0) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    (shortWeierstrassCurve A B).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, shortWeierstrassCurve_Δ]
  exact mul_ne_zero (neg_ne_zero.mpr (sixteen_ne_zero_of_two_ne_zero h2)) hΔ

/-- The Mathlib-defined $j$-invariant of a short Weierstrass curve agrees with the
explicit formula `jInvariant A B = 1728 \cdot 4A^3 / (4A^3 + 27B^2)` of Definition 13.11. -/
theorem j_eq_jInvariant (A B : k) (h2 : (2 : k) ≠ 0)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    haveI := shortWeierstrassCurve_isElliptic A B h2 hΔ
    (shortWeierstrassCurve A B).j = jInvariant A B := by
  haveI := shortWeierstrassCurve_isElliptic A B h2 hΔ
  simp only [WeierstrassCurve.j, jInvariant]
  have hΔ_val : ((shortWeierstrassCurve A B).Δ' : k) = (shortWeierstrassCurve A B).Δ :=
    WeierstrassCurve.coe_Δ' _
  simp only [Units.val_inv_eq_inv_val, hΔ_val, shortWeierstrassCurve_Δ,
    shortWeierstrassCurve_c₄]
  have h16 : (16 : k) ≠ 0 := sixteen_ne_zero_of_two_ne_zero h2
  field_simp
  ring

/-- When $A = 0$, the $j$-invariant of $y^2 = x^3 + B$ is $0$. -/
@[simp]
theorem jInvariant_of_A_eq_zero (B : k) :
    jInvariant (0 : k) B = 0 := by
  simp [jInvariant]

/-- When $B = 0$ (and $A \neq 0$, $2 \neq 0$), the $j$-invariant of $y^2 = x^3 + Ax$
is exactly $1728$. -/
theorem jInvariant_of_B_eq_zero (A : k) (hA : A ≠ 0) (h2 : (2 : k) ≠ 0) :
    jInvariant A (0 : k) = 1728 := by
  simp only [jInvariant, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    add_zero]
  rw [mul_div_cancel_right₀]
  exact mul_ne_zero (four_ne_zero_of_two_ne_zero h2) (pow_ne_zero 3 hA)

/-- In a field where $3 \neq 0$, we also have $27 = 3^3 \neq 0$. -/
lemma twentyseven_ne_zero_of_three_ne_zero (h3 : (3 : k) ≠ 0) : (27 : k) ≠ 0 := by
  have : (27 : k) = 3 ^ 3 := by norm_num
  rw [this]; exact pow_ne_zero 3 h3

/-- In a field where $2 \neq 0$ and $3 \neq 0$, we have $108 = 2^2 \cdot 3^3 \neq 0$. -/
lemma onehundredeight_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) : (108 : k) ≠ 0 := by
  have : (108 : k) = 2 ^ 2 * 3 ^ 3 := by norm_num
  rw [this]; exact mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 3 h3)

/-- In a field where $2 \neq 0$ and $3 \neq 0$, we have $1728 = 2^6 \cdot 3^3 \neq 0$. -/
lemma seventeentwentyeight_ne_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    (1728 : k) ≠ 0 := by
  have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
  rw [this]; exact mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3)

/-- Theorem 13.12 (surjectivity of $j$): over any field of characteristic $\neq 2, 3$,
every $j_0 \in k$ arises as the $j$-invariant of some short Weierstrass curve. The
construction is explicit: $j_0 = 0$ uses $(A, B) = (0, 1)$, $j_0 = 1728$ uses
$(1, 0)$, and otherwise $(3 j_0 (1728 - j_0), 2 j_0 (1728 - j_0)^2)$. -/
theorem jInvariant_surjective (j₀ : k) (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    ∃ A B : k, 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 ∧ jInvariant A B = j₀ := by
  by_cases hj0 : j₀ = 0
  ·
    refine ⟨0, 1, ?_, ?_⟩
    · simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add,
        one_pow, mul_one]
      exact twentyseven_ne_zero_of_three_ne_zero h3
    · rw [hj0]; simp [jInvariant]
  · by_cases hj1728 : j₀ = 1728
    ·
      refine ⟨1, 0, ?_, ?_⟩
      · simp only [one_pow, mul_one, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, add_zero]
        exact four_ne_zero_of_two_ne_zero h2
      · rw [hj1728]; unfold jInvariant
        simp only [one_pow, mul_one, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, mul_zero, add_zero]
        have h4 : (4 : k) ≠ 0 := four_ne_zero_of_two_ne_zero h2
        field_simp
    ·
      have h1728' : (1728 : k) - j₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hj1728)
      have hdisc : 4 * (3 * j₀ * (1728 - j₀)) ^ 3 +
          27 * (2 * j₀ * (1728 - j₀) ^ 2) ^ 2 ≠ 0 := by
        rw [show 4 * (3 * j₀ * (1728 - j₀)) ^ 3 + 27 * (2 * j₀ * (1728 - j₀) ^ 2) ^ 2
          = 108 * 1728 * j₀ ^ 2 * (1728 - j₀) ^ 3 from by ring]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (onehundredeight_ne_zero h2 h3)
          (seventeentwentyeight_ne_zero h2 h3)) (pow_ne_zero 2 hj0)) (pow_ne_zero 3 h1728')
      refine ⟨3 * j₀ * (1728 - j₀), 2 * j₀ * (1728 - j₀) ^ 2, hdisc, ?_⟩

      unfold jInvariant
      rw [div_eq_iff hdisc]
      ring

/-- Forward direction of the isomorphism classification (Theorem 13.13): any change of
variables taking a short Weierstrass curve to another short Weierstrass curve must have
$s = r = t = 0$, with the action on the coefficients given by $A' = u^{-4} A$ and
$B' = u^{-6} B$. -/
theorem short_weierstrass_iso_forward (A B A' B' : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (C : WeierstrassCurve.VariableChange k)
    (hC : C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k) = ⟨0, 0, 0, A', B'⟩) :
    C.s = 0 ∧ C.r = 0 ∧ C.t = 0 ∧
    A' = (↑C.u⁻¹ : k) ^ 4 * A ∧ B' = (↑C.u⁻¹ : k) ^ 6 * B := by

  have ha₁ := congr_arg WeierstrassCurve.a₁ hC
  have ha₂ := congr_arg WeierstrassCurve.a₂ hC
  have ha₃ := congr_arg WeierstrassCurve.a₃ hC
  have ha₄ := congr_arg WeierstrassCurve.a₄ hC
  have ha₆ := congr_arg WeierstrassCurve.a₆ hC

  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆,
    zero_add, mul_zero, sub_zero, add_zero] at ha₁ ha₂ ha₃ ha₄ ha₆

  have hs : C.s = 0 := by
    have h1 : 2 * C.s = 0 := (mul_eq_zero.mp ha₁).resolve_left (Units.ne_zero _)
    exact (mul_eq_zero.mp h1).resolve_left h2

  have hr : C.r = 0 := by
    have h1 : 3 * C.r - C.s ^ 2 = 0 :=
      (mul_eq_zero.mp ha₂).resolve_left (pow_ne_zero 2 (Units.ne_zero _))
    rw [hs, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left h3

  have ht : C.t = 0 := by
    have h1 : 2 * C.t = 0 :=
      (mul_eq_zero.mp ha₃).resolve_left (pow_ne_zero 3 (Units.ne_zero _))
    exact (mul_eq_zero.mp h1).resolve_left h2

  simp only [hs, hr, ht, zero_mul, mul_zero, sub_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, add_zero] at ha₄ ha₆
  exact ⟨hs, hr, ht, ha₄.symm, ha₆.symm⟩

/-- Backward direction of the isomorphism classification: for each unit $\mu \in k^\times$
the variable change with parameter $\mu^{-1}$ (and $r = s = t = 0$) takes $(A, B)$ to
$(\mu^4 A, \mu^6 B)$. -/
theorem short_weierstrass_iso_backward (A B : k) (μ : kˣ) :
    (⟨μ⁻¹, 0, 0, 0⟩ : WeierstrassCurve.VariableChange k) •
      (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k) =
      ⟨0, 0, 0, (↑μ : k) ^ 4 * A, (↑μ : k) ^ 6 * B⟩ := by
  ext <;> simp [WeierstrassCurve.variableChange_def]

/-- Theorem 13.13 (isomorphism of short Weierstrass curves): two short Weierstrass
curves are isomorphic over $k$ iff $(A', B') = (\mu^4 A, \mu^6 B)$ for some $\mu \in k^\times$. -/
theorem short_weierstrass_iso_iff (A B A' B' : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    (∃ C : WeierstrassCurve.VariableChange k,
      C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k) = ⟨0, 0, 0, A', B'⟩) ↔
    (∃ μ : kˣ, A' = (↑μ : k) ^ 4 * A ∧ B' = (↑μ : k) ^ 6 * B) := by
  constructor
  ·
    rintro ⟨C, hC⟩
    obtain ⟨_, _, _, hA', hB'⟩ := short_weierstrass_iso_forward A B A' B' h2 h3 C hC
    exact ⟨C.u⁻¹, hA', hB'⟩
  ·
    rintro ⟨μ, hA', hB'⟩
    exact ⟨⟨μ⁻¹, 0, 0, 0⟩, by rw [hA', hB']; exact short_weierstrass_iso_backward A B μ⟩

/-- The $j$-invariant is scaling-invariant under $(A, B) \mapsto (\mu^4 A, \mu^6 B)$:
this is the algebraic incarnation of the geometric isomorphism class invariance. -/
theorem jInvariant_scaling (A B : k) (μ : k) (hμ : μ ≠ 0) :
    jInvariant (μ ^ 4 * A) (μ ^ 6 * B) = jInvariant A B := by
  unfold jInvariant
  have hμ12 : μ ^ 12 ≠ 0 := pow_ne_zero 12 hμ
  have h1 : 4 * (μ ^ 4 * A) ^ 3 + 27 * (μ ^ 6 * B) ^ 2 =
      μ ^ 12 * (4 * A ^ 3 + 27 * B ^ 2) := by ring
  rw [h1, show 1728 * (4 * (μ ^ 4 * A) ^ 3) = μ ^ 12 * (1728 * (4 * A ^ 3)) from by ring,
    mul_div_mul_left _ _ hμ12]

/-- If a nondegenerate short Weierstrass curve has $j = 0$ (in characteristic $\neq 2, 3$),
then $A = 0$. This corresponds to the special locus of curves $y^2 = x^3 + B$. -/
lemma A_eq_zero_of_jInvariant_eq_zero (A B : k)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hj : jInvariant A B = 0) : A = 0 := by
  unfold jInvariant at hj
  rw [div_eq_zero_iff] at hj
  rcases hj with h | h
  · rcases mul_eq_zero.mp h with h1728 | h4A3
    · have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
      rw [this] at h1728
      exact absurd h1728 (mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3))
    · rcases mul_eq_zero.mp h4A3 with h4 | hA3
      · have : (4 : k) = 2 ^ 2 := by norm_num
        rw [this] at h4
        exact absurd h4 (pow_ne_zero 2 h2)
      · exact (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hA3
  · exact absurd h hΔ

/-- If a nondegenerate short Weierstrass curve has $j = 1728$ (in characteristic $\neq 2, 3$),
then $B = 0$. This corresponds to the special locus of curves $y^2 = x^3 + Ax$. -/
lemma B_eq_zero_of_jInvariant_eq_1728 (A B : k)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hj : jInvariant A B = 1728) : B = 0 := by
  unfold jInvariant at hj
  rw [div_eq_iff hΔ] at hj
  have h1728 : (1728 : k) ≠ 0 := by
    have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3)
  have h27 : (27 : k) ≠ 0 := by
    have : (27 : k) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h3
  have heq : 4 * A ^ 3 = 4 * A ^ 3 + 27 * B ^ 2 := mul_left_cancel₀ h1728 hj
  have hB2 : 27 * B ^ 2 = 0 := by
    have : 4 * A ^ 3 + 27 * B ^ 2 - 4 * A ^ 3 = 0 := by rw [← heq]; ring
    simpa using this
  exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp ((mul_eq_zero.mp hB2).resolve_left h27)

/-- Cross-multiplying the equality $j(A, B) = j(A', B')$ on the $A$ side yields
$A^3 \Delta' = A'^3 \Delta$ where $\Delta = 4A^3 + 27 B^2$. -/
lemma jInvariant_cross_multiply (A B A' B' : k)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hj : jInvariant A B = jInvariant A' B') :
    A ^ 3 * (4 * A' ^ 3 + 27 * B' ^ 2) = A' ^ 3 * (4 * A ^ 3 + 27 * B ^ 2) := by
  unfold jInvariant at hj
  have h6912 : (6912 : k) ≠ 0 := by
    have : (6912 : k) = 2 ^ 8 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero 8 h2) (pow_ne_zero 3 h3)
  rw [div_eq_div_iff hΔ hΔ'] at hj
  exact mul_left_cancel₀ h6912
    (show 6912 * (A ^ 3 * (4 * A' ^ 3 + 27 * B' ^ 2)) =
      6912 * (A' ^ 3 * (4 * A ^ 3 + 27 * B ^ 2)) by
      rw [show 6912 * (A ^ 3 * (4 * A' ^ 3 + 27 * B' ^ 2)) =
        1728 * (4 * A ^ 3) * (4 * A' ^ 3 + 27 * B' ^ 2) from by ring,
        show 6912 * (A' ^ 3 * (4 * A ^ 3 + 27 * B ^ 2)) =
        1728 * (4 * A' ^ 3) * (4 * A ^ 3 + 27 * B ^ 2) from by ring]
      exact hj)

/-- From the cross-multiplication identity for $A$, derive the analogous identity for
$B$: $B^2 \Delta' = B'^2 \Delta$. -/
lemma jInvariant_cross_multiply_B (A B A' B' : k)
    (h3 : (3 : k) ≠ 0)
    (hjcross : A ^ 3 * (4 * A' ^ 3 + 27 * B' ^ 2) = A' ^ 3 * (4 * A ^ 3 + 27 * B ^ 2)) :
    B ^ 2 * (4 * A' ^ 3 + 27 * B' ^ 2) = B' ^ 2 * (4 * A ^ 3 + 27 * B ^ 2) := by
  have h27 : (27 : k) ≠ 0 := by
    have : (27 : k) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero 3 h3
  have hab : A ^ 3 * B' ^ 2 = A' ^ 3 * B ^ 2 :=
    mul_left_cancel₀ h27 (add_left_cancel
      (show 4 * A ^ 3 * A' ^ 3 + 27 * (A ^ 3 * B' ^ 2) =
        4 * A ^ 3 * A' ^ 3 + 27 * (A' ^ 3 * B ^ 2) by
        rw [show 4 * A ^ 3 * A' ^ 3 + 27 * (A ^ 3 * B' ^ 2) =
          A ^ 3 * (4 * A' ^ 3 + 27 * B' ^ 2) from by ring,
          show 4 * A ^ 3 * A' ^ 3 + 27 * (A' ^ 3 * B ^ 2) =
          A' ^ 3 * (4 * A ^ 3 + 27 * B ^ 2) from by ring]
        exact hjcross))
  rw [show B ^ 2 * (4 * A' ^ 3 + 27 * B' ^ 2) =
    4 * (A' ^ 3 * B ^ 2) + 27 * B ^ 2 * B' ^ 2 from by ring,
    show B' ^ 2 * (4 * A ^ 3 + 27 * B ^ 2) =
    4 * (A ^ 3 * B' ^ 2) + 27 * B ^ 2 * B' ^ 2 from by ring, hab]

/-- Generic case of the $j$-invariant converse: when $A, B, A', B' \neq 0$ and
$j(A,B) = j(A',B')$, there exists $u \neq 0$ with $A' = u^2 A$ and $B' = u^3 B$.
This produces the explicit isomorphism witness in the open locus $j \notin \{0, 1728\}$. -/
theorem jInvariant_converse_generic (A B A' B' : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hA' : A' ≠ 0) (hB' : B' ≠ 0)
    (hj : jInvariant A B = jInvariant A' B') :
    ∃ u : k, u ≠ 0 ∧ A' = u ^ 2 * A ∧ B' = u ^ 3 * B := by
  have hjcross := jInvariant_cross_multiply A B A' B' hΔ hΔ' h2 h3 hj
  have hBcross := jInvariant_cross_multiply_B A B A' B' h3 hjcross
  have hden : (4 * A ^ 3 + 27 * B ^ 2) * A' * B' ≠ 0 :=
    mul_ne_zero (mul_ne_zero hΔ hA') hB'
  refine ⟨A * B * (4 * A' ^ 3 + 27 * B' ^ 2) / ((4 * A ^ 3 + 27 * B ^ 2) * A' * B'),
    div_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hΔ') hden, ?_, ?_⟩
  ·
    suffices h : (A * B * (4 * A' ^ 3 + 27 * B' ^ 2)) ^ 2 * A =
      A' * ((4 * A ^ 3 + 27 * B ^ 2) * A' * B') ^ 2 by
      rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hden)]
      exact h.symm
    calc (A * B * (4 * A' ^ 3 + 27 * B' ^ 2)) ^ 2 * A
        = (A ^ 3 * (4 * A' ^ 3 + 27 * B' ^ 2)) *
          (B ^ 2 * (4 * A' ^ 3 + 27 * B' ^ 2)) := by ring
      _ = (A' ^ 3 * (4 * A ^ 3 + 27 * B ^ 2)) *
          (B' ^ 2 * (4 * A ^ 3 + 27 * B ^ 2)) := by rw [hjcross, hBcross]
      _ = A' * ((4 * A ^ 3 + 27 * B ^ 2) * A' * B') ^ 2 := by ring
  ·
    suffices h : (A * B * (4 * A' ^ 3 + 27 * B' ^ 2)) ^ 3 * B =
      B' * ((4 * A ^ 3 + 27 * B ^ 2) * A' * B') ^ 3 by
      rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 hden)]
      exact h.symm
    calc (A * B * (4 * A' ^ 3 + 27 * B' ^ 2)) ^ 3 * B
        = (A ^ 3 * (4 * A' ^ 3 + 27 * B' ^ 2)) *
          (B ^ 2 * (4 * A' ^ 3 + 27 * B' ^ 2)) *
          (B ^ 2 * (4 * A' ^ 3 + 27 * B' ^ 2)) := by ring
      _ = (A' ^ 3 * (4 * A ^ 3 + 27 * B ^ 2)) *
          (B' ^ 2 * (4 * A ^ 3 + 27 * B ^ 2)) *
          (B' ^ 2 * (4 * A ^ 3 + 27 * B ^ 2)) := by rw [hjcross, hBcross]
      _ = B' * ((4 * A ^ 3 + 27 * B ^ 2) * A' * B') ^ 3 := by ring

/-- If two short Weierstrass curves are related by the standard scaling
$A' = \mu^4 A, B' = \mu^6 B$, then they have the same $j$-invariant. -/
theorem jInvariant_eq_of_iso (A B A' B' : k) (μ : k) (hμ : μ ≠ 0)
    (hA' : A' = μ ^ 4 * A) (hB' : B' = μ ^ 6 * B) :
    jInvariant A B = jInvariant A' B' := by
  rw [hA', hB', jInvariant_scaling A B μ hμ]

/-- Converse of equality of $j$-invariants in the generic case $j \neq 0, 1728$:
deduces from $\Delta, \Delta' \neq 0$ and $j(A,B) = j(A',B')$ that all of $A, B, A', B'$
are nonzero, then applies `jInvariant_converse_generic`. -/
theorem jInvariant_converse_ne_zero_ne_1728 (A B A' B' : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0)
    (hj : jInvariant A B = jInvariant A' B')
    (hj0 : jInvariant A B ≠ 0) (hj1728 : jInvariant A B ≠ 1728) :
    ∃ u : k, u ≠ 0 ∧ A' = u ^ 2 * A ∧ B' = u ^ 3 * B := by
  have hA : A ≠ 0 := by
    intro hA; apply hj0; rw [hA]; simp [jInvariant]
  have hA' : A' ≠ 0 := by
    intro hA'; apply hj0; rw [hj]; rw [hA']; simp [jInvariant]
  have hB : B ≠ 0 := by
    intro hB; apply hj1728
    simp only [jInvariant, hB, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, add_zero]
    rw [mul_div_cancel_right₀]
    exact mul_ne_zero (by have : (4 : k) = 2 ^ 2 := by norm_num
                          rw [this]; exact pow_ne_zero 2 h2) (pow_ne_zero 3 hA)
  have hB' : B' ≠ 0 := by
    intro hB'


    by_cases hA'0 : A' = 0
    · apply hj0; rw [hj, hB', hA'0]; simp [jInvariant]
    · apply hj1728; rw [hj, hB']
      simp only [jInvariant, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, add_zero]
      rw [mul_div_cancel_right₀]
      exact mul_ne_zero (by have : (4 : k) = 2 ^ 2 := by norm_num
                            rw [this]; exact pow_ne_zero 2 h2) (pow_ne_zero 3 hA'0)

  exact jInvariant_converse_generic A B A' B' h2 h3 hΔ hΔ' hA hB hA' hB' hj

/-- If $j(A, B) = j(A', B') = 0$, then both $A$ and $A'$ are zero (special locus
of $j = 0$). -/
theorem jInvariant_converse_eq_zero (A B A' B' : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0)
    (hj : jInvariant A B = jInvariant A' B')
    (hj0 : jInvariant A B = 0) :
    A = 0 ∧ A' = 0 := by
  exact ⟨A_eq_zero_of_jInvariant_eq_zero A B hΔ h2 h3 hj0,
    A_eq_zero_of_jInvariant_eq_zero A' B' hΔ' h2 h3 (hj ▸ hj0)⟩

/-- If $j(A, B) = j(A', B') = 1728$, then both $B$ and $B'$ are zero (special locus
of $j = 1728$). -/
theorem jInvariant_converse_eq_1728 (A B A' B' : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0)
    (hj : jInvariant A B = jInvariant A' B')
    (hj1728 : jInvariant A B = 1728) :
    B = 0 ∧ B' = 0 := by
  exact ⟨B_eq_zero_of_jInvariant_eq_1728 A B hΔ h2 h3 hj1728,
    B_eq_zero_of_jInvariant_eq_1728 A' B' hΔ' h2 h3 (hj ▸ hj1728)⟩

/-- The $j$-invariant is preserved under base change along any field extension
$K/k$: $\mathrm{alg.map}(j(A, B)) = j(\mathrm{alg.map}(A), \mathrm{alg.map}(B))$. -/
lemma jInvariant_algebraMap (K : Type*) [Field K] [Algebra k K] (A B : k) :
    algebraMap k K (jInvariant A B) =
    jInvariant (algebraMap k K A) (algebraMap k K B) := by
  simp only [jInvariant, map_div₀, map_mul, map_pow, map_add, map_ofNat]

open Polynomial in
/-- If $\mu \in K$ satisfies $\mu^n = a$ for some $a \in k$ and $n > 0$, then $\mu$ is
algebraic over $k$ of degree at most $n$ (since $X^n - a$ is a degree-$n$ annihilating
polynomial). -/
lemma minpoly_natDegree_le_of_pow_eq {K : Type*} [Field K] [Algebra k K]
    (μ : K) (a : k) (n : ℕ) (hn : 0 < n) (hμ : μ ^ n = algebraMap k K a) :
    (minpoly k μ).natDegree ≤ n := by
  have hroot : aeval μ (X ^ n - C a : k[X]) = 0 := by simp [hμ]
  have hne : (X ^ n - C a : k[X]) ≠ 0 := X_pow_sub_C_ne_zero hn a
  calc (minpoly k μ).natDegree ≤ (X ^ n - C a : k[X]).natDegree :=
    natDegree_le_of_dvd (minpoly.dvd k μ hroot) hne
  _ = n := natDegree_X_pow_sub_C

/-- Theorem 13.14 (isomorphism over the algebraic closure): two short Weierstrass curves
$E_{A,B}$ and $E_{A',B'}$ over $k$ become isomorphic over $\overline{k}$ iff they have
the same $j$-invariant. The isomorphism is via $(A', B') = (\mu^4 A, \mu^6 B)$ for some
$\mu \in \overline{k}^\times$. -/
theorem isomorphic_over_algClosure_iff_jInvariant_eq (A B A' B' : k)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0) :
    (∃ μ : AlgebraicClosure k, μ ≠ 0 ∧
      algebraMap k _ A' = μ ^ 4 * algebraMap k _ A ∧
      algebraMap k _ B' = μ ^ 6 * algebraMap k _ B) ↔
    jInvariant A B = jInvariant A' B' := by
  have hinj := (algebraMap k (AlgebraicClosure k)).injective
  constructor
  ·
    rintro ⟨μ, hμ, hA', hB'⟩
    apply hinj
    rw [jInvariant_algebraMap, jInvariant_algebraMap, hA', hB',
        jInvariant_scaling _ _ μ hμ]
  ·
    intro hj
    by_cases hj0 : jInvariant A B = 0
    ·
      obtain ⟨hA0, hA'0⟩ := jInvariant_converse_eq_zero A B A' B' h2 h3 hΔ hΔ' hj hj0
      subst hA0; subst hA'0
      have hB : B ≠ 0 := by intro hB; apply hΔ; rw [hB]; ring
      have hB' : B' ≠ 0 := by intro hB'; apply hΔ'; rw [hB']; ring
      obtain ⟨μ, hμ6⟩ := IsAlgClosed.exists_pow_nat_eq
        (algebraMap k (AlgebraicClosure k) (B' / B)) (by norm_num : 0 < 6)
      refine ⟨μ, ?_, ?_, ?_⟩
      · intro hμ0; rw [hμ0, zero_pow (by norm_num : 6 ≠ 0)] at hμ6
        exact hB' (div_eq_zero_iff.mp ((map_eq_zero_iff _ hinj).mp hμ6.symm)
          |>.elim id (absurd · hB))
      · simp [map_zero]
      · rw [hμ6, map_div₀, div_mul_cancel₀]
        rwa [map_ne_zero_iff _ hinj]
    · by_cases hj1728 : jInvariant A B = 1728
      ·
        obtain ⟨hB0, hB'0⟩ := jInvariant_converse_eq_1728 A B A' B' h2 h3 hΔ hΔ' hj hj1728
        subst hB0; subst hB'0
        have hA : A ≠ 0 := by intro hA; apply hΔ; rw [hA]; ring
        have hA' : A' ≠ 0 := by intro hA'; apply hΔ'; rw [hA']; ring
        obtain ⟨μ, hμ4⟩ := IsAlgClosed.exists_pow_nat_eq
          (algebraMap k (AlgebraicClosure k) (A' / A)) (by norm_num : 0 < 4)
        refine ⟨μ, ?_, ?_, ?_⟩
        · intro hμ0; rw [hμ0, zero_pow (by norm_num : 4 ≠ 0)] at hμ4
          exact hA' (div_eq_zero_iff.mp ((map_eq_zero_iff _ hinj).mp hμ4.symm)
            |>.elim id (absurd · hA))
        · rw [hμ4, map_div₀, div_mul_cancel₀]
          rwa [map_ne_zero_iff _ hinj]
        · simp [map_zero]
      ·
        obtain ⟨u, hu, hA'u, hB'u⟩ := jInvariant_converse_ne_zero_ne_1728 A B A' B'
          h2 h3 hΔ hΔ' hj hj0 hj1728
        obtain ⟨μ, hμsq⟩ := IsAlgClosed.exists_pow_nat_eq
          (algebraMap k (AlgebraicClosure k) u) (by norm_num : 0 < 2)
        refine ⟨μ, ?_, ?_, ?_⟩
        · intro hμ0; rw [hμ0, zero_pow (by norm_num : 2 ≠ 0)] at hμsq
          exact hu ((map_eq_zero_iff _ hinj).mp hμsq.symm)
        · rw [hA'u, map_mul, map_pow,
              show μ ^ 4 = (μ ^ 2) ^ 2 from by ring, hμsq]
        · rw [hB'u, map_mul, map_pow,
              show μ ^ 6 = (μ ^ 2) ^ 3 from by ring, hμsq]
