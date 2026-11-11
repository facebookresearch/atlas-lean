/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Data.Nat.Squarefree
import Atlas.ArithmeticGeometry.code.HasseMinkowskiProof
import Atlas.ArithmeticGeometry.code.SquareClassApprox

open scoped Classical

noncomputable section

namespace QuadraticMap

/-- A quadratic form $Q$ on a module $M$ is **isotropic** if it has a nontrivial zero, i.e., there
exists $v \neq 0$ with $Q(v) = 0$. -/
def IsIsotropic {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (Q : QuadraticForm R M) : Prop :=
  ∃ v : M, v ≠ 0 ∧ Q v = 0


end QuadraticMap

/-- The diagonal quadratic form $\sum_i a_i x_i^2$ with rational coefficients
$a_0, \dots, a_{n-1} \in \mathbb{Q}$. -/
def diagQuadForm (n : ℕ) (a : Fin n → ℚ) : QuadraticForm ℚ (Fin n → ℚ) :=
  QuadraticMap.weightedSumSquares ℚ a

/-- The diagonal quadratic form $\sum_i a_i x_i^2$ with rational coefficients $a_i$, viewed as a
quadratic form over a $\mathbb{Q}$-algebra $F$. -/
def diagQuadFormOver (F : Type*) [Field F] [Algebra ℚ F]
    (n : ℕ) (a : Fin n → ℚ) : QuadraticForm F (Fin n → F) :=
  QuadraticMap.weightedSumSquares F (fun i => algebraMap ℚ F (a i))

/-- If a diagonal quadratic form is isotropic over $\mathbb{Q}$, then it remains isotropic over
any $\mathbb{Q}$-algebra $F$ (by extending scalars). -/
theorem diagQuadForm_isIsotropic_of_isIsotropic_over {n : ℕ} {a : Fin n → ℚ}
    {F : Type*} [Field F] [Algebra ℚ F]
    (h : (diagQuadForm n a).IsIsotropic) :
    (diagQuadFormOver F n a).IsIsotropic := by
  obtain ⟨v, hne, hQ⟩ := h
  refine ⟨fun i => algebraMap ℚ F (v i), ?_, ?_⟩
  ·
    intro heq
    apply hne
    funext i
    have hi : algebraMap ℚ F (v i) = 0 := congr_fun heq i
    exact (algebraMap ℚ F).injective (hi.trans (map_zero _).symm)
  ·
    simp only [diagQuadFormOver, diagQuadForm, QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul] at hQ ⊢
    rw [show (∑ i, algebraMap ℚ F (a i) * (algebraMap ℚ F (v i) * algebraMap ℚ F (v i))) =
      algebraMap ℚ F (∑ i, a i * (v i * v i)) from by push_cast; rfl]
    rw [hQ, map_zero]

/-- A binary diagonal form $a_0 x_0^2 + a_1 x_1^2$ is isotropic over a $\mathbb{Q}$-algebra $F$ iff
$a_0 = 0$, $a_1 = 0$, or $-a_0 a_1$ is a square in $F$. -/
theorem binary_form_isotropic_iff_neg_prod_sq
    {F : Type*} [Field F] [Algebra ℚ F] (a : Fin 2 → ℚ) :
    (diagQuadFormOver F 2 a).IsIsotropic ↔
    (a 0 = 0 ∨ a 1 = 0 ∨ IsSquare (algebraMap ℚ F (-(a 0) * a 1))) := by
  constructor
  ·
    intro ⟨v, hne, hQ⟩
    simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
      Fin.sum_univ_two] at hQ
    by_cases ha0 : a 0 = 0
    · exact Or.inl ha0
    · by_cases ha1 : a 1 = 0
      · exact Or.inr (Or.inl ha1)
      · right; right
        have ha0F : algebraMap ℚ F (a 0) ≠ 0 :=
          fun h => ha0 ((algebraMap ℚ F).injective (h.trans (map_zero _).symm))
        have ha1F : algebraMap ℚ F (a 1) ≠ 0 :=
          fun h => ha1 ((algebraMap ℚ F).injective (h.trans (map_zero _).symm))
        have hv0 : v 0 ≠ 0 := by
          intro h
          simp only [h, mul_zero, zero_add] at hQ
          have hv1 : v 1 = 0 := by
            rcases mul_eq_zero.mp hQ with h1 | h1
            · exact absurd h1 ha1F
            · rcases mul_eq_zero.mp h1 with h2 | h2 <;> exact h2
          apply hne; funext i; fin_cases i <;> assumption
        refine ⟨algebraMap ℚ F (a 1) * v 1 * (v 0)⁻¹, ?_⟩
        rw [map_mul, map_neg]
        have hv02 : v 0 * v 0 ≠ 0 := mul_ne_zero hv0 hv0
        have h1 : algebraMap ℚ F (a 0) * (v 0 * v 0) =
            -(algebraMap ℚ F (a 1) * (v 1 * v 1)) := by
          rwa [eq_neg_iff_add_eq_zero]
        have h2 : algebraMap ℚ F (a 0) =
            -(algebraMap ℚ F (a 1) * (v 1 * v 1)) * (v 0 * v 0)⁻¹ := by
          rw [← h1, mul_inv_cancel_right₀ hv02]
        rw [h2]; field_simp
  ·
    intro h
    rcases h with ha0 | ha1 | ⟨r, hr⟩
    ·
      refine ⟨![1, 0], ?_, ?_⟩
      · intro heq
        have : (![1, 0] : Fin 2 → F) 0 = 0 := congr_fun heq 0
        simp [Matrix.cons_val_zero] at this
      · simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        simp [ha0, map_zero]
    ·
      refine ⟨![0, 1], ?_, ?_⟩
      · intro heq
        have : (![0, 1] : Fin 2 → F) 1 = 0 := congr_fun heq 1
        simp [Matrix.cons_val_one] at this
      · simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        simp [ha1, map_zero]
    ·
      by_cases ha0 : a 0 = 0
      · refine ⟨![1, 0], ?_, ?_⟩
        · intro heq
          have : (![1, 0] : Fin 2 → F) 0 = 0 := congr_fun heq 0
          simp [Matrix.cons_val_zero] at this
        · simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
            Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          simp [ha0, map_zero]
      · by_cases ha1 : a 1 = 0
        · refine ⟨![0, 1], ?_, ?_⟩
          · intro heq
            have : (![0, 1] : Fin 2 → F) 1 = 0 := congr_fun heq 1
            simp [Matrix.cons_val_one] at this
          · simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
              Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
            simp [ha1, map_zero]
        ·
          have ha1F : algebraMap ℚ F (a 1) ≠ 0 :=
            fun h => ha1 ((algebraMap ℚ F).injective (h.trans (map_zero _).symm))
          refine ⟨![algebraMap ℚ F (a 1), r], ?_, ?_⟩
          · intro heq
            have : (![algebraMap ℚ F (a 1), r] : Fin 2 → F) 0 = 0 := congr_fun heq 0
            simp only [Matrix.cons_val_zero] at this
            exact ha1F this
          · simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
              Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
            rw [← hr, map_mul, map_neg]
            ring

/-- A positive natural number with even $p$-adic valuation at every prime $p$ is a perfect
square. -/
lemma nat_isSquare_of_even_padicVal (n : ℕ) (hn : 0 < n)
    (hev : ∀ (p : ℕ), Nat.Prime p → Even (padicValNat p n)) : IsSquare n := by
  obtain ⟨a, b, ha, hb, hab, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  suffices a = 1 by rw [this, mul_one] at hab; exact ⟨b, by rw [← hab]; ring⟩
  by_contra ha1
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpa_val : 1 ≤ padicValNat p a := one_le_padicValNat_of_dvd (by omega) hpa
  have hp2 : ¬(p * p ∣ a) := by
    intro h; exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p h))
  have hpa_le : padicValNat p a ≤ 1 := by
    by_contra h; push Not at h
    exact hp2 (by rw [← pow_two]
                  exact (padicValNat_dvd_iff_le_of_ne_one hp.ne_one (by omega)).mpr h)
  have hpa_eq : padicValNat p a = 1 := le_antisymm hpa_le hpa_val
  have hval_n : padicValNat p n = 2 * padicValNat p b + padicValNat p a := by
    rw [← hab, padicValNat.mul (by positivity) (by omega), padicValNat.pow 2 (by omega)]
  have hev_p := hev p hp; rw [hval_n, hpa_eq] at hev_p; simp [Even] at hev_p; omega

/-- If a nonzero rational $q$ is a square in $\mathbb{Q}_p$, then its $p$-adic valuation is
even. -/
lemma isSquare_padic_to_even_val (p : ℕ) [hp : Fact p.Prime] (q : ℚ) (hq : q ≠ 0)
    (h : IsSquare (algebraMap ℚ ℚ_[p] q)) : Even (padicValRat p q) := by
  obtain ⟨a, ha⟩ := h
  have hq' : (algebraMap ℚ ℚ_[p] q) ≠ 0 :=
    fun heq => hq ((algebraMap ℚ ℚ_[p]).injective (heq.trans (map_zero _).symm))
  have ha_ne : a ≠ 0 := fun heq => hq' (by rw [ha, heq, mul_zero])
  rw [show padicValRat p q = (algebraMap ℚ ℚ_[p] q).valuation from
    (Padic.valuation_ratCast q).symm, ha, Padic.valuation_mul ha_ne ha_ne]
  exact ⟨a.valuation, rfl⟩

/-- If a rational $q = m/n$ (in lowest terms) has even $p$-adic valuation, then both
$\mathrm{val}_p(m)$ and $\mathrm{val}_p(n)$ are even. -/
lemma even_padicValRat_split (q : ℚ) (p : ℕ) (hp : Nat.Prime p)
    (hev : Even (padicValRat p q)) :
    Even (padicValNat p q.num.natAbs) ∧ Even (padicValNat p q.den) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrw : padicValRat p q = (padicValNat p q.num.natAbs : ℤ) - (padicValNat p q.den : ℤ) := by
    simp [padicValRat, padicValInt]
  have hdisjoint : padicValNat p q.num.natAbs = 0 ∨ padicValNat p q.den = 0 := by
    by_contra h; push Not at h
    have ha : p ∣ q.num.natAbs := dvd_of_one_le_padicValNat (by omega)
    have hb : p ∣ q.den := dvd_of_one_le_padicValNat (by omega)
    exact absurd (Nat.le_of_dvd one_pos (q.reduced ▸ Nat.dvd_gcd ha hb)) (not_le.mpr hp.one_lt)
  rcases hdisjoint with h | h
  · exact ⟨by rw [h]; exact Even.zero,
      by rw [hrw, h, Nat.cast_zero, zero_sub] at hev; rw [even_neg] at hev;
         exact (Int.even_coe_nat _).mp hev⟩
  · exact ⟨by rw [hrw, h, Nat.cast_zero, sub_zero] at hev; exact (Int.even_coe_nat _).mp hev,
      by rw [h]; exact Even.zero⟩

/-- **Local-global for squares.** A rational number $q$ is a square in $\mathbb{Q}$ iff it is a
square in $\mathbb{R}$ and a square in $\mathbb{Q}_p$ for every prime $p$. -/
theorem rat_square_of_locally_square (q : ℚ)
    (hR : IsSquare (algebraMap ℚ ℝ q))
    (hp : ∀ (p : ℕ) [Fact p.Prime], IsSquare (algebraMap ℚ ℚ_[p] q)) :
    IsSquare q := by

  by_cases hq : q = 0
  · rw [hq]; exact ⟨0, by ring⟩

  have hnn : 0 ≤ q := by
    obtain ⟨r, hr⟩ := hR
    have : (0 : ℝ) ≤ algebraMap ℚ ℝ q := hr ▸ mul_self_nonneg r
    exact Rat.cast_nonneg.mp (by simpa using this)

  have hpos : 0 < q := lt_of_le_of_ne hnn (Ne.symm hq)

  have hev : ∀ (p : ℕ), Nat.Prime p → Even (padicValRat p q) := by
    intro p hpp; haveI : Fact p.Prime := ⟨hpp⟩
    exact isSquare_padic_to_even_val p q hq (hp p)

  rw [Rat.isSquare_iff]
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hpos
  constructor
  ·
    have hnatabs_pos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum_pos)
    have hev_num : ∀ (p : ℕ), Nat.Prime p → Even (padicValNat p q.num.natAbs) :=
      fun p hpp => (even_padicValRat_split q p hpp (hev p hpp)).1
    obtain ⟨k, hk⟩ := nat_isSquare_of_even_padicVal q.num.natAbs hnatabs_pos hev_num
    refine ⟨(k : ℤ), ?_⟩
    have h1 : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
    have h2 : (q.num.natAbs : ℤ) = (k : ℤ) * (k : ℤ) := by exact_mod_cast hk
    linarith
  ·
    exact nat_isSquare_of_even_padicVal q.den q.den_pos
      (fun p hpp => (even_padicValRat_split q p hpp (hev p hpp)).2)

/-- If $-a_0 a_1$ is a rational square, then the binary form $a_0 x_0^2 + a_1 x_1^2$ is isotropic
over $\mathbb{Q}$. -/
theorem binary_form_isotropic_of_neg_prod_sq (a : Fin 2 → ℚ)
    (h : IsSquare (-(a 0) * a 1)) :
    (diagQuadForm 2 a).IsIsotropic := by
  obtain ⟨r, hr⟩ := h
  by_cases ha1 : a 1 = 0
  ·
    refine ⟨![0, 1], ?_, ?_⟩
    · intro heq
      have : (![0, 1] : Fin 2 → ℚ) 1 = 0 := congr_fun heq 1
      simp [Matrix.cons_val_one] at this
    · simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
        Fin.sum_univ_two]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, ha1]
  · by_cases ha0 : a 0 = 0
    ·
      refine ⟨![1, 0], ?_, ?_⟩
      · intro heq
        have : (![1, 0] : Fin 2 → ℚ) 0 = 0 := congr_fun heq 0
        simp [Matrix.cons_val_zero] at this
      · simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_two]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, ha0]
    ·

      refine ⟨![a 1, r], ?_, ?_⟩
      · intro heq
        have : (![a 1, r] : Fin 2 → ℚ) 0 = 0 := congr_fun heq 0
        simp [Matrix.cons_val_zero] at this
        exact ha1 this
      · simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hr]
        ring

/-- **Hasse-Minkowski for binary forms ($n = 2$).** A binary diagonal form over $\mathbb{Q}$ is
isotropic iff it is isotropic over $\mathbb{R}$ and over every $\mathbb{Q}_p$. -/
lemma hasse_minkowski_case_n2 (a : Fin 2 → ℚ)
    (hR : (diagQuadFormOver ℝ 2 a).IsIsotropic)
    (hp : ∀ (p : ℕ) [Fact p.Prime], (diagQuadFormOver ℚ_[p] 2 a).IsIsotropic) :
    (diagQuadForm 2 a).IsIsotropic := by

  by_cases ha0 : a 0 = 0
  · refine ⟨fun i => if i = 0 then 1 else 0, ?_, ?_⟩
    · intro h; exact absurd (congr_fun h ⟨0, by omega⟩) (by simp)
    · simp [diagQuadForm, QuadraticMap.weightedSumSquares_apply, ha0]
  by_cases ha1 : a 1 = 0
  · refine ⟨fun i => if i = 1 then 1 else 0, ?_, ?_⟩
    · intro h; exact absurd (congr_fun h ⟨1, by omega⟩) (by simp)
    · simp [diagQuadForm, QuadraticMap.weightedSumSquares_apply, ha1]


  have hR_sq : IsSquare (algebraMap ℚ ℝ (-(a 0) * a 1)) := by
    rcases (binary_form_isotropic_iff_neg_prod_sq (F := ℝ) a).mp hR with h | h | h
    · exact absurd h ha0
    · exact absurd h ha1
    · exact h

  have hp_sq : ∀ (p : ℕ) [Fact p.Prime],
      IsSquare (algebraMap ℚ ℚ_[p] (-(a 0) * a 1)) := by
    intro p _
    rcases (binary_form_isotropic_iff_neg_prod_sq (F := ℚ_[p]) a).mp (hp p) with h | h | h
    · exact absurd h ha0
    · exact absurd h ha1
    · exact h

  have hQ_sq := rat_square_of_locally_square _ hR_sq hp_sq

  exact binary_form_isotropic_of_neg_prod_sq a hQ_sq

/-- For a ternary diagonal form with all coefficients nonzero, isotropy over $F$ is equivalent
to the `TernaryForm.RepresentsZero` predicate on the corresponding units of $F$. -/
lemma diagQuadFormOver_isIsotropic_iff_ternary_represents_zero
    {F : Type*} [Field F] [Algebra ℚ F]
    (a : Fin 3 → ℚ) (hne : ∀ i, a i ≠ 0) :
    (diagQuadFormOver F 3 a).IsIsotropic ↔
    TernaryForm.RepresentsZero F
      (Units.mk0 (algebraMap ℚ F (a 0))
        (by intro h; exact hne 0 ((algebraMap ℚ F).injective (h.trans (map_zero _).symm))))
      (Units.mk0 (algebraMap ℚ F (a 1))
        (by intro h; exact hne 1 ((algebraMap ℚ F).injective (h.trans (map_zero _).symm))))
      (Units.mk0 (algebraMap ℚ F (a 2))
        (by intro h; exact hne 2 ((algebraMap ℚ F).injective (h.trans (map_zero _).symm)))) := by
  simp only [QuadraticMap.IsIsotropic, diagQuadFormOver, QuadraticMap.weightedSumSquares_apply,
    smul_eq_mul, Fin.sum_univ_three, TernaryForm.RepresentsZero, Units.val_mk0]
  constructor
  · rintro ⟨v, hne_v, hsum⟩
    refine ⟨v 0, v 1, v 2, ?_, ?_⟩
    · by_contra h
      push Not at h
      obtain ⟨h0, h1, h2⟩ := h
      apply hne_v; funext i; fin_cases i <;> assumption
    · convert hsum using 1; ring
  · rintro ⟨x, y, z, hne_xyz, hsum⟩
    let v : Fin 3 → F := fun i => match i with | 0 => x | 1 => y | 2 => z
    refine ⟨v, ?_, ?_⟩
    · intro heq
      have hx : x = 0 := congr_fun heq 0
      have hy : y = 0 := congr_fun heq 1
      have hz : z = 0 := congr_fun heq 2
      rcases hne_xyz with h | h | h <;> contradiction
    · show (algebraMap ℚ F) (a 0) * (v 0 * v 0) + (algebraMap ℚ F) (a 1) * (v 1 * v 1) +
        (algebraMap ℚ F) (a 2) * (v 2 * v 2) = 0
      show (algebraMap ℚ F) (a 0) * (x * x) + (algebraMap ℚ F) (a 1) * (y * y) +
        (algebraMap ℚ F) (a 2) * (z * z) = 0
      have h1 : ∀ (w : F), w * w = w ^ 2 := fun w => (sq w).symm
      rw [h1, h1, h1]
      exact hsum

/-- Specialization of `diagQuadFormOver_isIsotropic_iff_ternary_represents_zero` to
$F = \mathbb{Q}$. -/
lemma diagQuadForm_isIsotropic_iff_ternary_represents_zero_rat
    (a : Fin 3 → ℚ) (hne : ∀ i, a i ≠ 0) :
    (diagQuadForm 3 a).IsIsotropic ↔
    TernaryForm.RepresentsZero ℚ
      (Units.mk0 (a 0) (hne 0))
      (Units.mk0 (a 1) (hne 1))
      (Units.mk0 (a 2) (hne 2)) := by
  simp only [QuadraticMap.IsIsotropic, diagQuadForm, QuadraticMap.weightedSumSquares_apply,
    smul_eq_mul, Fin.sum_univ_three, TernaryForm.RepresentsZero, Units.val_mk0]
  constructor
  · rintro ⟨v, hne_v, hsum⟩
    refine ⟨v 0, v 1, v 2, ?_, ?_⟩
    · by_contra h
      push Not at h
      obtain ⟨h0, h1, h2⟩ := h
      apply hne_v; funext i; fin_cases i <;> assumption
    · convert hsum using 1; ring
  · rintro ⟨x, y, z, hne_xyz, hsum⟩
    let v : Fin 3 → ℚ := fun i => match i with | 0 => x | 1 => y | 2 => z
    refine ⟨v, ?_, ?_⟩
    · intro heq
      have hx : x = 0 := congr_fun heq 0
      have hy : y = 0 := congr_fun heq 1
      have hz : z = 0 := congr_fun heq 2
      rcases hne_xyz with h | h | h <;> contradiction
    · show a 0 * (v 0 * v 0) + a 1 * (v 1 * v 1) + a 2 * (v 2 * v 2) = 0
      show a 0 * (x * x) + a 1 * (y * y) + a 2 * (z * z) = 0
      have h1 : ∀ (w : ℚ), w * w = w ^ 2 := fun w => (sq w).symm
      rw [h1, h1, h1]
      exact hsum






/-- Expansion of the $3$-variable weighted sum of squares over $\mathbb{Q}_p$. -/
lemma wss_vec3_padic {p : ℕ} [Fact p.Prime] (w₀ w₁ w₂ x₀ x₁ x₂ : ℚ_[p]) :
    QuadraticMap.weightedSumSquares ℚ_[p] ![w₀, w₁, w₂] ![x₀, x₁, x₂] =
    w₀ * (x₀ * x₀) + w₁ * (x₁ * x₁) + w₂ * (x₂ * x₂) := by
  simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul]

/-- The $\mathbb{Q}_p$-triple $[a, b, c]$ is nonzero if its first component is. -/
lemma vec3_ne_zero_of_idx0_padic {p : ℕ} [Fact p.Prime] (a b c : ℚ_[p]) (ha : a ≠ 0) :
    ![a, b, c] ≠ 0 := by
  intro h; exact ha (by have := congr_fun h 0; simpa using this)

/-- The $\mathbb{Q}_p$-triple $[a, b, c]$ is nonzero if its second component is. -/
lemma vec3_ne_zero_of_idx1_padic {p : ℕ} [Fact p.Prime] (a b c : ℚ_[p]) (hb : b ≠ 0) :
    ![a, b, c] ≠ 0 := by
  intro h; exact hb (by have := congr_fun h 1; simpa using this)

/-- The $\mathbb{Q}_p$-triple $[a, b, c]$ is nonzero if its third component is. -/
lemma vec3_ne_zero_of_idx2_padic {p : ℕ} [Fact p.Prime] (a b c : ℚ_[p]) (hc : c ≠ 0) :
    ![a, b, c] ≠ 0 := by
  intro h; exact hc (by have := congr_fun h 2; simpa using this)






/-- Assembly: from rational isotropy of two ternary subforms with the splitting value $t$,
construct a rational isotropic vector for the original quaternary form. -/
theorem ternary_pair_to_quaternary
    (a : Fin 4 → ℚ) (t : ℚ) (ht : t ≠ 0)
    (h₁ : (diagQuadForm 3 ![a 0, a 1, -t]).IsIsotropic)
    (h₂ : (diagQuadForm 3 ![a 2, a 3, t]).IsIsotropic) :
    (diagQuadForm 4 a).IsIsotropic := by
  obtain ⟨v₁, hv₁ne, hv₁⟩ := h₁
  obtain ⟨v₂, hv₂ne, hv₂⟩ := h₂
  simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
    Fin.sum_univ_three] at hv₁ hv₂
  change a 0 * (v₁ 0 * v₁ 0) + a 1 * (v₁ 1 * v₁ 1) + (-t) * (v₁ 2 * v₁ 2) = 0 at hv₁
  change a 2 * (v₂ 0 * v₂ 0) + a 3 * (v₂ 1 * v₂ 1) + t * (v₂ 2 * v₂ 2) = 0 at hv₂
  by_cases hc₁ : v₁ 2 = 0
  ·

    refine ⟨![v₁ 0, v₁ 1, 0, 0], ?_, ?_⟩
    · intro h; apply hv₁ne; funext i; fin_cases i
      · exact congr_fun h 0
      · exact congr_fun h 1
      · exact hc₁
    · simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
        Fin.sum_univ_four]
      show a 0 * (v₁ 0 * v₁ 0) + a 1 * (v₁ 1 * v₁ 1) + a 2 * (0 * 0) + a 3 * (0 * 0) = 0
      simp only [hc₁, mul_zero, add_zero] at hv₁; linarith
  · by_cases hc₂ : v₂ 2 = 0
    ·

      refine ⟨![0, 0, v₂ 0, v₂ 1], ?_, ?_⟩
      · intro h; apply hv₂ne; funext i; fin_cases i
        · exact congr_fun h 2
        · exact congr_fun h 3
        · exact hc₂
      · simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_four]
        show a 0 * (0 * 0) + a 1 * (0 * 0) + a 2 * (v₂ 0 * v₂ 0) + a 3 * (v₂ 1 * v₂ 1) = 0
        simp only [hc₂, mul_zero, add_zero] at hv₂; linarith
    ·


      refine ⟨![v₁ 0 * v₂ 2, v₁ 1 * v₂ 2, v₂ 0 * v₁ 2, v₂ 1 * v₁ 2], ?_, ?_⟩
      ·

        intro h
        have hv10 : v₁ 0 = 0 := (mul_eq_zero.mp (congr_fun h 0)).resolve_right hc₂
        have hv11 : v₁ 1 = 0 := (mul_eq_zero.mp (congr_fun h 1)).resolve_right hc₂
        have : (-t) * (v₁ 2 * v₁ 2) = 0 := by rw [hv10, hv11] at hv₁; linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd (neg_eq_zero.mp h') ht
        · exact absurd (mul_self_eq_zero.mp h') hc₁
      ·
        simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
          Fin.sum_univ_four]
        show a 0 * ((v₁ 0 * v₂ 2) * (v₁ 0 * v₂ 2)) +
          a 1 * ((v₁ 1 * v₂ 2) * (v₁ 1 * v₂ 2)) +
          a 2 * ((v₂ 0 * v₁ 2) * (v₂ 0 * v₁ 2)) +
          a 3 * ((v₂ 1 * v₁ 2) * (v₂ 1 * v₁ 2)) = 0
        nlinarith [mul_comm (v₂ 2 * v₂ 2) (a 0 * (v₁ 0 * v₁ 0)),
                   mul_comm (v₂ 2 * v₂ 2) (a 1 * (v₁ 1 * v₁ 1)),
                   mul_comm (v₁ 2 * v₁ 2) (a 2 * (v₂ 0 * v₂ 0)),
                   mul_comm (v₁ 2 * v₁ 2) (a 3 * (v₂ 1 * v₂ 1))]


/-- Given coefficients $a_0, \dots, a_{m+4}$ and a value $t$, form the "replaced" sequence
$(t, a_2, a_3, \dots, a_{m+4})$ of length $m + 4$ (where the first two coefficients $a_0, a_1$
have been merged into a single value $t$). -/
def replacedForm {m : ℕ} (a : Fin (m + 5) → ℚ) (t : ℚ) : Fin (m + 4) → ℚ :=
  fun i => if i.val = 0 then t else a ⟨i.val + 1, by omega⟩

/-- The "subform" coefficients obtained by dropping the first two entries
$(a_2, a_3, \dots, a_{m+4})$. -/
def subFormCoeffs {m : ℕ} (a : Fin (m + 5) → ℚ) : Fin (m + 3) → ℚ :=
  fun j => a ⟨j.val + 2, by omega⟩

/-- If the subform $\sum_{i \ge 2} a_i x_i^2$ is isotropic over $F$, then for any $t$, the
replaced form is also isotropic over $F$ (set $x_0 = 0$). -/
lemma subform_isotropic_implies_replaced_isotropic
    (F : Type*) [Field F] [Algebra ℚ F] {m : ℕ}
    (a : Fin (m + 5) → ℚ) (t : ℚ)
    (hsub : (diagQuadFormOver F (m + 3) (subFormCoeffs a)).IsIsotropic) :
    (diagQuadFormOver F (m + 4) (replacedForm a t)).IsIsotropic := by
  obtain ⟨v, hv, hQ⟩ := hsub
  simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
    QuadraticMap.IsIsotropic] at hQ ⊢
  refine ⟨Fin.cons 0 v, ?_, ?_⟩
  · intro h; apply hv; funext j; have := congr_fun h j.succ
    simp [Fin.cons_succ] at this; exact this
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, mul_zero, zero_add, Fin.cons_succ]
    exact hQ
/-- **Corollary 11.2 (cofinite local isotropy of subforms).** For the subform with $m + 3 \ge 3$
variables, the form is isotropic over $\mathbb{Q}_p$ for all but finitely many primes $p$. -/
lemma corollary_11_2_subform_isotropy {m : ℕ} (a : Fin (m + 5) → ℚ) :
    ∃ (S : Finset ℕ), ∀ (p : ℕ) [Fact p.Prime],
      p ∉ S → (diagQuadFormOver ℚ_[p] (m + 3) (subFormCoeffs a)).IsIsotropic := by

  by_cases hall : ∀ i, subFormCoeffs a i ≠ 0
  ·
    obtain ⟨S, hS⟩ := diagonal_form_represents_zero_locally_cofinitely
      (by omega : 2 < m + 3) (subFormCoeffs a) hall
    exact ⟨S, fun p inst hpS => by
      obtain ⟨x, hne, hsum⟩ := hS p (Fact.out) hpS
      refine ⟨x, ?_, ?_⟩
      · intro h0; obtain ⟨i, hi⟩ := hne; exact hi (congr_fun h0 i)
      · simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
        simp_rw [← sq]
        exact hsum⟩
  ·
    simp only [not_forall, Classical.not_not] at hall
    obtain ⟨j, hj⟩ := hall
    exact ⟨∅, fun p _ _ => by
      refine ⟨Function.update 0 j 1, ?_, ?_⟩
      · intro h
        have : (Function.update (0 : Fin (m + 3) → ℚ_[p]) j 1) j =
            (0 : Fin (m + 3) → ℚ_[p]) j := by rw [h]
        rw [Function.update_self] at this; simp at this
      · simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
        apply Finset.sum_eq_zero; intro i _
        by_cases hi : i = j
        · subst hi; simp [Function.update_self, hj]
        · have := Function.update_of_ne hi (1 : ℚ_[p]) (0 : Fin (m + 3) → ℚ_[p])
          simp [this]⟩

/-- Updating a nonzero vector $v$ at index $k$ by multiplying that coordinate by a nonzero
scalar $c$ yields a nonzero vector. -/
lemma update_mul_ne_zero_of_ne_zero {n : ℕ} {F : Type*} [Field F]
    {v : Fin n → F} (hv : v ≠ 0) {k : Fin n} {c : F} (hc : c ≠ 0) :
    Function.update v k (v k * c) ≠ 0 := by
  intro h; apply hv; funext i; simp only [Pi.zero_apply]
  by_cases hi : i = k
  · have h1 := congr_fun h i; simp only [Pi.zero_apply] at h1
    rw [hi, Function.update_self] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [hi]; exact h2
    · exact absurd h2 hc
  · have h1 := congr_fun h i
    simp only [Pi.zero_apply, Function.update_of_ne hi] at h1; exact h1

/-- Scaling a coefficient $b_k$ by a nonzero square $u^2$ does not change whether the diagonal
quadratic form is isotropic. -/
lemma diagQuadFormOver_isIsotropic_of_scale_coeff
    (F : Type*) [Field F] [Algebra ℚ F] {n : ℕ}
    (b : Fin n → ℚ) (k : Fin n) (u : ℚ) (hu : u ≠ 0) :
    (diagQuadFormOver F n (Function.update b k (b k * u ^ 2))).IsIsotropic ↔
    (diagQuadFormOver F n b).IsIsotropic := by
  have hu_F : algebraMap ℚ F u ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hu_inv_F : (algebraMap ℚ F u)⁻¹ ≠ 0 := inv_ne_zero hu_F
  constructor
  ·
    rintro ⟨v, hv, hQ⟩
    refine ⟨Function.update v k (v k * algebraMap ℚ F u),
            update_mul_ne_zero_of_ne_zero hv hu_F, ?_⟩
    simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at hQ ⊢
    rw [Finset.sum_congr rfl (fun i _ => ?_)]
    · exact hQ
    · by_cases hi : i = k
      · subst hi; simp only [Function.update_self, map_mul, map_pow]; ring
      · simp only [Function.update_of_ne hi]
  ·
    rintro ⟨v, hv, hQ⟩
    refine ⟨Function.update v k (v k * (algebraMap ℚ F u)⁻¹),
            update_mul_ne_zero_of_ne_zero hv hu_inv_F, ?_⟩
    simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at hQ ⊢
    rw [Finset.sum_congr rfl (fun i _ => ?_)]
    · exact hQ
    · by_cases hi : i = k
      · subst hi; simp only [Function.update_self, map_mul, map_pow]; field_simp
      · simp only [Function.update_of_ne hi]

/-- Specialization of `diagQuadFormOver_isIsotropic_of_scale_coeff` to scaling the first
coefficient. -/
lemma diagQuadFormOver_isIsotropic_of_scale_first_coeff
    (F : Type*) [Field F] [Algebra ℚ F] {n : ℕ}
    (b : Fin (n + 1) → ℚ) (u : ℚ) (hu : u ≠ 0) :
    (diagQuadFormOver F (n + 1) (Function.update b 0 (b 0 * u ^ 2))).IsIsotropic ↔
    (diagQuadFormOver F (n + 1) b).IsIsotropic :=
  diagQuadFormOver_isIsotropic_of_scale_coeff F b 0 u hu

/-- The isotropy of a replaced form depends only on the square class of $t$ over $\mathbb{Q}$:
if $c = t \cdot u^2$ for some nonzero rational $u$, then `replacedForm a c` is isotropic iff
`replacedForm a t` is. -/
lemma replaced_form_isotropic_same_rat_square_class
    (F : Type*) [Field F] [Algebra ℚ F] {m : ℕ}
    (a : Fin (m + 5) → ℚ) (t c : ℚ)
    (hiso_t : (diagQuadFormOver F (m + 4) (replacedForm a t)).IsIsotropic)
    (hsq : ∃ u : ℚ, u ≠ 0 ∧ c = t * u ^ 2) :
    (diagQuadFormOver F (m + 4) (replacedForm a c)).IsIsotropic := by
  obtain ⟨u, hu, hcu⟩ := hsq


  have h0 : replacedForm a t 0 = t := by simp [replacedForm]
  have hc_eq : replacedForm a c = Function.update (replacedForm a t) 0 (replacedForm a t 0 * u ^ 2) := by
    funext i
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      rw [hi0, Function.update_self, h0]
      simp [replacedForm, hcu]
    · rw [Function.update_of_ne (Fin.ne_of_val_ne hi)]
      simp [replacedForm, hi]
  rw [hc_eq]
  exact (diagQuadFormOver_isIsotropic_of_scale_first_coeff F (replacedForm a t) u hu).mpr hiso_t




/-- The $p$-adic isotropy of a replaced form depends only on the $p$-adic square class of $t$:
if $c$ and $t$ lie in the same square class over $\mathbb{Q}_p$, then `replacedForm a c` is
isotropic over $\mathbb{Q}_p$ iff `replacedForm a t` is. -/
lemma replaced_form_isotropic_of_padic_sq_class {m : ℕ} {p : ℕ} [Fact p.Prime]
    (a : Fin (m + 5) → ℚ) (c : ℚ) (t : ℚ) (ht : t ≠ 0)
    (hiso_t : (diagQuadFormOver ℚ_[p] (m + 4) (replacedForm a t)).IsIsotropic)
    (hsq : PadicSameSquareClass p (↑c) (↑t)) :
    (diagQuadFormOver ℚ_[p] (m + 4) (replacedForm a c)).IsIsotropic := by


  obtain ⟨u, hu, hcu⟩ := hsq
  obtain ⟨v, hv, hQ⟩ := hiso_t
  simp only [diagQuadFormOver, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
    QuadraticMap.IsIsotropic] at hQ ⊢

  refine ⟨Function.update v 0 (v 0 * u⁻¹), ?_, ?_⟩
  ·
    intro heq
    apply hv; funext i; simp only [Pi.zero_apply]
    by_cases hi : i = 0
    · have h0 := congr_fun heq i; simp only [Pi.zero_apply] at h0
      rw [hi, Function.update_self] at h0
      have : v 0 = 0 := by
        by_contra hv0
        exact absurd h0 (mul_ne_zero hv0 (inv_ne_zero hu))
      rw [hi]; exact this
    · have h0 := congr_fun heq i; simp only [Pi.zero_apply] at h0
      rw [Function.update_of_ne hi] at h0; exact h0
  ·
    rw [Fin.sum_univ_succ] at hQ ⊢
    simp only [Function.update_self]
    have hrepl_t : replacedForm a t 0 = t := by simp [replacedForm]
    have htail : ∀ (j : Fin (m + 3)),
        replacedForm a c j.succ = replacedForm a t j.succ := by
      intro j; simp [replacedForm, Fin.val_succ, show j.val + 1 ≠ 0 from by omega]

    have htail_sum : ∑ i : Fin (m + 3),
        algebraMap ℚ ℚ_[p] (replacedForm a c i.succ) *
        (Function.update v 0 (v 0 * u⁻¹) i.succ *
         Function.update v 0 (v 0 * u⁻¹) i.succ) =
        ∑ i : Fin (m + 3),
        algebraMap ℚ ℚ_[p] (replacedForm a t i.succ) * (v i.succ * v i.succ) := by
      congr 1
    rw [htail_sum]


    have hhead : (algebraMap ℚ ℚ_[p]) (replacedForm a c 0) * (v 0 * u⁻¹ * (v 0 * u⁻¹)) =
        (algebraMap ℚ ℚ_[p]) (replacedForm a t 0) * (v 0 * v 0) := by
      simp only [replacedForm, show (0 : Fin (m + 4)).val = 0 from rfl, if_true]


      have : (algebraMap ℚ ℚ_[p]) c = (↑t : ℚ_[p]) * u ^ 2 := hcu
      rw [show (algebraMap ℚ ℚ_[p]) c = (algebraMap ℚ ℚ_[p]) t * u ^ 2 from this]
      field_simp
    rw [hhead]
    exact hQ








/-- **Assembly step.** From an isotropic vector for the replaced $(m+4)$-variable form
`replacedForm a (a 0 * x^2 + a 1 * y^2)` over $\mathbb{Q}$, and rationals $x, y$ with the head
expression nonzero, construct an isotropic vector for the original $(m+5)$-variable form
`diagQuadForm (m+5) a` over $\mathbb{Q}$ by splitting the first coordinate into $(x v_0, y v_0)$. -/
theorem assembly_large_form {m : ℕ} (a : Fin (m + 5) → ℚ) (x y : ℚ)
    (ht : a 0 * x ^ 2 + a 1 * y ^ 2 ≠ 0)
    (hiso : (diagQuadForm (m + 4)
      (replacedForm a (a 0 * x ^ 2 + a 1 * y ^ 2))).IsIsotropic) :
    (diagQuadForm (m + 5) a).IsIsotropic := by
  obtain ⟨v, hv_ne, hv_eval⟩ := hiso

  refine ⟨fun i => if i.val = 0 then x * v 0
                    else if i.val = 1 then y * v 0
                    else v ⟨i.val - 1, by omega⟩, ?_, ?_⟩
  ·
    by_cases h_tail : ∃ j : Fin (m + 3), v j.succ ≠ 0
    ·
      obtain ⟨j, hj⟩ := h_tail
      intro heq; apply hj
      have h := congr_fun heq ⟨j.val + 2, by omega⟩
      simp only [Pi.zero_apply] at h
      rw [if_neg (by omega : ¬ (j.val + 2 = 0)),
          if_neg (by omega : ¬ (j.val + 2 = 1))] at h
      rwa [show (⟨j.val + 2 - 1, by omega⟩ : Fin (m + 4)) = j.succ from
        Fin.ext (by simp [Fin.val_succ])] at h
    ·
      simp only [not_exists, not_not] at h_tail
      have hv0 : v 0 ≠ 0 := by
        intro hv0; apply hv_ne; ext i; simp only [Pi.zero_apply]
        match i with
        | ⟨0, _⟩ => exact hv0
        | ⟨n + 1, _⟩ => convert h_tail ⟨n, by omega⟩ using 1


      have hxy : x ≠ 0 ∨ y ≠ 0 := by
        by_contra h
        push Not at h

        exact ht (by simp [h.1, h.2])
      cases hxy with
      | inl hx =>

        intro heq
        have h := congr_fun heq ⟨0, by omega⟩
        simp only [Pi.zero_apply] at h; norm_num at h
        exact h.elim hx hv0
      | inr hy =>

        intro heq
        have h := congr_fun heq ⟨1, by omega⟩
        simp only [Pi.zero_apply] at h; norm_num at h
        exact h.elim hy hv0

  ·
    simp only [diagQuadForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at hv_eval ⊢
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, ite_true, Fin.val_succ]; norm_num
    rw [Fin.sum_univ_succ] at hv_eval
    simp only [replacedForm, Fin.val_zero, ite_true, Fin.val_succ, Nat.succ_ne_zero,
               ite_false] at hv_eval
    ring_nf; ring_nf at hv_eval
    have sum_eq : ∑ i : Fin (m + 3), a i.succ.succ * v ⟨1 + ↑i, by omega⟩ ^ 2 =
                  ∑ i : Fin (m + 3), a ⟨2 + ↑i, by omega⟩ * v i.succ ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; congr 1
      · congr 1; ext; simp [Fin.val_succ]; omega
      · congr 1; congr 1; ext; simp [Fin.val_succ]; omega
    linarith [sum_eq]




end
