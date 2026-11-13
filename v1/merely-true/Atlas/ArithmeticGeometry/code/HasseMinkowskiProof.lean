/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HilbertSymbol
import Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions
import Atlas.ArithmeticGeometry.code.Theorem11_1
import Atlas.ArithmeticGeometry.code.HilbertProductFormula
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.QuadraticForm.Radical

open scoped Classical




/-- Solvability of the Hilbert equation $b x^2 + c y^2 = 1$ over $\mathbb{Q}$ implies its
solvability over $\mathbb{Q}_p$, obtained by base change of the rational solution. -/
lemma rat_isSolvable_implies_padic (p : ℕ) [Fact (Nat.Prime p)] (b c : ℚˣ)
    (h : HilbertSymbol.IsSolvable ℚ b c) :
    HilbertSymbol.IsSolvable ℚ_[p] (ratToQpUnits p b) (ratToQpUnits p c) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨(x : ℚ_[p]), (y : ℚ_[p]), ?_⟩
  have hb_val : (ratToQpUnits p b : ℚ_[p]) = ((b : ℚ) : ℚ_[p]) := ratToQpUnits_val p b
  have hc_val : (ratToQpUnits p c : ℚ_[p]) = ((c : ℚ) : ℚ_[p]) := ratToQpUnits_val p c
  rw [hb_val, hc_val]
  exact_mod_cast hxy

/-- If the rational Hilbert symbol $(b, c)_\mathbb{Q} = 1$, then the $p$-adic Hilbert symbol
$(b, c)_p = 1$ for every prime $p$. -/
lemma rat_hilbert_one_implies_local (p : ℕ) [Fact (Nat.Prime p)] (b c : ℚˣ)
    (h : hilbertSymbol ℚ b c = 1) :
    hilbertAtPrime p b c = 1 := by
  rw [hilbertSymbol.eq_one_iff] at h
  simp only [hilbertAtPrime, padicHilbertSymbol, hilbertSymbol.eq_one_iff]
  exact rat_isSolvable_implies_padic p b c h


namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- For any field $F$ with $2 \neq 0$ and any unit $x$, the Hilbert symbol $(x, -x) = 1$,
witnessed by the identity solution $x \cdot ((x^{-1}+1)/2)^2 + (-x) \cdot ((x^{-1}-1)/2)^2 = 1$. -/
theorem self_neg_self [NeZero (2 : F)] (x : Fˣ) : hilbertSymbol F x (-x) = 1 := by
  rw [eq_one_iff]
  refine ⟨((x : F)⁻¹ + 1) / 2, ((x : F)⁻¹ - 1) / 2, ?_⟩
  have hx : (x : F) ≠ 0 := x.ne_zero
  simp only [Units.val_neg]
  field_simp
  ring


/-- The Hilbert equation $(a c^2) x^2 + b y^2 = 1$ is solvable iff $a x^2 + b y^2 = 1$ is,
since multiplying $a$ by a square does not change the square class. -/
lemma IsSolvable_sq_mul_left (a b c : Fˣ) :
    HilbertSymbol.IsSolvable F (a * c * c) b ↔ HilbertSymbol.IsSolvable F a b := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨(c : F) * x, y, by
      simp only [Units.val_mul] at h ⊢
      have : ↑a * (↑c * x) ^ 2 = ↑a * ↑c * ↑c * x ^ 2 := by ring
      rw [this]; exact h⟩
  · rintro ⟨x, y, h⟩
    refine ⟨(↑c)⁻¹ * x, y, ?_⟩
    simp only [Units.val_mul] at h ⊢
    have hc : (c : F) ≠ 0 := c.ne_zero
    have key : ↑a * ↑c * ↑c * ((↑c : F)⁻¹ * x) ^ 2 = ↑a * x ^ 2 := by field_simp
    rw [key]; exact h

/-- The Hilbert equation $a x^2 + (b c^2) y^2 = 1$ is solvable iff $a x^2 + b y^2 = 1$ is,
by symmetry from `IsSolvable_sq_mul_left`. -/
lemma IsSolvable_sq_mul_right (a b c : Fˣ) :
    HilbertSymbol.IsSolvable F a (b * c * c) ↔ HilbertSymbol.IsSolvable F a b := by
  have comm : ∀ u v : Fˣ, HilbertSymbol.IsSolvable F u v ↔ HilbertSymbol.IsSolvable F v u := by
    intro u v
    constructor
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
  rw [comm, IsSolvable_sq_mul_left, comm]

/-- The Hilbert symbol is invariant under scaling the first argument by a square:
$(a c^2, b) = (a, b)$. -/
lemma sq_mul_left (a c b : Fˣ) :
    hilbertSymbol F (a * c * c) b = hilbertSymbol F a b := by
  unfold hilbertSymbol
  simp only [IsSolvable_sq_mul_left]

/-- The Hilbert symbol is invariant under scaling the second argument by a square:
$(a, b c^2) = (a, b)$. -/
lemma sq_mul_right (a b c : Fˣ) :
    hilbertSymbol F a (b * c * c) = hilbertSymbol F a b := by
  unfold hilbertSymbol
  simp only [IsSolvable_sq_mul_right]

/-- The "division" identity for the Hilbert symbol over a field with bilinear Hilbert symbol:
$(a/t, b/t) = (a, b) \cdot (t, -ab)$. A key step in relating binary form representation to the
Hilbert symbol. -/
theorem div_div_eq_mul [HilbertBilinearField F] (a b t : Fˣ) :
    hilbertSymbol F (a * t⁻¹) (b * t⁻¹) =
    hilbertSymbol F a b * hilbertSymbol F t (-(a * b)) := by

  have sq_inv : hilbertSymbol F (a * t⁻¹) (b * t⁻¹) = hilbertSymbol F (a * t) (b * t) := by
    have h1 : a * t = a * t⁻¹ * t * t := by group
    have h2 : b * t = b * t⁻¹ * t * t := by group
    rw [h1, h2, sq_mul_left, sq_mul_right]

  rw [sq_inv, mul_left, mul_right a b t, mul_right t b t, symm a t]


  have rearr : hilbertSymbol F a b * hilbertSymbol F t a *
      (hilbertSymbol F t b * hilbertSymbol F t t) =
      hilbertSymbol F a b * (hilbertSymbol F t a * hilbertSymbol F t b *
      hilbertSymbol F t t) := by ring
  rw [rearr, ← mul_right t a b, ← mul_right t (a * b) t]

  congr 1


  have absorb : hilbertSymbol F t (a * b * t) = hilbertSymbol F t (a * b * t * (-t)) := by
    have h1 := mul_right t (a * b * t) (-t)
    rw [h1, self_neg_self, mul_one]
  have unit_eq : a * b * t * (-t) = -(a * b) * t * t := by
    ext; simp only [Units.val_mul, Units.val_neg]; ring
  rw [absorb, unit_eq, sq_mul_right]

/-- For integers $x, y \in \{1, -1\}$, the product $x y = 1$ iff $x = y$. -/
lemma prod_pm_one_eq_one_iff {x y : ℤ}
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ↔ x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

end hilbertSymbol

/-- The ternary form $a x^2 + b y^2 + c z^2$ with unit coefficients $a, b, c \in F^\times$
**represents zero** if there is a nontrivial solution $(x, y, z) \neq (0, 0, 0)$ with
$a x^2 + b y^2 + c z^2 = 0$. -/
def TernaryForm.RepresentsZero (F : Type*) [Field F] (a b c : Fˣ) : Prop :=
  ∃ x y z : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    (a : F) * x ^ 2 + (b : F) * y ^ 2 + (c : F) * z ^ 2 = 0

/-- The binary form $a x^2 + b y^2$ with unit coefficients $a, b \in F^\times$ **represents**
$t \in F$ if there exist $x, y \in F$ such that $a x^2 + b y^2 = t$. -/
def BinaryForm.Represents (F : Type*) [Field F] (a b : Fˣ) (t : F) : Prop :=
  ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = t

/-- **Representation criterion via Hilbert symbols.** Over a field with bilinear Hilbert symbol,
the binary form $a x^2 + b y^2$ represents $t \in F^\times$ if and only if
$(a, b) = (t, -ab)$ in $\{1, -1\}$. -/
theorem binary_form_represents_iff_hilbert {F : Type*} [Field F] [HilbertBilinearField F]
    (a b t : Fˣ) :
    BinaryForm.Represents F a b (t : F) ↔
    hilbertSymbol F a b = hilbertSymbol F t (-(a * b)) := by

  have represents_iff_solvable :
      BinaryForm.Represents F a b (t : F) ↔
      HilbertSymbol.IsSolvable F (a * t⁻¹) (b * t⁻¹) := by
    constructor
    · rintro ⟨x, y, h⟩
      refine ⟨x, y, ?_⟩
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      have ht : (t : F) ≠ 0 := t.ne_zero
      field_simp
      exact h
    · rintro ⟨x, y, h⟩
      refine ⟨x, y, ?_⟩
      simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h
      have ht : (t : F) ≠ 0 := t.ne_zero
      field_simp at h
      exact h

  have solvable_iff_one :
      HilbertSymbol.IsSolvable F (a * t⁻¹) (b * t⁻¹) ↔
      hilbertSymbol F (a * t⁻¹) (b * t⁻¹) = 1 :=
    (hilbertSymbol.eq_one_iff).symm

  rw [represents_iff_solvable, solvable_iff_one, hilbertSymbol.div_div_eq_mul]

  exact hilbertSymbol.prod_pm_one_eq_one_iff
    (hilbertSymbol.eq_one_or_neg_one a b)
    (hilbertSymbol.eq_one_or_neg_one t (-(a * b)))

section Corollary114

variable {F : Type*} [Field F] [HilbertBilinearField F]

/-- If the binary form $a x^2 + b y^2$ represents $-c$, then the ternary form
$a x^2 + b y^2 + c z^2$ represents zero (with $z = 1$). -/
lemma BinaryForm.Represents.ternary_represents_zero
    {a b c : Fˣ} (h : BinaryForm.Represents F a b ((-c : Fˣ) : F)) :
    TernaryForm.RepresentsZero F a b c := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨x, y, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
  simp only [Units.val_neg, one_pow, mul_one] at hxy ⊢
  linear_combination hxy

/-- If the ternary form $a x^2 + b y^2 + c z^2$ represents zero, then the binary form
$a x^2 + b y^2$ represents $-c$: either dehomogenize by dividing by $z$ if $z \neq 0$, or use the
"represents-all" property of an isotropic binary form. -/
lemma TernaryForm.RepresentsZero.binary_represents_neg
    {a b c : Fˣ} (h : TernaryForm.RepresentsZero F a b c) :
    BinaryForm.Represents F a b ((-c : Fˣ) : F) := by
  obtain ⟨x, y, z, hne, heq⟩ := h
  by_cases hz : z ≠ 0
  ·
    refine ⟨x / z, y / z, ?_⟩
    simp only [Units.val_neg]
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
    field_simp
    linear_combination heq
  ·
    push Not at hz
    subst hz
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at heq
    have hne' : x ≠ 0 ∨ y ≠ 0 := by
      rcases hne with hx | hy | hz'
      · exact Or.inl hx
      · exact Or.inr hy
      · exact absurd rfl hz'

    rcases hne' with hx | hy
    · exact HilbertSymbol.binary_form_represents_all hx heq ((-c : Fˣ) : F)
    ·
      by_cases hx : x ≠ 0
      · exact HilbertSymbol.binary_form_represents_all hx heq ((-c : Fˣ) : F)
      · push Not at hx
        subst hx
        simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at heq

        exfalso
        have : (b : F) * y ^ 2 ≠ 0 :=
          mul_ne_zero b.ne_zero (pow_ne_zero 2 hy)
        exact this heq

/-- The ternary form $a x^2 + b y^2 + c z^2$ represents zero iff the binary form
$a x^2 + b y^2$ represents $-c$. -/
theorem ternary_represents_zero_iff_binary_represents_neg
    {a b c : Fˣ} :
    TernaryForm.RepresentsZero F a b c ↔
    BinaryForm.Represents F a b ((-c : Fˣ) : F) :=
  ⟨TernaryForm.RepresentsZero.binary_represents_neg,
   BinaryForm.Represents.ternary_represents_zero⟩

/-- **Corollary 11.4.** The ternary form $a x^2 + b y^2 + c z^2$ represents zero over $F$ iff
$(a, b) = (-c, -(ab))$ in $\{1, -1\}$. -/
theorem ternary_form_represents_zero_iff_hilbert
    (a b c : Fˣ) :
    TernaryForm.RepresentsZero F a b c ↔
    hilbertSymbol F a b = hilbertSymbol F (-c) (-(a * b)) := by
  rw [ternary_represents_zero_iff_binary_represents_neg,
      binary_form_represents_iff_hilbert a b (-c)]

end Corollary114

section Corollary112

/-- For a nonzero integer $a$, the set of primes $p$ for which $|a|_p \neq 1$ is finite
(equivalently, only finitely many primes divide $a$). -/
lemma int_padicNorm_eq_one_cofinitely (a : ℤ) (ha : a ≠ 0) :
    Set.Finite {p : ℕ | p.Prime ∧ padicNorm p (a : ℚ) ≠ 1} := by
  apply Set.Finite.subset (Set.finite_Icc 0 a.natAbs)
  intro p ⟨hp, hne⟩
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : (p : ℤ) ∣ a := by
    by_contra hndvd; exact hne ((padicNorm.int_eq_one_iff a).mpr hndvd)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
    (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd))

/-- For a nonzero natural number $d$, the set of primes $p$ for which $|d|_p \neq 1$ is finite. -/
lemma nat_padicNorm_eq_one_cofinitely (d : ℕ) (hd : d ≠ 0) :
    Set.Finite {p : ℕ | p.Prime ∧ padicNorm p (d : ℚ) ≠ 1} := by
  apply Set.Finite.subset (Set.finite_Icc 0 d)
  intro p ⟨hp, hne⟩
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ d := by
    by_contra hndvd; exact hne ((padicNorm.nat_eq_one_iff d).mpr hndvd)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd

/-- For a nonzero rational $q$, the set of primes $p$ for which $|q|_p \neq 1$ is finite.
That is, $q$ is a $p$-adic unit for all but finitely many primes. -/
lemma rat_padicNorm_eq_one_cofinitely (q : ℚ) (hq : q ≠ 0) :
    Set.Finite {p : ℕ | p.Prime ∧ padicNorm p q ≠ 1} := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : q.den ≠ 0 := Nat.pos_iff_ne_zero.mp q.pos
  apply Set.Finite.subset (Set.Finite.union
    (int_padicNorm_eq_one_cofinitely q.num hnum)
    (nat_padicNorm_eq_one_cofinitely q.den hden))
  intro p ⟨hp, hne⟩
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hall
  simp only [not_or, not_and] at hall
  have hnum_ok : padicNorm p (q.num : ℚ) = 1 := not_not.mp (hall.1 hp)
  have hden_ok : padicNorm p (q.den : ℚ) = 1 := not_not.mp (hall.2 hp)
  apply hne
  conv_lhs => rw [show q = (q.num : ℚ) / q.den from by rw [Rat.num_div_den]]
  rw [padicNorm.div, hnum_ok, hden_ok, div_one]

/-- For a finite tuple of nonzero rationals $w_0, \dots, w_{n-1}$, the set of "bad" primes
(those at which some $w_i$ is not a unit) is finite. -/
lemma finitely_many_bad_primes {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, w i ≠ 0) :
    Set.Finite {p : ℕ | p.Prime ∧ ∃ i, padicNorm p (w i) ≠ 1} := by
  apply Set.Finite.subset (Set.finite_iUnion
    (fun i => rat_padicNorm_eq_one_cofinitely (w i) (hw i)))
  intro p ⟨hp, i, hne⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, hp, hne⟩

/-- Bridge between rational and $p$-adic norms: if the rational $p$-adic norm $|q|_p = 1$, then
the $p$-adic norm of $q$ viewed in $\mathbb{Q}_p$ also equals $1$. -/
lemma padicNorm_eq_one_to_padic_norm {p : ℕ} [Fact p.Prime] (q : ℚ)
    (h : padicNorm p q = 1) : ‖(q : ℚ_[p])‖ = 1 := by
  rw [Padic.eq_padicNorm]
  simp [h]

/-- **Corollary 11.2.** A diagonal quadratic form $\sum_{i < n} w_i x_i^2$ with $n > 2$ variables
and nonzero rational coefficients represents zero in $\mathbb{Q}_p$ for all but finitely many
primes $p$. The exceptional set consists of $\{2\}$ together with primes dividing some
coefficient. -/
theorem diagonal_form_represents_zero_locally_cofinitely
    {n : ℕ} (hn : 2 < n) (w : Fin n → ℚ) (hw : ∀ i, w i ≠ 0) :
    ∃ S : Finset ℕ, ∀ (p : ℕ) (_ : p.Prime) (_ : p ∉ S),
      haveI : Fact p.Prime := ⟨‹Nat.Prime p›⟩
      ∃ x : Fin n → ℚ_[p], (∃ i, x i ≠ 0) ∧
        ∑ i, (w i : ℚ_[p]) * x i ^ 2 = 0 := by


  have hfin : Set.Finite ({2} ∪ {p : ℕ | p.Prime ∧ ∃ i, padicNorm p (w i) ≠ 1}) :=
    Set.Finite.union (Set.finite_singleton 2) (finitely_many_bad_primes w hw)
  refine ⟨hfin.toFinset, fun p hp hpS => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩

  have hp_ne_2 : p ≠ 2 := by
    intro h; subst h
    apply hpS; rw [Set.Finite.mem_toFinset]; exact Set.mem_union_left _ rfl
  have hw_norm : ∀ i, padicNorm p (w i) = 1 := by
    intro i
    by_contra hi
    apply hpS; rw [Set.Finite.mem_toFinset]
    exact Set.mem_union_right _ ⟨hp, i, hi⟩

  have hw_pnorm : ∀ i, ‖(w i : ℚ_[p])‖ = 1 :=
    fun i => padicNorm_eq_one_to_padic_norm (w i) (hw_norm i)
  set a : Fin n → ℤ_[p]ˣ := fun i => PadicInt.mkUnits (hw_pnorm i) with ha_def


  obtain ⟨x, hne, hsum⟩ := diagonal_unit_form_represents_zero hp_ne_2 hn a

  refine ⟨x, hne, ?_⟩
  convert hsum using 1

end Corollary112

section Corollary115

open HilbertSymbol

noncomputable section

/-- The canonical map sending a rational unit $a \in \mathbb{Q}^\times$ to a real unit
$a \in \mathbb{R}^\times$. -/
def Corollary115.ratToRealUnits (a : ℚˣ) : ℝˣ :=
  Units.mk0 ((a : ℚ) : ℝ) (by exact_mod_cast a.ne_zero)

/-- The canonical map sending a rational unit $a \in \mathbb{Q}^\times$ to a $p$-adic unit
$a \in \mathbb{Q}_p^\times$. -/
def Corollary115.ratToQpUnits (p : ℕ) [Fact (Nat.Prime p)] (a : ℚˣ) : ℚ_[p]ˣ :=
  Units.mk0 ((a : ℚ) : ℚ_[p]) (by exact_mod_cast a.ne_zero)

/-- The Hilbert symbol at the archimedean place: $(a, b)_\infty$ equals the real Hilbert
symbol of $a, b$ regarded as units of $\mathbb{R}^\times$. -/
def Corollary115.hilbertAtInfty (a b : ℚˣ) : ℤ :=
  realHilbertSymbol (Corollary115.ratToRealUnits a) (Corollary115.ratToRealUnits b)

/-- The Hilbert symbol at the finite place $p$: $(a, b)_p$ is the $p$-adic Hilbert symbol
of $a, b$ regarded as units of $\mathbb{Q}_p^\times$. -/
def Corollary115.hilbertAtPrime (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚˣ) : ℤ :=
  padicHilbertSymbol p (Corollary115.ratToQpUnits p a) (Corollary115.ratToQpUnits p b)

/-- The **global Hilbert product** $\prod_v (a, b)_v$, taken over all places of $\mathbb{Q}$:
the archimedean place $\infty$ and all finite primes $p$. -/
def Corollary115.globalHilbertProduct (a b : ℚˣ) : ℤ :=
  Corollary115.hilbertAtInfty a b *
  ∏ᶠ (p : Nat.Primes),
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    Corollary115.hilbertAtPrime p.val a b


/-- For any $a, b \in \mathbb{Q}^\times$, the local Hilbert symbol $(a, b)_p$ is equal to $1$
for all but finitely many primes $p$. -/
theorem Corollary115.hilbert_product_formula_finite_support (a b : ℚˣ) :
    (Function.mulSupport (fun p : Nat.Primes =>
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      Corollary115.hilbertAtPrime p.val a b)).Finite := by


  have h := _root_.hilbert_product_formula_finite_support a b

  rw [Set.Finite] at h
  exact h

/-- The set of places of $\mathbb{Q}$: either the archimedean (infinite) place $\infty$
or a finite place $p$ given by a prime. -/
inductive Place where
  | infty : Place
  | finite : Nat.Primes → Place
  deriving DecidableEq

/-- The Hilbert symbol $(a, b)_v$ at the place $v$ of $\mathbb{Q}$, taking values in
$\{1, -1\}$. -/
def hilbertAt (v : Place) (a b : ℚˣ) : ℤ :=
  match v with
  | Place.infty => Corollary115.hilbertAtInfty a b
  | Place.finite p =>
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    Corollary115.hilbertAtPrime p.val a b

/-- The Hilbert symbol at any place takes values in $\{1, -1\}$. -/
lemma hilbertAt_eq_one_or_neg_one (v : Place) (a b : ℚˣ) :
    hilbertAt v a b = 1 ∨ hilbertAt v a b = -1 := by
  cases v with
  | infty =>
    simp only [hilbertAt, Corollary115.hilbertAtInfty, realHilbertSymbol]
    exact hilbertSymbol.eq_one_or_neg_one _ _
  | finite p =>
    simp only [hilbertAt, Corollary115.hilbertAtPrime, padicHilbertSymbol]
    exact hilbertSymbol.eq_one_or_neg_one _ _

/-- The global Hilbert product can be rewritten using the `hilbertAt` notation indexed by
places: $\prod_v (a, b)_v = (a, b)_\infty \cdot \prod_p (a, b)_p$. -/
lemma globalHilbertProduct_eq_hilbertAt (a b : ℚˣ) :
    Corollary115.globalHilbertProduct a b =
    hilbertAt Place.infty a b *
    ∏ᶠ (p : Nat.Primes),
      hilbertAt (Place.finite p) a b := by
  unfold Corollary115.globalHilbertProduct hilbertAt
  rfl

/-- **A consequence of Hilbert reciprocity.** If two pairs $(a, b)$ and $(c, d)$ have matching
local Hilbert symbols at all places except possibly one place $v_0$, then they also match at
$v_0$. This follows from the product formula $\prod_v (a, b)_v = 1$. -/
theorem hilbert_symbol_determined_by_all_but_one (a b c d : ℚˣ)
    (hprod1 : Corollary115.globalHilbertProduct a b = 1)
    (hprod2 : Corollary115.globalHilbertProduct c d = 1)
    (v₀ : Place)
    (h_agree : ∀ v : Place, v ≠ v₀ → hilbertAt v a b = hilbertAt v c d) :
    hilbertAt v₀ a b = hilbertAt v₀ c d := by


  rw [globalHilbertProduct_eq_hilbertAt] at hprod1 hprod2

  cases v₀ with
  | infty =>

    have hfin : ∀ p : Nat.Primes, hilbertAt (Place.finite p) a b =
        hilbertAt (Place.finite p) c d :=
      fun p => h_agree (Place.finite p) (by simp)

    have hprod_eq : ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) a b =
        ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) c d :=
      finprod_congr hfin


    have h1 := hprod1
    have h2 := hprod2
    rw [hprod_eq] at h1

    have hne : ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) c d ≠ 0 := by
      intro heq; rw [heq, mul_zero] at h2; exact one_ne_zero h2.symm
    exact mul_right_cancel₀ hne (by rw [h1, h2])
  | finite p₀ =>

    have hinfty : hilbertAt Place.infty a b = hilbertAt Place.infty c d :=
      h_agree Place.infty (by simp)

    have hfin : ∀ p : Nat.Primes, p ≠ p₀ →
        hilbertAt (Place.finite p) a b = hilbertAt (Place.finite p) c d :=
      fun p hp => h_agree (Place.finite p) (by simp [hp])


    rw [hinfty] at hprod1
    have hne_infty : hilbertAt Place.infty c d ≠ 0 := by
      intro heq; rw [heq, zero_mul] at hprod2; exact one_ne_zero hprod2.symm
    have hprod_fin_eq : ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) a b =
        ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) c d :=
      mul_left_cancel₀ hne_infty (by rw [hprod1, hprod2])

    have hsupp1 : (Function.mulSupport
        (fun p => hilbertAt (Place.finite p) a b)).Finite :=
      Corollary115.hilbert_product_formula_finite_support a b
    have hsupp2 : (Function.mulSupport
        (fun p => hilbertAt (Place.finite p) c d)).Finite :=
      Corollary115.hilbert_product_formula_finite_support c d

    set S := hsupp1.toFinset ∪ hsupp2.toFinset ∪ {p₀} with hS_def
    have hfS : Function.mulSupport (fun p => hilbertAt (Place.finite p) a b) ⊆ ↑S := by
      intro x hx
      simp only [hS_def, Finset.coe_union, Finset.coe_singleton,
        Set.mem_union, Set.mem_singleton_iff]
      left; left; exact (Set.Finite.mem_toFinset hsupp1).mpr hx
    have hgS : Function.mulSupport (fun p => hilbertAt (Place.finite p) c d) ⊆ ↑S := by
      intro x hx
      simp only [hS_def, Finset.coe_union, Finset.coe_singleton,
        Set.mem_union, Set.mem_singleton_iff]
      left; right; exact (Set.Finite.mem_toFinset hsupp2).mpr hx
    rw [finprod_eq_prod_of_mulSupport_subset _ hfS,
        finprod_eq_prod_of_mulSupport_subset _ hgS] at hprod_fin_eq
    have hp₀S : p₀ ∈ S := by simp [hS_def]
    rw [← Finset.mul_prod_erase S _ hp₀S,
        ← Finset.mul_prod_erase S _ hp₀S] at hprod_fin_eq
    have hrest : ∏ i ∈ S.erase p₀, (fun p => hilbertAt (Place.finite p) a b) i =
        ∏ i ∈ S.erase p₀, (fun p => hilbertAt (Place.finite p) c d) i :=
      Finset.prod_congr rfl (fun x hx => hfin x (Finset.ne_of_mem_erase hx))
    rw [hrest] at hprod_fin_eq
    have hP_ne : ∏ i ∈ S.erase p₀,
        (fun p => hilbertAt (Place.finite p) c d) i ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro x _
      rcases hilbertAt_eq_one_or_neg_one (Place.finite x) c d with h | h <;> simp [h]
    exact mul_right_cancel₀ hP_ne hprod_fin_eq



end

end Corollary115

section Corollary112General

open Matrix

/-- The element $2 \in \mathbb{Q}$ is invertible (needed for converting between quadratic forms
and their associated symmetric matrices over $\mathbb{Q}$). -/
noncomputable instance invertibleTwoQ : Invertible (2 : ℚ) :=
  invertibleOfNonzero (by norm_num : (2 : ℚ) ≠ 0)

/-- A symmetric matrix $M$ over $\mathbb{Q}$ defines a quadratic form $x \mapsto x^T M x$, and
**represents zero $p$-adically** if there exists a nonzero vector $x \in \mathbb{Q}_p^n$ with
$x^T M x = 0$. -/
def QuadraticForm.RepresentsZeroPadically {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ x : Fin n → ℚ_[p], (∃ i, x i ≠ 0) ∧
    dotProduct x (mulVec (M.map (fun q : ℚ => (q : ℚ_[p]))) x) = 0




end Corollary112General
