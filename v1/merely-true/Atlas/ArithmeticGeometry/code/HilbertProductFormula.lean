/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HilbertBilinear
import Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import Atlas.ArithmeticGeometry.code.HilbertSymbol2Adic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open HilbertSymbol

noncomputable section

/-- Inclusion of rational units into real units: $\mathbb{Q}^\times \to \mathbb{R}^\times$. -/
def ratToRealUnits (a : ℚˣ) : ℝˣ :=
  Units.mk0 ((a : ℚ) : ℝ) (by exact_mod_cast a.ne_zero)

/-- Inclusion of rational units into $p$-adic units: $\mathbb{Q}^\times \to \mathbb{Q}_p^\times$. -/
def ratToQpUnits (p : ℕ) [Fact (Nat.Prime p)] (a : ℚˣ) : ℚ_[p]ˣ :=
  Units.mk0 ((a : ℚ) : ℚ_[p]) (by exact_mod_cast a.ne_zero)

/-- The image of `ratToRealUnits a` in $\mathbb{R}$ is just the inclusion of $a$. -/
@[simp]
lemma ratToRealUnits_val (a : ℚˣ) : (ratToRealUnits a : ℝ) = ((a : ℚ) : ℝ) := rfl

/-- The image of `ratToQpUnits p a` in $\mathbb{Q}_p$ is just the inclusion of $a$. -/
@[simp]
lemma ratToQpUnits_val (p : ℕ) [Fact (Nat.Prime p)] (a : ℚˣ) :
    (ratToQpUnits p a : ℚ_[p]) = ((a : ℚ) : ℚ_[p]) := rfl

/-- The inclusion $\mathbb{Q}^\times \to \mathbb{R}^\times$ is multiplicative. -/
lemma ratToRealUnits_mul (a b : ℚˣ) :
    ratToRealUnits (a * b) = ratToRealUnits a * ratToRealUnits b := by
  ext; simp [ratToRealUnits]

/-- The inclusion $\mathbb{Q}^\times \to \mathbb{Q}_p^\times$ is multiplicative. -/
lemma ratToQpUnits_mul (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚˣ) :
    ratToQpUnits p (a * b) = ratToQpUnits p a * ratToQpUnits p b := by
  ext; simp [ratToQpUnits]

/-- The image of $-1 \in \mathbb{Q}^\times$ in $\mathbb{Q}_p^\times$ is $-1$
(coming from $\mathbb{Z}_p^\times$). -/
lemma ratToQpUnits_neg_one (p : ℕ) [Fact (Nat.Prime p)] :
    ratToQpUnits p (-1 : ℚˣ) = unitZpToQp (-1 : ℤ_[p]ˣ) := by
  ext
  simp [ratToQpUnits, unitZpToQp_coe]

/-- The Hilbert symbol $(a, b)_\infty$ at the infinite (archimedean) place,
computed by viewing $a, b \in \mathbb{Q}^\times$ as elements of $\mathbb{R}^\times$. -/
def hilbertAtInfty (a b : ℚˣ) : ℤ :=
  realHilbertSymbol (ratToRealUnits a) (ratToRealUnits b)

/-- The Hilbert symbol $(a, b)_p$ at the prime $p$, computed by viewing
$a, b \in \mathbb{Q}^\times$ as elements of $\mathbb{Q}_p^\times$. -/
def hilbertAtPrime (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚˣ) : ℤ :=
  padicHilbertSymbol p (ratToQpUnits p a) (ratToQpUnits p b)

/-- At an odd prime $p$, the Hilbert symbol $(-1, -1)_p = 1$, since $-1$ is a $p$-adic unit
and by Lemma 10.5 the symbol on units is $1$ for odd primes. -/
lemma hilbertAtPrime_neg_one_neg_one_odd (p : ℕ) [Fact (Nat.Prime p)] (hp : p ≠ 2) :
    hilbertAtPrime p (-1) (-1) = 1 := by
  unfold hilbertAtPrime
  rw [show ratToQpUnits p (-1 : ℚˣ) = unitZpToQp (-1 : ℤ_[p]ˣ) from
    ratToQpUnits_neg_one p]
  exact hilbert_symbol_units_eq_one_of_odd p hp (-1) (-1)

/-- The image of $-1$ in $\mathbb{Q}_2^\times$ agrees with the `padicUnit_one` representation
of $-1 \in \mathbb{Z}_2^\times$. -/
lemma ratToQpUnits_neg_one_eq_padicUnit_one :
    ratToQpUnits 2 (-1 : ℚˣ) = padicUnit_one (-1 : ℤ_[2]ˣ) := by
  ext
  simp [ratToQpUnits, padicUnit_one_val]


/-- At the archimedean place, the Hilbert symbol $(-1, -1)_\infty = -1$: the equation
$-x^2 - y^2 = 1$ is unsolvable over $\mathbb{R}$. -/
lemma hilbertAtInfty_neg_one_neg_one :
    hilbertAtInfty (-1) (-1) = -1 := by
  unfold hilbertAtInfty
  rw [realHilbertSymbol.eq_neg_one_iff_both_neg]
  exact ⟨by simp [ratToRealUnits], by simp [ratToRealUnits]⟩

/-- If a rational $a$ has $p \nmid \text{num}(a)$ and $p \nmid \text{den}(a)$, then
$a$ is a $p$-adic unit, i.e., comes from $\mathbb{Z}_p^\times$. -/
lemma ratToQpUnits_eq_unitZpToQp_of_not_dvd (p : ℕ) [Fact (Nat.Prime p)] (a : ℚˣ)
    (hnum : ¬ (p : ℕ) ∣ (a : ℚ).num.natAbs) (hden : ¬ (p : ℕ) ∣ (a : ℚ).den) :
    ∃ u : ℤ_[p]ˣ, ratToQpUnits p a = unitZpToQp u := by
  have hq : (a : ℚ) ≠ 0 := a.ne_zero
  have hpn : padicNorm p (a : ℚ) = 1 := by
    rw [padicNorm.eq_zpow_of_nonzero hq, padicValRat_def,
        padicValInt.eq_zero_of_not_dvd (by rwa [Int.natCast_dvd]),
        padicValNat.eq_zero_of_not_dvd hden]
    simp
  have hnorm : ‖((a : ℚ) : ℚ_[p])‖ = 1 := by
    rw [Padic.eq_padicNorm]
    exact_mod_cast hpn
  have hle : ‖((a : ℚ) : ℚ_[p])‖ ≤ 1 := le_of_eq hnorm
  let z : ℤ_[p] := ⟨((a : ℚ) : ℚ_[p]), hle⟩
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr (by rwa [PadicInt.norm_def])
  refine ⟨hz.unit, Units.ext ?_⟩
  simp only [ratToQpUnits_val]
  rw [unitZpToQp_coe]
  simp [z, IsUnit.unit_spec]

/-- The image of $2 \in \mathbb{Q}^\times$ inside $\mathbb{Q}_2^\times$ agrees with `twoQp`. -/
lemma ratToQpUnits_two_eq_twoQp :
    ratToQpUnits 2 (Units.mk0 (2 : ℚ) (by norm_num)) = twoQp := by
  ext
  simp only [ratToQpUnits_val, Units.val_mk0, Rat.cast_ofNat, twoQp_val]

/-- The image of $q \in \mathbb{Q}^\times$ inside $\mathbb{Q}_q^\times$ agrees with `qpPrime q`. -/
lemma ratToQpUnits_natPrime_eq_qpPrime (q : ℕ) [Fact (Nat.Prime q)] :
    ratToQpUnits q (Units.mk0 (q : ℚ) (by exact_mod_cast (Fact.out : Nat.Prime q).ne_zero)) =
      qpPrime q := by
  ext
  simp only [ratToQpUnits_val, Units.val_mk0, qpPrime]
  push_cast
  rfl

/-- The rational $2$, viewed in $\mathbb{Q}_p^\times$ for an odd prime $p$, is a $p$-adic unit. -/
lemma ratToQpUnits_two_at_odd_prime (p : ℕ) [Fact (Nat.Prime p)] (hp : p ≠ 2) :
    ∃ u : ℤ_[p]ˣ, ratToQpUnits p (Units.mk0 (2 : ℚ) (by norm_num)) = unitZpToQp u := by
  apply ratToQpUnits_eq_unitZpToQp_of_not_dvd
  ·
    simp only [Units.val_mk0]
    norm_num
    have : 2 < p := by have := (Fact.out : Nat.Prime p).two_le; omega
    exact fun h => Nat.not_lt.mpr (Nat.le_of_dvd (by norm_num) h) this
  ·
    simp only [Units.val_mk0]
    norm_num
    exact (Fact.out : Nat.Prime p).one_lt.ne'

/-- An odd prime $q$, viewed in $\mathbb{Q}_2^\times$, is a $2$-adic unit. -/
lemma ratToQpUnits_prime_at_two (q : ℕ) (hq : Nat.Prime q) (hq_odd : q ≠ 2) :
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    ∃ u : ℤ_[2]ˣ, ratToQpUnits 2 (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) =
      unitZpToQp u := by
  apply ratToQpUnits_eq_unitZpToQp_of_not_dvd
  ·
    simp only [Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]
    intro h
    have := hq.eq_one_or_self_of_dvd 2 h
    omega
  ·
    simp only [Units.val_mk0, Rat.den_natCast]
    omega

/-- (Textbook Corollary 10.10) For any $a, b \in \mathbb{Q}^\times$, the set of primes $p$
where $(a, b)_p \neq 1$ is finite. This is the finiteness condition that makes the global
Hilbert product well-defined. -/
theorem hilbert_product_formula_finite_support (a b : ℚˣ) :
    Set.Finite {p : Nat.Primes |
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      hilbertAtPrime p.val a b ≠ 1} := by


  let N := 2 * (a : ℚ).num.natAbs * (a : ℚ).den * ((b : ℚ).num.natAbs * (b : ℚ).den)
  have hN : N ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · omega
    · exact (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr a.ne_zero)).ne'
    · exact a.val.den_pos.ne'
    · exact mul_ne_zero (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr b.ne_zero)).ne' b.val.den_pos.ne'

  have hfin : Set.Finite {p : Nat.Primes | p.val ∣ N} :=
    Set.Finite.subset
      (Set.Finite.preimage (fun a _ b _ hab => Subtype.val_injective hab)
        (Nat.divisors N).finite_toSet)
      (fun p hp => by
        simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors] at *
        exact ⟨hp, hN⟩)

  apply hfin.subset
  intro ⟨p_val, hp_prime⟩ hmem
  simp only [Set.mem_setOf_eq] at hmem ⊢

  by_contra h_not_dvd
  apply hmem
  haveI : Fact (Nat.Prime p_val) := ⟨hp_prime⟩


  have h_no_factor : ¬ (p_val ∣ 2) ∧ ¬ (p_val ∣ (a : ℚ).num.natAbs) ∧
      ¬ (p_val ∣ (a : ℚ).den) ∧ ¬ (p_val ∣ (b : ℚ).num.natAbs) ∧ ¬ (p_val ∣ (b : ℚ).den) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> apply h_not_dvd
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _
  obtain ⟨h2, hnd, hdd, hnb, hdb⟩ := h_no_factor
  have hp2 : p_val ≠ 2 := fun h => h2 (h ▸ dvd_refl p_val)

  obtain ⟨ua, hua⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p_val a hnd hdd
  obtain ⟨ub, hub⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p_val b hnb hdb

  unfold hilbertAtPrime
  rw [hua, hub]
  exact hilbert_symbol_units_eq_one_of_odd p_val hp2 ua ub

/-- The global Hilbert product over all places: $\prod_v (a, b)_v$ where $v$ ranges over
$\{\infty\} \cup \{p : p \text{ prime}\}$. By the product formula (Theorem 10.11), this always
equals $1$. The product over primes is a `finprod` (well-defined by `hilbert_product_formula_finite_support`). -/
def globalHilbertProduct (a b : ℚˣ) : ℤ :=
  hilbertAtInfty a b *
  ∏ᶠ (p : Nat.Primes),
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    hilbertAtPrime p.val a b



/-- Bilinearity in the first argument at the infinite place:
$(ab, c)_\infty = (a, c)_\infty \cdot (b, c)_\infty$. -/
lemma hilbertAtInfty_mul_left (a b c : ℚˣ) :
    hilbertAtInfty (a * b) c = hilbertAtInfty a c * hilbertAtInfty b c := by
  unfold hilbertAtInfty
  rw [ratToRealUnits_mul]
  exact hilbertSymbol.mul_left (ratToRealUnits a) (ratToRealUnits b) (ratToRealUnits c)


/-- Symmetry of the Hilbert symbol at the infinite place: $(a, b)_\infty = (b, a)_\infty$. -/
lemma hilbertAtInfty_comm (a b : ℚˣ) :
    hilbertAtInfty a b = hilbertAtInfty b a := by
  unfold hilbertAtInfty realHilbertSymbol
  simp only [hilbertSymbol.symm]

/-- Symmetry of the Hilbert symbol at a prime: $(a, b)_p = (b, a)_p$. -/
lemma hilbertAtPrime_comm (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚˣ) :
    hilbertAtPrime p a b = hilbertAtPrime p b a := by
  unfold hilbertAtPrime padicHilbertSymbol
  exact hilbertSymbol.symm (ratToQpUnits p a) (ratToQpUnits p b)


/-- Symmetry of the global Hilbert product: $\prod_v (a, b)_v = \prod_v (b, a)_v$. -/
theorem globalHilbertProduct_comm (a b : ℚˣ) :
    globalHilbertProduct a b = globalHilbertProduct b a := by
  unfold globalHilbertProduct
  rw [hilbertAtInfty_comm]
  congr 1
  apply finprod_congr
  intro p
  haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
  exact hilbertAtPrime_comm p.val a b


/-- The global Hilbert product always takes the value $1$ or $-1$, as a product of
$\pm 1$ values from a finite set of non-trivial contributions. -/
theorem globalHilbertProduct_eq_one_or_neg_one (a b : ℚˣ) :
    globalHilbertProduct a b = 1 ∨ globalHilbertProduct a b = -1 := by

  have mul_pm_one : ∀ x y : ℤ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) →
      (x * y = 1 ∨ x * y = -1) := by
    intros x y hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

  have hinfty : hilbertAtInfty a b = 1 ∨ hilbertAtInfty a b = -1 := by
    unfold hilbertAtInfty
    exact realHilbertSymbol.eq_one_or_neg_one _ _

  let f : Nat.Primes → ℤ := fun p =>
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    hilbertAtPrime p.val a b
  have hf_pm : ∀ p : Nat.Primes, f p = 1 ∨ f p = -1 := by
    intro p
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    simp only [f]
    unfold hilbertAtPrime
    exact padicHilbertSymbol.eq_one_or_neg_one _ _

  have hfin := hilbert_product_formula_finite_support a b
  have hsupp : (Function.mulSupport f).Finite := by
    apply Set.Finite.subset hfin
    intro p hp
    simp only [Set.mem_setOf_eq, Function.mem_mulSupport] at *
    exact hp

  have hfinprod_eq : ∏ᶠ (p : Nat.Primes), f p =
      hsupp.toFinset.prod f :=
    finprod_eq_prod_of_mulSupport_subset f (by
      intro p hp
      exact Finset.mem_coe.mpr (hsupp.mem_toFinset.mpr hp))

  suffices h : globalHilbertProduct a b = hilbertAtInfty a b * (∏ᶠ (p : Nat.Primes), f p) by
    rw [h, hfinprod_eq]
    suffices hprod : hsupp.toFinset.prod f = 1 ∨ hsupp.toFinset.prod f = -1 from
      mul_pm_one _ _ hinfty hprod
    have : ∀ (s : Finset Nat.Primes), (∀ x ∈ s, f x = 1 ∨ f x = -1) →
        s.prod f = 1 ∨ s.prod f = -1 := by
      intro s hs
      induction s using Finset.induction with
      | empty => simp
      | @insert p t hpt ih =>
        rw [Finset.prod_insert hpt]
        exact mul_pm_one _ _ (hs _ (Finset.mem_insert_self _ _))
          (ih (fun x hx => hs x (Finset.mem_insert_of_mem hx)))
    exact this _ (fun p _ => hf_pm p)
  rfl


/-- If the global Hilbert product equals $1$ on the generators of $\mathbb{Q}^\times$
(namely $-1$, and primes $p$ paired against each other), then it equals $1$ on any
pair of primes $(p, q)$. -/
lemma globalHilbertProduct_generators
    (h1 : globalHilbertProduct (-1) (-1) = 1)
    (h2 : ∀ q : ℕ, (hq : Nat.Prime q) →
      haveI : Fact (Nat.Prime q) := ⟨hq⟩
      globalHilbertProduct (-1) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1)
    (h3 : ∀ q : ℕ, (hq : Nat.Prime q) →
      haveI : Fact (Nat.Prime q) := ⟨hq⟩
      let q' := Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)
      globalHilbertProduct q' q' = 1)
    (h4 : ∀ q : ℕ, (hq : Nat.Prime q) → q ≠ 2 →
      haveI : Fact (Nat.Prime q) := ⟨hq⟩
      globalHilbertProduct (Units.mk0 (2 : ℚ) (by norm_num))
        (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1)
    (h5 : ∀ a b : ℕ, (ha : Nat.Prime a) → (hb : Nat.Prime b) → a ≠ 2 → b ≠ 2 → a ≠ b →
      haveI : Fact (Nat.Prime a) := ⟨ha⟩
      haveI : Fact (Nat.Prime b) := ⟨hb⟩
      globalHilbertProduct (Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne_zero))
        (Units.mk0 (b : ℚ) (by exact_mod_cast hb.ne_zero)) = 1)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    globalHilbertProduct (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  by_cases hpq : p = q
  · subst hpq; exact h3 p hp
  · by_cases hp2 : p = 2
    · subst hp2
      by_cases hq2 : q = 2
      · subst hq2; exact h3 2 (by decide)
      · exact h4 q hq hq2
    · by_cases hq2 : q = 2
      · subst hq2
        rw [globalHilbertProduct_comm]
        exact h4 p hp hp2
      · exact h5 p q hp hq hp2 hq2 hpq









/-- At an odd prime $p$ with $p \neq q$ (odd), both $2$ and $q$ are $p$-adic units,
so $(2, q)_p = 1$ by Lemma 10.5. -/
lemma hilbertAtPrime_two_q_eq_one_of_ne (q : ℕ) (hq : Nat.Prime q) (hq_odd : q ≠ 2)
    (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hpq : p ≠ q) :
    hilbertAtPrime p (Units.mk0 (2 : ℚ) (by norm_num))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
  unfold hilbertAtPrime
  obtain ⟨u, hu⟩ := ratToQpUnits_two_at_odd_prime p hp2
  have hpq_dvd : ¬ (p ∣ q) := by
    intro h
    have := hq.eq_one_or_self_of_dvd p h
    rcases this with h1 | h1
    · exact (Fact.out : Nat.Prime p).one_lt.ne' h1
    · exact absurd h1 hpq
  obtain ⟨v, hv⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p
    (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero))
    (by simp only [Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]; exact hpq_dvd)
    (by simp only [Units.val_mk0, Rat.den_natCast]
        exact Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p))
  rw [hu, hv]
  exact hilbert_symbol_units_eq_one_of_odd p hp2 u v


/-- At the archimedean place, $(2, q)_\infty = 1$ for any prime $q$, since $2 > 0$. -/
lemma hilbertAtInfty_two_q (q : ℕ) (hq : Nat.Prime q) :
    hilbertAtInfty (Units.mk0 (2 : ℚ) (by norm_num))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
  unfold hilbertAtInfty
  rw [realHilbertSymbol.eq_one_iff]
  exact realHilbertSymbol.isSolvable_of_pos_left (by simp [ratToRealUnits])

/-- At the prime $q$ (odd), if $2 = u$ in $\mathbb{Z}_q^\times$, then by Lemma 10.8
$(2, q)_q = (q, u)_q = \left(\frac{u}{q}\right) = \left(\frac{2}{q}\right)$. -/
lemma hilbertAtPrime_two_q_at_q (q : ℕ) (hq : Nat.Prime q) (hq_odd : q ≠ 2) :
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    ∀ u : ℤ_[q]ˣ, ratToQpUnits q (Units.mk0 (2 : ℚ) (by norm_num)) = unitZpToQp u →
    hilbertAtPrime q (Units.mk0 (2 : ℚ) (by norm_num))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = padicUnitLegendre u := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  intro u hu
  unfold hilbertAtPrime
  rw [hu, ratToQpUnits_natPrime_eq_qpPrime q]


  show padicHilbertSymbol q (unitZpToQp u) (qpPrime q) = padicUnitLegendre u
  rw [show padicHilbertSymbol q (unitZpToQp u) (qpPrime q) =
    padicHilbertSymbol q (qpPrime q) (unitZpToQp u) from
    hilbertSymbol.symm (unitZpToQp u) (qpPrime q)]
  exact hilbert_p_unit_eq_legendre hq_odd u






/-- (The quadratic reciprocity cancellation) For distinct odd primes $a, b$,
the product $\text{hilbert2Adic}(\bar a, \bar b, 0, 0) \cdot \left(\frac{b}{a}\right) \cdot
\left(\frac{a}{b}\right) = 1$. This is the heart of the proof of the global product formula
for $(a, b)$ with both $a$ and $b$ distinct odd primes, and is equivalent to the law of
quadratic reciprocity. -/
theorem hilbert_qr_cancellation {a b : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (ha_odd : a ≠ 2) (hb_odd : b ≠ 2) (hab : a ≠ b)
    [instA : Fact (Nat.Prime a)] [instB : Fact (Nat.Prime b)]
    (u_a2 : ℤ_[2]ˣ) (u_b2 : ℤ_[2]ˣ)
    (hu_a2 : ratToQpUnits 2 (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) = unitZpToQp u_a2)
    (hu_b2 : ratToQpUnits 2 (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) = unitZpToQp u_b2)
    (ub_a : ℤ_[a]ˣ)
    (hub_a : ratToQpUnits a (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) = unitZpToQp ub_a)
    (ua_b : ℤ_[b]ˣ)
    (hua_b : ratToQpUnits b (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) = unitZpToQp ua_b) :
    hilbert2Adic_formula (toZModPow_unit 3 u_a2) (toZModPow_unit 3 u_b2) 0 0 *
      padicUnitLegendre ub_a * padicUnitLegendre ua_b = 1 := by

  have hub_val : (ub_a : ℤ_[a]) = (b : ℤ_[a]) := by
    have h1 : (unitZpToQp ub_a : ℚ_[a]) = ((ub_a : ℤ_[a]) : ℚ_[a]) := unitZpToQp_coe ub_a
    have h2 : (ratToQpUnits a (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) : ℚ_[a]) =
      ((b : ℚ) : ℚ_[a]) := ratToQpUnits_val a _
    have h3 : ((ub_a : ℤ_[a]) : ℚ_[a]) = ((b : ℤ_[a]) : ℚ_[a]) := by
      rw [← h1, ← hub_a, h2]; push_cast; ring
    exact Subtype.val_injective h3

  have hua_val : (ua_b : ℤ_[b]) = (a : ℤ_[b]) := by
    have h1 : (unitZpToQp ua_b : ℚ_[b]) = ((ua_b : ℤ_[b]) : ℚ_[b]) := unitZpToQp_coe ua_b
    have h2 : (ratToQpUnits b (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) : ℚ_[b]) =
      ((a : ℚ) : ℚ_[b]) := ratToQpUnits_val b _
    have h3 : ((ua_b : ℤ_[b]) : ℚ_[b]) = ((a : ℤ_[b]) : ℚ_[b]) := by
      rw [← h1, ← hua_b, h2]; push_cast; ring
    exact Subtype.val_injective h3

  have hu_a2_val : (u_a2 : ℤ_[2]) = (a : ℤ_[2]) := by
    have h1 : (unitZpToQp u_a2 : ℚ_[2]) = ((u_a2 : ℤ_[2]) : ℚ_[2]) := unitZpToQp_coe u_a2
    have h2 : (ratToQpUnits 2 (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) : ℚ_[2]) =
      ((a : ℚ) : ℚ_[2]) := ratToQpUnits_val 2 _
    have h3 : ((u_a2 : ℤ_[2]) : ℚ_[2]) = ((a : ℤ_[2]) : ℚ_[2]) := by
      rw [← h1, ← hu_a2, h2]; push_cast; ring
    exact Subtype.val_injective h3

  have hu_b2_val : (u_b2 : ℤ_[2]) = (b : ℤ_[2]) := by
    have h1 : (unitZpToQp u_b2 : ℚ_[2]) = ((u_b2 : ℤ_[2]) : ℚ_[2]) := unitZpToQp_coe u_b2
    have h2 : (ratToQpUnits 2 (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) : ℚ_[2]) =
      ((b : ℚ) : ℚ_[2]) := ratToQpUnits_val 2 _
    have h3 : ((u_b2 : ℤ_[2]) : ℚ_[2]) = ((b : ℤ_[2]) : ℚ_[2]) := by
      rw [← h1, ← hu_b2, h2]; push_cast; ring
    exact Subtype.val_injective h3

  have hleg_ba : padicUnitLegendre ub_a = legendreSym a (b : ℤ) := by
    unfold padicUnitLegendre
    rw [hub_val, map_natCast, ZMod.val_natCast]
    simp only [legendreSym]
    congr 1
    exact_mod_cast (ZMod.natCast_mod b a ▸ rfl : ((b % a : ℕ) : ZMod a) = ((b : ℕ) : ZMod a))

  have hleg_ab : padicUnitLegendre ua_b = legendreSym b (a : ℤ) := by
    unfold padicUnitLegendre
    rw [hua_val, map_natCast, ZMod.val_natCast]
    simp only [legendreSym]
    congr 1
    exact_mod_cast (ZMod.natCast_mod a b ▸ rfl : ((a % b : ℕ) : ZMod b) = ((a : ℕ) : ZMod b))

  rw [hleg_ba, hleg_ab]

  have hqr := legendreSym.quadratic_reciprocity ha_odd hb_odd hab


  have hleg_prod : legendreSym a (↑b) * legendreSym b (↑a) = (-1) ^ (a / 2 * (b / 2)) := by
    rw [mul_comm]; exact hqr

  rw [mul_assoc, hleg_prod]


  unfold hilbert2Adic_formula
  simp only [Nat.cast_zero, zero_mul, add_zero]


  have hcoe_a : (toZModPow_unit 3 u_a2 : ZMod (2^3)) = (a : ZMod (2^3)) := by
    rw [toZModPow_unit_coe, hu_a2_val, map_natCast]
  have hcoe_b : (toZModPow_unit 3 u_b2 : ZMod (2^3)) = (b : ZMod (2^3)) := by
    rw [toZModPow_unit_coe, hu_b2_val, map_natCast]


  have hval_a : (toZModPow_unit 3 u_a2 : ZMod (2^3)).val = a % (2^3) := by
    rw [hcoe_a]; exact ZMod.val_natCast (n := 2^3) a
  have hval_b : (toZModPow_unit 3 u_b2 : ZMod (2^3)).val = b % (2^3) := by
    rw [hcoe_b]; exact ZMod.val_natCast (n := 2^3) b


  simp only [epsilon_ZMod8, hval_a, hval_b]


  have ha2_odd : a % 2 = 1 := by
    rcases ha.eq_two_or_odd with rfl | h
    · exact absurd rfl ha_odd
    · exact h
  have hb2_odd : b % 2 = 1 := by
    rcases hb.eq_two_or_odd with rfl | h
    · exact absurd rfl hb_odd
    · exact h
  have ha2 : ((((a % 2 ^ 3 - 1) / 2 : ℕ) : ZMod 2)) = ((a / 2 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff']; omega
  have hb2 : ((((b % 2 ^ 3 - 1) / 2 : ℕ) : ZMod 2)) = ((b / 2 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff']; omega
  rw [ha2, hb2, ← Nat.cast_mul, ZMod.val_natCast (n := 2)]
  set n := a / 2 * (b / 2)
  have : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 2) := by
    conv_lhs => rw [show n = 2 * (n / 2) + n % 2 from (Nat.div_add_mod n 2).symm]
    simp [pow_add, pow_mul]
  rw [this, ← pow_add]
  simp



end
