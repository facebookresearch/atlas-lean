/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
namespace Factorization

theorem associated_iff_exists_unit {R : Type*} [Monoid R] (a b : R) :
    Associated a b ↔ ∃ u : Rˣ, a = b * ↑u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u⁻¹, by simp [← hu, mul_assoc]⟩
  · rintro ⟨u, hu⟩
    exact ⟨u⁻¹, by simp [hu, mul_assoc]⟩

theorem polynomial_irreducible_dvd_mul (F : Type*) [Field F]
    {p q s : Polynomial F} (hp : Irreducible p) (h : p ∣ q * s) :
    p ∣ q ∨ p ∣ s :=
  hp.prime.dvd_or_dvd h

theorem gauss_lemma {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    {p q : Polynomial R} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one]
  rw [Polynomial.content_mul, hp.content_eq_one, hq.content_eq_one, mul_one]

theorem polynomial_ufd (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid (Polynomial R) := inferInstance

theorem primitive_dvd_iff_fraction_map_dvd {R : Type*} [CommRing R] [IsDomain R]
    [Nonempty (NormalizedGCDMonoid R)] {p q : Polynomial R}
    (hp : p.IsPrimitive) :
    p ∣ q ↔ Polynomial.map (algebraMap R (FractionRing R)) p ∣
      Polynomial.map (algebraMap R (FractionRing R)) q := by
  constructor
  · exact fun ⟨r, hr⟩ => ⟨r.map _, hr ▸ Polynomial.map_mul _⟩
  · intro h_dvd
    by_cases hq : q = 0
    · simp [hq]
    · have := Classical.arbitrary (NormalizedGCDMonoid R)
      have hprim : q.primPart.IsPrimitive := q.isPrimitive_primPart
      have hcontent_ne : (q.content : R) ≠ 0 := by
        rwa [Ne, Polynomial.content_eq_zero_iff]
      have h_map_q : Polynomial.map (algebraMap R (FractionRing R)) q =
          Polynomial.C (algebraMap R (FractionRing R) q.content) *
          Polynomial.map (algebraMap R (FractionRing R)) q.primPart := by
        rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Polynomial.eq_C_content_mul_primPart]
      have h_unit : IsUnit (Polynomial.C (algebraMap R (FractionRing R) q.content) :
          Polynomial (FractionRing R)) := by
        apply Polynomial.isUnit_C.mpr
        rw [isUnit_iff_ne_zero]
        exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hcontent_ne
      have h_dvd' : Polynomial.map (algebraMap R (FractionRing R)) p ∣
          Polynomial.map (algebraMap R (FractionRing R)) q.primPart := by
        rw [h_map_q] at h_dvd
        exact h_unit.dvd_mul_left.mp h_dvd
      exact (hp.dvd_primPart_iff_dvd hq).mp
        (hp.dvd_of_fraction_map_dvd_fraction_map hprim h_dvd')

theorem gaussian_prime_of_norm_natAbs_prime (z : GaussianInt) (p : ℕ) (hpp : Nat.Prime p)
    (hn : (Zsqrtd.norm z).natAbs = p) : Prime z := by
  rw [← irreducible_iff_prime]
  constructor
  · intro hu
    have h1 := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hn] at h1; exact hpp.ne_one h1
  · intro x y hxy
    have hnorm : (Zsqrtd.norm x).natAbs * (Zsqrtd.norm y).natAbs = p := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hxy, hn]
    have hdvd : (Zsqrtd.norm x).natAbs ∣ p := ⟨_, hnorm.symm⟩
    rcases hpp.eq_one_or_self_of_dvd _ hdvd with h | h
    · left; exact Zsqrtd.norm_eq_one_iff.mp h
    · right
      have hb1 : (Zsqrtd.norm y).natAbs = 1 := by nlinarith [hpp.one_lt]
      exact Zsqrtd.norm_eq_one_iff.mp hb1

theorem gaussian_primes_classification :

    (∀ (p : ℕ) [Fact (Nat.Prime p)], Prime (↑p : GaussianInt) ↔ p % 4 = 3) ∧

    (∀ (p : ℕ) [Fact (Nat.Prime p)], p % 4 = 1 →
      ∃ a b : ℕ, a ^ 2 + b ^ 2 = p ∧ Prime (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∧
        Prime (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt)) ∧

    Prime (⟨1, 1⟩ : GaussianInt) ∧

    (∀ (z : GaussianInt), Prime z →
      (∃ (p : ℕ), Nat.Prime p ∧ p % 4 = 3 ∧ Associated z ↑p) ∨
      (∃ (a b : ℕ) (p : ℕ), Nat.Prime p ∧ p % 4 = 1 ∧ a ^ 2 + b ^ 2 = p ∧
        (Associated z ⟨(a : ℤ), (b : ℤ)⟩ ∨ Associated z ⟨(a : ℤ), -(b : ℤ)⟩)) ∨
      Associated z ⟨1, 1⟩) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro p _
    exact GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p
  ·
    intro p hp hp1
    have hp4 : p % 4 ≠ 3 := by omega
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp4
    have hpp : Nat.Prime p := hp.out
    have hn_pos : (Zsqrtd.norm (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)).natAbs = p := by
      simp [Zsqrtd.norm]
      rw [show (a : ℤ) * a + (b : ℤ) * b = ↑(a ^ 2 + b ^ 2) by push_cast; ring]
      rw [hab]; simp
    have hn_neg : (Zsqrtd.norm (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt)).natAbs = p := by
      simp [Zsqrtd.norm]
      rw [show (a : ℤ) * a + (b : ℤ) * b = ↑(a ^ 2 + b ^ 2) by push_cast; ring]
      rw [hab]; simp
    exact ⟨a, b, hab, gaussian_prime_of_norm_natAbs_prime _ p hpp hn_pos,
      gaussian_prime_of_norm_natAbs_prime _ p hpp hn_neg⟩
  ·
    have hn : (Zsqrtd.norm (⟨1, 1⟩ : GaussianInt)).natAbs = 2 := by
      simp [Zsqrtd.norm]
    exact gaussian_prime_of_norm_natAbs_prime _ 2 (by norm_num) hn
  ·


    intro z hz
    have hzu : ¬IsUnit z := hz.not_unit
    have hne0 : z ≠ 0 := hz.ne_zero
    have hnorm_ne1 : (Zsqrtd.norm z).natAbs ≠ 1 := fun h => hzu (Zsqrtd.norm_eq_one_iff.mp h)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hnorm_ne1
    have hpdvd_int : (p : ℤ) ∣ Zsqrtd.norm z := by
      have h := Int.natCast_dvd_natCast.mpr hpdvd
      rwa [Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)] at h
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have heq : z * star z = (↑(Zsqrtd.norm z) : GaussianInt) := by
      ext
      · simp [Zsqrtd.norm]
      · simp; ring
    by_cases hp3 : p % 4 = 3
    ·
      left
      have hpG : Prime (↑p : GaussianInt) :=
        (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr hp3
      have hdvd_prod : (↑p : GaussianInt) ∣ z * star z := by
        rw [heq]; exact_mod_cast hpdvd_int
      rcases hpG.dvd_or_dvd hdvd_prod with h1 | h2
      · exact ⟨p, hp, hp3, (hpG.irreducible.associated_of_dvd hz.irreducible h1).symm⟩
      · have h1 : (↑p : GaussianInt) ∣ z := by
          have h3 := map_dvd (starRingEnd GaussianInt) h2
          change star (↑p : GaussianInt) ∣ star (star z) at h3
          rw [star_star] at h3
          have hsp : star (↑p : GaussianInt) = ↑p := by ext <;> simp
          rwa [hsp] at h3
        exact ⟨p, hp, hp3, (hpG.irreducible.associated_of_dvd hz.irreducible h1).symm⟩
    ·
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp3
      have hn_pos : (Zsqrtd.norm (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)).natAbs = p := by
        simp [Zsqrtd.norm]
        rw [show (a : ℤ) * a + (b : ℤ) * b = ↑(a ^ 2 + b ^ 2) by push_cast; ring]
        rw [hab]; simp
      have hπ : Prime (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) := by
        rw [← irreducible_iff_prime]; constructor
        · intro hu; exact hp.ne_one (hn_pos ▸ Zsqrtd.norm_eq_one_iff.mpr hu)
        · intro x y hxy
          have hnorm : (Zsqrtd.norm x).natAbs * (Zsqrtd.norm y).natAbs = p := by
            rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hxy, hn_pos]
          rcases hp.eq_one_or_self_of_dvd _ ⟨_, hnorm.symm⟩ with h | h
          · left; exact Zsqrtd.norm_eq_one_iff.mp h
          · right; exact Zsqrtd.norm_eq_one_iff.mp (by nlinarith [hp.one_lt])
      have hfactor : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) * ⟨(a : ℤ), -(b : ℤ)⟩ = ↑(p : ℤ) := by
        ext
        · simp; nlinarith
        · simp; ring
      have hdvd_prod : (↑(p : ℤ) : GaussianInt) ∣ z * star z := by
        rw [heq]; exact_mod_cast hpdvd_int
      have hdvd3 : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∣ z * star z :=
        dvd_trans (dvd_mul_right _ _) (hfactor ▸ hdvd_prod)
      have hab_of_p2 (hp2 : p = 2) : a = 1 ∧ b = 1 := by
        subst hp2
        have ha : a ≤ 1 := by nlinarith [sq_nonneg b]
        have hb : b ≤ 1 := by nlinarith [sq_nonneg a]
        have ha0 : a ≠ 0 := by intro h; subst h; simp at hab; nlinarith [sq_nonneg b]
        have hb0 : b ≠ 0 := by intro h; subst h; simp at hab; nlinarith [sq_nonneg a]
        exact ⟨by omega, by omega⟩
      have hp1_of_ne2 (hp2 : p ≠ 2) : p % 4 = 1 := by
        have h4 : p % 4 < 4 := Nat.mod_lt _ (by omega)
        have h0 : p % 4 ≠ 0 := by
          intro h; have h4dvd : 4 ∣ p := Nat.dvd_of_mod_eq_zero h
          have h2dvd : 2 ∣ p := Nat.dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4dvd
          have := hp.eq_one_or_self_of_dvd 2 h2dvd; omega
        have h2m : p % 4 ≠ 2 := by
          intro h; have h2dvd : 2 ∣ p := by omega
          have := hp.eq_one_or_self_of_dvd 2 h2dvd; omega
        omega
      rcases hπ.dvd_or_dvd hdvd3 with h1 | h2
      · have hassoc := (hπ.irreducible.associated_of_dvd hz.irreducible h1).symm
        by_cases hp2 : p = 2
        · right; right
          obtain ⟨ha1, hb1⟩ := hab_of_p2 hp2
          rw [ha1, hb1] at hassoc; simpa using hassoc
        · right; left
          exact ⟨a, b, p, hp, hp1_of_ne2 hp2, hab, Or.inl hassoc⟩
      · have h3 : (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt) ∣ z := by
          have h3 := map_dvd (starRingEnd GaussianInt) h2
          change star (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∣ star (star z) at h3
          rw [star_star] at h3
          have hstar : star (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) = ⟨(a : ℤ), -(b : ℤ)⟩ := by
            ext <;> simp
          rwa [hstar] at h3
        have hn_neg : (Zsqrtd.norm (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt)).natAbs = p := by
          simp [Zsqrtd.norm]
          rw [show (a : ℤ) * a + (b : ℤ) * b = ↑(a ^ 2 + b ^ 2) by push_cast; ring]
          rw [hab]; simp
        have hπ_neg : Prime (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt) := by
          rw [← irreducible_iff_prime]; constructor
          · intro hu; exact hp.ne_one (hn_neg ▸ Zsqrtd.norm_eq_one_iff.mpr hu)
          · intro x y hxy
            have hnorm : (Zsqrtd.norm x).natAbs * (Zsqrtd.norm y).natAbs = p := by
              rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hxy, hn_neg]
            rcases hp.eq_one_or_self_of_dvd _ ⟨_, hnorm.symm⟩ with h | h
            · left; exact Zsqrtd.norm_eq_one_iff.mp h
            · right; exact Zsqrtd.norm_eq_one_iff.mp (by nlinarith [hp.one_lt])
        have hassoc := (hπ_neg.irreducible.associated_of_dvd hz.irreducible h3).symm
        by_cases hp2 : p = 2
        · right; right
          obtain ⟨ha1, hb1⟩ := hab_of_p2 hp2
          rw [ha1, hb1] at hassoc
          exact hassoc.trans ⟨⟨⟨0, 1⟩, ⟨0, -1⟩, by decide, by decide⟩, by decide⟩
        · right; left
          exact ⟨a, b, p, hp, hp1_of_ne2 hp2, hab, Or.inr hassoc⟩

theorem int_prime_not_gaussian_prime_iff (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ¬Prime ((p : ℤ) : GaussianInt) ↔ (p = 2 ∨ p % 4 = 1) := by
  have hpp := hp.out
  rw [show ((p : ℤ) : GaussianInt) = (↑p : GaussianInt) from rfl,
      GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p]
  constructor
  · intro hne3
    have h1 : p % 4 < 4 := Nat.mod_lt _ (by omega)
    have h0 : p % 4 ≠ 0 := by
      intro h
      have h4dvd : 4 ∣ p := Nat.dvd_of_mod_eq_zero h
      have h2dvd : 2 ∣ p := Nat.dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4dvd
      have := hpp.eq_one_or_self_of_dvd 2 h2dvd
      omega
    have hcases : p % 4 = 1 ∨ p % 4 = 2 := by omega
    rcases hcases with h | h
    · right; exact h
    · left
      have h2dvd : 2 ∣ p := by
        have : p % 2 = 0 := by omega
        exact Nat.dvd_of_mod_eq_zero this
      have := hpp.eq_one_or_self_of_dvd 2 h2dvd
      omega
  · intro h
    rcases h with h2 | h1
    · subst h2; norm_num
    · omega

theorem gaussian_not_prime_iff (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ¬ Prime (↑p : GaussianInt) ↔ (p = 2 ∨ p % 4 = 1) :=
  int_prime_not_gaussian_prime_iff p


theorem ufd_gcd_exists {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b : R) : ∃ g : R, g ∣ a ∧ g ∣ b ∧ ∀ d : R, d ∣ a → d ∣ b → d ∣ g := by
  letI := UniqueFactorizationMonoid.toGCDMonoid (α := R)
  exact ⟨GCDMonoid.gcd a b, gcd_dvd_left a b, gcd_dvd_right a b, fun d ha hb => dvd_gcd ha hb⟩

end Factorization
