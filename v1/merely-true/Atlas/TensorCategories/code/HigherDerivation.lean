/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

set_option maxHeartbeats 800000

universe v u w

namespace TensorCategories

section Ext1UnitVanishing

/-- A higher derivation system on a `k`-algebra `A` augmented by `ε : A →ₐ[k] k`: a sequence of
`k`-linear functionals `χ n : A → k` with `χ 0 = ε` and the Leibniz-type product formula
`χ_n(ab) = ∑_j (n choose j) χ_j(a) χ_{n-j}(b)`. Used to prove vanishing of higher derivations
on finite-dimensional algebras in characteristic zero. -/
structure HigherDerivationSystem (k : Type w) [Field k] (A : Type w) [Ring A] [Algebra k A]
    (ε : A →ₐ[k] k) where
  χ : ℕ → (A →ₗ[k] k)
  χ_zero : χ 0 = ε.toLinearMap
  χ_mul : ∀ (n : ℕ) (a b : A),
    χ n (a * b) = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : k) * χ j a * χ (n - j) b

/-- Leibniz rule at level one: `χ_1` is an `ε`-twisted derivation. -/
theorem HigherDerivationSystem.χ_one_mul {k : Type w} [Field k] {A : Type w} [Ring A]
    [Algebra k A] {ε : A →ₐ[k] k} (hds : HigherDerivationSystem k A ε) (a b : A) :
    hds.χ 1 (a * b) = hds.χ 1 a * ε b + ε a * hds.χ 1 b := by
  have h := hds.χ_mul 1 a b
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
    zero_add] at h
  rw [hds.χ_zero] at h
  simp only [AlgHom.toLinearMap_apply] at h
  rw [h]; ring

namespace HigherDerivationSystem

variable {k : Type w} [Field k] {A : Type w} [Ring A] [Algebra k A]
variable {ε : A →ₐ[k] k} (hds : HigherDerivationSystem k A ε)

/-- The zeroth functional `χ 0` agrees with the augmentation `ε`. -/
lemma χ_apply_zero (a : A) : hds.χ 0 a = ε a := by rw [hds.χ_zero]; rfl

/-- `χ 1` vanishes on the unit of `A`. -/
lemma χ_one_one : hds.χ 1 1 = 0 := by
  have h := hds.χ_mul 1 1 1
  simp only [mul_one, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self, zero_add] at h
  rw [hds.χ_zero] at h
  simp only [AlgHom.toLinearMap_apply, map_one, one_mul, mul_one] at h
  have := sub_eq_zero.mpr h; simp at this; exact this

/-- `χ 1` vanishes on scalars from `k`. -/
lemma χ_one_algebraMap (r : k) : hds.χ 1 (algebraMap k A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul_of_tower, hds.χ_one_one, smul_zero]

/-- For `a` in the augmentation ideal, `χ_m (a^n) = 0` whenever `m < n`. -/
lemma χ_pow_vanish {a : A} (ha : ε a = 0) (m n : ℕ) (hmn : m < n) :
    hds.χ m (a ^ n) = 0 := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    rw [pow_succ', hds.χ_mul m a (a ^ n)]
    apply Finset.sum_eq_zero
    intro j hj; rw [Finset.mem_range] at hj
    by_cases hj0 : j = 0
    · subst hj0; simp [hds.χ_apply_zero, ha]
    · rw [ih (m - j) (by omega)]; ring

/-- For `a` in the augmentation ideal, `χ_n (a^n) = n! · (χ_1 a)^n`. -/
lemma χ_pow_diagonal {a : A} (ha : ε a = 0) (n : ℕ) :
    hds.χ n (a ^ n) = (n.factorial : k) * (hds.χ 1 a) ^ n := by
  induction n with
  | zero => simp [hds.χ_apply_zero, map_one]
  | succ n ih =>
    rw [pow_succ', hds.χ_mul (n + 1) a (a ^ n)]
    have hsum : ∀ j ∈ Finset.range (n + 2),
        ((n + 1).choose j : k) * hds.χ j a * hds.χ ((n + 1) - j) (a ^ n) =
        if j = 1 then (↑(n + 1) : k) * hds.χ 1 a * ((↑n.factorial : k) * (hds.χ 1 a) ^ n)
        else 0 := by
      intro j hj; rw [Finset.mem_range] at hj
      by_cases hj1 : j = 1
      · subst hj1; simp [Nat.choose_one_right, ih]
      · simp only [hj1, ite_false]
        by_cases hj0 : j = 0
        · subst hj0; simp [hds.χ_apply_zero, ha]
        · rw [hds.χ_pow_vanish ha _ n (by omega)]; ring
    rw [Finset.sum_congr rfl hsum, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    rw [if_pos (by omega : 1 < n + 2), Nat.factorial_succ, Nat.cast_mul, pow_succ]; ring

/-- In characteristic zero, any nontrivial polynomial relation `∑ g_j • a^j = 0` among the
powers of an augmentation-ideal element with `χ_1 a ≠ 0` forces all coefficients to vanish. -/
lemma coeff_zero_of_sum_pow_eq_zero [CharZero k]
    {a : A} (ha : ε a = 0) (hne : hds.χ 1 a ≠ 0)
    (s : Finset ℕ) (g : ℕ → k) (hzero : ∑ j ∈ s, g j • a ^ j = 0)
    (i : ℕ) (hi : i ∈ s) : g i = 0 := by
  suffices key : ∀ n, ∀ j ∈ s, j < n → g j = 0 by
    exact key (i + 1) i hi (Nat.lt_succ_iff.mpr le_rfl)
  intro n
  induction n with
  | zero => intro j _ hjn; omega
  | succ n ih =>
    intro j hj hjn
    by_cases hjn' : j < n
    · exact ih j hj hjn'
    · replace hjn : j = n := by omega
      subst hjn
      have heval : ∑ j' ∈ s, g j' • hds.χ j (a ^ j') = 0 := by
        have := congr_arg (hds.χ j) hzero
        simp only [map_sum, LinearMap.map_smul_of_tower, map_zero] at this; exact this
      rw [← Finset.add_sum_erase s _ hj] at heval
      have : ∑ j' ∈ s.erase j, g j' • hds.χ j (a ^ j') = 0 := by
        apply Finset.sum_eq_zero; intro j' hj'
        have hne' := Finset.ne_of_mem_erase hj'
        have hj'_mem := Finset.mem_of_mem_erase hj'
        by_cases hjlt' : j' < j
        · rw [ih j' hj'_mem hjlt', zero_smul]
        · rw [hds.χ_pow_vanish ha j j' (by omega), smul_zero]
      rw [this, add_zero, hds.χ_pow_diagonal ha, smul_eq_mul] at heval
      exact (mul_eq_zero.mp heval).resolve_right
        (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (pow_ne_zero _ hne))

/-- In characteristic zero, the powers of `a` are `k`-linearly independent whenever `a` lies
in the augmentation ideal and `χ_1 a ≠ 0`. -/
lemma powers_linearIndependent [CharZero k]
    {a : A} (ha : ε a = 0) (hne : hds.χ 1 a ≠ 0) :
    LinearIndependent k (fun n : ℕ => a ^ n) :=
  linearIndependent_iff'.mpr fun s g hsum i hi =>
    hds.coeff_zero_of_sum_pow_eq_zero ha hne s g hsum i hi

/-- Main vanishing theorem (used in the proof of Theorem 1.27.4): on a finite-dimensional
algebra in characteristic zero, the first higher derivation `χ 1` of any system is zero. -/
theorem higher_derivation_vanishes [CharZero k] [FiniteDimensional k A] :
    hds.χ 1 = 0 := by
  by_contra hne
  have hne' : ∃ a₀ : A, hds.χ 1 a₀ ≠ 0 := by
    by_contra h; push Not at h; exact hne (LinearMap.ext h)
  obtain ⟨a₀, ha₀⟩ := hne'
  set a := a₀ - algebraMap k A (ε a₀)
  have ha_ker : ε a = 0 := by
    show ε (a₀ - algebraMap k A (ε a₀)) = 0
    rw [map_sub, AlgHom.commutes]; exact sub_self _
  have hχ₁a : hds.χ 1 a ≠ 0 := by
    show hds.χ 1 (a₀ - algebraMap k A (ε a₀)) ≠ 0
    rw [map_sub, hds.χ_one_algebraMap, sub_zero]; exact ha₀

  have hli := hds.powers_linearIndependent ha_ker hχ₁a

  set N := Module.finrank k A + 1
  have hli_fin : LinearIndependent k ((fun n : ℕ => a ^ n) ∘ (Fin.val : Fin N → ℕ)) :=
    hli.comp Fin.val Fin.val_injective

  have hcard := hli_fin.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

end HigherDerivationSystem

/-- Typeclass packaging the vanishing of `χ 1` for every higher derivation system on every
finite-dimensional `k`-algebra, used as a hypothesis in higher-level results. -/
class HasHigherDerivationContradiction (k : Type w) [Field k] [CharZero k] : Prop where
  higher_derivation_vanishes :
    ∀ (A : Type w) [Ring A] [Algebra k A] [FiniteDimensional k A]
      (ε : A →ₐ[k] k) (hds : HigherDerivationSystem k A ε),
      hds.χ 1 = 0

/-- Any field of characteristic zero satisfies `HasHigherDerivationContradiction`, via the
vanishing theorem `higher_derivation_vanishes`. -/
instance instHasHigherDerivationContradiction (k : Type w) [Field k] [CharZero k] :
    HasHigherDerivationContradiction k where
  higher_derivation_vanishes := fun _ _ _ _ _ hds =>
    hds.higher_derivation_vanishes

end Ext1UnitVanishing

end TensorCategories
