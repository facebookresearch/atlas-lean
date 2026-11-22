/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.SeparableDegree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary

open Polynomial

namespace EtaleAlgebras

theorem separable_polynomial_def {K : Type*} [CommSemiring K] (f : K[X]) :
    f.Separable ↔ IsCoprime f (derivative f) :=
  Iff.rfl

theorem isSeparable_extension_def (F : Type*) (K : Type*) [CommRing F] [Ring K] [Algebra F K] :
    Algebra.IsSeparable F K ↔ ∀ x : K, IsSeparable F x :=
  Algebra.isSeparable_def F K

theorem irreducible_not_separable_iff_derivative_eq_zero {K : Type*} [Field K] {f : K[X]}
    (hf : Irreducible f) : ¬f.Separable ↔ derivative f = 0 := by
  constructor
  ·

    intro hinsep
    by_contra hf'
    apply hinsep

    apply EuclideanDomain.isCoprime_of_dvd
    · rintro ⟨-, h⟩; exact hf' h
    ·
      intro g hg_not_unit _ hg_dvd_f hg_dvd_f'

      obtain ⟨p, hp⟩ := hg_dvd_f
      rcases hf.isUnit_or_isUnit hp with hu | hu
      · exact hg_not_unit hu
      ·
        have hf_dvd_f' : f ∣ derivative f := by
          obtain ⟨u, rfl⟩ := hu
          exact dvd_trans (hp ▸ Units.mul_right_dvd.mpr dvd_rfl) hg_dvd_f'

        exact absurd (natDegree_le_of_dvd hf_dvd_f' hf')
          (not_le.mpr (natDegree_derivative_lt (mt derivative_of_natDegree_zero hf')))
  ·
    intro hf' hsep
    rw [Polynomial.Separable, hf'] at hsep
    exact hf.not_isUnit (isCoprime_zero_right.mp hsep)

end EtaleAlgebras

section Corollary_4_5

variable {K : Type*} [Field K]

theorem irreducible_eq_expand_separable
    {f : K[X]} (hf : Irreducible f) :
    ∃ (n : ℕ) (g : K[X]), Irreducible g ∧ g.Separable ∧
      expand K ((ringChar K) ^ n) g = f := by
  haveI hchar : CharP K (ringChar K) := ringChar.charP K
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  ·
    obtain ⟨n, g, hg_sep, hgf⟩ := exists_separable_of_irreducible (ringChar K) hf hp.ne_zero
    refine ⟨n, g, ?_, hg_sep, hgf⟩
    have hpos : 0 < (ringChar K) ^ n := pow_pos hp.pos n
    haveI := isLocalHom_expand K hpos
    exact Irreducible.of_map (f := expand K ((ringChar K) ^ n)) (by rwa [hgf])
  ·
    haveI : CharZero K := by rw [hp] at hchar; exact CharP.charP_to_charZero K
    rw [hp]
    exact ⟨0, f, hf, hf.separable, by simp [expand_one]⟩

end Corollary_4_5

section Corollary_4_6

theorem isSeparable_of_charZero_of_isAlgebraic
    (K : Type*) [Field K] [CharZero K]
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    Algebra.IsSeparable K L :=
  ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩

end Corollary_4_6

noncomputable section SimpleExtensionDegree

open IntermediateField Field

variable (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]

theorem algHom_card_eq_roots {α : L} (halg : IsAlgebraic K α) :
    finSepDegree K K⟮α⟯ = (minpoly K α).natSepDegree :=
  finSepDegree_adjoin_simple_eq_natSepDegree K L halg

theorem algHom_card_le_finrank {α : L} (halg : IsAlgebraic K α) :
    finSepDegree K K⟮α⟯ ≤ Module.finrank K K⟮α⟯ :=
  finSepDegree_adjoin_simple_le_finrank K L α halg

theorem algHom_card_eq_finrank_iff_separable {α : L} (halg : IsAlgebraic K α) :
    finSepDegree K K⟮α⟯ = Module.finrank K K⟮α⟯ ↔ IsSeparable K α :=
  finSepDegree_adjoin_simple_eq_finrank_iff K L α halg

theorem algHom_card_properties {α : L} (halg : IsAlgebraic K α) :
    finSepDegree K K⟮α⟯ = (minpoly K α).natSepDegree ∧
    finSepDegree K K⟮α⟯ ≤ Module.finrank K K⟮α⟯ ∧
    (finSepDegree K K⟮α⟯ = Module.finrank K K⟮α⟯ ↔ IsSeparable K α) :=
  ⟨algHom_card_eq_roots K L halg,
   algHom_card_le_finrank K L halg,
   algHom_card_eq_finrank_iff_separable K L halg⟩

theorem separable_degree_def : finSepDegree K L = Nat.card (Emb K L) := rfl

end SimpleExtensionDegree

noncomputable section Theorem_4_9

theorem exists_ringHom_extension_of_isAlgClosed
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed Ω]
    (φ_K : K →+* Ω) :
    ∃ φ_L : L →+* Ω, φ_L.comp (algebraMap K L) = φ_K := by
  letI : Algebra K Ω := φ_K.toAlgebra
  let φ_L : L →ₐ[K] Ω := IsAlgClosed.lift
  exact ⟨φ_L.toRingHom, by ext x; exact φ_L.commutes x⟩

end Theorem_4_9

noncomputable section

open IntermediateField

theorem mem_separableClosure_iff_isSeparable (K L : Type*) [Field K] [Field L] [Algebra K L] (x : L) :
    x ∈ separableClosure K L ↔ IsSeparable K x :=
  mem_separableClosure_iff

theorem algebraic_isSeparable_of_perfectField (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [PerfectField K] :
    Algebra.IsSeparable K L :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem perfectField_iff_frobenius_surjective (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    PerfectField K ↔ Function.Surjective (frobenius K p) := by
  haveI : ExpChar K p := ExpChar.prime (Fact.out)
  constructor
  · intro h
    haveI := PerfectField.toPerfectRing (K := K) p
    exact surjective_frobenius K p
  · intro h
    haveI := PerfectRing.ofSurjective K p h
    exact PerfectRing.toPerfectField K p

theorem finiteField_perfectField (K : Type*) [Field K] [Finite K] : PerfectField K :=
  PerfectField.ofFinite

theorem sepClosed_iff_splits_separable (K : Type*) [Field K] :
    IsSepClosed K ↔ ∀ f : K[X], f.Separable → f.Splits :=
  ⟨fun _ f hf => IsSepClosed.splits_of_separable f hf, fun h => ⟨h⟩⟩

theorem isPurelyInseparable_iff_finSepDegree (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IsPurelyInseparable K L ↔ Field.finSepDegree K L = 1 :=
  isPurelyInseparable_iff_finSepDegree_eq_one K L

end

open Field

noncomputable section

universe u v w

variable (K' : Type u) (F : Type v) (L : Type w)
  [Field K'] [Field F] [Field L]
  [Algebra K' F] [Algebra K' L] [Algebra F L] [IsScalarTower K' F L]

section Lemma_4_10

theorem hom_count_mul_tower [FiniteDimensional K' F] [FiniteDimensional F L] :
    finSepDegree K' F * finSepDegree F L = finSepDegree K' L := by
  haveI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  exact finSepDegree_mul_finSepDegree_of_isAlgebraic K' F L

end Lemma_4_10

section Corollary_4_11

theorem separable_degree_mul_tower [FiniteDimensional K' F] [FiniteDimensional F L] :
    finSepDegree K' F * finSepDegree F L = finSepDegree K' L :=
  hom_count_mul_tower K' F L

end Corollary_4_11

end

noncomputable section Inseparable_Decomposition

open Polynomial IntermediateField Field

theorem purelyInseparable_prime_degree_structure (K L : Type*) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsPurelyInseparable K L] [FiniteDimensional K L]
    (hdeg : Module.finrank K L = p) :
    ∃ (α : L) (a : K),
      minpoly K α = X ^ p - C a ∧
      (∀ b : K, b ^ p ≠ a) ∧
      K⟮α⟯ = ⊤ := by
  have hp : p.Prime := Fact.out

  have hne : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro h
    have : Module.finrank K L = 1 := by rw [← finrank_top', ← h, IntermediateField.finrank_bot]
    linarith [hp.one_lt]
  obtain ⟨α, -, hα_not_bot⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le hne)
  haveI : ExpChar K p := ExpChar.prime hp

  obtain ⟨n, a, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C K p α
  have hα_int : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hmin_deg : (minpoly K α).natDegree = p ^ n := by
    rw [hmin, natDegree_sub_C, natDegree_X_pow]

  have hdvd : p ^ n ∣ p := by
    have : Module.finrank K K⟮α⟯ ∣ Module.finrank K L :=
      ⟨Module.finrank (↥K⟮α⟯) L, (Module.finrank_mul_finrank K (↥K⟮α⟯) L).symm⟩
    rwa [adjoin.finrank hα_int, hmin_deg, hdeg] at this

  have hα_not_in_range : α ∉ Set.range (algebraMap K L) := by
    intro ⟨c, hc⟩
    exact hα_not_bot (IntermediateField.mem_bot.mpr ⟨c, hc⟩)
  have hdeg_gt1 : 1 < p ^ n := by
    by_contra h
    push Not at h
    have heq1 : p ^ n = 1 := le_antisymm h (Nat.one_le_pow n p hp.pos)
    exact hα_not_in_range (minpoly.natDegree_eq_one_iff.mp (hmin_deg.trans heq1))

  have hn : n = 1 := by
    rcases n with _ | m
    · simp at hdeg_gt1
    rcases m with _ | k
    · rfl
    exfalso
    have h1 : p * p ≤ p ^ (k + 2) := by
      calc p * p = p ^ 2 := (sq p).symm
      _ ≤ p ^ (k + 2) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ (k + 2) ≤ p := Nat.le_of_dvd hp.pos hdvd
    nlinarith [hp.two_le]
  subst hn; simp only [pow_one] at hmin ⊢

  have htop : K⟮α⟯ = ⊤ := by
    rw [primitive_element_iff_minpoly_natDegree_eq K α]
    rw [hmin, natDegree_sub_C, natDegree_X_pow, hdeg]

  have ha : ∀ b : K, b ^ p ≠ a := by
    intro b hb
    have hirr := minpoly.irreducible hα_int
    rw [hmin] at hirr
    have heq : X ^ p - C a = (X - C b) ^ p := by
      rw [sub_pow_expChar]
      congr 1
      rw [← hb, map_pow]
    rw [heq] at hirr
    exact not_irreducible_pow hp.ne_one hirr
  exact ⟨α, a, hmin, ha, htop⟩

theorem separableClosure_isPurelyInseparable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] :
    IsPurelyInseparable (separableClosure K L) L :=
  separableClosure.isPurelyInseparable K L

theorem separableClosure_decomposition (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] :
    Algebra.IsSeparable K (separableClosure K L) ∧
    IsPurelyInseparable (separableClosure K L) L ∧
    ∀ (F : IntermediateField K L),
      Algebra.IsSeparable K F → IsPurelyInseparable F L → F = separableClosure K L := by
  refine ⟨separableClosure.isSeparable K L, separableClosure.isPurelyInseparable K L, ?_⟩
  intro F hF_sep hF_insep
  exact @eq_separableClosure K L _ _ _ F hF_sep hF_insep

theorem finInsepDegree_eq_expChar_pow (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (q : ℕ) [ExpChar K q] :
    ∃ n : ℕ, finInsepDegree K L = q ^ n :=
  finInsepDegree_eq_pow K L q

end Inseparable_Decomposition

noncomputable section EtaleBaseChange

open scoped TensorProduct

theorem etale_base_change (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (L : Type*) [CommRing L] [Algebra K L] [Algebra.Etale K L] [Module.Finite K L] :
    Algebra.Etale K' (K' ⊗[K] L) := inferInstance

theorem etale_finite_base_change (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (L : Type*) [CommRing L] [Algebra K L] [Algebra.Etale K L] [Module.Finite K L] :
    Module.Finite K' (K' ⊗[K] L) := inferInstance

theorem etale_base_change_finrank_eq (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (L : Type*) [CommRing L] [Algebra K L] [Algebra.Etale K L] [Module.Finite K L] :
    Module.finrank K L = Module.finrank K' (K' ⊗[K] L) := by
  haveI : Module.Free K L := inferInstance
  exact (Module.finrank_baseChange (S := K) (R := K')).symm

theorem etale_base_change_bundle (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (L : Type*) [CommRing L] [Algebra K L] [Algebra.Etale K L] [Module.Finite K L] :
    Algebra.Etale K' (K' ⊗[K] L) ∧ Module.Finite K' (K' ⊗[K] L) ∧
    Module.finrank K L = Module.finrank K' (K' ⊗[K] L) :=
  ⟨etale_base_change K K' L, etale_finite_base_change K K' L, etale_base_change_finrank_eq K K' L⟩

theorem semisimple_iff_reduced (K : Type*) [Field K]
    (A : Type*) [CommRing A] [Algebra K A] [Module.Finite K A] :
    IsSemisimpleRing A ↔ IsReduced A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  constructor
  · intro _; infer_instance
  · intro _; exact IsArtinianRing.isSemisimpleRing_of_isReduced A

end EtaleBaseChange
