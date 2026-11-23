/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.NoetherNormalization
import Atlas.AlgebraicGeometryI.code.NakayamaApplications

noncomputable section

open MvPolynomial

section NakayamaForFields

/-- Nakayama step: if A is a finite injective extension of B as a B-module via f and I
is a proper ideal of B, then IA is a proper B-submodule of A. -/
lemma nakayama_proper_ideal_stays_proper
    {B : Type*} [CommRing B] {A : Type*} [Field A]
    (f : B →+* A) (hf_inj : Function.Injective f) (hf_fin : f.Finite)
    (I : Ideal B) (hI : I ≠ ⊤) :
    letI : Algebra B A := f.toAlgebra
    I • (⊤ : Submodule B A) ≠ ⊤ := by
  letI : Algebra B A := f.toAlgebra
  have : Module.Finite B A := hf_fin
  intro h_eq

  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    I ⊤ Module.Finite.fg_top (ge_of_eq h_eq)

  have hr_zero : f r = 0 := by
    have := hr2 1 Submodule.mem_top
    simp [Algebra.smul_def] at this
    exact this

  have hr_eq : r = 0 := hf_inj (by simp [hr_zero])

  rw [hr_eq] at hr1
  have : (1 : B) ∈ I := by
    have h : (-1 : B) ∈ I := by simpa using hr1
    simpa using I.neg_mem h

  exact hI (I.eq_top_iff_one.mpr this)

end NakayamaForFields

section FieldPropagation

/-- Field propagation: if a domain B injects into a field A via a finite ring map, then
B itself is a field. -/
lemma isField_of_injective_finite_of_isField
    {B : Type*} [CommRing B] {A : Type*} [Field A]
    (f : B →+* A) (hf_inj : Function.Injective f) (hf_fin : f.Finite) :
    IsField B := by
  letI : Algebra B A := f.toAlgebra
  have _hfin : Module.Finite B A := hf_fin
  haveI _hnt : Nontrivial B := f.domain_nontrivial

  by_contra h_not_field
  rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top] at h_not_field
  obtain ⟨I, hI_bot, hI_top⟩ := h_not_field
  have hI_ne_top : I ≠ ⊤ := ne_top_of_lt hI_top
  have hI_ne_bot : I ≠ ⊥ := ne_bot_of_gt hI_bot

  have hIA := nakayama_proper_ideal_stays_proper f hf_inj hf_fin I hI_ne_top

  apply hIA
  rw [eq_top_iff]
  intro a _

  obtain ⟨b, hbI, hb⟩ : ∃ b ∈ I, b ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hI_ne_bot ((Submodule.eq_bot_iff I).mpr fun x hx => h' x hx)

  have hfb : f b ≠ 0 := fun h => hb (hf_inj (by simp [h]))

  rw [show a = f b * ((f b)⁻¹ * a) by field_simp]
  exact Submodule.smul_mem_smul hbI Submodule.mem_top

end FieldPropagation

section ZariskiLemmaTextbook

/-- A polynomial ring k[x_1,...,x_{n+1}] with at least one variable is never a field. -/
lemma mvPolynomial_fin_succ_not_isField (k : Type*) [Field k] (n : ℕ) :
    ¬ IsField (MvPolynomial (Fin (n + 1)) k) := by
  intro h
  exact Polynomial.not_isField _
    ((finSuccEquiv k n).toRingEquiv.symm.toMulEquiv.isField h)

/-- Zariski's lemma, proved by chaining Noether normalization with the Nakayama field
propagation: any finitely generated k-algebra that is a field is algebraic over k. -/
theorem zariski_lemma_textbook_proof
    (k A : Type*) [Field k] [Field A] [Algebra k A]
    [Algebra.FiniteType k A] : Algebra.IsAlgebraic k A := by

  obtain ⟨d, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k A

  have hB_field := isField_of_injective_finite_of_isField g.toRingHom hg_inj hg_fin

  have hd_zero : d = 0 := by
    by_contra hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := Nat.exists_eq_succ_of_ne_zero hd
    exact mvPolynomial_fin_succ_not_isField k d' hB_field

  subst hd_zero
  have : Module.Finite k A := by

    letI : Algebra (MvPolynomial (Fin 0) k) A := g.toRingHom.toAlgebra
    haveI : IsScalarTower k (MvPolynomial (Fin 0) k) A := by
      constructor
      intro x b a
      show g (x • b) * a = x • (g b * a)
      simp [Algebra.smul_def, map_mul, mul_assoc]
    haveI : Module.Finite (MvPolynomial (Fin 0) k) A := hg_fin

    haveI : Module.Finite k (MvPolynomial (Fin 0) k) :=
      Module.Finite.of_surjective (isEmptyAlgEquiv k (Fin 0)).symm.toLinearMap
        (isEmptyAlgEquiv k (Fin 0)).symm.surjective

    exact Module.Finite.trans (MvPolynomial (Fin 0) k) A
  exact Algebra.IsAlgebraic.of_finite k A

end ZariskiLemmaTextbook

end
