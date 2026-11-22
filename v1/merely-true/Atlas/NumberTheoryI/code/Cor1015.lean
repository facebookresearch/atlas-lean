/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.ResidueFieldFunctor
import Atlas.NumberTheoryI.code.HenselFactorization
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section

open Polynomial IsLocalRing Ideal

instance Module.IsTorsionFree.of_noZeroSMulDivisors
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [NoZeroSMulDivisors A B] : Module.IsTorsionFree A B where
  isSMulRegular r hr a b hab := by
    have hsub : r • (a - b) = 0 := by rw [smul_sub, sub_eq_zero]; exact hab
    rcases NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hsub with hr0 | hab0
    · exfalso
      have : r ≠ 0 := by
        intro h; have := hr.left (show r * 1 = r * 0 by simp [h]); simp at this
      exact this hr0
    · exact sub_eq_zero.mp hab0

section Cor_10_15

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]

abbrev reducedMinpoly (α : B) : (ResidueField A)[X] :=
  (minpoly A α).map (residue A)

omit [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)] in
lemma minpoly_irreducible_of_dvr (α : B) :
    Irreducible (minpoly A α) :=
  (minpoly.prime_of_isIntegrallyClosed (IsIntegral.of_finite A α)).irreducible

omit [IsAdicComplete (maximalIdeal A) A] [Module.Finite A B] [NoZeroSMulDivisors A B] in
theorem residue_separable_of_irred_sep_reduction
    (α : B) (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
    (hirred : Irreducible (reducedMinpoly A B α))
    (hsep : (reducedMinpoly A B α).Separable) :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
  set k := ResidueField A
  set l := ResidueField B
  set abar := residue B α
  set gbar := reducedMinpoly A B α with hgbar_def

  have hne : minpoly A α ≠ 0 := by
    intro h
    have : gbar = 0 := by rw [hgbar_def, reducedMinpoly, h, Polynomial.map_zero]
    exact hirred.ne_zero this
  have hint : IsIntegral A α := minpoly.ne_zero_iff.mp hne

  have hres_top : Algebra.adjoin k ({abar} : Set l) = ⊤ := adjoin_residue_top_of_adjoin_top α hα

  have heval : Polynomial.aeval abar gbar = 0 := by
    show Polynomial.aeval (residue B α) ((minpoly A α).map (residue A)) = 0
    rw [← residue_aeval_eq]
    simp [minpoly.aeval]

  have hmon_gbar : gbar.Monic := (minpoly.monic hint).map (residue A)

  have heq : gbar = minpoly k abar := minpoly.eq_of_irreducible_of_monic hirred heval hmon_gbar

  have hsep_abar : IsSeparable k abar := by
    unfold IsSeparable
    rw [← heq]
    exact hsep

  have hmem : abar ∈ separableClosure k l :=
    mem_separableClosure_iff.mpr hsep_abar


  have hle : Algebra.adjoin k ({abar} : Set l) ≤
      (separableClosure k l).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem)

  have htop : separableClosure k l = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra]
    exact top_le_iff.mp (hres_top ▸ hle)
  rwa [separableClosure.eq_top_iff] at htop

omit [IsAdicComplete (maximalIdeal A) A] in

theorem finrank_eq_of_irred_reduction
    (α : B) (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
    (hirred : Irreducible (reducedMinpoly A B α)) :
    Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B) := by
  set k := ResidueField A
  set l := ResidueField B
  set abar := residue B α
  set gbar := reducedMinpoly A B α with hgbar_def

  have hint : IsIntegral A α := IsIntegral.of_finite A α
  have hmon := minpoly.monic hint

  have hmon_gbar : gbar.Monic := hmon.map (residue A)
  have heval : Polynomial.aeval abar gbar = 0 := by
    show Polynomial.aeval (residue B α) ((minpoly A α).map (residue A)) = 0
    rw [← residue_aeval_eq]; simp [minpoly.aeval]
  have hintk : IsIntegral k abar :=
    ⟨gbar, hmon_gbar, heval⟩
  have hres_top : Algebra.adjoin k ({abar} : Set l) = ⊤ := adjoin_residue_top_of_adjoin_top α hα

  have heq : gbar = minpoly k abar := minpoly.eq_of_irreducible_of_monic hirred heval hmon_gbar

  let pbA := PowerBasis.ofAdjoinEqTop' hint hα
  let pbk := PowerBasis.ofAdjoinEqTop' hintk hres_top

  calc Module.finrank A B
      = pbA.dim := pbA.finrank
    _ = (minpoly A α).natDegree := PowerBasis.ofAdjoinEqTop'_dim hint hα
    _ = gbar.natDegree := (hmon.natDegree_map (residue A)).symm
    _ = (minpoly k abar).natDegree := by rw [heq]
    _ = pbk.dim := (PowerBasis.ofAdjoinEqTop'_dim hintk hres_top).symm
    _ = Module.finrank k l := pbk.finrank.symm

omit [IsAdicComplete (maximalIdeal A) A] in
theorem reduced_minpoly_separable_of_separable_residue
    (α : B) (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B))
    (hdeg : Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B)) :
    (reducedMinpoly A B α).Separable := by
  set k := ResidueField A
  set l := ResidueField B
  set abar := residue B α
  set gbar := reducedMinpoly A B α with hgbar_def

  have hint : IsIntegral A α := IsIntegral.of_finite A α
  have hmon := minpoly.monic hint

  have hmon_gbar : gbar.Monic := hmon.map (residue A)

  have heval : Polynomial.aeval abar gbar = 0 := by
    show Polynomial.aeval (residue B α) ((minpoly A α).map (residue A)) = 0
    rw [← residue_aeval_eq]; simp [minpoly.aeval]

  have hintk : IsIntegral k abar := ⟨gbar, hmon_gbar, heval⟩

  have hres_top : Algebra.adjoin k ({abar} : Set l) = ⊤ := adjoin_residue_top_of_adjoin_top α hα

  have hdvd : minpoly k abar ∣ gbar := minpoly.dvd k abar heval

  have hdeg_gbar : gbar.natDegree = (minpoly A α).natDegree := hmon.natDegree_map (residue A)

  let pbA := PowerBasis.ofAdjoinEqTop' hint hα
  let pbk := PowerBasis.ofAdjoinEqTop' hintk hres_top
  have hfin_l : Module.finrank k l = (minpoly k abar).natDegree := by
    rw [pbk.finrank, PowerBasis.ofAdjoinEqTop'_dim]
  have hfin_A : Module.finrank A B = (minpoly A α).natDegree := by
    rw [pbA.finrank, PowerBasis.ofAdjoinEqTop'_dim]

  have hdeg_eq : gbar.natDegree = (minpoly k abar).natDegree := by
    rw [hdeg_gbar, ← hfin_A, hdeg, hfin_l]

  have heq : gbar = minpoly k abar :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintk) hmon_gbar hdvd
      (le_of_eq hdeg_eq)

  have hsep_abar : (minpoly k abar).Separable := Algebra.IsSeparable.isSeparable k abar

  rw [heq]; exact hsep_abar


set_option linter.unusedSectionVars false in
theorem cor_10_15_forward
    [IsUnramifiedDVRExtension A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)] :
    ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ ∧
      (reducedMinpoly A B α).Separable := by
  have hsep := IsUnramifiedDVRExtension.residue_separable (A := A) (B := B)
  have hdeg := IsUnramifiedDVRExtension.degree_eq (A := A) (B := B)
  obtain ⟨α, hα⟩ := dvr_monogenicity A B hsep
  exact ⟨α, hα, reduced_minpoly_separable_of_separable_residue A B α hα hsep hdeg⟩



end Cor_10_15

section Cor_10_16

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]

omit [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing B]
     [IsLocalHom (algebraMap A B)] [Module.Finite A B] in
theorem minpoly_reduction_separable
    {n : ℕ} {ζ : B} (hζ_int : IsIntegral A ζ) (hζ : ζ ^ n = 1)
    (hn : (n : ResidueField A) ≠ 0) :

    ((minpoly A ζ).map (residue A)).Separable := by

  haveI : IsIntegrallyClosed A := GCDMonoid.toIsIntegrallyClosed
  have hdvd : minpoly A ζ ∣ X ^ n - C 1 :=
    minpoly.isIntegrallyClosed_dvd hζ_int (by simp [hζ])

  have hdvd_bar : (minpoly A ζ).map (residue A) ∣
      (X ^ n - C 1 : A[X]).map (residue A) :=
    Polynomial.map_dvd _ hdvd

  have hmap : (X ^ n - C 1 : A[X]).map (residue A) = X ^ n - C 1 := by
    simp [Polynomial.map_sub, Polynomial.map_pow, map_X, map_one]
  rw [hmap] at hdvd_bar

  have hsep : (X ^ n - C (1 : ResidueField A)).Separable :=
    separable_X_pow_sub_C 1 hn one_ne_zero

  exact hsep.of_dvd hdvd_bar



end Cor_10_16

end
