/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Atlas.NumberTheoryI.code.GlobalFields
import Atlas.NumberTheoryI.code.KrasnerLemma
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Atlas.NumberTheoryI.code.AdicCompletionAlgebra

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

theorem finrank_le_two_of_isReal_place
    {K : Type} [Field K] [NumberField K]
    {v : InfinitePlace K} (hv : InfinitePlace.IsReal v)
    (M : Type*) [Field M] [Algebra (InfinitePlace.Completion v) M]
    [FiniteDimensional (InfinitePlace.Completion v) M] :
    Module.finrank (InfinitePlace.Completion v) M ≤ 2 := by

  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  letI : Algebra ℝ M :=
    RingHom.toAlgebra ((algebraMap (InfinitePlace.Completion v) M).comp e.symm.toRingHom)

  have hcompat : (algebraMap ℝ M).comp e.toRingHom =
      (RingEquiv.refl M).toRingHom.comp (algebraMap (InfinitePlace.Completion v) M) := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.refl_apply,
      RingHom.coe_coe]
    show (algebraMap v.Completion M) (e.symm (e x)) = algebraMap v.Completion M x
    rw [e.symm_apply_apply]

  haveI : Module.Finite ℝ M := Module.Finite.of_equiv_equiv e (RingEquiv.refl M) hcompat
  haveI : Algebra.IsAlgebraic ℝ M := Algebra.IsAlgebraic.of_finite ℝ M

  have hfr : Module.finrank (InfinitePlace.Completion v) M = Module.finrank ℝ M :=
    Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl M) hcompat
  rw [hfr]

  rcases Real.nonempty_algEquiv_or M with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  ·
    have : Module.finrank ℝ M = Module.finrank ℝ ℝ := f.toLinearEquiv.finrank_eq
    rw [this, Module.finrank_self]; omega
  ·
    have : Module.finrank ℝ M = Module.finrank ℝ ℂ := f.toLinearEquiv.finrank_eq
    rw [this, Complex.finrank_real_complex]

theorem exists_degree_two_extension_above_real_place
    {K : Type} [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : InfinitePlace.IsReal v)
    (M : Type*) [Field M] [Algebra (InfinitePlace.Completion v) M]
    [FiniteDimensional (InfinitePlace.Completion v) M]
    [Algebra.IsSeparable (InfinitePlace.Completion v) M]
    (hfin : Module.finrank (InfinitePlace.Completion v) M = 2) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L)
      (w : InfinitePlace L)
      (_ : w.comap (algebraMap K L) = v),
      Module.finrank K L = 2
      ∧ ∃ (_ : Algebra (InfinitePlace.Completion v) (InfinitePlace.Completion w)),
          Nonempty (@AlgEquiv (InfinitePlace.Completion v) M
            (InfinitePlace.Completion w) _ _ _ _ ‹_›) := by

  let e_real := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let φ_real : K →+* ℝ := e_real.toRingHom.comp (algebraMap K (InfinitePlace.Completion v))

  set f := (Polynomial.X : Polynomial K)^2 + 1 with hf_def
  have h_eq_XC : f = Polynomial.X^2 + Polynomial.C 1 := by simp [hf_def]
  have hne : (Polynomial.X^2 + Polynomial.C (1 : K)) ≠ 0 :=
    (Polynomial.monic_X_pow_add_C (1 : K) two_ne_zero).ne_zero
  have hmonic : Polynomial.Monic f := by
    rw [h_eq_XC]; exact Polynomial.monic_X_pow_add_C 1 two_ne_zero
  have hirr : Irreducible f := by
    rw [show Irreducible f ↔ f.roots = 0 from
      Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [h_eq_XC, Polynomial.natDegree_X_pow_add_C])
        (by rw [h_eq_XC, Polynomial.natDegree_X_pow_add_C]; omega)]
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    rw [Polynomial.mem_roots (by rw [h_eq_XC]; exact hne)] at ha
    have heval : a ^ 2 + 1 = (0 : K) := by
      rw [Polynomial.IsRoot.def] at ha
      simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, hf_def] using ha
    have := congr_arg φ_real heval
    simp at this
    linarith [sq_nonneg (φ_real a)]

  haveI : Fact (Irreducible f) := ⟨hirr⟩
  haveI : CharZero (AdjoinRoot f) :=
    charZero_of_injective_algebraMap (algebraMap K (AdjoinRoot f)).injective
  haveI : Module.Finite K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  haveI : Module.Finite ℚ (AdjoinRoot f) := Module.Finite.trans K (AdjoinRoot f)
  haveI : NumberField (AdjoinRoot f) := NumberField.mk
  haveI : FiniteDimensional K (AdjoinRoot f) := inferInstance
  haveI : Algebra.IsIntegral K (AdjoinRoot f) := Algebra.IsIntegral.of_finite K (AdjoinRoot f)
  haveI : Algebra.IsSeparable K (AdjoinRoot f) :=
    Algebra.IsSeparable.of_integral K (AdjoinRoot f)

  let ψ : AdjoinRoot f →+* ℂ :=
    AdjoinRoot.lift v.embedding Complex.I (by
      simp [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one, Complex.I_sq, hf_def])

  let w : InfinitePlace (AdjoinRoot f) := InfinitePlace.mk ψ

  have hcomap : w.comap (algebraMap K (AdjoinRoot f)) = v := by
    show (InfinitePlace.mk ψ).comap (algebraMap K (AdjoinRoot f)) = v
    rw [InfinitePlace.comap_mk]
    have : ψ.comp (algebraMap K (AdjoinRoot f)) = v.embedding := by
      ext x; simp [ψ, AdjoinRoot.algebraMap_eq]
    rw [this, InfinitePlace.mk_embedding]

  have hfinrank : Module.finrank K (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank]
    show f.natDegree = 2
    conv_lhs => rw [h_eq_XC]
    exact Polynomial.natDegree_X_pow_add_C

  have hw_complex : w.IsComplex := by
    rw [InfinitePlace.not_isReal_iff_isComplex.symm, InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
    intro hreal
    have h1 := congr_fun (congr_arg DFunLike.coe hreal) (AdjoinRoot.root f)
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq] at h1
    rw [AdjoinRoot.lift_root,
        show (starRingEnd ℂ) Complex.I = -Complex.I from by simp [Complex.conj_I]] at h1
    have h3 : -Complex.I + Complex.I = Complex.I + Complex.I := congr_arg (· + Complex.I) h1
    rw [neg_add_cancel] at h3
    have := mul_eq_zero.mp (show (2 : ℂ) * Complex.I = 0 by rw [two_mul]; exact h3.symm)
    exact Complex.I_ne_zero (this.resolve_left (by norm_num))

  let e_w := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw_complex
  let alg_vw : Algebra v.Completion w.Completion :=
    RingHom.toAlgebra (e_w.symm.toRingHom.comp ((algebraMap ℝ ℂ).comp e_real.toRingHom))
  letI alg_RM : Algebra ℝ M :=
    RingHom.toAlgebra ((algebraMap v.Completion M).comp e_real.symm.toRingHom)
  letI alg_RW : Algebra ℝ w.Completion :=
    RingHom.toAlgebra (e_w.symm.toRingHom.comp (algebraMap ℝ ℂ))
  have hcompat_M : (algebraMap ℝ M).comp e_real.toRingHom =
      (RingEquiv.refl M).toRingHom.comp (algebraMap v.Completion M) := by
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.refl_apply,
      RingHom.coe_coe]
    show (algebraMap v.Completion M) (e_real.symm (e_real x)) = algebraMap v.Completion M x
    rw [e_real.symm_apply_apply]
  haveI : Module.Finite ℝ M := Module.Finite.of_equiv_equiv e_real (RingEquiv.refl M) hcompat_M
  haveI : Algebra.IsAlgebraic ℝ M := Algebra.IsAlgebraic.of_finite ℝ M
  have hfr : Module.finrank ℝ M = 2 := by
    rw [← hfin]
    exact (Algebra.finrank_eq_of_equiv_equiv e_real (RingEquiv.refl M) hcompat_M).symm

  refine ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, w, hcomap, hfinrank, alg_vw, ?_⟩

  rcases Real.nonempty_algEquiv_or M with ⟨⟨fR⟩⟩ | ⟨⟨fC⟩⟩
  ·
    exfalso
    have := fR.toLinearEquiv.finrank_eq
    rw [hfr, Module.finrank_self] at this; omega
  ·
    let ew_alg : ℂ ≃ₐ[ℝ] w.Completion := AlgEquiv.ofRingEquiv (f := e_w.symm) (fun _ => rfl)
    let f_RMW : M ≃ₐ[ℝ] w.Completion := fC.trans ew_alg
    have hf_compat : ∀ x : v.Completion,
        f_RMW.toRingEquiv ((algebraMap v.Completion M) x) =
        @algebraMap v.Completion w.Completion _ _ alg_vw x := by
      intro x
      have h1 : (algebraMap v.Completion M) x = @algebraMap ℝ M _ _ alg_RM (e_real x) := by
        show (algebraMap v.Completion M) x =
          (algebraMap v.Completion M) (e_real.symm (e_real x))
        rw [e_real.symm_apply_apply]
      rw [h1]
      show f_RMW (@algebraMap ℝ M _ _ alg_RM (e_real x)) =
        @algebraMap v.Completion w.Completion _ _ alg_vw x
      rw [f_RMW.commutes]
      rfl
    exact ⟨AlgEquiv.ofRingEquiv (f := f_RMW.toRingEquiv) hf_compat⟩

lemma finrank_eq_one_of_isAlgClosed (F E : Type*) [Field F] [Field E] [Algebra F E]
    [IsAlgClosed F] [FiniteDimensional F E] : Module.finrank F E = 1 := by
  have hsurj : Function.Surjective (algebraMap F E) := fun x =>
    minpoly.mem_range_of_degree_eq_one _ x
      (IsAlgClosed.degree_eq_one_of_irreducible _
        (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)))
  have hle : F ≃ₗ[F] E := LinearEquiv.ofBijective (Algebra.linearMap _ E)
    ⟨(algebraMap F E).injective, hsurj⟩
  rw [← Module.finrank_self (R := F)]; exact hle.finrank_eq.symm

def algEquivOfFinrankOne (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E = 1) : E ≃ₐ[F] F := by
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hsurj : Function.Surjective (algebraMap F E) := fun x => by
    have : x ∈ (⊤ : Subalgebra F E) := Algebra.mem_top; rwa [← htop] at this
  exact (AlgEquiv.ofBijective (Algebra.ofId F E) ⟨(algebraMap F E).injective, hsurj⟩).symm

theorem exists_heightOneSpectrum_above {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ w : HeightOneSpectrum (𝓞 L),
      w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  obtain ⟨Q, _, hQ_prime, hQ_comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 L)) (by simp)
  have hQ_ne : Q ≠ ⊥ := by
    intro h; rw [h] at hQ_comap; simp at hQ_comap; exact v.ne_bot hQ_comap.symm
  exact ⟨⟨Q, hQ_prime, hQ_ne⟩, hQ_comap⟩

open Polynomial Finset in
theorem exists_monic_approx_poly

    {K : Type*} [Field K] {K_v : Type*} [NontriviallyNormedField K_v] [Algebra K K_v]
    (hdense : DenseRange (algebraMap K K_v))
    (f : Polynomial K_v) (hf_monic : f.Monic) (hf_deg : 0 < f.natDegree)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : Polynomial K, g.Monic ∧ g.natDegree = f.natDegree ∧
      Polynomial.L1norm (normAbsVal K_v) (f - g.map (algebraMap K K_v)) < δ := by
  classical
  set n := f.natDegree with hn_def
  set ε := δ / (↑n + 1)
  have hε : (0 : ℝ) < ε := div_pos hδ (by positivity)
  have hn1 : (0 : ℝ) < ↑n + 1 := by positivity

  choose b hb using fun i : Fin n => hdense.exists_dist_lt (f.coeff i) hε

  set g : Polynomial K := X ^ n + ∑ i : Fin n, C (b i) * X ^ (i : ℕ)

  have hdeg_low : (∑ i : Fin n, C (b i) * X ^ (i : ℕ) : Polynomial K).degree < ↑n := by
    apply lt_of_le_of_lt (degree_sum_le _ _)
    apply (Finset.sup_lt_iff _).mpr
    · intro i _; exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)
    · exact WithBot.bot_lt_coe n
  have hg_monic : g.Monic := monic_X_pow_add hdeg_low
  have hg_natdeg : g.natDegree = n := by
    have : (∑ i : Fin n, C (b i) * X ^ (i : ℕ) : Polynomial K).degree <
        (X ^ n : Polynomial K).degree := by rwa [degree_X_pow]
    simp only [g, natDegree_add_eq_left_of_degree_lt this, natDegree_X_pow]
  refine ⟨g, hg_monic, hg_natdeg, ?_⟩

  set p := f - g.map (algebraMap K K_v)

  have hsupp : p.support ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_range]; by_contra h; push Not at h
    rw [mem_support_iff] at hi; apply hi
    show (f - g.map (algebraMap K K_v)).coeff i = 0
    rw [coeff_sub, coeff_map]
    rcases eq_or_lt_of_le h with rfl | hlt
    · rw [hf_monic.coeff_natDegree, show g.coeff n = 1 from hg_natdeg ▸ hg_monic.coeff_natDegree,
          map_one, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega),
          coeff_eq_zero_of_natDegree_lt (by omega), map_zero, sub_self]

  have hL1 : Polynomial.L1norm (normAbsVal K_v) p =
      ∑ i ∈ Finset.range n, normAbsVal K_v (p.coeff i) :=
    Finset.sum_subset hsupp (fun i _ hi => by
      rw [mem_support_iff, not_not] at hi; rw [hi, map_zero])

  have hg_coeff : ∀ i (hi : i < n), g.coeff i = b ⟨i, hi⟩ := by
    intro i hi
    simp only [g, coeff_add, coeff_X_pow, finset_sum_coeff, coeff_C_mul_X_pow,
      if_neg (Nat.ne_of_lt hi), zero_add]
    rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro j _ hj
      simp [show i ≠ (j : ℕ) from fun h => hj (Fin.ext (h ▸ rfl))]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hcoeff : ∀ i (hi : i < n),
      p.coeff i = f.coeff i - algebraMap K K_v (b ⟨i, hi⟩) := by
    intro i hi
    show (f - g.map (algebraMap K K_v)).coeff i = _
    rw [coeff_sub, coeff_map, hg_coeff i hi]

  rw [hL1]
  calc ∑ i ∈ Finset.range n, normAbsVal K_v (p.coeff i)
      < ∑ _ ∈ Finset.range n, ε := by
        apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
        intro i hi; rw [Finset.mem_range] at hi
        rw [hcoeff i hi]
        show ‖f.coeff i - algebraMap K K_v (b ⟨i, hi⟩)‖ < ε
        rw [← dist_eq_norm]; exact hb ⟨i, hi⟩
    _ = ↑n * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ < δ := by
        calc ↑n * (δ / (↑n + 1)) = δ * (↑n / (↑n + 1)) := by ring
          _ < δ * 1 := by
              apply mul_lt_mul_of_pos_left _ hδ
              rw [div_lt_one hn1]; linarith
          _ = δ := mul_one δ

theorem krasner_irreducible
    {K_v : Type*} [NontriviallyNormedField K_v] [IsUltrametricDist K_v] [CompleteSpace K_v]
    (f g : Polynomial K_v)
    (hf_monic : f.Monic) (hf_irr : Irreducible f) (hf_sep : f.Separable)
    (hg_monic : g.Monic) (hg_deg : g.natDegree = f.natDegree)
    (hclose : ∃ δ : ℝ, 0 < δ ∧
      Polynomial.L1norm (normAbsVal K_v) (f - g) < δ ∧
      ∀ g' : Polynomial K_v, g'.Monic → g'.natDegree = f.natDegree →
        Polynomial.L1norm (normAbsVal K_v) (f - g') < δ →
        ∀ β : AlgebraicClosure K_v, Polynomial.aeval β g' = 0 →
          ∃ α : AlgebraicClosure K_v, Polynomial.aeval α f = 0 ∧
            IntermediateField.adjoin K_v {α} = IntermediateField.adjoin K_v {β}) :
    Irreducible g := by
  obtain ⟨δ, _, hfg_close, hδ_approx⟩ := hclose

  have hg_deg_pos : 0 < g.natDegree := hg_deg ▸ hf_irr.natDegree_pos
  have hg_deg_ne : g.degree ≠ 0 :=
    ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hg_deg_pos)

  obtain ⟨β, hβ⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K_v) g hg_deg_ne

  obtain ⟨α, hα_root, hfield_eq⟩ :=
    hδ_approx g hg_monic hg_deg hfg_close β hβ

  have hα_int : IsIntegral K_v α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral

  have hmin_α_eq_f : minpoly K_v α = f := by
    have hmin_dvd : minpoly K_v α ∣ f := minpoly.dvd K_v α hα_root
    exact Polynomial.eq_of_monic_of_associated (minpoly.monic hα_int) hf_monic
      ((minpoly.irreducible hα_int).associated_of_dvd hf_irr hmin_dvd)

  have hβ_int : IsIntegral K_v β := (Algebra.IsAlgebraic.isAlgebraic β).isIntegral

  have hmin_dvd_g : minpoly K_v β ∣ g := minpoly.dvd K_v β hβ

  open IntermediateField in
  have hfinrank_eq : Module.finrank K_v K_v⟮α⟯ = Module.finrank K_v K_v⟮β⟯ := by
    have : K_v⟮α⟯.toSubalgebra = K_v⟮β⟯.toSubalgebra := congrArg toSubalgebra hfield_eq
    exact LinearEquiv.finrank_eq (Subalgebra.equivOfEq _ _ this).toLinearEquiv
  open IntermediateField in
  have hdeg_min_β : (minpoly K_v β).natDegree = f.natDegree := by
    have h1 := adjoin.finrank hα_int
    have h2 := adjoin.finrank hβ_int
    rw [hmin_α_eq_f] at h1
    omega

  have hg_eq : g = minpoly K_v β :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ_int) hg_monic
      hmin_dvd_g (by omega)

  rw [hg_eq]
  exact minpoly.irreducible hβ_int

theorem algEquiv_adjoinRoot_of_root
    (F : Type*) [Field F]
    (g : Polynomial F) (hg_irr : Irreducible g) (hg_monic : g.Monic)
    (M : Type*) [Field M] [Algebra F M]
    [FiniteDimensional F M]
    (hM_deg : Module.finrank F M = g.natDegree)
    (α : M) (hα : Polynomial.aeval α g = 0) :
    Nonempty (M ≃ₐ[F] AdjoinRoot g) := by
  haveI : Fact (Irreducible g) := ⟨hg_irr⟩

  have hα' : Polynomial.eval₂ (algebraMap F M) α g = 0 := by
    rwa [Polynomial.aeval_def] at hα
  let hlift : AdjoinRoot g →ₐ[F] M := AdjoinRoot.liftAlgHom g (Algebra.ofId F M) α hα'

  have hinj : Function.Injective hlift := RingHom.injective hlift.toRingHom

  have hfr : Module.finrank F (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg_monic).finrank]; rfl

  haveI : FiniteDimensional F (AdjoinRoot g) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Irreducible.natDegree_pos hg_irr)

  have hdim : Module.finrank F (AdjoinRoot g) = Module.finrank F M := by
    rw [hfr, hM_deg]

  have hsurj : Function.Surjective hlift :=
    (hlift.toLinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨(AlgEquiv.ofBijective hlift ⟨hinj, hsurj⟩).symm⟩

theorem adjoinRoot_equiv_of_intermediateField_eq
    (K : Type*) [Field K] (E : Type*) [Field E] [Algebra K E]
    (p q : Polynomial K) (hp_irr : Irreducible p) (hp_monic : p.Monic)
    (hq_irr : Irreducible q) (hq_monic : q.Monic)
    (α β : E) (hα : Polynomial.aeval α p = 0) (hβ : Polynomial.aeval β q = 0)
    (heq : IntermediateField.adjoin K {α} = IntermediateField.adjoin K {β}) :
    Nonempty (AdjoinRoot p ≃ₐ[K] AdjoinRoot q) := by
  have hα_int : IsIntegral K α := ⟨p, hp_monic, hα⟩
  have hβ_int : IsIntegral K β := ⟨q, hq_monic, hβ⟩
  have hminα : minpoly K α = p :=
    (minpoly.eq_of_irreducible_of_monic hp_irr hα hp_monic).symm
  have hminβ : minpoly K β = q :=
    (minpoly.eq_of_irreducible_of_monic hq_irr hβ hq_monic).symm
  have e1 : AdjoinRoot p ≃ₐ[K] ↥(IntermediateField.adjoin K {α}) := by
    rw [← hminα]; exact IntermediateField.adjoinRootEquivAdjoin K hα_int
  have e2 : ↥(IntermediateField.adjoin K {α}) ≃ₐ[K] ↥(IntermediateField.adjoin K {β}) :=
    IntermediateField.equivOfEq heq
  have e3 : ↥(IntermediateField.adjoin K {β}) ≃ₐ[K] AdjoinRoot q := by
    rw [← hminβ]; exact (IntermediateField.adjoinRootEquivAdjoin K hβ_int).symm
  exact ⟨e1.trans (e2.trans e3)⟩








theorem separableExtension_isCompletion_infinitePlace
    {K : Type} [Field K] [NumberField K]
    (v : InfinitePlace K)
    (M : Type*) [Field M] [Algebra (InfinitePlace.Completion v) M]
    [FiniteDimensional (InfinitePlace.Completion v) M]
    [Algebra.IsSeparable (InfinitePlace.Completion v) M] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : Algebra.IsSeparable K L) (_ : FiniteDimensional K L)
      (w : InfinitePlace L)
      (_ : w.comap (algebraMap K L) = v),
      Module.finrank K L =
        Module.finrank (InfinitePlace.Completion v) M
      ∧ ∃ (_ : Algebra (InfinitePlace.Completion v) (InfinitePlace.Completion w)),
          Nonempty (@AlgEquiv (InfinitePlace.Completion v) M
            (InfinitePlace.Completion w) _ _ _ _ ‹_›) := by

  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  ·
    have hle := finrank_le_two_of_isReal_place hv M
    have hpos : 0 < Module.finrank (InfinitePlace.Completion v) M := Module.finrank_pos
    by_cases h1 : Module.finrank (InfinitePlace.Completion v) M = 1
    ·
      refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        v, rfl, ?_, inferInstance, ?_⟩
      · rw [h1]; exact Module.finrank_self K
      · exact ⟨algEquivOfFinrankOne _ _ h1⟩
    ·
      have h2 : Module.finrank (InfinitePlace.Completion v) M = 2 := by omega
      obtain ⟨L, hL1, hL2, hL3, hL4, hL5, w, hw, hfin, halg, hiso⟩ :=
        exists_degree_two_extension_above_real_place v hv M h2
      exact ⟨L, hL1, hL2, hL3, hL4, hL5, w, hw, by rw [hfin, h2], halg, hiso⟩
  ·

    haveI : IsAlgClosed (InfinitePlace.Completion v) :=
      IsAlgClosed.of_ringEquiv _ _
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
    have h1 := finrank_eq_one_of_isAlgClosed (InfinitePlace.Completion v) M
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      v, rfl, ?_, inferInstance, ?_⟩
    · rw [h1]; exact Module.finrank_self K
    · exact ⟨algEquivOfFinrankOne _ _ h1⟩









lemma algEquiv_eq_refl_of_finrank_one {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E = 1) (e : E ≃ₐ[F] E) :
    e = AlgEquiv.refl := by
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h
  ext x
  have hx : x ∈ (⊤ : Subalgebra F E) := Algebra.mem_top
  rw [← htop] at hx
  obtain ⟨y, rfl⟩ := hx
  simp [AlgEquiv.commutes]

def galoisGroupMulEquivTrivial (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] (h : Module.finrank F E = 1) :
    MulEquiv (K ≃ₐ[K] K) (E ≃ₐ[F] E) where
  toFun _ := AlgEquiv.refl
  invFun _ := AlgEquiv.refl
  left_inv e := by ext x; exact (AlgEquiv.commutes e x).symm
  right_inv e := (algEquiv_eq_refl_of_finrank_one h e).symm
  map_mul' _ _ := by symm; exact algEquiv_eq_refl_of_finrank_one h _

theorem galoisExtension_isCompletion_infinitePlace
    {K : Type} [Field K] [NumberField K]
    (v : InfinitePlace K)
    (M : Type*) [Field M] [Algebra (InfinitePlace.Completion v) M]
    [FiniteDimensional (InfinitePlace.Completion v) M]
    [IsGalois (InfinitePlace.Completion v) M] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : IsGalois K L) (_ : FiniteDimensional K L)
      (w : InfinitePlace L)
      (_ : w.comap (algebraMap K L) = v),
      (∃ (_ : Algebra (InfinitePlace.Completion v) (InfinitePlace.Completion w)),
          Nonempty (@AlgEquiv (InfinitePlace.Completion v) M
            (InfinitePlace.Completion w) _ _ _ _ ‹_›))
      ∧ Nonempty (MulEquiv (L ≃ₐ[K] L)
          (M ≃ₐ[InfinitePlace.Completion v] M)) := by

  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  ·
    have hle := finrank_le_two_of_isReal_place hv M
    have hpos : 0 < Module.finrank (InfinitePlace.Completion v) M := Module.finrank_pos
    by_cases h1 : Module.finrank (InfinitePlace.Completion v) M = 1
    ·

      refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        v, rfl, ?_, ?_⟩
      · exact ⟨inferInstance, ⟨algEquivOfFinrankOne _ _ h1⟩⟩
      · exact ⟨galoisGroupMulEquivTrivial K _ _ h1⟩
    ·


      have h2 : Module.finrank (InfinitePlace.Completion v) M = 2 := by omega

      haveI : Algebra.IsSeparable (InfinitePlace.Completion v) M := inferInstance
      obtain ⟨L, hFL, hNF, hAlg, hSep, hFD, w, hw, hfin, halg, hiso⟩ :=
        exists_degree_two_extension_above_real_place v hv M h2

      letI := hFL; letI := hNF; letI := hAlg; letI := hSep; letI := hFD


      haveI : Algebra.IsQuadraticExtension K L := ⟨hfin⟩
      haveI : IsGalois K L := inferInstance
      refine ⟨L, hFL, hNF, hAlg, inferInstance, hFD, w, hw, ?_, ?_⟩

      · exact ⟨halg, hiso⟩

      · haveI : Fact (Nat.Prime 2) := Fact.mk (by decide)
        exact ⟨mulEquivOfPrimeCardEq
          ((IsGalois.card_aut_eq_finrank K L).trans hfin)
          ((IsGalois.card_aut_eq_finrank _ M).trans h2)⟩
  ·

    haveI : IsAlgClosed (InfinitePlace.Completion v) :=
      IsAlgClosed.of_ringEquiv _ _
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
    have h1 := finrank_eq_one_of_isAlgClosed (InfinitePlace.Completion v) M
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      v, rfl, ?_, ?_⟩
    · exact ⟨inferInstance, ⟨algEquivOfFinrankOne _ _ h1⟩⟩
    · exact ⟨galoisGroupMulEquivTrivial K _ _ h1⟩


section NormTraceCompletion

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

noncomputable def commKvAlgEquiv (v : HeightOneSpectrum (𝓞 K)) :
    letI := @Algebra.TensorProduct.rightAlgebra K L (v.adicCompletion K) _ _ _ _ _
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K) := by
  letI := @Algebra.TensorProduct.rightAlgebra K L (v.adicCompletion K) _ _ _ _ _
  exact @AlgEquiv.ofRingEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    inferInstance
    Algebra.TensorProduct.rightAlgebra
    (f := (Algebra.TensorProduct.comm K (v.adicCompletion K) L).toRingEquiv)
    (fun r => by
      simp [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.right_algebraMap_apply])

lemma norm_baseChange_eq
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
    @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.norm_apply K α, ← LinearMap.det_baseChange (Algebra.lmul K L α),
      Algebra.baseChange_lmul, ← Algebra.norm_apply (v.adicCompletion K)
        ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : commKvAlgEquiv v ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
    simp [commKvAlgEquiv, AlgEquiv.ofRingEquiv, Algebra.TensorProduct.comm_tmul]
  rw [← h]
  exact (@Algebra.norm_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra (commKvAlgEquiv v)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

lemma trace_baseChange_eq
    (v : HeightOneSpectrum (𝓞 K))
    (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
    @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.trace_apply K α,
      ← LinearMap.trace_baseChange (Algebra.lmul K L α) (v.adicCompletion K),
      Algebra.baseChange_lmul,
      ← Algebra.trace_apply (v.adicCompletion K) ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : commKvAlgEquiv v ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
    simp [commKvAlgEquiv, AlgEquiv.ofRingEquiv, Algebra.TensorProduct.comm_tmul]
  rw [← h]
  exact (@Algebra.trace_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra (commKvAlgEquiv v)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

def finSuccLinearEquiv' (R : Type*) [CommRing R] {n : ℕ} (A : Fin (n + 1) → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    (∀ i : Fin (n + 1), A i) ≃ₗ[R] A 0 × (∀ i : Fin n, A (Fin.succ i)) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by ext i; exact congr_fun (Fin.cons_self_tail f) i
  right_inv p := by
    ext
    · exact Fin.cons_zero p.1 p.2
    · exact Fin.cons_succ p.1 p.2 _
  map_add' f g := by ext <;> rfl
  map_smul' r f := by ext <;> rfl

lemma norm_pi_fin' {R : Type*} [CommRing R]
    {n : ℕ} {A : Fin n → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    Algebra.norm R f = ∏ i, Algebra.norm R (f i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact (congr_arg _ (Subsingleton.elim f 1)).trans (map_one _)
  | succ n ih =>
    let e := finSuccLinearEquiv' R A
    have step1 : Algebra.norm R f =
        LinearMap.det (e.toLinearMap ∘ₗ (Algebra.lmul R _ f) ∘ₗ e.symm.toLinearMap) := by
      rw [LinearMap.det_conj, Algebra.norm_apply]
    have hmul : e.toLinearMap ∘ₗ (Algebra.lmul R _ f) ∘ₗ e.symm.toLinearMap =
        ((Algebra.lmul R (A 0)) (f 0)).prodMap ((Algebra.lmul R _) (Fin.tail f)) := by
      apply LinearMap.ext; intro ⟨a, g⟩
      show e (f * e.symm (a, g)) = (f 0 * a, Fin.tail f * g)
      simp only [e, finSuccLinearEquiv', LinearEquiv.coe_mk]
      ext
      · simp [Pi.mul_apply, Fin.cons_zero]
      · simp [Pi.mul_apply, Fin.tail, Fin.cons_succ]
    rw [step1, hmul, LinearMap.det_prodMap, ← Algebra.norm_apply, ← Algebra.norm_apply,
        ih (Fin.tail f), Fin.prod_univ_succ]
    simp only [Fin.tail]

theorem Algebra.norm_pi_apply' {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    (Algebra.norm R) f = ∏ i, (Algebra.norm R) (f i) := by
  classical
  let e := Fintype.equivFin ι
  let φ := AlgEquiv.piCongrLeft R A e.symm
  have h1 : Algebra.norm R f = Algebra.norm R (φ.symm f) := by
    conv_lhs => rw [← φ.apply_symm_apply f]
    exact Algebra.norm_eq_of_algEquiv φ (φ.symm f)
  rw [h1, norm_pi_fin' (φ.symm f)]
  exact Fintype.prod_equiv e.symm _ _ (fun j => by congr 1)

lemma algEquiv_tmul_one_component
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L))
    (e : @AlgEquiv (v.adicCompletion K)
      (L ⊗[K] v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L)
      _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _))
    (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α)
    (α : L)
    (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) :
    e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α :=
  he α w

lemma norm_pi_eq_prod
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L))
    (e : @AlgEquiv (v.adicCompletion K)
      (L ⊗[K] v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L)
      _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _))
    (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α)
    (α : L) :
    @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) =
    ∏ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Algebra.norm (v.adicCompletion K) (w.val.adicCompletion L) _ _ (localAlg w)
        (algebraMap L (w.val.adicCompletion L) α) := by
  classical


  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w =>
    @Module.Free.of_divisionRing (v.adicCompletion K) (w.val.adicCompletion L)
      inferInstance inferInstance (localAlg w).toModule
  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Finite (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w => by
    letI := localAlg w

    letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite (v.adicCompletion K)
        (v.adicCompletion K ⊗[K] L) := Module.Finite.base_change K _ L
    haveI : Module.Finite (v.adicCompletion K)
        ((w' : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
          w'.val.adicCompletion L) :=
      Module.Finite.equiv ((commKvAlgEquiv v).trans e).toLinearEquiv
    exact Module.Finite.of_surjective
      (@LinearMap.proj (v.adicCompletion K) _ _
        (fun w' => w'.val.adicCompletion L) _ (fun w' => (localAlg w').toModule) w)
      (LinearMap.proj_surjective w)


  letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
    Algebra.TensorProduct.rightAlgebra
  rw [← Algebra.norm_eq_of_algEquiv e (α ⊗ₜ[K] 1)]

  rw [Algebra.norm_pi_apply' (e (α ⊗ₜ[K] 1))]

  congr 1; ext w; congr 1
  exact algEquiv_tmul_one_component v localAlg e he α w

lemma trace_single_comp_aux {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (j : ι) (f : A j →ₗ[R] A j) :
    (LinearMap.trace R (∀ i, A i)) ((LinearMap.single R A j) ∘ₗ (f ∘ₗ (LinearMap.proj j))) =
    (LinearMap.trace R (A j)) f := by
  rw [LinearMap.trace_comp_comm' (f ∘ₗ LinearMap.proj j) (LinearMap.single R A j)]
  congr 1; ext x
  simp [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]

lemma pi_lmul_decomp_aux {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (f : ∀ i, A i) :
    (Algebra.lmul R (∀ i, A i) f) =
    ∑ i : ι, (LinearMap.single R A i).comp
      ((Algebra.lmul R (A i) (f i)).comp (LinearMap.proj i)) := by
  apply LinearMap.ext; intro x; funext k
  simp only [LinearMap.comp_apply, LinearMap.proj_apply,
             LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single k (fun b _ hbk => ?_) (fun hk => ?_)]
  · simp [LinearMap.single_apply]
  · simp [LinearMap.single_apply, hbk]
  · exact absurd (Finset.mem_univ k) hk

theorem Algebra.trace_pi_apply' {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    (Algebra.trace R (∀ i, A i)) f = ∑ i, (Algebra.trace R (A i)) (f i) := by
  simp only [Algebra.trace_apply]
  rw [pi_lmul_decomp_aux f, map_sum]
  congr 1; ext i; exact trace_single_comp_aux i _

lemma trace_pi_eq_sum
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
    (localAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      Algebra (v.adicCompletion K) (w.val.adicCompletion L))
    (e : @AlgEquiv (v.adicCompletion K)
      (L ⊗[K] v.adicCompletion K)
      ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
        w.val.adicCompletion L)
      _ _ _ Algebra.TensorProduct.rightAlgebra (Pi.algebra _ _))
    (he : ∀ (α : L) (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
      e (α ⊗ₜ[K] (1 : v.adicCompletion K)) w = algebraMap L (w.val.adicCompletion L) α)
    (α : L) :
    @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
      Algebra.TensorProduct.rightAlgebra
      (α ⊗ₜ[K] (1 : v.adicCompletion K)) =
    ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Algebra.trace (v.adicCompletion K) (w.val.adicCompletion L) _ _ (localAlg w)
        (algebraMap L (w.val.adicCompletion L) α) := by
  classical

  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w =>
    @Module.Free.of_divisionRing (v.adicCompletion K) (w.val.adicCompletion L)
      inferInstance inferInstance (localAlg w).toModule
  haveI : ∀ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      @Module.Finite (v.adicCompletion K) (w.val.adicCompletion L) _ _
        (localAlg w).toModule := fun w => by
    letI := localAlg w

    letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite (v.adicCompletion K)
        (v.adicCompletion K ⊗[K] L) := Module.Finite.base_change K _ L
    haveI : Module.Finite (v.adicCompletion K)
        ((w' : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
          w'.val.adicCompletion L) :=
      Module.Finite.equiv ((commKvAlgEquiv v).trans e).toLinearEquiv
    exact Module.Finite.of_surjective
      (@LinearMap.proj (v.adicCompletion K) _ _
        (fun w' => w'.val.adicCompletion L) _ (fun w' => (localAlg w').toModule) w)
      (LinearMap.proj_surjective w)


  letI : Algebra (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
    Algebra.TensorProduct.rightAlgebra
  rw [← Algebra.trace_eq_of_algEquiv e (α ⊗ₜ[K] 1)]

  rw [Algebra.trace_pi_apply' (e (α ⊗ₜ[K] 1))]

  congr 1; ext w; congr 1
  exact algEquiv_tmul_one_component v localAlg e he α w




end NormTraceCompletion



section NormTraceCompletionAliases

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]


end NormTraceCompletionAliases

end
