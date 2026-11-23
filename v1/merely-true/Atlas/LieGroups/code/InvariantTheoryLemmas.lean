/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ChevalleyRestriction
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.GoingUp

set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

section ReynoldsOperator

variable {k : Type*} [Field k] [CharZero k]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def reynoldsOperator :
    MvPolynomial ι k →ₗ[k] MvPolynomial ι k where
  toFun h := (Fintype.card G : k)⁻¹ • Finset.univ.sum fun g => (algAct g) h
  map_add' x y := by
    simp only [map_add, Finset.sum_add_distrib, smul_add]
  map_smul' r x := by
    simp only [map_smul, Finset.smul_sum, smul_comm r, RingHom.id_apply]

theorem reynolds_maps_to_invariants
    (h : MvPolynomial ι k) :
    reynoldsOperator algAct h ∈ polynomialInvariantSubalgebra k G ι algAct := by

  intro g₀
  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_smul (algAct g₀ : MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)]
  congr 1
  rw [map_sum]

  apply Finset.sum_equiv (Equiv.mulLeft g₀)
  · intro g; simp
  · intro g _
    show (algAct g₀) ((algAct g) h) = (algAct (g₀ * g)) h
    rw [map_mul]
    rfl

theorem reynolds_identity_on_invariants
    (h : MvPolynomial ι k)
    (hh : h ∈ polynomialInvariantSubalgebra k G ι algAct) :
    reynoldsOperator algAct h = h := by

  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]

  have : Finset.univ.sum (fun g => (algAct g) h) = (Fintype.card G : k) • h := by
    rw [Finset.sum_congr rfl (fun g _ => hh g)]
    rw [Finset.sum_const, Finset.card_univ]
    simp [Algebra.smul_def]
  rw [this]
  rw [smul_smul]
  rw [inv_mul_cancel₀]
  · simp
  · exact Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')

end ReynoldsOperator

section Lemma11_1

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def positiveInvariantIdeal :
    Ideal (MvPolynomial ι k) :=
  Ideal.span {f | f ∈ polynomialInvariantSubalgebra k G ι algAct ∧
    f ≠ 0 ∧ MvPolynomial.totalDegree f > 0}

lemma reynolds_mul_invariant
    {k : Type*} [Field k] [CharZero k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (h f : MvPolynomial ι k)
    (hf : f ∈ polynomialInvariantSubalgebra k G ι algAct) :
    reynoldsOperator algAct (h * f) = reynoldsOperator algAct h * f := by
  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.smul_sum, Finset.smul_sum, Finset.sum_mul]
  congr 1
  funext g
  simp only [Algebra.smul_mul_assoc]
  congr 1
  rw [map_mul, hf g]

theorem invariant_subalgebra_generated_by_ideal_generators
    (r : ℕ) (f : Fin r → MvPolynomial ι k)
    (hf_inv : ∀ i, f i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hf_gen : positiveInvariantIdeal algAct = Ideal.span (Set.range f))


    (hf_pos : ∀ i, 0 < (f i).totalDegree)
    (h_deg_pres : ∀ (g : G) (p : MvPolynomial ι k),
        ((algAct g) p).totalDegree ≤ p.totalDegree)
    (h_coeff_deg : ∀ (q : MvPolynomial ι k), q ∈ Ideal.span (Set.range f) → q ≠ 0 →
        ∃ (s : Fin r → MvPolynomial ι k),
          q = ∑ i, s i * f i ∧
          ∀ i, s i ≠ 0 → (s i).totalDegree + (f i).totalDegree ≤ q.totalDegree) :
    polynomialInvariantSubalgebra k G ι algAct =
      Algebra.adjoin k (Set.range f) := by
  apply le_antisymm
  ·

    intro p hp

    suffices key : ∀ n, ∀ q : MvPolynomial ι k,
        q ∈ polynomialInvariantSubalgebra k G ι algAct →
        q.totalDegree = n →
        q ∈ Algebra.adjoin k (Set.range f) by
      exact key p.totalDegree p hp rfl
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro q hq hq_deg
    by_cases h0 : n = 0
    ·
      subst h0
      have : q = MvPolynomial.C (MvPolynomial.coeff 0 q) := by
        ext a
        simp only [MvPolynomial.coeff_C]
        split_ifs with ha
        · subst ha; rfl
        · have hsup := (MvPolynomial.totalDegree_eq_zero_iff ι q).mp hq_deg
          rw [MvPolynomial.notMem_support_iff.mp]
          intro hmem
          exact ha (Finsupp.ext (fun x => by
            simp [Finsupp.zero_apply]
            have := hsup a hmem x
            omega))
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    ·
      have hq_pos : q.totalDegree > 0 := by omega

      have hq_ne : q ≠ 0 := by
        intro heq; subst heq; simp at hq_pos
      have hq_in_I : q ∈ positiveInvariantIdeal algAct := by
        rw [positiveInvariantIdeal]
        exact Ideal.subset_span ⟨hq, hq_ne, hq_pos⟩

      have hq_in_span : q ∈ Ideal.span (Set.range f) := hf_gen ▸ hq_in_I

      obtain ⟨s, hs, hs_deg⟩ := h_coeff_deg q hq_in_span hq_ne


      let a : Fin r → MvPolynomial ι k := fun i => reynoldsOperator algAct (s i)
      have ha_inv : ∀ i, a i ∈ polynomialInvariantSubalgebra k G ι algAct :=
        fun i => reynolds_maps_to_invariants algAct (s i)
      have ha_eq : q = ∑ i : Fin r, a i * f i := by
        have h1 : reynoldsOperator algAct q = q :=
          reynolds_identity_on_invariants algAct q hq
        rw [← h1, hs]
        simp only [map_sum, a]
        congr 1
        funext i
        exact reynolds_mul_invariant algAct (s i) (f i) (hf_inv i)


      have reynolds_deg_le : ∀ (p : MvPolynomial ι k),
          (reynoldsOperator algAct p).totalDegree ≤ p.totalDegree := by
        intro p₀
        show ((Fintype.card G : k)⁻¹ • Finset.univ.sum fun g => (algAct g) p₀).totalDegree
            ≤ p₀.totalDegree
        calc ((Fintype.card G : k)⁻¹ • Finset.univ.sum fun g => (algAct g) p₀).totalDegree
            ≤ (Finset.univ.sum fun g => (algAct g) p₀).totalDegree := by
              exact MvPolynomial.totalDegree_smul_le _ _
          _ ≤ p₀.totalDegree := by
              apply MvPolynomial.totalDegree_finsetSum_le
              intro g _
              exact h_deg_pres g p₀
      have ha_deg : ∀ i, (a i).totalDegree < q.totalDegree := by
        intro i
        by_cases hsi : s i = 0
        ·
          show (reynoldsOperator algAct (s i)).totalDegree < q.totalDegree
          rw [hsi, map_zero]
          exact hq_pos
        ·
          have h_bound := hs_deg i hsi
          have h_si_lt : (s i).totalDegree < q.totalDegree := by
            have := hf_pos i
            omega
          exact lt_of_le_of_lt (reynolds_deg_le (s i)) h_si_lt

      rw [ha_eq]
      apply Subalgebra.sum_mem
      intro i _
      apply Subalgebra.mul_mem
      ·
        exact ih (a i).totalDegree (hq_deg ▸ ha_deg i) (a i) (ha_inv i) rfl
      ·
        exact Algebra.subset_adjoin ⟨i, rfl⟩
  ·
    rw [Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact hf_inv i

def normPoly (x : MvPolynomial ι k) : Polynomial (MvPolynomial ι k) :=
  Finset.univ.prod (fun g : G => Polynomial.X - Polynomial.C ((algAct g) x))

lemma normPoly_eval_self (x : MvPolynomial ι k) :
    Polynomial.eval x (normPoly algAct x) = 0 := by
  simp only [normPoly, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  simp [map_one]

lemma normPoly_monic (x : MvPolynomial ι k) :
    (normPoly algAct x).Monic := by
  simp only [normPoly]
  exact Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)

lemma normPoly_coeff_invariant (x : MvPolynomial ι k) (n : ℕ) (h : G) :
    (algAct h) ((normPoly algAct x).coeff n) = (normPoly algAct x).coeff n := by
  suffices key : Polynomial.map (algAct h : MvPolynomial ι k →+* MvPolynomial ι k)
      (normPoly algAct x) = normPoly algAct x by
    have := congr_arg (fun p => Polynomial.coeff p n) key
    simp [Polynomial.coeff_map] at this
    exact this
  simp only [normPoly]
  rw [Polynomial.map_prod]
  apply Finset.prod_equiv (Equiv.mulLeft h)
  · intro g; simp
  · intro g _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 1
    congr 1
    show (algAct h) ((algAct g) x) = (algAct (h * g)) x
    rw [map_mul]; rfl

lemma normPoly_coeffs_subset (x : MvPolynomial ι k) :
    (↑(normPoly algAct x).coeffs : Set (MvPolynomial ι k)) ⊆
      (polynomialInvariantSubalgebra k G ι algAct).toSubring := by
  intro c hc
  rw [Polynomial.coeffs] at hc
  simp only [Finset.coe_image, Set.mem_image] at hc
  obtain ⟨n, _, rfl⟩ := hc
  intro g
  exact normPoly_coeff_invariant algAct x n g

lemma isIntegral_over_invariants (x : MvPolynomial ι k) :
    IsIntegral (polynomialInvariantSubalgebra k G ι algAct) x := by
  let SR := (polynomialInvariantSubalgebra k G ι algAct).toSubring
  let p_sub := (normPoly algAct x).toSubring SR (normPoly_coeffs_subset algAct x)
  refine ⟨p_sub, ?_, ?_⟩
  · rw [Polynomial.monic_toSubring]
    exact normPoly_monic algAct x
  · rw [Polynomial.eval₂_eq_eval_map]
    have h_eq_map : Polynomial.map (algebraMap ↥(polynomialInvariantSubalgebra k G ι algAct)
        (MvPolynomial ι k)) p_sub = normPoly algAct x := by
      have h1 := Polynomial.map_toSubring (normPoly algAct x) SR (normPoly_coeffs_subset algAct x)
      convert h1 using 1
    rw [h_eq_map]
    exact normPoly_eval_self algAct x

theorem invariant_subalgebra_fg :
    (polynomialInvariantSubalgebra k G ι algAct).FG := by

  have h_int : Algebra.IsIntegral (polynomialInvariantSubalgebra k G ι algAct) (MvPolynomial ι k) :=
    ⟨fun x => isIntegral_over_invariants algAct x⟩


  have h_ft : Algebra.FiniteType (↥(polynomialInvariantSubalgebra k G ι algAct)) (MvPolynomial ι k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _

  have h_mf : Module.Finite (↥(polynomialInvariantSubalgebra k G ι algAct)) (MvPolynomial ι k) :=
    @Algebra.IsIntegral.finite _ _ _ _ _ h_int h_ft

  rw [← Subalgebra.fg_top]
  exact fg_of_fg_of_fg (A := k) (B := ↥(polynomialInvariantSubalgebra k G ι algAct))
    (C := MvPolynomial ι k)
    (Algebra.FiniteType.out (R := k) (A := MvPolynomial ι k))
    (Module.finite_def.mp h_mf)
    Subtype.val_injective

end Lemma11_1

section Remark11_2

theorem hilbert_noether_lemma
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {A : Type*} [CommRing A] [Algebra k A]
    {G : Type*} [Group G] [Fintype G]
    (algAct : G →* (A ≃ₐ[k] A))
    (hA_fg : Subalgebra.FG (⊤ : Subalgebra k A)) :
    (Subalgebra.invariants G algAct).FG := by


  let S := Subalgebra.invariants G algAct


  have h_int : Algebra.IsIntegral S A := by
    constructor
    intro x

    let p := Finset.univ.prod (fun g : G => Polynomial.X - Polynomial.C ((algAct g) x))

    have hp_monic : p.Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)

    have hp_eval : Polynomial.eval x p = 0 := by
      simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
      simp [map_one]

    have hp_coeff_inv : ∀ n h_g, (algAct h_g) (p.coeff n) = p.coeff n := by
      intro n h_g
      suffices key : Polynomial.map (algAct h_g : A →+* A) p = p by
        have := congr_arg (fun q => Polynomial.coeff q n) key
        simp [Polynomial.coeff_map] at this
        exact this
      simp only [p]
      rw [Polynomial.map_prod]
      apply Finset.prod_equiv (Equiv.mulLeft h_g)
      · intro g; simp
      · intro g _
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        congr 1; congr 1
        show (algAct h_g) ((algAct g) x) = (algAct (h_g * g)) x
        rw [map_mul]; rfl

    have hp_coeffs_sub : (↑p.coeffs : Set A) ⊆ S.toSubring := by
      intro c hc
      rw [Polynomial.coeffs] at hc
      simp only [Finset.coe_image, Set.mem_image] at hc
      obtain ⟨n, _, rfl⟩ := hc
      intro g
      exact hp_coeff_inv n g
    let p_sub := p.toSubring S.toSubring hp_coeffs_sub
    exact ⟨p_sub, by rw [Polynomial.monic_toSubring]; exact hp_monic,
      by rw [Polynomial.eval₂_eq_eval_map]
         have h_eq : Polynomial.map (algebraMap ↥S A) p_sub = p := by
           have h1 := Polynomial.map_toSubring p S.toSubring hp_coeffs_sub
           convert h1 using 1
         rw [h_eq]; exact hp_eval⟩

  haveI : Algebra.FiniteType k A := ⟨hA_fg⟩
  have h_ft : Algebra.FiniteType S A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _

  have h_mf : Module.Finite S A := Algebra.IsIntegral.finite

  rw [← Subalgebra.fg_top]
  exact fg_of_fg_of_fg (A := k) (B := ↥S) (C := A)
    hA_fg
    (Module.finite_def.mp h_mf)
    Subtype.val_injective

end Remark11_2

section Lemma11_3

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (ρ : G →* V ≃ₗ[k] V)
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

lemma reynolds_diff_of_groupDiff_mem
    {k : Type*} [Field k] [CharZero k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k)
    (I : Ideal (MvPolynomial ι k))
    (h_all : ∀ w : G, (algAct w) p - p ∈ I) :
    reynoldsOperator algAct p - p ∈ I := by

  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]

  have hG_ne : (Fintype.card G : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')


  suffices h : (Fintype.card G : k)⁻¹ •
      (Finset.univ.sum fun w => ((algAct w) p - p)) ∈ I by
    convert h using 1
    have hsum : Finset.univ.sum (fun g => (algAct g) p) =
        Finset.univ.sum (fun g => ((algAct g) p - p)) +
        Finset.univ.sum (fun _ : G => p) := by
      rw [← Finset.sum_add_distrib]
      congr 1; ext g; ring
    rw [hsum, smul_add]
    have hconst : (Fintype.card G : k)⁻¹ • Finset.univ.sum (fun _ : G => p) = p := by
      rw [Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul k (Fintype.card G) p]
      rw [smul_smul, inv_mul_cancel₀ hG_ne, one_smul]
    rw [hconst]
    ring
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  exact Ideal.mul_mem_left I _ (I.sum_mem (fun w _ => h_all w))

lemma positiveInvariantIdeal_stable
    {k : Type*} [Field k]
    {G : Type*} [Group G]
    {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (w : G) (f : MvPolynomial ι k)
    (hf : f ∈ positiveInvariantIdeal algAct) :
    (algAct w) f ∈ positiveInvariantIdeal algAct := by
  have hmem : Ideal.map (algAct w).toAlgHom.toRingHom (positiveInvariantIdeal algAct) ≤
      positiveInvariantIdeal algAct := by
    rw [positiveInvariantIdeal, Ideal.map_span, Ideal.span_le]
    intro x ⟨y, hy, hyx⟩
    have hinv : y ∈ polynomialInvariantSubalgebra k G ι algAct := hy.1
    have heq : (algAct w) y = y := hinv w
    subst hyx
    rw [show (↑(algAct w).toAlgHom.toRingHom : MvPolynomial ι k → MvPolynomial ι k) y =
        (algAct w) y from rfl, heq]
    exact Ideal.subset_span hy
  exact hmem (Ideal.mem_map_of_mem _ hf)

lemma list_prod_diff_mem_ideal
    {k : Type*} [Field k]
    {G : Type*} [Group G]
    {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (I : Ideal (MvPolynomial ι k))
    (hstable : ∀ (w : G) (f : MvPolynomial ι k), f ∈ I → (algAct w) f ∈ I)
    (p : MvPolynomial ι k)
    (L : List G)
    (hL : ∀ g ∈ L, (algAct g) p - p ∈ I) :
    (algAct L.prod) p - p ∈ I := by
  induction L with
  | nil => simp [map_one]
  | cons σ rest ih =>
    have hσ : (algAct σ) p - p ∈ I := hL σ List.mem_cons_self
    have hrest : (algAct rest.prod) p - p ∈ I :=
      ih (fun g hg => hL g (List.mem_cons_of_mem _ hg))
    simp only [List.prod_cons]
    have key : (algAct (σ * rest.prod)) p - p =
        (algAct σ) ((algAct rest.prod) p - p) + ((algAct σ) p - p) := by
      simp only [map_mul, AlgEquiv.mul_apply, map_sub]
      ring
    rw [key]
    exact I.add_mem (hstable σ _ hrest) hσ

lemma algHom_sub_dvd_of_X_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [CommRing k]
    (φ : MvPolynomial ι k →ₐ[k] MvPolynomial ι k)
    (α : MvPolynomial ι k)
    (hX : ∀ i : ι, α ∣ (φ (MvPolynomial.X i) - MvPolynomial.X i))
    (p : MvPolynomial ι k) :
    α ∣ (φ p - p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q ihp ihq =>
    have : φ p + φ q - (p + q) = (φ p - p) + (φ q - q) := by ring
    rw [map_add, this]; exact dvd_add ihp ihq
  | mul_X p i ih =>
    have key : φ (p * MvPolynomial.X i) - p * MvPolynomial.X i =
        φ p * (φ (MvPolynomial.X i) - MvPolynomial.X i) +
        (φ p - p) * MvPolynomial.X i := by
      simp only [map_mul]; ring
    rw [key]; exact dvd_add ((hX i).mul_left _) (ih.mul_right _)




lemma reynolds_invariant_pos_deg_mem_positiveInvariantIdeal
    (_hG : IsComplexReflectionGroup G ρ)
    (m : ℕ) (hm_pos : 0 < m)
    (F : Fin m → MvPolynomial ι k) (g : Fin m → MvPolynomial ι k)
    (hF_inv : ∀ i, F i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (_hF_homog : ∀ i, ∃ d, (F i).IsHomogeneous d)
    (_hg_homog : ∀ i, ∃ d, (g i).IsHomogeneous d)
    (hF1_not_in_invG :
      ¬ ∃ (c : {j : Fin m // j ≠ ⟨0, hm_pos⟩} → MvPolynomial ι k),
        (∀ i, c i ∈ polynomialInvariantSubalgebra k G ι algAct) ∧
        F ⟨0, hm_pos⟩ = ∑ i : {j : Fin m // j ≠ ⟨0, hm_pos⟩}, c i * F i.val)
    (h_relation : Finset.univ.sum (fun i => g i * F i) = 0) :
    reynoldsOperator algAct (g ⟨0, hm_pos⟩) ∈ positiveInvariantIdeal algAct := by
  set R := reynoldsOperator algAct (g ⟨0, hm_pos⟩) with hR_def

  have hR_inv : R ∈ polynomialInvariantSubalgebra k G ι algAct :=
    reynolds_maps_to_invariants algAct (g ⟨0, hm_pos⟩)

  by_cases h0 : R = 0
  · rw [h0]; exact Ideal.zero_mem _

  · by_cases hdeg : R.totalDegree > 0
    ·
      exact Ideal.subset_span ⟨hR_inv, h0, hdeg⟩
    ·


      exfalso
      push Not at hdeg
      have hdeg0 : R.totalDegree = 0 := Nat.le_zero.mp hdeg

      have hR_const : ∃ r : k, r ≠ 0 ∧ R = MvPolynomial.C r := by
        rw [MvPolynomial.totalDegree_eq_zero_iff] at hdeg0
        refine ⟨MvPolynomial.coeff 0 R, ?_, ?_⟩
        · intro hr0
          apply h0
          ext a
          by_cases ha : a = 0
          · subst ha; simp [hr0]
          · simp only [MvPolynomial.coeff_zero]
            exact MvPolynomial.notMem_support_iff.mp (fun hmem =>
              ha (Finsupp.ext (fun x => by
                simp [Finsupp.zero_apply]
                have := hdeg0 a hmem x
                omega)))
        · ext a
          simp only [MvPolynomial.coeff_C]
          split_ifs with ha
          · subst ha; rfl
          · exact MvPolynomial.notMem_support_iff.mp (fun hmem =>
              ha (Finsupp.ext (fun x => by
                simp [Finsupp.zero_apply]
                have := hdeg0 a hmem x
                omega)))
      obtain ⟨r, hr_ne, hR_eq⟩ := hR_const

      have h_avg_rel : ∑ i : Fin m, reynoldsOperator algAct (g i) * F i = 0 := by
        have h1 : reynoldsOperator algAct (∑ i : Fin m, g i * F i) = 0 := by
          rw [h_relation]; simp [map_zero]
        rw [map_sum] at h1
        convert h1 using 1
        congr 1; funext i
        exact (reynolds_mul_invariant algAct (g i) (F i) (hF_inv i)).symm

      have h_split : R * F ⟨0, hm_pos⟩ +
          ∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
            reynoldsOperator algAct (g j.val) * F j.val = 0 := by
        have := h_avg_rel
        rw [Fintype.sum_eq_add_sum_subtype_ne _ ⟨0, hm_pos⟩] at this
        exact this

      have h_F1 : MvPolynomial.C r * F ⟨0, hm_pos⟩ =
          -(∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
            reynoldsOperator algAct (g j.val) * F j.val) := by
        have h_split' := h_split
        rw [hR_eq] at h_split'
        rw [add_eq_zero_iff_eq_neg] at h_split'
        exact h_split'

      apply hF1_not_in_invG
      refine ⟨fun j => -(MvPolynomial.C r⁻¹) * reynoldsOperator algAct (g j.val), ?_, ?_⟩
      ·
        intro j
        apply (polynomialInvariantSubalgebra k G ι algAct).mul_mem
        · apply (polynomialInvariantSubalgebra k G ι algAct).neg_mem

          show ∀ g₀ : G, (algAct g₀) (MvPolynomial.C r⁻¹) = MvPolynomial.C r⁻¹
          intro g₀; exact AlgEquiv.commutes (algAct g₀) r⁻¹
        · exact reynolds_maps_to_invariants algAct (g j.val)
      ·
        have hC_ne : (MvPolynomial.C r : MvPolynomial ι k) ≠ 0 := by
          intro h
          apply hr_ne
          rw [← map_zero (MvPolynomial.C (R := k) (σ := ι))] at h
          exact MvPolynomial.C_injective ι k h
        have key : F ⟨0, hm_pos⟩ = MvPolynomial.C r⁻¹ *
            (-(∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
            reynoldsOperator algAct (g j.val) * F j.val)) := by
          have h2 : MvPolynomial.C r * F ⟨0, hm_pos⟩ = MvPolynomial.C r *
              (MvPolynomial.C r⁻¹ * (-(∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
              reynoldsOperator algAct (g j.val) * F j.val))) := by
            rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr_ne, map_one, one_mul]
            exact h_F1
          exact mul_left_cancel₀ hC_ne h2
        rw [key]
        simp only [mul_neg, Finset.mul_sum, neg_mul, mul_assoc]
        simp only [Finset.sum_neg_distrib]





end Lemma11_3

section Lemma11_4

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (ρ : G →* V ≃ₗ[k] V)
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def IsMinimalGeneratingSet (r : ℕ) (f : Fin r → MvPolynomial ι k)
    (I : Ideal (MvPolynomial ι k)) : Prop :=
  I = Ideal.span (Set.range f) ∧
    ∀ j : Fin r, f j ∉ Ideal.span (Set.range (fun i : {i : Fin r // i ≠ j} => f i.val))

lemma pderiv_aeval_chain_rule {k' : Type*} [CommRing k'] {σ' τ' : Type*} [DecidableEq σ']
    [Fintype σ'] (h : MvPolynomial σ' k') (g : σ' → MvPolynomial τ' k') (κ : τ') :
    MvPolynomial.pderiv κ (MvPolynomial.aeval g h) =
      ∑ j : σ', MvPolynomial.aeval g (MvPolynomial.pderiv j h) *
        MvPolynomial.pderiv κ (g j) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    rw [hp, hq, ← Finset.sum_add_distrib]
    congr 1; ext j; rw [add_mul]

  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    rw [MvPolynomial.pderiv_mul, hp]
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, map_add, map_mul, MvPolynomial.aeval_X]
    have h1 : ∀ x : σ', (MvPolynomial.aeval g) (if i = x then p else 0) =
        if i = x then (MvPolynomial.aeval g) p else 0 := by
      intro x; split_ifs <;> simp
    simp_rw [h1, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · symm
      have h2 : ∀ x : σ', (if i = x then (MvPolynomial.aeval g) p else 0) *
          (MvPolynomial.pderiv κ) (g x) =
          if x = i then (MvPolynomial.aeval g) p * (MvPolynomial.pderiv κ) (g x) else 0 := by
        intro x
        by_cases hxi : i = x
        · simp [hxi]
        · simp [hxi, Ne.symm hxi]
      simp_rw [h2]
      rw [Finset.sum_ite_eq' _ i]; exact if_pos (Finset.mem_univ _)
    · rw [Finset.sum_mul]; congr 1; ext j; ring

theorem sum_X_mul_pderiv_eq (r : ℕ)
    (f : Fin r → MvPolynomial ι k) (d : Fin r → ℕ)
    (a : Fin r → MvPolynomial ι k)
    (b : Fin r → ι → MvPolynomial ι k)
    (hf_homog : ∀ j, (f j).IsHomogeneous (d j))
    (heq : ∀ κ : ι, ∑ j, a j * pderiv κ (f j) = ∑ j, b j κ * f j) :
    ∑ j, (d j) • (a j * f j) = ∑ j, (∑ κ, X κ * b j κ) * f j := by
  have h1 : ∑ κ, X κ * ∑ j, a j * pderiv κ (f j) =
      ∑ κ, X κ * ∑ j, b j κ * f j := by
    congr 1; ext κ; rw [heq]
  simp_rw [Finset.mul_sum] at h1
  rw [Finset.sum_comm] at h1
  conv at h1 => rhs; rw [Finset.sum_comm]
  have h2 : ∀ j : Fin r,
      ∑ κ : ι, X κ * (a j * pderiv κ (f j)) = (d j) • (a j * f j) := by
    intro j
    simp_rw [← mul_assoc, mul_comm (X _) (a j), mul_assoc]
    rw [← Finset.mul_sum, (hf_homog j).sum_X_mul_pderiv, mul_smul_comm]
  simp_rw [h2] at h1
  have h3 : ∀ j : Fin r,
      ∑ κ : ι, X κ * (b j κ * f j) = (∑ κ, X κ * b j κ) * f j := by
    intro j
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  simp_rw [h3] at h1
  exact h1




end Lemma11_4

section Remark11_5

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

end Remark11_5

section Lemma11_6

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def jacobianMatrixAt (y : ι → MvPolynomial ι k) (u : ι → k) : Matrix ι ι k :=
  fun i j => MvPolynomial.eval u ((MvPolynomial.pderiv j) (y i))

lemma eval_algAct_eq_eval_actPoint
    (g : G) (w : ι → k) (f : MvPolynomial ι k) :
    MvPolynomial.eval w ((algAct g) f) =
    MvPolynomial.eval (fun i => MvPolynomial.eval w ((algAct g) (MvPolynomial.X i))) f := by
  have key : (MvPolynomial.eval w : MvPolynomial ι k →+* k).comp
      (↑(algAct g) : MvPolynomial ι k →+* MvPolynomial ι k) =
      MvPolynomial.eval (fun i => MvPolynomial.eval w ((algAct g) (MvPolynomial.X i))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply]
      change MvPolynomial.eval w ((algAct g) ((algebraMap k _) r)) = _
      rw [(algAct g).commutes]; simp [MvPolynomial.eval_C]
    · intro i; simp only [RingHom.comp_apply, MvPolynomial.eval_X]; rfl
  exact RingHom.congr_fun key f

lemma mv_polynomial_disjoint_separation
    (S T : Finset (ι → k)) (hST : Disjoint S T) :
    ∃ p : MvPolynomial ι k,
      (∀ w ∈ S, MvPolynomial.eval w p = 0) ∧
      (∀ w ∈ T, MvPolynomial.eval w p = 1) := by
  haveI : DecidableEq (ι → k) := Classical.decEq _
  have h_ne : ∀ s ∈ S, ∀ t ∈ T, s ≠ t := by
    intro s hs t ht hst; exact Finset.disjoint_left.mp hST hs (hst ▸ ht)
  have h_sep : ∀ s ∈ S, ∀ t ∈ T, ∃ i : ι, s i ≠ t i := by
    intro s hs t ht; by_contra h; push Not at h; exact h_ne s hs t ht (funext h)
  let i_st : (s : { x // x ∈ S }) → (t : { x // x ∈ T }) → ι := fun s t =>
    Classical.choose (h_sep s.val s.prop t.val t.prop)
  have hi_st : ∀ (s : { x // x ∈ S }) (t : { x // x ∈ T }),
      s.val (i_st s t) ≠ t.val (i_st s t) := fun s t =>
    Classical.choose_spec (h_sep s.val s.prop t.val t.prop)
  let φ : { x // x ∈ S } → MvPolynomial ι k := fun s =>
    T.attach.prod (fun t => MvPolynomial.X (i_st s t) - MvPolynomial.C (t.val (i_st s t)))
  have hφ_s_ne : ∀ (s : { x // x ∈ S }), MvPolynomial.eval s.val (φ s) ≠ 0 := by
    intro s
    simp only [φ, map_prod, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [Finset.prod_ne_zero_iff]; intro t _; exact sub_ne_zero.mpr (hi_st s t)
  have hφ_zero : ∀ (s : { x // x ∈ S }) (t₀ : ι → k) (ht₀ : t₀ ∈ T),
      MvPolynomial.eval t₀ (φ s) = 0 := by
    intro s t₀ ht₀
    simp only [φ, map_prod, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_attach T ⟨t₀, ht₀⟩) (by simp [sub_self])
  let ψ : { x // x ∈ S } → MvPolynomial ι k := fun s =>
    MvPolynomial.C (MvPolynomial.eval s.val (φ s))⁻¹ * φ s
  have hψ_one : ∀ (s : { x // x ∈ S }), MvPolynomial.eval s.val (ψ s) = 1 := by
    intro s; simp only [ψ, map_mul, MvPolynomial.eval_C]; exact inv_mul_cancel₀ (hφ_s_ne s)
  have hψ_zero : ∀ (s : { x // x ∈ S }) (t : ι → k) (ht : t ∈ T),
      MvPolynomial.eval t (ψ s) = 0 := by
    intro s t ht; simp only [ψ, map_mul, MvPolynomial.eval_C, hφ_zero s t ht, mul_zero]
  let p : MvPolynomial ι k := S.attach.prod (fun s => 1 - ψ s)
  exact ⟨p, fun w hw => by
    simp only [p, map_prod, map_sub, map_one]
    exact Finset.prod_eq_zero (Finset.mem_attach S ⟨w, hw⟩) (by simp [hψ_one ⟨w, hw⟩]),
   fun w hw => by
    simp only [p, map_prod, map_sub, map_one]
    exact Finset.prod_eq_one (fun s _ => by simp [hψ_zero s w hw])⟩

theorem maximal_ideals_invariants_bij_orbits
    (u v : ι → k) :
    (∀ f ∈ polynomialInvariantSubalgebra k G ι algAct,
      MvPolynomial.eval u f = MvPolynomial.eval v f) ↔
    (∃ g : G, ∀ i, MvPolynomial.eval v ((algAct g) (MvPolynomial.X i)) = u i) := by
  constructor
  ·

    intro hall
    by_contra h_not_orbit
    push Not at h_not_orbit

    haveI : DecidableEq (ι → k) := Classical.decEq _

    let orbitV : Finset (ι → k) :=
      Finset.univ.image (fun g : G => fun i =>
        MvPolynomial.eval v ((algAct g) (MvPolynomial.X i)))

    let orbitU : Finset (ι → k) :=
      Finset.univ.image (fun g : G => fun i =>
        MvPolynomial.eval u ((algAct g) (MvPolynomial.X i)))

    have hu_not_in_orbitV : u ∉ orbitV := by
      simp only [orbitV, Finset.mem_image, Finset.mem_univ, true_and]
      push Not
      intro g
      obtain ⟨i, hi⟩ := h_not_orbit g
      exact fun h => absurd (congrFun h i ▸ rfl) hi

    have h_disj : Disjoint orbitV orbitU := by
      rw [Finset.disjoint_left]
      intro w hw_in_V hw_in_U
      simp only [orbitU, Finset.mem_image, Finset.mem_univ, true_and] at hw_in_U
      simp only [orbitV, Finset.mem_image, Finset.mem_univ, true_and] at hw_in_V
      obtain ⟨g₁, hg₁⟩ := hw_in_U
      obtain ⟨g₂, hg₂⟩ := hw_in_V
      have : ∀ i, MvPolynomial.eval v
          ((algAct (g₂ * g₁⁻¹)) (MvPolynomial.X i)) = u i := by
        intro i
        have h1 : ∀ f, MvPolynomial.eval u ((algAct g₁) f) =
            MvPolynomial.eval w f := by
          intro f
          rw [eval_algAct_eq_eval_actPoint algAct g₁ u f, hg₁]
        have h2 : ∀ f, MvPolynomial.eval v ((algAct g₂) f) =
            MvPolynomial.eval w f := by
          intro f
          rw [eval_algAct_eq_eval_actPoint algAct g₂ v f, hg₂]
        have step1 : (algAct (g₂ * g₁⁻¹)) (MvPolynomial.X i) =
            (algAct g₂) ((algAct g₁⁻¹) (MvPolynomial.X i)) := by
          rw [map_mul algAct]; rfl
        rw [step1, h2, ← h1]
        have step2 : (algAct g₁) ((algAct g₁⁻¹) (MvPolynomial.X i)) =
            (algAct (g₁ * g₁⁻¹)) (MvPolynomial.X i) := by
          rw [map_mul algAct]; rfl
        rw [step2, mul_inv_cancel, map_one algAct]
        simp
      obtain ⟨i, hi⟩ := h_not_orbit (g₂ * g₁⁻¹)
      exact hi (this i)

    obtain ⟨h, h_vanish, h_one⟩ :=
      mv_polynomial_disjoint_separation orbitV orbitU h_disj

    let Rh := reynoldsOperator algAct h
    have hRh_inv : Rh ∈ polynomialInvariantSubalgebra k G ι algAct :=
      reynolds_maps_to_invariants algAct h

    have hRh_v : MvPolynomial.eval v Rh = 0 := by
      simp only [Rh, reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
      have heval_smul : MvPolynomial.eval v ((Fintype.card G : k)⁻¹ •
        Finset.univ.sum fun g => (algAct g) h) =
        (Fintype.card G : k)⁻¹ *
        MvPolynomial.eval v (Finset.univ.sum fun g => (algAct g) h) := by
        rw [Algebra.smul_def, map_mul]; simp
      rw [heval_smul, map_sum]
      have hsum : ∑ g : G, MvPolynomial.eval v ((algAct g) h) = 0 := by
        apply Finset.sum_eq_zero
        intro g _
        rw [eval_algAct_eq_eval_actPoint algAct g v h]
        apply h_vanish
        simp only [orbitV, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨g, rfl⟩
      rw [hsum, mul_zero]

    have hRh_u : MvPolynomial.eval u Rh = 1 := by
      simp only [Rh, reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
      have heval_smul : MvPolynomial.eval u ((Fintype.card G : k)⁻¹ •
        Finset.univ.sum fun g => (algAct g) h) =
        (Fintype.card G : k)⁻¹ *
        MvPolynomial.eval u (Finset.univ.sum fun g => (algAct g) h) := by
        rw [Algebra.smul_def, map_mul]; simp
      rw [heval_smul, map_sum]
      have hsum : ∑ g : G, MvPolynomial.eval u ((algAct g) h) =
          (Fintype.card G : k) := by
        have h1 : ∑ g : G, MvPolynomial.eval u ((algAct g) h) =
            ∑ _g : G, (1 : k) := by
          apply Finset.sum_congr rfl
          intro g _
          rw [eval_algAct_eq_eval_actPoint algAct g u h]
          apply h_one
          simp only [orbitU, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨g, rfl⟩
        rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [hsum]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')

    have key := hall Rh hRh_inv
    rw [hRh_u, hRh_v] at key
    exact one_ne_zero key

  ·
    intro ⟨g, hg⟩ f hf
    have h1 : MvPolynomial.eval v ((algAct g) f) = MvPolynomial.eval u f := by
      rw [eval_algAct_eq_eval_actPoint algAct g v f]
      have : (fun i => MvPolynomial.eval v ((algAct g) (MvPolynomial.X i))) = u :=
        funext hg
      rw [this]
    rw [← h1, hf g]

end Lemma11_6

section Section11_3

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (ρ : G →* V ≃ₗ[k] V)
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def IsProductOfReflections (g : G) : Prop :=
  ∃ (n : ℕ) (reflections : Fin n → G),
    (∀ i, IsComplexReflection (ρ (reflections i))) ∧
    g = (List.ofFn reflections).prod

end Section11_3

end
