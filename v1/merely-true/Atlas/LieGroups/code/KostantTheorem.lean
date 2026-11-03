/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HarishChandraIsomorphism
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.SimpleModule.Basic

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def qInteger (d : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range d, PowerSeries.X ^ i

variable {P' : Type*} [DecidableEq P'] [AddCommGroup P']

def groupRingExp (α : P') : AddMonoidAlgebra ℤ P' := Finsupp.single α 1

def groupRingOneMinusExp (α : P') : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (0 : P') 1 - Finsupp.single α 1

def numeratorProd (S : Finset P') : AddMonoidAlgebra ℤ P' :=
  S.prod (fun α => groupRingOneMinusExp α)

def groupRingCT (f : AddMonoidAlgebra ℤ P') : ℤ := f 0

def singleFactorCoeff (α : P') (n : ℕ) : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (n • α) (1 : ℤ) - Finsupp.single ((n + 1) • α) 1

def singleFactorPS (α : P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  PowerSeries.mk (singleFactorCoeff α)

def fullProductPS (S : Finset P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  S.prod (fun α => singleFactorPS α)

def geomFactorCoeff (α : P') (n : ℕ) : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (n • α) (1 : ℤ)

def geomFactorPS (α : P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  PowerSeries.mk (geomFactorCoeff α)

def geomProductPS (S : Finset P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  S.prod (fun α => geomFactorPS α)

def powerSeriesCT (f : PowerSeries (AddMonoidAlgebra ℤ P')) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => groupRingCT (PowerSeries.coeff n f))

def concreteCT_fullRoots (roots : Finset P') : PowerSeries ℤ :=
  powerSeriesCT (fullProductPS roots)

def concreteCT_posRoots (roots posRoots : Finset P') : PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (C (numeratorProd posRoots) * geomProductPS roots)

def concreteCT_fullRoots_char (roots : Finset P') (chi : AddMonoidAlgebra ℤ P') :
    PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (fullProductPS roots * C chi)

def concreteCT_posRoots_lambda (roots posRoots : Finset P') (wt : P') :
    PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (C (groupRingExp wt * numeratorProd posRoots) * geomProductPS roots)

def qIntegerProd (r : ℕ) (degrees : Fin r → ℕ) : PowerSeries ℤ :=
  ∏ i : Fin r, qInteger (degrees i)

def gradedHilbertSeries (dimFun : ℕ → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (dimFun n : ℤ))

structure KostantSetupData
    [LieAlgebra.IsSemisimple R 𝔤] where
  cartanSubalgebra : LieSubalgebra R 𝔤
  [instCartan : cartanSubalgebra.IsCartanSubalgebra]
  [instLieRingModuleSg : LieRingModule 𝔤 (SymmetricAlgebra R 𝔤)]
  [instLieModuleSg : LieModule R 𝔤 (SymmetricAlgebra R 𝔤)]
  invariantSubalgebra : Subalgebra R (SymmetricAlgebra R 𝔤)
  invariantSubalgebra_eq :
    ∀ x : SymmetricAlgebra R 𝔤,
      x ∈ invariantSubalgebra ↔ x ∈ LieModule.maxTrivSubmodule R 𝔤 (SymmetricAlgebra R 𝔤)
  harmonicSubspace : Submodule R (SymmetricAlgebra R 𝔤)
  [instFreeHarmonic : Module.Free R harmonicSubspace]
  harmonicSubspaceUEA : Submodule R (UniversalEnvelopingAlgebra R 𝔤)
  pbwHarmonicEquiv : harmonicSubspace ≃ₗ[R] harmonicSubspaceUEA
  pbwSymmEquiv : SymmetricAlgebra R 𝔤 ≃ₗ[R] UniversalEnvelopingAlgebra R 𝔤
  pbwInvariantToCenter : invariantSubalgebra ≃ₐ[R]
    Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)
  pbwSymmCompat : ∀ (a : ↥invariantSubalgebra) (h : ↥harmonicSubspace),
    pbwSymmEquiv (a.val * h.val) =
    (pbwInvariantToCenter a).val * (pbwHarmonicEquiv h).val
  W : Type*
  [instGroup : Group W]
  [instFintype : Fintype W]
  rank : ℕ
  degrees : Fin rank → ℕ
  P : Type*
  [instAddCommGroup_P : AddCommGroup P]
  [instDecEq_P : DecidableEq P]
  roots : Finset P
  posRoots : Finset P
  posRoots_sub_roots : posRoots ⊆ roots
  dominantWeights : Set P
  simpleCoroots : Fin rank → P
  pairingCoroot : P → Fin rank → ℤ
  dominantWeights_spec : dominantWeights = {μ : P | ∀ i : Fin rank, 0 ≤ pairingCoroot μ i}
  pairingCoroot_zero : ∀ i : Fin rank, pairingCoroot 0 i = 0
  rho : P
  signRep : W → ℤ
  actionW : W → P → P
  weylCharacter : P → AddMonoidAlgebra ℤ P

  gradedHomDim : P → ℕ → ℕ

  equation12_geom_form_field :
    ∀ (wt : P) (_ : wt ∈ dominantWeights),
      (Fintype.card W : ℤ) • gradedHilbertSeries (gradedHomDim wt) =
      (∏ i : Fin rank, qInteger (degrees i)) *
      powerSeriesCT (geomProductPS roots *
        PowerSeries.C (numeratorProd roots * weylCharacter wt))

  cst_equiv : TensorProduct R invariantSubalgebra harmonicSubspace ≃ₗ[R] SymmetricAlgebra R 𝔤
  cst_equiv_apply_tmul :
    ∀ (a : invariantSubalgebra) (h : harmonicSubspace),
      cst_equiv (a ⊗ₜ[R] h) = a.val * h.val
  invariantPolynomial : invariantSubalgebra ≃ₐ[R] MvPolynomial (Fin rank) R

attribute [instance] KostantSetupData.instCartan
attribute [instance] KostantSetupData.instLieRingModuleSg KostantSetupData.instLieModuleSg
attribute [instance] KostantSetupData.instGroup KostantSetupData.instFintype
attribute [instance] KostantSetupData.instAddCommGroup_P KostantSetupData.instDecEq_P
attribute [instance] KostantSetupData.instFreeHarmonic

theorem KostantSetupData.zero_mem_dominantWeights
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) :
    (0 : ksd.P) ∈ ksd.dominantWeights := by
  rw [ksd.dominantWeights_spec]
  intro i
  rw [ksd.pairingCoroot_zero i]





omit [DecidableEq P'] in
lemma singleFactorCoeff_eq_mul (α : P') (n : ℕ) :
    singleFactorCoeff α n = groupRingOneMinusExp α * geomFactorCoeff α n := by
  let a : AddMonoidAlgebra ℤ P' := AddMonoidAlgebra.single (0 : P') 1
  let b : AddMonoidAlgebra ℤ P' := AddMonoidAlgebra.single α 1
  let c : AddMonoidAlgebra ℤ P' := AddMonoidAlgebra.single (n • α) 1
  have ha : groupRingOneMinusExp α = a - b := rfl
  have hc : geomFactorCoeff α n = c := rfl
  rw [ha, hc, sub_mul]
  have hac : a * c = AddMonoidAlgebra.single (n • α) (1 : ℤ) := by
    simp [a, c, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  have hbc : b * c = AddMonoidAlgebra.single ((n + 1) • α) (1 : ℤ) := by
    simp [b, c, AddMonoidAlgebra.single_mul_single, mul_one, add_comm α (n • α), succ_nsmul]
  rw [hac, hbc]
  rfl

omit [DecidableEq P'] in
lemma singleFactorPS_eq (α : P') :
    singleFactorPS α =
      PowerSeries.C (groupRingOneMinusExp α) * geomFactorPS α := by
  apply PowerSeries.ext; intro n
  simp only [singleFactorPS, geomFactorPS, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
  exact singleFactorCoeff_eq_mul α n

omit [DecidableEq P'] in
lemma fullProductPS_eq_C_numeratorProd_mul_geomProductPS (S : Finset P') :
    fullProductPS S =
      PowerSeries.C (numeratorProd S) * geomProductPS S := by
  simp only [fullProductPS, geomProductPS, numeratorProd]
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro α _
  exact singleFactorPS_eq α

theorem KostantSetupData.equation12_geom_form
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) :
    ∀ (wt : ksd.P) (_ : wt ∈ ksd.dominantWeights),
      (Fintype.card ksd.W : ℤ) • gradedHilbertSeries (ksd.gradedHomDim wt) =
      (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) *
      powerSeriesCT (geomProductPS ksd.roots *
        PowerSeries.C (numeratorProd ksd.roots * ksd.weylCharacter wt)) :=
  fun wt hwt => ksd.equation12_geom_form_field wt hwt

theorem KostantSetupData.equation12_spec
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) :
    ∀ (wt : ksd.P) (_ : wt ∈ ksd.dominantWeights),
      (Fintype.card ksd.W : ℤ) • gradedHilbertSeries (ksd.gradedHomDim wt) =
      (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) *
      (concreteCT_fullRoots_char ksd.roots (ksd.weylCharacter wt)) := by
  intro wt hwt
  rw [ksd.equation12_geom_form wt hwt]
  congr 1
  simp only [concreteCT_fullRoots_char]
  congr 1
  rw [fullProductPS_eq_C_numeratorProd_mul_geomProductPS, map_mul]
  ring


theorem KostantSetupData.equation12_hilbert_series
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) :
    ∀ (wt : ksd.P) (_ : wt ∈ ksd.dominantWeights),
      (Fintype.card ksd.W : ℤ) • gradedHilbertSeries (ksd.gradedHomDim wt) =
      (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) *
      (concreteCT_fullRoots_char ksd.roots (ksd.weylCharacter wt)) :=
  ksd.equation12_spec

def KostantSetupData.isDominant
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (μ : ksd.P) : Prop :=
  ∀ i : Fin ksd.rank, 0 ≤ ksd.pairingCoroot μ i

theorem KostantSetupData.isDominant_iff_mem_dominantWeights
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (μ : ksd.P) :
    ksd.isDominant μ ↔ μ ∈ ksd.dominantWeights := by
  unfold isDominant
  rw [ksd.dominantWeights_spec]
  rfl

def KostantSetupData.dotAction
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (w : ksd.W) (μ : ksd.P) : ksd.P :=
  ksd.actionW w (μ + ksd.rho) - ksd.rho


variable [LieAlgebra.IsSemisimple R 𝔤]
variable (ksd : @KostantSetupData R _ 𝔤 _ _ _)

def KostantSetupData.hilbertSeriesHomDual
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (wt : ksd.P) : PowerSeries ℤ :=
  (∏ i : Fin ksd.rank, qInteger (ksd.degrees i)) *
  (concreteCT_posRoots_lambda ksd.roots ksd.posRoots wt : PowerSeries ℤ)

def KostantSetupData.actualHilbertSeriesHom
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) (wt : ksd.P) : PowerSeries ℤ :=
  gradedHilbertSeries (ksd.gradedHomDim wt)


omit [DecidableEq P'] in
lemma singleFactorPS_eq_mul (α : P') :
    singleFactorPS α =
    (PowerSeries.C (groupRingOneMinusExp α) : PowerSeries (AddMonoidAlgebra ℤ P')) *
      geomFactorPS α := by
  ext n
  simp only [singleFactorPS, geomFactorPS, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
  exact congr_fun (congr_arg _ (singleFactorCoeff_eq_mul α n)) _

lemma fullProductPS_eq_numerator_mul_geom (S : Finset P') :
    fullProductPS S =
    (PowerSeries.C (numeratorProd S) : PowerSeries (AddMonoidAlgebra ℤ P')) *
      geomProductPS S := by
  unfold fullProductPS geomProductPS numeratorProd
  induction S using Finset.induction with
  | empty => simp [Finset.prod_empty, map_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [singleFactorPS_eq_mul, ih]
    simp only [map_mul]
    ring










def kostant_cst_mulBilinear :
    ksd.invariantSubalgebra →ₗ[R] ksd.harmonicSubspace →ₗ[R] SymmetricAlgebra R 𝔤 where
  toFun a := {
    toFun := fun h => a.val * h.val
    map_add' := by intros x y; simp [mul_add]
    map_smul' := by intros r x; simp [Algebra.mul_smul_comm]
  }
  map_add' := by intros a b; ext h; simp [add_mul]
  map_smul' := by intros r a; ext h; simp [Algebra.smul_mul_assoc]

def kostant_cst_mulMap_R :
    TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace →ₗ[R]
    SymmetricAlgebra R 𝔤 :=
  TensorProduct.lift (kostant_cst_mulBilinear ksd)

set_option synthInstance.maxHeartbeats 80000 in
def kostant_cst_mulMap :
    TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace →ₗ[ksd.invariantSubalgebra]
    SymmetricAlgebra R 𝔤 where
  toFun := kostant_cst_mulMap_R ksd
  map_add' := (kostant_cst_mulMap_R ksd).map_add
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a' h =>
      simp only [kostant_cst_mulMap_R, TensorProduct.lift.tmul, kostant_cst_mulBilinear,
                  RingHom.id_apply, TensorProduct.smul_tmul', LinearMap.coe_mk, AddHom.coe_mk]
      show (↑(a * a') : SymmetricAlgebra R 𝔤) * (↑h : SymmetricAlgebra R 𝔤) =
           ↑a * (↑a' * ↑h)
      rw [Subalgebra.coe_mul, mul_assoc]
    | add x y hx hy =>
      simp [map_add, hx, hy]

set_option synthInstance.maxHeartbeats 80000 in
theorem kostant_cst_mulMap_bijective :
    Function.Bijective (kostant_cst_mulMap ksd) := by


  have h_eq : (kostant_cst_mulMap ksd : TensorProduct R ksd.invariantSubalgebra
      ksd.harmonicSubspace → SymmetricAlgebra R 𝔤) = ksd.cst_equiv := by

    have h_lin_l : (kostant_cst_mulMap_R ksd : TensorProduct R ksd.invariantSubalgebra
        ksd.harmonicSubspace →ₗ[R] SymmetricAlgebra R 𝔤) =
        ksd.cst_equiv.toLinearMap := by
      ext a h
      simp only [kostant_cst_mulMap_R, kostant_cst_mulBilinear]
      exact (ksd.cst_equiv_apply_tmul a h).symm
    ext x
    exact congr_fun (congr_arg DFunLike.coe h_lin_l) x
  rw [h_eq]
  exact ksd.cst_equiv.bijective

set_option synthInstance.maxHeartbeats 80000 in
def kostant_cst_tensor :
    (TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace) ≃ₗ[ksd.invariantSubalgebra]
    SymmetricAlgebra R 𝔤 :=
  LinearEquiv.ofBijective (kostant_cst_mulMap ksd) (kostant_cst_mulMap_bijective ksd)

theorem kostant_cst_free :
    Module.Free ksd.invariantSubalgebra (SymmetricAlgebra R 𝔤) := by
  haveI : Module.Free ksd.invariantSubalgebra
      (TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace) :=
    Algebra.TensorProduct.instFree R ksd.invariantSubalgebra ksd.harmonicSubspace
  exact Module.Free.of_equiv (kostant_cst_tensor ksd)

set_option synthInstance.maxHeartbeats 80000 in
def kostant_Sg_tensor_decomposition :
    (TensorProduct R ksd.harmonicSubspace ksd.invariantSubalgebra) ≃ₗ[R]
    SymmetricAlgebra R 𝔤 :=
  (TensorProduct.comm R ksd.harmonicSubspace ksd.invariantSubalgebra).trans
    ((kostant_cst_tensor ksd).restrictScalars R)

theorem kostant_Sg_free_over_invariants :
    Module.Free ksd.invariantSubalgebra (SymmetricAlgebra R 𝔤) :=
  kostant_cst_free ksd

set_option synthInstance.maxHeartbeats 80000


lemma nontrivial_of_irreducible_module
    (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [LieModule.IsIrreducible R 𝔤 V] : Nontrivial R := by
  haveI : Nontrivial V := LieModule.nontrivial_of_isIrreducible R 𝔤 V
  by_contra hr
  rw [not_nontrivial_iff_subsingleton] at hr
  haveI := hr; haveI : Subsingleton V := Module.subsingleton R V
  exact not_subsingleton V (by infer_instance)









lemma powerSeries_zsmul_left_cancel {n : ℤ} (hn : n ≠ 0) {a b : PowerSeries ℤ}
    (h : n • a = n • b) : a = b := by
  ext m
  have := congr_arg (PowerSeries.coeff (R := ℤ) m) h
  simp only [map_zsmul] at this
  exact mul_left_cancel₀ hn this

lemma weylGroup_card_ne_zero : (Fintype.card ksd.W : ℤ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero


lemma concreteCT_fullRoots_char_one (roots : Finset ksd.P) :
    concreteCT_fullRoots_char roots (Finsupp.single (0 : ksd.P) 1) =
    concreteCT_fullRoots roots := by
  unfold concreteCT_fullRoots_char concreteCT_fullRoots
  simp [AddMonoidAlgebra.one_def.symm, map_one, mul_one]

lemma concreteCT_posRoots_lambda_zero (roots posRoots : Finset ksd.P) :
    concreteCT_posRoots_lambda roots posRoots (0 : ksd.P) =
    concreteCT_posRoots roots posRoots := by
  unfold concreteCT_posRoots_lambda concreteCT_posRoots groupRingExp
  simp [AddMonoidAlgebra.one_def.symm, one_mul]





def kostant_center_is_polynomial :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) ≃ₐ[R]
    MvPolynomial (Fin ksd.rank) R :=
  ksd.pbwInvariantToCenter.symm.trans ksd.invariantPolynomial

def pbw_mulBilinear :
    (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₗ[R]
    ksd.harmonicSubspaceUEA →ₗ[R] UniversalEnvelopingAlgebra R 𝔤 where
  toFun z := {
    toFun := fun h => z.val * h.val
    map_add' := by intros x y; simp [mul_add]
    map_smul' := by intros r x; simp [Algebra.mul_smul_comm]
  }
  map_add' := by intros a b; ext h; simp [add_mul]
  map_smul' := by intros r a; ext h; simp [Algebra.smul_mul_assoc]

def pbw_mulMap_R :
    TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA →ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  TensorProduct.lift (pbw_mulBilinear ksd)

set_option synthInstance.maxHeartbeats 80000 in
def pbw_mulMap :
    TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA →ₗ[Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)]
    UniversalEnvelopingAlgebra R 𝔤 where
  toFun := pbw_mulMap_R ksd
  map_add' := (pbw_mulMap_R ksd).map_add
  map_smul' := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a' h =>
      simp only [pbw_mulMap_R, TensorProduct.lift.tmul, pbw_mulBilinear,
                  RingHom.id_apply, TensorProduct.smul_tmul', LinearMap.coe_mk, AddHom.coe_mk]
      show (↑(a * a') : UniversalEnvelopingAlgebra R 𝔤) * (↑h : UniversalEnvelopingAlgebra R 𝔤) =
           ↑a * (↑a' * ↑h)
      rw [Subalgebra.coe_mul, mul_assoc]
    | add x y hx hy =>
      simp [map_add, hx, hy]

set_option synthInstance.maxHeartbeats 80000 in
theorem pbw_mulMap_bijective :
    Function.Bijective (pbw_mulMap ksd) := by

  show Function.Bijective (pbw_mulMap_R ksd)

  let α : ksd.invariantSubalgebra ≃ₗ[R]
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :=
    ksd.pbwInvariantToCenter.toLinearEquiv
  let β : ksd.harmonicSubspace ≃ₗ[R] ksd.harmonicSubspaceUEA := ksd.pbwHarmonicEquiv
  let τ : TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace ≃ₗ[R]
      TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
        ksd.harmonicSubspaceUEA :=
    TensorProduct.congr α β
  let σ := ksd.pbwSymmEquiv

  have hcompat : ∀ (x : TensorProduct R ksd.invariantSubalgebra ksd.harmonicSubspace),
      pbw_mulMap_R ksd (τ x) = σ (kostant_cst_mulMap_R ksd x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul a h =>

      show pbw_mulMap_R ksd (TensorProduct.congr α β (a ⊗ₜ[R] h)) = σ (kostant_cst_mulMap_R ksd (a ⊗ₜ[R] h))
      rw [TensorProduct.congr_tmul]
      simp only [pbw_mulMap_R, kostant_cst_mulMap_R, TensorProduct.lift.tmul,
        pbw_mulBilinear, kostant_cst_mulBilinear, LinearMap.coe_mk, AddHom.coe_mk]
      exact (ksd.pbwSymmCompat a h).symm
    | add x y hx hy => simp [map_add, hx, hy]

  have hfactor : ∀ y, pbw_mulMap_R ksd y =
      σ (kostant_cst_mulMap_R ksd (τ.symm y)) := by
    intro y
    rw [← hcompat, LinearEquiv.apply_symm_apply]


  have hcst : Function.Bijective (kostant_cst_mulMap_R ksd) := by
    show Function.Bijective (kostant_cst_mulMap ksd)
    exact kostant_cst_mulMap_bijective ksd

  constructor
  · intro a b hab
    rw [hfactor a, hfactor b] at hab
    have h1 := σ.injective hab
    have h2 := hcst.1 h1
    exact τ.symm.injective h2
  · intro y
    obtain ⟨s, hs⟩ := σ.surjective y
    obtain ⟨t, ht⟩ := hcst.2 s
    exact ⟨τ t, by rw [hfactor, LinearEquiv.symm_apply_apply, ht, hs]⟩

set_option synthInstance.maxHeartbeats 80000 in
noncomputable def pbwTensorEquivUEA :
    (TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA) ≃ₗ[Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)]
    UniversalEnvelopingAlgebra R 𝔤 :=
  LinearEquiv.ofBijective (pbw_mulMap ksd) (pbw_mulMap_bijective ksd)

noncomputable abbrev pbw_cst_tensor_UEA := pbwTensorEquivUEA (R := R) (𝔤 := 𝔤) ksd

theorem pbwHarmonicFreeUEA :
    Module.Free R ksd.harmonicSubspaceUEA :=
  Module.Free.of_equiv' inferInstance ksd.pbwHarmonicEquiv

theorem pbw_harmonicFree_UEA : Module.Free R ksd.harmonicSubspaceUEA :=
  pbwHarmonicFreeUEA ksd

include ksd in
theorem pbw_free_lift :
    Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (UniversalEnvelopingAlgebra R 𝔤) := by
  haveI : Module.Free R ksd.harmonicSubspaceUEA := pbwHarmonicFreeUEA ksd
  haveI : Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      (TensorProduct R (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
        ksd.harmonicSubspaceUEA) :=
    Algebra.TensorProduct.instFree R
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      ksd.harmonicSubspaceUEA
  exact Module.Free.of_equiv (pbwTensorEquivUEA ksd)

include ksd in
theorem kostant_Ug_free_over_center_of_setupData :
    Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (UniversalEnvelopingAlgebra R 𝔤) :=
  pbw_free_lift ksd

theorem kostant_Ug_free_over_center
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤]
    (ksd : @KostantSetupData R _ 𝔤 _ _ _) :
    Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (UniversalEnvelopingAlgebra R 𝔤) :=
  pbw_free_lift ksd



def kostant_Ug_tensor_decomposition :
    (TensorProduct R ksd.harmonicSubspaceUEA
      (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)).toSubmodule) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  (TensorProduct.comm R ksd.harmonicSubspaceUEA
    (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)).toSubmodule).trans
    ((pbwTensorEquivUEA ksd).restrictScalars R)

theorem theorem_13_5 :

    Nonempty (↑(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) ≃ₐ[R]
      MvPolynomial (Fin ksd.rank) R) ∧

    Module.Free (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      (UniversalEnvelopingAlgebra R 𝔤) :=
  ⟨⟨kostant_center_is_polynomial ksd⟩, kostant_Ug_free_over_center ksd⟩

open MeasureTheory Filter

def KostantFqSingleFactor (q : ℝ) (z : ℂ) : ℂ :=
  (1 - z) / (1 - (q : ℂ) * z)

def KostantFqProd {ι T : Type*} (posRoots : Finset ι) (φ : ι → T → ℂ)
    (q : ℝ) (x : T) : ℂ :=
  ∏ α ∈ posRoots, KostantFqSingleFactor q (φ α x)

lemma KostantFq_denom_ne_zero (q : ℝ) (z : ℂ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hz : ‖z‖ = 1) : (1 : ℂ) - (q : ℂ) * z ≠ 0 := by
  intro h
  have h0 : ‖(1 : ℂ) - (q : ℂ) * z‖ = 0 := by rw [h, norm_zero]
  have hqz : ‖(q : ℂ) * z‖ = q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq, hz, mul_one]
  linarith [show ‖(1 : ℂ) - (q : ℂ) * z‖ ≥ 1 - q from
    calc ‖(1 : ℂ) - (q : ℂ) * z‖ ≥ ‖(1 : ℂ)‖ - ‖(q : ℂ) * z‖ := norm_sub_norm_le _ _
      _ = 1 - q := by rw [hqz, norm_one]]

lemma KostantFq_normSq_bound (q : ℝ) (z : ℂ) (hq : 0 ≤ q)
    (hz : ‖z‖ = 1) :
    Complex.normSq (1 - z) ≤ 4 * Complex.normSq (1 - (q : ℂ) * z) := by
  have hz' : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have hns1 : Complex.normSq (1 - z) = 2 - 2 * z.re := by
    rw [Complex.normSq_sub, Complex.normSq_one, hz']
    simp only [one_mul, Complex.conj_re]; ring
  have hns2 : Complex.normSq (1 - (q : ℂ) * z) = 1 - 2 * q * z.re + q ^ 2 := by
    rw [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul,
        Complex.normSq_ofReal, hz']
    simp only [one_mul, mul_one, map_mul, Complex.conj_ofReal, Complex.conj_re,
               Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hns1, hns2]
  have hre_sq : z.re * z.re ≤ 1 := by
    have : z.re * z.re + z.im * z.im = 1 := by rw [← Complex.normSq_apply]; exact hz'
    linarith [mul_self_nonneg z.im]
  nlinarith [sq_nonneg (1 - q), mul_self_nonneg (1 + z.re), mul_self_nonneg (1 - z.re)]

lemma KostantFq_single_tendsto_one (z : ℂ) (hz1 : z ≠ 1) :
    Tendsto (fun q : ℝ => (1 - z) / (1 - (q : ℂ) * z))
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 1) := by
  have h1z : (1 : ℂ) - z ≠ 0 := by rw [Ne, sub_eq_zero]; exact Ne.symm hz1
  have h1z' : (1 : ℂ) - (1 : ℂ) * z ≠ 0 := by rwa [one_mul]
  suffices h : Tendsto (fun q : ℝ => (1 - z) / (1 - (q : ℂ) * z))
      (nhds 1) (nhds ((1 - z) / (1 - (1 : ℂ) * z))) by
    have hval : (1 - z) / (1 - (1 : ℂ) * z) = 1 := by rw [one_mul]; exact div_self h1z
    rw [hval] at h; exact h.mono_left nhdsWithin_le_nhds
  apply Tendsto.div tendsto_const_nhds
  · apply Tendsto.const_sub
    apply Tendsto.mul_const
    exact Complex.continuous_ofReal.continuousAt.tendsto
  · exact h1z'

lemma tendsto_norm_sq_sub_zero_complex {α : Type*} {l : Filter α} {f : α → ℂ} {a : ℂ}
    (hf : Tendsto f l (nhds a)) :
    Tendsto (fun x => ‖f x - a‖ ^ 2) l (nhds 0) := by
  have h1 : Tendsto (fun x => f x - a) l (nhds 0) := by
    rw [show (0 : ℂ) = a - a from by ring]; exact Tendsto.sub hf tendsto_const_nhds
  have h2 : Tendsto (fun x => ‖f x - a‖) l (nhds 0) := by
    rw [show (0 : ℝ) = ‖(0 : ℂ)‖ from by simp]; exact Tendsto.norm h1
  simpa using h2.pow 2

theorem kostant_lemma_13_2
    {ι T : Type*} [MeasurableSpace T] {μ : Measure T} [IsFiniteMeasure μ]
    (posRoots : Finset ι) (φ : ι → T → ℂ)
    (hφ_norm : ∀ α ∈ posRoots, ∀ x, ‖φ α x‖ = 1)
    (hφ_meas : ∀ α ∈ posRoots, Measurable (φ α))
    (hφ_ne_one : ∀ α ∈ posRoots, μ {x | φ α x = 1} = 0) :
    Tendsto (fun q : ℝ => ∫ x, ‖KostantFqProd posRoots φ q x - 1‖^2 ∂μ)
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 0) := by


  suffices h : Tendsto (fun q : ℝ => ∫ x, ‖KostantFqProd posRoots φ q x - 1‖ ^ 2 ∂μ)
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds (∫ _ : T, (0 : ℝ) ∂μ)) by
    simp only [integral_zero] at h; exact h
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => ((2 : ℝ) ^ posRoots.card + 1) ^ 2)

  · apply eventually_of_mem self_mem_nhdsWithin
    intro q _
    exact ((Finset.measurable_prod posRoots fun α hα =>
      (measurable_const.sub (hφ_meas α hα)).div
        (measurable_const.sub (measurable_const.mul (hφ_meas α hα)))).sub
      measurable_const).norm.pow_const _ |>.aestronglyMeasurable

  · apply eventually_of_mem self_mem_nhdsWithin
    intro q hq
    apply Eventually.of_forall; intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hq0 := hq.1; have hq1 := hq.2


    have hpn : ‖KostantFqProd posRoots φ q x‖ ≤ 2 ^ posRoots.card := by
      unfold KostantFqProd
      rw [show ‖∏ α ∈ posRoots, KostantFqSingleFactor q (φ α x)‖ =
          ∏ α ∈ posRoots, ‖KostantFqSingleFactor q (φ α x)‖ from by
        change (normHom : ℂ →*₀ ℝ) _ = _; exact map_prod normHom _ posRoots]
      calc ∏ α ∈ posRoots, ‖KostantFqSingleFactor q (φ α x)‖
          ≤ ∏ _ ∈ posRoots, (2 : ℝ) :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => by
              unfold KostantFqSingleFactor; rw [norm_div]
              rw [div_le_iff₀ (norm_pos_iff.mpr
                (KostantFq_denom_ne_zero q (φ i x) (le_of_lt hq0) hq1 (hφ_norm i hi x)))]
              nlinarith [KostantFq_normSq_bound q (φ i x) (le_of_lt hq0) (hφ_norm i hi x),
                sq_nonneg (‖(1 : ℂ) - φ i x‖ - 2 * ‖(1 : ℂ) - (q : ℂ) * φ i x‖),
                norm_nonneg ((1 : ℂ) - φ i x), norm_nonneg ((1 : ℂ) - (q : ℂ) * φ i x),
                Complex.normSq_eq_norm_sq (1 - φ i x),
                Complex.normSq_eq_norm_sq (1 - (q : ℂ) * φ i x)]
        _ = 2 ^ posRoots.card := by rw [Finset.prod_const, Finset.card_def]

    have h_sub : ‖KostantFqProd posRoots φ q x - 1‖ ≤ 2 ^ posRoots.card + 1 := by
      linarith [norm_sub_le (KostantFqProd posRoots φ q x) 1, norm_one (α := ℂ)]
    exact pow_le_pow_left₀ (norm_nonneg _) h_sub 2

  · exact integrable_const _

  ·
    have hae : ∀ᵐ x ∂μ, ∀ α ∈ posRoots, φ α x ≠ 1 := by
      rw [ae_iff]
      apply measure_mono_null (show {a | ¬∀ α ∈ posRoots, φ α a ≠ 1} ⊆
          ⋃ α ∈ (posRoots : Set ι), {x | φ α x = 1} from by
        intro x hx; push Not at hx
        exact let ⟨α, hα, heq⟩ := hx; Set.mem_biUnion hα heq)
      exact (measure_biUnion_null_iff posRoots.countable_toSet).mpr
        fun α hα => hφ_ne_one α hα

    filter_upwards [hae] with t ht
    apply tendsto_norm_sq_sub_zero_complex

    show Tendsto (fun q => ∏ α ∈ posRoots, KostantFqSingleFactor q (φ α t))
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 1)
    rw [show (1 : ℂ) = ∏ _ ∈ posRoots, (1 : ℂ) from by simp]
    exact @tendsto_finset_prod ι ℝ ℂ _ _ _
      (fun α (q : ℝ) => KostantFqSingleFactor q (φ α t)) _ _
      posRoots (fun α hα => KostantFq_single_tendsto_one (φ α t) (ht α hα))

end
