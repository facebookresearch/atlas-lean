/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ChevalleyRestriction
import Atlas.LieGroups.code.SyzygiesKoszul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Invariant.Basic

noncomputable section

universe u

def qIntegerCST (d : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range d, PowerSeries.X ^ i

def quotientGradedComponent (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (N : ℕ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ ⧸ I) :=
  Submodule.map (I.mkQ.restrictScalars ℂ)
    (MvPolynomial.homogeneousSubmodule (Fin n) ℂ N)

def polyRepresentation {n : ℕ} {G : Type*} [Group G]
    (algAct : G →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)) :
    Representation ℂ G (MvPolynomial (Fin n) ℂ) where
  toFun g := (algAct g).toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [map_mul]

structure CSTPartIIData where
  n : ℕ
  G : Type*
  [instGroup : Group G]
  [instFintype : Fintype G]
  [instDecEq : DecidableEq G]
  linearAction : G →* ((Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
  is_reflection_group : IsComplexReflectionGroup G linearAction
  algAct : G →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
  invariantSubalgebra : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)
  mem_invariant_iff : ∀ p : MvPolynomial (Fin n) ℂ,
    p ∈ invariantSubalgebra ↔ ∀ g : G, algAct g p = p
  basicInvariants : Fin n → ↥invariantSubalgebra
  alg_independent : AlgebraicIndependent ℂ basicInvariants
  generators_generate : Algebra.adjoin ℂ (Set.range basicInvariants) = ⊤
  degrees : Fin n → ℕ
  basicInvariants_homogeneous : ∀ i,
    (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ).IsHomogeneous (degrees i)
  basicInvariants_vanish : ∀ (v : Fin n → ℂ),
    (∀ i, MvPolynomial.eval v (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ) = 0) → v = 0
  R₀ : Type*
  [instR₀AddCommGroup : AddCommGroup R₀]
  [instR₀Module : Module ℂ R₀]
  [instR₀FiniteDimensional : FiniteDimensional ℂ R₀]
  R₀Action : Representation ℂ G R₀
  R₀_quotient_iso : R₀ ≃ₗ[ℂ]
    (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun i => (basicInvariants i : MvPolynomial (Fin n) ℂ))))
  hilbertR₀ : PowerSeries ℤ
  hilbertR₀_coeff_eq : ∀ N : ℕ,
    (PowerSeries.coeff N) hilbertR₀ =
      ↑(Module.finrank ℂ
        (quotientGradedComponent n
          (Ideal.span (Set.range (fun i => (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ))))
          N))

attribute [instance] CSTPartIIData.instGroup CSTPartIIData.instFintype
attribute [instance] CSTPartIIData.instDecEq
attribute [instance] CSTPartIIData.instR₀AddCommGroup CSTPartIIData.instR₀Module
attribute [instance] CSTPartIIData.instR₀FiniteDimensional

def CSTPartIIData.polyRep (cst : CSTPartIIData) :
    Representation ℂ cst.G (MvPolynomial (Fin cst.n) ℂ) :=
  polyRepresentation cst.algAct

variable (cst : CSTPartIIData)

theorem cst_pos_degrees (cst : CSTPartIIData) : ∀ i, 0 < cst.degrees i := by
  intro i
  by_contra h
  simp only [not_lt, Nat.le_zero] at h


  have h0 := cst.basicInvariants_homogeneous i
  rw [h] at h0
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous] at h0
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
  set c := MvPolynomial.coeff 0 (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)

  have hxi : cst.basicInvariants i = algebraMap ℂ _ c := by
    ext; simp [h0, MvPolynomial.algebraMap_eq]

  have hp : MvPolynomial.aeval cst.basicInvariants
      (MvPolynomial.X i - MvPolynomial.C c) = (0 : ↥cst.invariantSubalgebra) := by
    simp [hxi]
  have hne : MvPolynomial.X i - MvPolynomial.C c ≠
      (0 : MvPolynomial (Fin cst.n) ℂ) := by
    intro h
    have h1 := sub_eq_zero.mp h
    have h2 := MvPolynomial.totalDegree_X (R := ℂ) i
    have h3 := MvPolynomial.totalDegree_C (σ := Fin cst.n) c
    linarith [congr_arg MvPolynomial.totalDegree h1]
  exact hne (cst.alg_independent hp)

theorem cst_finite_over_invariants (cst : CSTPartIIData) :
    Module.Finite (Algebra.adjoin ℂ (Set.range (fun i =>
      (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ))))
      (MvPolynomial (Fin cst.n) ℂ) := by

  set S := Algebra.adjoin ℂ (Set.range (fun i =>
    (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)))

  haveI : Algebra.FiniteType (↥S) (MvPolynomial (Fin cst.n) ℂ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _


  suffices Algebra.IsIntegral (↥S) (MvPolynomial (Fin cst.n) ℂ) from
    Algebra.IsIntegral.finite

  have hS_eq : S = cst.invariantSubalgebra := by
    apply le_antisymm
    ·
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact (cst.basicInvariants i).2
    ·
      intro p hp
      have hmem : (⟨p, hp⟩ : ↥cst.invariantSubalgebra) ∈
          Algebra.adjoin ℂ (Set.range cst.basicInvariants) :=
        cst.generators_generate ▸ Algebra.mem_top

      have key : ∀ (x : ↥cst.invariantSubalgebra),
          x ∈ Algebra.adjoin ℂ (Set.range cst.basicInvariants) →
          (x : MvPolynomial (Fin cst.n) ℂ) ∈ S := by
        intro x hx
        induction hx using Algebra.adjoin_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        | algebraMap r => exact S.algebraMap_mem r
        | add _ _ _ _ ha hb => exact S.add_mem ha hb
        | mul _ _ _ _ ha hb => exact S.mul_mem ha hb
      exact key ⟨p, hp⟩ hmem

  letI : MulSemiringAction cst.G (MvPolynomial (Fin cst.n) ℂ) :=
    MulSemiringAction.compHom _
      { toFun := fun g => (cst.algAct g).toRingEquiv
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
  have hsmul : ∀ (g : cst.G) (f : MvPolynomial (Fin cst.n) ℂ),
      g • f = cst.algAct g f := fun _ _ => rfl

  letI : SMulCommClass cst.G ℂ (MvPolynomial (Fin cst.n) ℂ) :=
    ⟨fun g c f => by
      show cst.algAct g (c • f) = c • (cst.algAct g f)
      rw [Algebra.smul_def, map_mul, (cst.algAct g).commutes, ← Algebra.smul_def]⟩

  haveI : Algebra.IsInvariant (↥S) (MvPolynomial (Fin cst.n) ℂ) cst.G := by
    constructor
    intro b hb
    have hb_inv : b ∈ cst.invariantSubalgebra := by
      rw [cst.mem_invariant_iff]; intro g; exact hsmul g b ▸ hb g
    have hb_S : b ∈ S := hS_eq ▸ hb_inv
    exact ⟨⟨b, hb_S⟩, rfl⟩

  exact Algebra.IsInvariant.isIntegral (↥S) (MvPolynomial (Fin cst.n) ℂ) cst.G

lemma qIntegerCST_eq_qAnalog (d : ℕ) : qIntegerCST d = qAnalog d := by
  simp only [qIntegerCST, qAnalog]
  ext n
  simp [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_X_pow]

lemma quotientGradedComponent_eq_quotientHomogeneousSubmodule
    (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (N : ℕ) :
    quotientGradedComponent n I N = quotientHomogeneousSubmodule ℂ n I N := rfl

lemma isHomogeneous_to_coeff_form {n : ℕ} {p : MvPolynomial (Fin n) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m p ≠ 0 → (m.sum fun _ e => e) = d := by
  intro m hm
  have := hp hm
  simp [Finsupp.weight_apply] at this
  exact this


def qIntPoly (d : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range d, Polynomial.X ^ i

lemma qIntPoly_coe_eq_qIntegerCST (d : ℕ) :
    (qIntPoly d : PowerSeries ℤ) = qIntegerCST d := by
  ext n; simp only [qIntPoly, qIntegerCST]
  simp [Polynomial.coeff_coe, Polynomial.coeff_X_pow, PowerSeries.coeff_X_pow, map_sum]

lemma qIntPoly_eval_one (d : ℕ) : Polynomial.eval 1 (qIntPoly d) = ↑d := by
  simp only [qIntPoly]; simp [Polynomial.eval_finset_sum, Polynomial.eval_pow]

lemma prod_qIntPoly_coe_eq_prod_qIntegerCST {n : ℕ} (degrees : Fin n → ℕ) :
    ((∏ i : Fin n, qIntPoly (degrees i) : Polynomial ℤ) : PowerSeries ℤ) =
    ∏ i : Fin n, qIntegerCST (degrees i) := by
  rw [show (↑(∏ i : Fin n, qIntPoly (degrees i)) : PowerSeries ℤ) =
    Polynomial.coeToPowerSeries.ringHom (∏ i, qIntPoly (degrees i)) from rfl]
  rw [map_prod]; congr 1; funext i
  show (qIntPoly (degrees i) : PowerSeries ℤ) = _
  exact qIntPoly_coe_eq_qIntegerCST (degrees i)

lemma prod_qIntCST_coeff_eq_poly_coeff {n : ℕ} (degrees : Fin n → ℕ) (N : ℕ) :
    (PowerSeries.coeff N) (∏ i : Fin n, qIntegerCST (degrees i)) =
    (∏ i : Fin n, qIntPoly (degrees i)).coeff N := by
  rw [← prod_qIntPoly_coe_eq_prod_qIntegerCST]; simp [Polynomial.coeff_coe]

lemma sum_poly_coeff_eq_eval_one {p : Polynomial ℤ} {B : ℕ} (hB : p.natDegree < B) :
    ∑ i ∈ Finset.range B, p.coeff i = Polynomial.eval 1 p := by
  rw [Polynomial.eval_eq_sum_range]; simp only [one_pow, mul_one]; symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro x hx1 hx2
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Finset.mem_range] at hx1 hx2; omega)

lemma sum_prod_qIntCST_coeff_eq_prod_degrees {n : ℕ} (degrees : Fin n → ℕ) {B : ℕ}
    (hB : (∏ i : Fin n, qIntPoly (degrees i)).natDegree < B) :
    ∑ N ∈ Finset.range B,
      (PowerSeries.coeff N) (∏ i : Fin n, qIntegerCST (degrees i)) =
    ↑(∏ i : Fin n, degrees i) := by
  simp_rw [prod_qIntCST_coeff_eq_poly_coeff]
  rw [sum_poly_coeff_eq_eval_one hB]
  simp [Polynomial.eval_prod, qIntPoly_eval_one]






section CSTHomGradedProjective
set_option synthInstance.maxHeartbeats 200000



end CSTHomGradedProjective














end
