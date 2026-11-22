/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.DegreePullback
import Atlas.ArithmeticGeometry.code.RationalLineCriterion

structure ClosedPointRes (k : Type*) [Field k] where
  residueField : Type*
  [residueFieldField : Field residueField]
  [residueFieldAlgebra : Algebra k residueField]
  [finiteDimensional : FiniteDimensional k residueField]

attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional

namespace ClosedPointRes

variable {k : Type*} [Field k]

noncomputable def degreePoint (P : ClosedPointRes k) : ℕ :=
  Module.finrank k P.residueField


end ClosedPointRes

abbrev CurveDivisor (C : Type*) := C →₀ ℤ

namespace CurveDivisor

variable {C : Type*}

noncomputable def coeff (D : CurveDivisor C) (P : C) : ℤ := D P

noncomputable def divisorSupport (D : CurveDivisor C) : Finset C := D.support

variable (C) in
noncomputable def degree : CurveDivisor C →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

@[simp]
theorem degree_single (P : C) (n : ℤ) :
    degree C (Finsupp.single P n) = n := by
  simp [degree]

@[simp]
theorem degree_zero : degree C (0 : CurveDivisor C) = 0 :=
  map_zero _

@[simp]
theorem degree_add (D₁ D₂ : CurveDivisor C) :
    degree C (D₁ + D₂) = degree C D₁ + degree C D₂ :=
  map_add _ _ _

@[simp]
theorem degree_neg (D : CurveDivisor C) :
    degree C (-D) = -(degree C D) :=
  map_neg _ _

theorem degree_sub (D₁ D₂ : CurveDivisor C) :
    degree C (D₁ - D₂) = degree C D₁ - degree C D₂ :=
  map_sub _ _ _

theorem degree_eq_sum (D : CurveDivisor C) :
    degree C D = D.sum (fun _ n => n) := by
  simp [degree, Finsupp.liftAddHom_apply]
  rfl

noncomputable def degreeWeighted (deg : C → ℕ) : CurveDivisor C →+ ℤ :=
  Finsupp.liftAddHom (fun p => (deg p : ℤ) • AddMonoidHom.id ℤ)


theorem degreeWeighted_sub (deg : C → ℕ) (D₁ D₂ : CurveDivisor C) :
    degreeWeighted deg (D₁ - D₂) = degreeWeighted deg D₁ - degreeWeighted deg D₂ :=
  map_sub _ _ _

theorem degreeWeighted_eq_sum (deg : C → ℕ) (D : CurveDivisor C) :
    degreeWeighted deg D = D.sum (fun p n => n * (deg p : ℤ)) := by
  simp only [degreeWeighted, Finsupp.liftAddHom_apply, Finsupp.sum]
  congr 1
  ext p
  simp [mul_comm]


section GaloisAction

variable {G : Type*} [Group G] [MulAction G C]

noncomputable instance galoisSMul : SMul G (CurveDivisor C) :=
  Finsupp.comapSMul

noncomputable instance galoisMulAction : MulAction G (CurveDivisor C) :=
  Finsupp.comapMulAction


def IsDefinedOverK (G : Type*) [Group G] [MulAction G C]
    (D : CurveDivisor C) : Prop :=
  ∀ (σ : G), σ • D = D


end GaloisAction

noncomputable def divZeros (D : CurveDivisor C) : CurveDivisor C := D ⊔ 0

noncomputable def divPoles (D : CurveDivisor C) : CurveDivisor C := (-D) ⊔ 0

@[simp]
theorem divZeros_apply (D : CurveDivisor C) (P : C) : divZeros D P = max (D P) 0 := by
  simp [divZeros, Finsupp.sup_apply, Finsupp.coe_zero]

@[simp]
theorem divPoles_apply (D : CurveDivisor C) (P : C) : divPoles D P = max (-(D P)) 0 := by
  simp [divPoles, Finsupp.sup_apply, Finsupp.coe_zero, Finsupp.neg_apply]

theorem divZeros_nonneg (D : CurveDivisor C) (P : C) : 0 ≤ divZeros D P := by
  simp

theorem divPoles_nonneg (D : CurveDivisor C) (P : C) : 0 ≤ divPoles D P := by
  simp

theorem eq_divZeros_sub_divPoles (D : CurveDivisor C) : D = divZeros D - divPoles D := by
  ext P
  simp [Finsupp.sub_apply]

end CurveDivisor

abbrev ClosedPoint (G : Type*) (C : Type*) [Group G] [MulAction G C] :=
  MulAction.orbitRel.Quotient G C

namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

def mk (P : C) : ClosedPoint G C := ⟦P⟧

def toOrbit (P : ClosedPoint G C) : Set C :=
  MulAction.orbitRel.Quotient.orbit P

theorem mk_eq_mk_iff (P Q : C) :
    mk (G := G) P = mk Q ↔ P ∈ MulAction.orbit G Q := by
  simp only [mk]
  constructor
  · intro h
    exact MulAction.orbitRel_apply.mp (Quotient.exact' h)
  · intro h
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr h)

end ClosedPoint

noncomputable def degreeClosedPoint (k K : Type*) [Field k] [Field K] [Algebra k K] : ℕ :=
  Module.finrank k K


abbrev RationalDivisor (G : Type*) (C : Type*) [Group G] [MulAction G C] :=
  ClosedPoint G C →₀ ℤ

namespace RationalDivisor

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

noncomputable def coeff (D : RationalDivisor G C) (P : ClosedPoint G C) : ℤ := D P

noncomputable def rationalDivisorSupport (D : RationalDivisor G C) :
    Finset (ClosedPoint G C) := D.support

end RationalDivisor

class CurveWithOrd (C : Type*) (F : Type*) [Field F] where
  ord : C → Fˣ → ℤ
  ord_mul : ∀ (P : C) (f g : Fˣ), ord P (f * g) = ord P f + ord P g
  ord_add : ∀ (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0),
    ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥ min (ord P f) (ord P g)
  uniformizer_exists : ∀ (P : C), ∃ (π : Fˣ), ord P π = 1


class FunctionFieldCurve (C : Type*) (F : Type*) [Field F]
    extends CurveWithOrd C F where
  isCoordRingElem : Fˣ → Prop
  fraction_rep : ∀ (f : Fˣ), ∃ (g h : Fˣ), isCoordRingElem g ∧ isCoordRingElem h ∧
    f = g * h⁻¹
  ord_nonneg_of_coordRingElem : ∀ (f : Fˣ), isCoordRingElem f →
    ∀ (P : C), 0 ≤ CurveWithOrd.ord (F := F) P f
  zeroLocus_finite : ∀ (f : Fˣ), isCoordRingElem f →
    Set.Finite {P : C | 0 < CurveWithOrd.ord (F := F) P f}


theorem FunctionFieldCurve.coordRing_finite_support {C : Type*} {F : Type*} [Field F]
    [inst : FunctionFieldCurve C F] (f : Fˣ) (hf : inst.isCoordRingElem f) :
    (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by
  apply Set.Finite.subset (inst.zeroLocus_finite f hf)
  intro P hP
  simp only [Set.mem_setOf_eq, Function.mem_support] at hP ⊢
  have := inst.ord_nonneg_of_coordRingElem f hf P
  omega

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [CurveWithOrd C F]

theorem ord_one (P : C) : ord (F := F) P 1 = 0 := by
  have h := ord_mul (F := F) P 1 1
  simp at h
  linarith

theorem ord_inv (P : C) (f : Fˣ) : ord (F := F) P f⁻¹ = -ord P f := by
  have h := ord_mul (F := F) P f f⁻¹
  simp only [mul_inv_cancel] at h
  rw [ord_one] at h
  linarith

end CurveWithOrd

theorem ord_finite_support {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]
    (f : Fˣ) :
    (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by

  obtain ⟨g, h, hg, hh, hf⟩ := FunctionFieldCurve.fraction_rep (C := C) (F := F) f

  have hg_fin := FunctionFieldCurve.coordRing_finite_support g hg
  have hh_fin := FunctionFieldCurve.coordRing_finite_support h hh

  apply Set.Finite.subset (hg_fin.union hh_fin)
  intro P hP
  simp only [Function.mem_support, Set.mem_union] at hP ⊢


  by_contra h_contra
  push Not at h_contra
  obtain ⟨hgP, hhP⟩ := h_contra
  apply hP
  rw [hf, CurveWithOrd.ord_mul, CurveWithOrd.ord_inv]
  omega

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

noncomputable def principalDivisor (f : Fˣ) : CurveDivisor C :=
  Finsupp.ofSupportFinite (fun P => ord P f) (ord_finite_support f)

@[simp]
theorem principalDivisor_apply (f : Fˣ) (P : C) :
    (principalDivisor f : CurveDivisor C) P = ord P f := by
  simp [principalDivisor, Finsupp.ofSupportFinite]

@[simp]
theorem principalDivisor_one : principalDivisor (C := C) (F := F) (1 : Fˣ) = 0 := by
  ext P
  simp [ord_one]

theorem principalDivisor_mul (f g : Fˣ) :
    principalDivisor (C := C) (f * g) = principalDivisor f + principalDivisor g := by
  ext P
  simp [ord_mul]

theorem principalDivisor_inv (f : Fˣ) :
    principalDivisor (C := C) f⁻¹ = -principalDivisor f := by
  ext P
  simp [ord_inv]

noncomputable def principalDivisorHom :
    Fˣ →* Multiplicative (CurveDivisor C) where
  toFun f := Multiplicative.ofAdd (principalDivisor f)
  map_one' := by simp
  map_mul' f g := by
    simp only [principalDivisor_mul]
    rfl

noncomputable def principalDivisors : AddSubgroup (CurveDivisor C) where
  carrier := Set.range (fun f : Fˣ => principalDivisor (C := C) f)
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, principalDivisor_mul f g⟩
  zero_mem' := ⟨1, principalDivisor_one⟩
  neg_mem' := by
    rintro _ ⟨f, rfl⟩
    exact ⟨f⁻¹, principalDivisor_inv f⟩

def IsPrincipal (D : CurveDivisor C) : Prop :=
  D ∈ principalDivisors (F := F)

theorem isPrincipal_iff (D : CurveDivisor C) :
    IsPrincipal (F := F) D ↔ ∃ f : Fˣ, principalDivisor f = D := by
  simp [IsPrincipal, principalDivisors, Set.mem_range]


end CurveWithOrd

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

noncomputable def divAddHom : Additive Fˣ →+ CurveDivisor C where
  toFun f := principalDivisor (Additive.toMul f)
  map_zero' := by show principalDivisor (1 : Fˣ) = 0; exact principalDivisor_one
  map_add' f g := by
    show principalDivisor (_ * _) = principalDivisor _ + principalDivisor _
    exact principalDivisor_mul _ _


abbrev PicardGroup (C : Type*) (F : Type*) [Field F] [FunctionFieldCurve C F] :=
  CurveDivisor C ⧸ principalDivisors (C := C) (F := F)

noncomputable def toPicardGroup : CurveDivisor C →+ PicardGroup C F :=
  QuotientAddGroup.mk' (principalDivisors (F := F))

theorem exact_at_divisors :
    AddMonoidHom.range (divAddHom (C := C) (F := F)) =
    (toPicardGroup (C := C) (F := F)).ker := by
  rw [toPicardGroup, QuotientAddGroup.ker_mk']
  ext D
  simp only [AddMonoidHom.mem_range, principalDivisors]
  constructor
  · rintro ⟨f, rfl⟩; exact ⟨Additive.toMul f, rfl⟩
  · rintro ⟨f, rfl⟩; exact ⟨Additive.ofMul f, rfl⟩


theorem ker_toPicardGroup :
    (toPicardGroup (C := C) (F := F)).ker = principalDivisors (F := F) :=
  QuotientAddGroup.ker_mk' _


end CurveWithOrd

class CurveWithConstants (C : Type*) (k : Type*) (F : Type*) [Field k] [Field F]
    [Algebra k F] extends FunctionFieldCurve C F where
  const_isCoordRingElem : ∀ (a : kˣ),
    toFunctionFieldCurve.isCoordRingElem (Units.map (algebraMap k F).toMonoidHom a)
  const_inv_isCoordRingElem : ∀ (a : kˣ),
    toFunctionFieldCurve.isCoordRingElem (Units.map (algebraMap k F).toMonoidHom a)⁻¹
  algClosed_in_extension : ∀ (x : F), IsAlgebraic k x → x ∈ (algebraMap k F).range
  ord_zero_algebraic : ∀ (f : Fˣ), (∀ P : C, CurveWithOrd.ord P f = 0) →
    IsAlgebraic k (f : F)
  residue_eval : ∀ (P : C), ∃ (evalP : F →ₗ[k] k),
    ∀ (f : Fˣ), CurveWithOrd.ord P f ≥ 0 → evalP (f : F) = 0 →
      CurveWithOrd.ord P f ≥ 1


theorem CurveWithConstants.ord_constant {C : Type*} {k : Type*} {F : Type*}
    [Field k] [Field F] [Algebra k F] [inst : CurveWithConstants C k F]
    (P : C) (a : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) = 0 := by
  have h_pos : (0 : ℤ) ≤ CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) :=
    inst.toFunctionFieldCurve.ord_nonneg_of_coordRingElem _ (inst.const_isCoordRingElem a) P
  have h_neg : (0 : ℤ) ≤ CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a)⁻¹ :=
    inst.toFunctionFieldCurve.ord_nonneg_of_coordRingElem _ (inst.const_inv_isCoordRingElem a) P
  have h_inv : CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a)⁻¹ =
    -CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) :=
    CurveWithOrd.ord_inv P _
  omega

theorem CurveWithConstants.ker_div_eq_constants {C : Type*} {k : Type*} {F : Type*}
    [Field k] [Field F] [Algebra k F] [inst : CurveWithConstants C k F] (f : Fˣ)
    (hf : ∀ P : C, CurveWithOrd.ord P f = 0) :
    ∃ a : kˣ, Units.map (algebraMap k F).toMonoidHom a = f := by

  have h_alg : IsAlgebraic k (f : F) := inst.ord_zero_algebraic f hf

  obtain ⟨a, ha⟩ := inst.algClosed_in_extension (f : F) h_alg

  have ha_ne : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact Units.ne_zero f ha.symm

  exact ⟨Units.mk0 a ha_ne, Units.ext (by simp [Units.coe_map, ha])⟩

namespace CurveWithConstants

variable {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
  [Algebra k F] [CurveWithConstants C k F]

open CurveWithOrd

noncomputable def constantsEmb : kˣ →* Fˣ :=
  Units.map (algebraMap k F).toMonoidHom

@[simp]
theorem constantsEmb_def (a : kˣ) :
    (constantsEmb (k := k) (F := F) a : Fˣ) =
    Units.map (algebraMap k F).toMonoidHom a := rfl

theorem constantsEmb_injective :
    Function.Injective (constantsEmb (k := k) (F := F)) := by
  intro a b h
  ext
  have := congr_arg Units.val h
  simp only [constantsEmb, Units.coe_map] at this
  exact (algebraMap k F).injective this

theorem principalDivisor_constant (a : kˣ) :
    principalDivisor (C := C) (constantsEmb (F := F) a) = 0 := by
  ext P
  simp only [principalDivisor_apply, Finsupp.coe_zero, Pi.zero_apply,
    constantsEmb_def, ord_constant]

theorem exact_at_functionField (f : Fˣ) :
    principalDivisor (C := C) f = 0 ↔
    ∃ a : kˣ, constantsEmb (F := F) a = f := by
  constructor
  · intro hf
    have hord : ∀ P : C, ord P f = 0 := by
      intro P
      have := Finsupp.ext_iff.mp hf P
      simp at this
      exact this
    exact ker_div_eq_constants f hord
  · rintro ⟨a, rfl⟩
    exact principalDivisor_constant a

end CurveWithConstants

section TriangleEquality

variable {F : Type*} [Field F]
variable {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀]

theorem triangle_equality_valuation (v : AddValuation F Γ₀) {x y : F}
    (h : v x ≠ v y) : v (x + y) = min (v x) (v y) := by

  obtain hlt | hlt := Ne.lt_or_gt h
  ·
    rw [min_eq_left hlt.le]

    have h_le : v x ≤ v (x + y) := by
      have := AddValuation.map_add v x y
      rwa [min_eq_left hlt.le] at this

    by_contra h_ne
    have h_strict : v x < v (x + y) := lt_of_le_of_ne h_le (Ne.symm h_ne)


    have key : min (v (x + y)) (v (-y)) ≤ v ((x + y) + (-y)) :=
      AddValuation.map_add v (x + y) (-y)

    rw [AddValuation.map_neg, show (x + y) + (-y) = x from by ring] at key

    exact absurd (lt_min h_strict hlt) (not_lt.mpr key)
  ·
    rw [add_comm, min_comm, min_eq_left hlt.le]
    have h_le : v y ≤ v (y + x) := by
      have := AddValuation.map_add v y x
      rwa [min_eq_left hlt.le] at this
    by_contra h_ne
    have h_strict : v y < v (y + x) := lt_of_le_of_ne h_le (Ne.symm h_ne)
    have key : min (v (y + x)) (v (-x)) ≤ v ((y + x) + (-x)) :=
      AddValuation.map_add v (y + x) (-x)
    rw [AddValuation.map_neg, show (y + x) + (-x) = y from by ring] at key
    exact absurd (lt_min h_strict hlt) (not_lt.mpr key)

end TriangleEquality

structure FunctionFieldPlace (F : Type*) [Field F] (k : Type*) [Field k] where
  valuationSubring : ValuationSubring F
  isPrincipalIdealRing : IsPrincipalIdealRing valuationSubring
  notIsField : ¬ IsField valuationSubring
  residueFieldEquiv : letI := valuationSubring.isLocalRing
    IsLocalRing.ResidueField valuationSubring ≃+* k

namespace FunctionFieldPlace

variable {F : Type*} [Field F] {k : Type*} [Field k]

instance (P : FunctionFieldPlace F k) : IsPrincipalIdealRing P.valuationSubring :=
  P.isPrincipalIdealRing

instance (P : FunctionFieldPlace F k) : IsFractionRing P.valuationSubring F :=
  inferInstance

end FunctionFieldPlace

abbrev FunctionFieldDivisor (F : Type*) [Field F] (k : Type*) [Field k] :=
  FunctionFieldPlace F k →₀ ℤ

namespace FunctionFieldDivisor

variable {F : Type*} [Field F] {k : Type*} [Field k]

noncomputable def coeff (D : FunctionFieldDivisor F k) (P : FunctionFieldPlace F k) : ℤ :=
  D P

noncomputable def divisorSupport (D : FunctionFieldDivisor F k) :
    Finset (FunctionFieldPlace F k) :=
  D.support

end FunctionFieldDivisor

noncomputable section

namespace ArithmeticGeometry

namespace FunctionField_k

variable {k : Type*} [Field k]
variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

def Morphism.ramificationIndex
    (φ : F₂ →+* F₁)
    (ordP : F₁ˣ → ℤ)
    (tQ : F₂ˣ)
    : ℤ :=
  ordP (Units.map φ.toMonoidHom tQ)


def Morphism.IsUnramifiedAt
    (φ : F₂ →+* F₁)
    (ordP : F₁ˣ → ℤ)
    (tQ : F₂ˣ) : Prop :=
  Morphism.ramificationIndex φ ordP tQ = 1


def Morphism.IsUnramified
    (φ : F₂ →+* F₁)
    (places : Type*)
    (ordAt : places → F₁ˣ → ℤ)
    (uniformizerAt : places → F₂ˣ)
    : Prop :=
  ∀ P : places, Morphism.IsUnramifiedAt φ (ordAt P) (uniformizerAt P)


end FunctionField_k

end ArithmeticGeometry

namespace CurveWithConstants

variable {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
  [Algebra k F] [CurveWithConstants C k F]

open CurveWithOrd CurveDivisor

theorem divZeros_principalDivisor_constant (a : kˣ) :
    divZeros (principalDivisor (C := C) (constantsEmb (F := F) a)) = 0 := by
  have h := principalDivisor_constant (C := C) (F := F) (k := k) a
  rw [h]
  ext P
  simp [divZeros]

theorem divPoles_principalDivisor_constant (a : kˣ) :
    divPoles (principalDivisor (C := C) (constantsEmb (F := F) a)) = 0 := by
  have h := principalDivisor_constant (C := C) (F := F) (k := k) a
  rw [h]
  ext P
  simp [divPoles]

theorem degree_divZeros_principalDivisor_constant (a : kˣ) :
    degree C (divZeros (principalDivisor (C := C) (constantsEmb (F := F) a))) = 0 := by
  rw [divZeros_principalDivisor_constant a]
  exact degree_zero

theorem degree_divPoles_principalDivisor_constant (a : kˣ) :
    degree C (divPoles (principalDivisor (C := C) (constantsEmb (F := F) a))) = 0 := by
  rw [divPoles_principalDivisor_constant a]
  exact degree_zero

lemma degree_divZeros_principalDivisor_eq_sum_ord
    (f : Fˣ) :
    degree C (divZeros (principalDivisor (C := C) f)) =
    (divZeros (principalDivisor (C := C) f)).support.sum (fun P => ord P f) := by

  simp only [degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro P hP

  have hne : (divZeros (principalDivisor (C := C) f)) P ≠ 0 :=
    Finsupp.mem_support_iff.mp hP
  simp only [divZeros_apply, principalDivisor_apply, AddMonoidHom.id_apply] at hne ⊢
  omega

lemma nonconstant_transcendental
    {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
    [Algebra k F] [CurveWithConstants C k F]
    (f : Fˣ)
    (hf : ¬ ∃ a : kˣ, constantsEmb (F := F) a = f) :
    Transcendental k (f : F) := by
  intro h_alg
  apply hf
  obtain ⟨a, ha⟩ := algClosed_in_extension C (f : F) h_alg
  have ha_ne : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha; exact Units.ne_zero f ha.symm
  exact ⟨Units.mk0 a ha_ne, Units.ext (by simp [constantsEmb, Units.coe_map, ha])⟩





theorem divPoles_eq_divZeros_inv (f : Fˣ) :
    divPoles (principalDivisor (C := C) f) = divZeros (principalDivisor (C := C) f⁻¹) := by
  rw [principalDivisor_inv]
  rfl

theorem not_constant_inv (f : Fˣ)
    (hf : ¬ ∃ a : kˣ, constantsEmb (F := F) a = f) :
    ¬ ∃ a : kˣ, constantsEmb (F := F) a = f⁻¹ := by
  intro ⟨a, ha⟩
  apply hf
  exact ⟨a⁻¹, by
    have : constantsEmb (F := F) a⁻¹ = (constantsEmb (F := F) a)⁻¹ :=
      map_inv (constantsEmb (F := F)) a
    rw [this, ha, inv_inv]⟩

theorem adjoin_inv_eq (f : Fˣ) :
    IntermediateField.adjoin k ({((f⁻¹ : Fˣ) : F)} : Set F) =
    IntermediateField.adjoin k ({(f : F)} : Set F) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx, Units.val_inv_eq_inv_val]
    exact (IntermediateField.adjoin k ({(f : F)} : Set F)).inv_mem
      (IntermediateField.subset_adjoin k _ (Set.mem_singleton _))
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    have : ((f⁻¹ : Fˣ) : F)⁻¹ = (f : F) := by
      rw [Units.val_inv_eq_inv_val, inv_inv]
    rw [← this]
    exact (IntermediateField.adjoin k ({((f⁻¹ : Fˣ) : F)} : Set F)).inv_mem
      (IntermediateField.subset_adjoin k _ (Set.mem_singleton _))





end CurveWithConstants

namespace CurveWithOrd

variable {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
  [Algebra k F] [CurveWithConstants C k F]

open CurveDivisor CurveWithConstants




end CurveWithOrd

end

structure CurveMorphismData (C₁ : Type*) (C₂ : Type*) where
  toFun : C₁ → C₂
  ramificationIndex : C₁ → ℤ
  fiber : C₂ → Finset C₁
  fiber_maps_to : ∀ Q : C₂, ∀ P ∈ fiber Q, toFun P = Q
  fiber_complete : ∀ Q : C₂, ∀ P : C₁, toFun P = Q → P ∈ fiber Q
  residueFieldDegreeRatio : C₁ → ℤ

noncomputable section

namespace CurveMorphismData

variable {C₁ C₂ : Type*}


def pullbackPoint (φ : CurveMorphismData C₁ C₂) (Q : C₂) : CurveDivisor C₁ :=
  (φ.fiber Q).sum (fun P => Finsupp.single P (φ.ramificationIndex P))

def pullback (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₂ →+ CurveDivisor C₁ :=
  Finsupp.liftAddHom (fun Q => {
    toFun := fun n => n • φ.pullbackPoint Q
    map_zero' := by simp
    map_add' := by intros; simp [add_smul]
  })


def pushforward (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₁ →+ CurveDivisor C₂ :=
  Finsupp.liftAddHom (fun P => {
    toFun := fun n => Finsupp.single (φ.toFun P) n
    map_zero' := by simp
    map_add' := by intros; simp [Finsupp.single_add]
  })

@[simp]
theorem pushforward_single (φ : CurveMorphismData C₁ C₂) (P : C₁) (n : ℤ) :
    φ.pushforward (Finsupp.single P n) = Finsupp.single (φ.toFun P) n := by
  simp [pushforward]

def pushforwardGeneral (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₁ →+ CurveDivisor C₂ :=
  Finsupp.liftAddHom (fun P => {
    toFun := fun n => Finsupp.single (φ.toFun P) (n * φ.residueFieldDegreeRatio P)
    map_zero' := by simp
    map_add' := by intros; simp [Finsupp.single_add, add_mul]
  })


end CurveMorphismData

end

namespace ArithmeticGeometry

variable {k : Type*} [Field k]



end ArithmeticGeometry
