/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryOII
import Atlas.LieGroups.code.DufloJoseph
import Atlas.LieGroups.code.TensorO

noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure RepGfObj (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  carrier : Type u
  inst_addCommGroup : AddCommGroup carrier
  inst_module : Module R carrier
  inst_lieRingModule : LieRingModule 𝔤 carrier
  inst_lieModule : LieModule R 𝔤 carrier

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule


structure RepGfHom (M N : RepGfObj R 𝔤) where
  toFun : M.carrier →ₗ⁅R, 𝔤⁆ N.carrier

def RepGfHom.comp {M N P : RepGfObj R 𝔤} (g : RepGfHom N P) (f : RepGfHom M N) :
    RepGfHom M P where
  toFun := g.toFun.comp f.toFun

def RepGfHom.id (M : RepGfObj R 𝔤) : RepGfHom M M where
  toFun := LieModuleHom.id

def RepGfHom.EqAsMap {M N : RepGfObj R 𝔤} (f g : RepGfHom M N) : Prop :=
  ∀ x : M.carrier, f.toFun x = g.toFun x












structure EndoFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  obj : RepGfObj R 𝔤 → RepGfObj R 𝔤
  mapHom : ∀ {M N : RepGfObj R 𝔤}, RepGfHom M N → RepGfHom (obj M) (obj N)
  map_id : ∀ (M : RepGfObj R 𝔤), (mapHom (RepGfHom.id M)).EqAsMap (RepGfHom.id (obj M))
  map_comp : ∀ {M N P : RepGfObj R 𝔤} (f : RepGfHom M N) (g : RepGfHom N P),
    (mapHom (g.comp f)).EqAsMap ((mapHom g).comp (mapHom f))

structure NatTransData (F G : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), RepGfHom (F.obj M) (G.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (f : RepGfHom M₁ M₂),
    ((app M₂).comp (F.mapHom f)).EqAsMap ((G.mapHom f).comp (app M₁))

def NatTransData.comp {F G H : EndoFunctorData R 𝔤}
    (β : NatTransData G H) (α : NatTransData F G) : NatTransData F H where
  app M := (β.app M).comp (α.app M)
  naturality f x := by


    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
    have hα := α.naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα
    rw [hα]
    have hβ := β.naturality f ((α.app _).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ
    exact hβ

def NatTransData.id (F : EndoFunctorData R 𝔤) : NatTransData F F where
  app _ := RepGfHom.id _
  naturality f x := by

    simp [RepGfHom.comp, RepGfHom.id]

def NatTransData.EqPointwise {F G : EndoFunctorData R 𝔤}
    (α β : NatTransData F G) : Prop :=
  ∀ M : RepGfObj R 𝔤, (α.app M).EqAsMap (β.app M)

def AreNatIso (F G : EndoFunctorData R 𝔤) : Prop :=
  ∃ (α : NatTransData F G) (β : NatTransData G F),
    (β.comp α).EqPointwise (NatTransData.id F) ∧
    (α.comp β).EqPointwise (NatTransData.id G)

def IsDirectSummand (F G : EndoFunctorData R 𝔤) : Prop :=
  ∃ (i : NatTransData F G) (p : NatTransData G F),
    (p.comp i).EqPointwise (NatTransData.id F)

lemma isDirectSummand_refl (F : EndoFunctorData R 𝔤) : IsDirectSummand F F :=
  ⟨NatTransData.id F, NatTransData.id F,
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id]⟩

def IsExactSequence {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃) : Prop :=
  ∀ (m : M₂.carrier), g.toFun m = 0 ↔ ∃ (x : M₁.carrier), f.toFun x = m

def IsProjectiveModule (M : RepGfObj R 𝔤) : Prop :=
  ∀ {N : RepGfObj R 𝔤} (p : RepGfHom N M),
    (Function.Surjective p.toFun) →
    ∃ (s : RepGfHom M N), (p.comp s).EqAsMap (RepGfHom.id M)












































def IsDirectSumDecompObj {n : ℕ}
    (M : RepGfObj R 𝔤) (summands : Fin n → RepGfObj R 𝔤) : Prop :=
  ∃ (section_i : ∀ i, RepGfHom (summands i) M)
    (retract_i : ∀ i, RepGfHom M (summands i)),

    (∀ i (x : (summands i).carrier),
      (retract_i i).toFun ((section_i i).toFun x) = x) ∧

    (∀ (x : M.carrier),
      x = Finset.univ.sum (fun i =>
        (section_i i).toFun ((retract_i i).toFun x)))

def IsIndecomposableObj (M : RepGfObj R 𝔤) : Prop :=
  ∀ (e : RepGfHom M M),
    (∀ x, e.toFun (e.toFun x) = e.toFun x) →
    (∀ x, e.toFun x = x) ∨ (∀ x, e.toFun x = 0)

def IsIndecomposable (F : EndoFunctorData R 𝔤) : Prop :=
  ∀ (e : NatTransData F F),
    (e.comp e).EqPointwise e →
    e.EqPointwise (NatTransData.id F) ∨
    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier), (e.app M).toFun x = 0)

def IsDirectSumDecomp (F : EndoFunctorData R 𝔤) {n : ℕ}
    (F_i : Fin n → EndoFunctorData R 𝔤) : Prop :=

  ∃ (section_i : ∀ i, NatTransData (F_i i) F)
    (retract_i : ∀ i, NatTransData F (F_i i)),

    (∀ i, ((retract_i i).comp (section_i i)).EqPointwise (NatTransData.id (F_i i))) ∧


    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      (RepGfHom.id (F.obj M)).toFun x =
      Finset.univ.sum (fun i =>
        ((section_i i).app M).toFun (((retract_i i).app M).toFun x)))

def IsDirectSumDecompGen (F : EndoFunctorData R 𝔤) {ι : Type u} [Fintype ι]
    (F_i : ι → EndoFunctorData R 𝔤) : Prop :=
  ∃ (section_i : ∀ i, NatTransData (F_i i) F)
    (retract_i : ∀ i, NatTransData F (F_i i)),
    (∀ i, ((retract_i i).comp (section_i i)).EqPointwise (NatTransData.id (F_i i))) ∧
    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      (RepGfHom.id (F.obj M)).toFun x =
      Finset.univ.sum (fun i =>
        ((section_i i).app M).toFun (((retract_i i).app M).toFun x)))







theorem idempotent_lift_gives_functor_decomp
    (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F : EndoFunctorData R 𝔤) {n : ℕ}
    (E_i : Fin n → NatTransData F F)

    (_hIdem : ∀ i, ((E_i i).comp (E_i i)).EqPointwise (E_i i))

    (M₀ : RepGfObj R 𝔤) (summands : Fin n → RepGfObj R 𝔤)
    (_hDecompObj : IsDirectSumDecompObj (F.obj M₀) summands)


    (_hEvalCompat : ∀ i, ∀ x : (F.obj M₀).carrier,
      ((E_i i).app M₀).toFun x =
      (_hDecompObj.choose i).toFun ((_hDecompObj.choose_spec.choose i).toFun x))


    (_hComplete : ∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      x = Finset.univ.sum (fun i => ((E_i i).app M).toFun x)) :
    ∃ (F_i : Fin n → EndoFunctorData R 𝔤),
      (∀ i, (F_i i).obj M₀ = summands i) ∧
      IsDirectSumDecomp F F_i := by


  let sec_obj := _hDecompObj.choose
  let ret_obj := _hDecompObj.choose_spec.choose
  have hRS_obj := _hDecompObj.choose_spec.choose_spec.1

  have hIdemElt : ∀ i (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      ((E_i i).app M).toFun (((E_i i).app M).toFun x) = ((E_i i).app M).toFun x :=
    fun i M x => _hIdem i M x

  classical

  let rangeObj : (i : Fin n) → (M : RepGfObj R 𝔤) → RepGfObj R 𝔤 := fun i M =>
    ⟨↥(((E_i i).app M).toFun.range), inferInstance, inferInstance, inferInstance, inferInstance⟩

  let Fi_obj : (i : Fin n) → RepGfObj R 𝔤 → RepGfObj R 𝔤 := fun i M =>
    if M = M₀ then summands i else rangeObj i M

  have hFi_M₀ : ∀ i, Fi_obj i M₀ = summands i := fun i => if_pos rfl


  suffices hMain : ∃ (F_i : Fin n → EndoFunctorData R 𝔤),
      (∀ i, (F_i i).obj M₀ = summands i) ∧


      (∀ i, ∃ (incl : NatTransData (F_i i) F) (proj : NatTransData F (F_i i)),
        ((proj.comp incl).EqPointwise (NatTransData.id (F_i i))) ∧
        (∀ M x, (incl.app M).toFun ((proj.app M).toFun x) = ((E_i i).app M).toFun x)) by
    obtain ⟨F_i, hObj, hSplit⟩ := hMain
    refine ⟨F_i, hObj, ?_⟩

    let incl_i : ∀ i, NatTransData (F_i i) F := fun i => (hSplit i).choose
    let proj_i : ∀ i, NatTransData F (F_i i) := fun i => (hSplit i).choose_spec.choose
    have hRetract : ∀ i, ((proj_i i).comp (incl_i i)).EqPointwise (NatTransData.id (F_i i)) :=
      fun i => (hSplit i).choose_spec.choose_spec.1
    have hInclProj : ∀ i (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
        ((incl_i i).app M).toFun (((proj_i i).app M).toFun x) = ((E_i i).app M).toFun x :=
      fun i => (hSplit i).choose_spec.choose_spec.2
    exact ⟨incl_i, proj_i, hRetract,
      fun M x => by


        simp only [RepGfHom.id, LieModuleHom.coe_id, id_eq]
        conv_rhs => arg 2; ext i; rw [hInclProj i M x]
        exact _hComplete M x⟩


  let eqToRepGfHom : ∀ {A B : RepGfObj R 𝔤}, A = B → RepGfHom A B :=
    fun h => h ▸ RepGfHom.id _
  have eqToRepGfHom_symm : ∀ {A B : RepGfObj R 𝔤} (h : A = B) (x : A.carrier),
      (eqToRepGfHom h.symm).toFun ((eqToRepGfHom h).toFun x) = x := by
    intro A B h; subst h; intro x; rfl
  have eqToRepGfHom_symm' : ∀ {A B : RepGfObj R 𝔤} (h : A = B) (x : B.carrier),
      (eqToRepGfHom h).toFun ((eqToRepGfHom h.symm).toFun x) = x := by
    intro A B h; subst h; intro x; rfl


  let myRangeRestrict' : ∀ (i : Fin n) (M : RepGfObj R 𝔤),
      @LieModuleHom R 𝔤 (F.obj M).carrier ↥(((E_i i).app M).toFun.range)
        _ _ (F.obj M).inst_addCommGroup _ (F.obj M).inst_module _
        (F.obj M).inst_lieRingModule _ := fun i M =>
    { toLinearMap := (((E_i i).app M).toFun : (F.obj M).carrier →ₗ[R] (F.obj M).carrier).rangeRestrict
      map_lie' := fun {x m} => by
        apply Subtype.ext
        simp only [LieSubmodule.coe_bracket]
        change ((E_i i).app M).toFun ⁅x, m⁆ = ⁅x, ((E_i i).app M).toFun m⁆
        exact ((E_i i).app M).toFun.map_lie x m }


  have rangeRestrict_incl : ∀ i M (x : (F.obj M).carrier),
      ((((E_i i).app M).toFun.range).incl (myRangeRestrict' i M x) : (F.obj M).carrier) =
      ((E_i i).app M).toFun x := by intro i M x; rfl


  have rangeRestrict_idem : ∀ i M (y : ↥(((E_i i).app M).toFun.range)),
      myRangeRestrict' i M (((E_i i).app M).toFun.range.incl y) = y := by
    intro i M y
    apply Subtype.ext
    change ((E_i i).app M).toFun ↑y = ↑y
    obtain ⟨z, hz⟩ := y.prop
    rw [← hz, hIdemElt i M z]


  let incl_at : ∀ (i : Fin n) (M : RepGfObj R 𝔤), RepGfHom (Fi_obj i M) (F.obj M) :=
    fun i M => if hM : M = M₀ then by
      subst hM

      exact (sec_obj i).comp (eqToRepGfHom (hFi_M₀ i))
    else by

      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM
      exact ⟨(((E_i i).app M).toFun.range.incl).comp (eqToRepGfHom h_ne).toFun⟩


  let proj_at : ∀ (i : Fin n) (M : RepGfObj R 𝔤), RepGfHom (F.obj M) (Fi_obj i M) :=
    fun i M => if hM : M = M₀ then by
      subst hM
      exact (eqToRepGfHom (hFi_M₀ i).symm).comp (ret_obj i)
    else by
      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM
      exact ⟨((eqToRepGfHom h_ne.symm).toFun).comp (myRangeRestrict' i M)⟩


  have incl_proj_eq : ∀ i M (x : (F.obj M).carrier),
      (incl_at i M).toFun ((proj_at i M).toFun x) = ((E_i i).app M).toFun x := by
    intro i M x
    by_cases hM : M = M₀
    · subst hM
      simp only [incl_at, proj_at, dif_pos rfl]
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      rw [eqToRepGfHom_symm' (hFi_M₀ i)]
      exact (_hEvalCompat i x).symm
    · simp only [incl_at, proj_at, dif_neg hM]
      simp only [LieModuleHom.coe_comp, Function.comp_apply]
      rw [eqToRepGfHom_symm' (show Fi_obj i M = rangeObj i M from if_neg hM)]
      rfl


  have proj_incl_id : ∀ i M (x : (Fi_obj i M).carrier),
      (proj_at i M).toFun ((incl_at i M).toFun x) = x := by
    intro i M x
    by_cases hM : M = M₀
    · subst hM
      simp only [incl_at, proj_at, dif_pos rfl]
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      rw [show (ret_obj i).toFun ((sec_obj i).toFun ((eqToRepGfHom (hFi_M₀ i)).toFun x)) =
          (eqToRepGfHom (hFi_M₀ i)).toFun x from hRS_obj i _]
      exact eqToRepGfHom_symm (hFi_M₀ i) x
    · simp only [incl_at, proj_at, dif_neg hM]
      simp only [LieModuleHom.coe_comp, Function.comp_apply]
      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM


      conv_rhs => rw [← eqToRepGfHom_symm h_ne x]
      congr 1
      exact rangeRestrict_idem i M ((eqToRepGfHom h_ne).toFun x)


  have E_i_nat : ∀ i {M N : RepGfObj R 𝔤} (f : RepGfHom M N) (x : (F.obj M).carrier),
      ((E_i i).app N).toFun ((F.mapHom f).toFun x) =
      (F.mapHom f).toFun (((E_i i).app M).toFun x) := by
    intro i M N f x
    have := (E_i i).naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at this
    exact this


  have E_i_fixes_incl : ∀ i M (x : (Fi_obj i M).carrier),
      ((E_i i).app M).toFun ((incl_at i M).toFun x) = (incl_at i M).toFun x := by
    intro i M x
    rw [← incl_proj_eq i M ((incl_at i M).toFun x), proj_incl_id]


  let mapHom_i : ∀ (i : Fin n) {M N : RepGfObj R 𝔤},
      RepGfHom M N → RepGfHom (Fi_obj i M) (Fi_obj i N) := fun i {M} {N} f =>
    (proj_at i N).comp ((F.mapHom f).comp (incl_at i M))


  refine ⟨fun i => ⟨Fi_obj i, @mapHom_i i, ?_, ?_⟩, hFi_M₀, fun i => ?_⟩


  · intro M x


    simp only [RepGfHom.EqAsMap, mapHom_i, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply, RepGfHom.id, LieModuleHom.coe_id, id_eq]
    have hFid := F.map_id M ((incl_at i M).toFun x)
    simp only [RepGfHom.id, LieModuleHom.coe_id, id_eq] at hFid
    rw [hFid]
    exact proj_incl_id i M x


  · intro M N P f g x
    simp only [RepGfHom.EqAsMap, mapHom_i, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply]


    have hFcomp := F.map_comp f g ((incl_at i M).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hFcomp
    rw [hFcomp]


    congr 1


    rw [incl_proj_eq]


    symm; rw [E_i_nat]


    congr 2
    exact E_i_fixes_incl i M x


  · refine ⟨⟨incl_at i, ?_⟩, ⟨proj_at i, ?_⟩, ?_, ?_⟩


    · intro M₁ M₂ f x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply, mapHom_i]


      rw [incl_proj_eq]


      rw [E_i_nat]
      congr 1
      exact E_i_fixes_incl i M₁ x


    · intro M₁ M₂ f x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply, mapHom_i]


      rw [show (incl_at i M₁).toFun ((proj_at i M₁).toFun x) =
          ((E_i i).app M₁).toFun x from incl_proj_eq i M₁ x]


      conv_lhs => rw [show (proj_at i M₂).toFun ((F.mapHom f).toFun x) =
          (proj_at i M₂).toFun (((E_i i).app M₂).toFun ((F.mapHom f).toFun x)) from by
        rw [← incl_proj_eq i M₂ ((F.mapHom f).toFun x)]
        rw [proj_incl_id]]

      rw [E_i_nat]


    · intro M x
      simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id, RepGfHom.EqAsMap,
        LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.coe_id, id_eq]
      exact proj_incl_id i M x


    · intro M x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      exact incl_proj_eq i M x

theorem isDirectSummand_trans
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (A B C : EndoFunctorData R 𝔤)
    (h1 : IsDirectSummand A B) (h2 : IsDirectSummand B C) :
    IsDirectSummand A C := by
  obtain ⟨i₁, p₁, hp₁⟩ := h1
  obtain ⟨i₂, p₂, hp₂⟩ := h2
  exact ⟨i₂.comp i₁, p₁.comp p₂, fun M x => by
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply,
               NatTransData.EqPointwise, RepGfHom.EqAsMap, NatTransData.id, RepGfHom.id] at *
    have h2' := hp₂ M ((i₁.app M).toFun x)
    rw [h2']
    exact hp₁ M x⟩


theorem isDirectSummand_of_isDirectSumDecomp
    (F : EndoFunctorData R 𝔤) {n : ℕ}
    (F_i : Fin n → EndoFunctorData R 𝔤)
    (h : IsDirectSumDecomp F F_i) (i : Fin n) :
    IsDirectSummand (F_i i) F := by
  obtain ⟨sec, ret, hRS, _⟩ := h
  exact ⟨sec i, ret i, hRS i⟩


lemma areNatIso_refl (F : EndoFunctorData R 𝔤) : AreNatIso F F :=
  ⟨NatTransData.id F, NatTransData.id F,
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id],
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id]⟩





lemma isDirectSumDecomp_to_gen
    (F : EndoFunctorData R 𝔤) {n : ℕ}
    (F_i : Fin n → EndoFunctorData R 𝔤)
    (h : IsDirectSumDecomp F F_i) :
    @IsDirectSumDecompGen R _ 𝔤 _ _ F (ULift.{u, 0} (Fin n)) (ULift.fintype _)
      (fun j => F_i j.down) := by
  obtain ⟨section_i, retract_i, hRetSec, hSum⟩ := h
  refine ⟨fun j => section_i j.down, fun j => retract_i j.down,
          fun j => hRetSec j.down, ?_⟩
  intro M x
  rw [hSum M x]
  symm
  exact Finset.sum_equiv (Equiv.ulift) (by simp) (by intro i _; rfl)





theorem direct_summand_preserves_categoryO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (F G : EndoFunctorData R 𝔤)
    (_hDS : IsDirectSummand F G)
    (M : RepGfObj R 𝔤)
    (hGMO : IsCategoryO Δ rd (G.obj M).carrier) :
    IsCategoryO Δ rd (F.obj M).carrier := by

  obtain ⟨i_nt, p_nt, hpi⟩ := _hDS

  let sec := (i_nt.app M).toFun
  let ret := (p_nt.app M).toFun
  have hret_sec : ∀ x : (F.obj M).carrier, ret (sec x) = x := hpi M
  exact {
    finitely_generated := by
      obtain ⟨S, hS⟩ := hGMO.finitely_generated
      classical
      refine ⟨S.image ret, ?_⟩
      rw [eq_top_iff]; intro x _
      rw [← hret_sec x]
      have hmem : sec x ∈ LieSubmodule.lieSpan R 𝔤 (↑S : Set (G.obj M).carrier) := by
        rw [hS]; trivial
      apply LieSubmodule.lieSpan_induction R 𝔤 (p := fun y _ =>
          ret y ∈ LieSubmodule.lieSpan R 𝔤 (↑(S.image ret) : Set (F.obj M).carrier))
      · intro m hm
        exact LieSubmodule.subset_lieSpan (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm, rfl⟩))
      · simp
      · intro a b _ _ ih1 ih2; rw [map_add]; exact add_mem ih1 ih2
      · intro r a _ ih; rw [map_smul]; exact SMulMemClass.smul_mem r ih
      · intro l a _ ih; rw [LieModuleHom.map_lie]; exact LieSubmodule.lie_mem _ ih
      · exact hmem
    weight_decomp := by
      intro m
      obtain ⟨S, v, hv⟩ := hGMO.weight_decomp (sec m)
      refine ⟨S, fun μ => ⟨ret (v μ), fun h => ?_⟩, ?_⟩
      ·
        have hv_wt := (v μ).property h
        rw [← LieModuleHom.map_lie, hv_wt, map_smul]
      ·
        conv_lhs => rw [← hret_sec m, hv]
        rw [map_sum]
    weight_bound := by
      obtain ⟨bds, hbds⟩ := hGMO.weight_bound
      refine ⟨bds, fun μ hμ => ?_⟩
      apply hbds μ


      unfold weights at hμ ⊢
      simp only [Set.mem_setOf_eq] at hμ ⊢
      intro h_contra
      apply hμ
      rw [Submodule.eq_bot_iff]
      intro x hx

      have hsec_x_wt : sec x ∈ WeightSpace Δ (G.obj M).carrier μ := by
        intro h
        rw [← LieModuleHom.map_lie]
        rw [hx h]
        exact map_smul sec (μ h) x

      rw [Submodule.eq_bot_iff] at h_contra
      have hsec_zero : sec x = 0 := h_contra (sec x) hsec_x_wt

      calc x = ret (sec x) := (hret_sec x).symm
        _ = ret 0 := by rw [hsec_zero]
        _ = 0 := map_zero ret
  }

theorem direct_summand_preserves_projectiveInO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (F G : EndoFunctorData R 𝔤)
    (_hDS : IsDirectSummand F G)
    (M : RepGfObj R 𝔤)
    (hFMO : IsCategoryO Δ rd (F.obj M).carrier)
    (hGMO : IsCategoryO Δ rd (G.obj M).carrier)
    (hGMproj : IsProjectiveInO rd (G.obj M).carrier hGMO) :
    IsProjectiveInO rd (F.obj M).carrier hFMO := by

  obtain ⟨i_nt, p_nt, hpi⟩ := _hDS

  let sec := (i_nt.app M).toFun
  let ret := (p_nt.app M).toFun

  have hret_sec : ∀ x : (F.obj M).carrier, ret (sec x) = x := hpi M

  intro X _ _ _ _ hXO N _ _ _ _ hNO f hf g

  let g' : (G.obj M).carrier →ₗ⁅R, 𝔤⁆ N := g.comp ret

  obtain ⟨h', hh'⟩ := hGMproj X hXO N hNO f hf g'

  exact ⟨h'.comp sec, fun x => by
    rw [LieModuleHom.comp_apply, hh']
    show g (ret (sec x)) = g x
    rw [hret_sec x]⟩












end ProjectiveFunctors

end
