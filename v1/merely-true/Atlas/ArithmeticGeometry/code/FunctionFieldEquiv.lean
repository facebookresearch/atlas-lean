/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.CurveTheory

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

structure FunctionFieldCat where
  carrier : Type u
  [fieldInst : Field carrier]
  [algInst : Algebra k carrier]
  finitelyGenerated : (⊤ : IntermediateField k carrier).FG
  transcendenceDegreeOne : ∃ (x : carrier), Transcendental k x ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) carrier
  algClosedInF : ∀ (x : carrier), IsAlgebraic k x → x ∈ Set.range (algebraMap k carrier)

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

instance : CoeSort (FunctionFieldCat k) (Type u) := ⟨FunctionFieldCat.carrier⟩

@[ext]
structure FunctionFieldCat.Hom (F₁ F₂ : FunctionFieldCat k) where
  toAlgHom : F₁.carrier →ₐ[k] F₂.carrier

instance : Category (FunctionFieldCat k) where
  Hom F₁ F₂ := FunctionFieldCat.Hom k F₁ F₂
  id F := ⟨AlgHom.id k F.carrier⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom⟩

structure SmProjCurve where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ Spec (.of k)
  [isIntegral : IsIntegral toScheme]
  [isProper : IsProper structureMorphism]
  [isSmooth : SmoothOfRelativeDimension 1 structureMorphism]

attribute [instance] SmProjCurve.isIntegral SmProjCurve.isProper SmProjCurve.isSmooth

@[ext]
structure SmProjCurve.Hom (C₁ C₂ : SmProjCurve k) where
  toSchemeHom : C₁.toScheme ⟶ C₂.toScheme
  over_spec : toSchemeHom ≫ C₂.structureMorphism = C₁.structureMorphism

instance SmProjCurve.categoryInstance : Category (SmProjCurve k) where
  Hom C₁ C₂ := SmProjCurve.Hom k C₁ C₂
  id C := ⟨𝟙 C.toScheme, by simp⟩
  comp f g := ⟨f.toSchemeHom ≫ g.toSchemeHom, by
    rw [Category.assoc, g.over_spec, f.over_spec]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

def SmProjCurve.algebraMapHom (C : SmProjCurve k) :
    CommRingCat.of k ⟶ C.toScheme.functionField := by
  haveI : IrreducibleSpace C.toScheme := irreducibleSpace_of_isIntegral C.toScheme
  haveI : Nonempty C.toScheme := IsIntegral.nonempty
  haveI : Nonempty (⊤ : C.toScheme.Opens) := ⟨⟨IsIntegral.nonempty.some, trivial⟩⟩
  exact (Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMorphism.appTop ≫
    C.toScheme.germToFunctionField ⊤

instance SmProjCurve.algebraFunctionField (C : SmProjCurve k) :
    Algebra k C.toScheme.functionField :=
  (C.algebraMapHom k).hom.toAlgebra











lemma SmProjCurve.fromSpecStalk_genericPoint_isDominant (C : SmProjCurve k) :
    IsDominant (C.toScheme.fromSpecStalk (genericPoint C.toScheme)) := by
  haveI : IrreducibleSpace C.toScheme := irreducibleSpace_of_isIntegral C.toScheme
  constructor
  show Dense (Set.range (C.toScheme.fromSpecStalk (genericPoint C.toScheme)))
  rw [show Set.range (⇑(C.toScheme.fromSpecStalk (genericPoint C.toScheme))) =
      {y | y ⤳ genericPoint C.toScheme} from Scheme.range_fromSpecStalk]
  apply Dense.mono (s₁ := {genericPoint C.toScheme})
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [Set.mem_setOf_eq, hy]
  · rw [dense_iff_closure_eq]
    exact genericPoint_closure (α := C.toScheme)

lemma SmProjCurve.Hom.ext_of_fromSpecStalk_genericPoint {C₁ C₂ : SmProjCurve k}
    (f g : C₁ ⟶ C₂)
    (h : C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ f.toSchemeHom =
         C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ g.toSchemeHom) :
    f = g := by
  have hfg : f.toSchemeHom = g.toSchemeHom := by
    haveI : IsReduced C₁.toScheme := inferInstance
    haveI : IsSeparated C₂.structureMorphism := inferInstance
    haveI : IrreducibleSpace C₁.toScheme := irreducibleSpace_of_isIntegral C₁.toScheme
    haveI := C₁.fromSpecStalk_genericPoint_isDominant k
    exact ext_of_isDominant_of_isSeparated C₂.structureMorphism
      (by rw [f.over_spec, g.over_spec]) _ h
  exact SmProjCurve.Hom.ext hfg



instance FunctionFieldCat.toFunctionField_k (F : FunctionFieldCat k) :
    ArithmeticGeometry.FunctionField_k k F.carrier where
  finitelyGenerated := F.finitelyGenerated
  transcendenceDegreeOne := F.transcendenceDegreeOne
  algClosedInF := fun x hx => by
    have := F.algClosedInF x hx
    rwa [IntermediateField.mem_bot, Set.mem_range]










end Thm19_2

end ArithmeticGeometry
