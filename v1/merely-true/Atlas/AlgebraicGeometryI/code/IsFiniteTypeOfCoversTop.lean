/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open CategoryTheory Limits SheafOfModules

section bind_finite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Glueing finite-presentation quasicoherent data along a covering: if every local
piece `D i` is finitely presented, so is their bind. -/
lemma QuasicoherentData.bind_isFinitePresentation
    {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (D : Π i, QuasicoherentData (M.over (X i)))
    (hD : ∀ i, (D i).IsFinitePresentation) :
    (QuasicoherentData.bind M X hX D).IsFinitePresentation where
  isFinite_presentation ij := {
    isFiniteType_generators := {
      finite := by
        simp only [QuasicoherentData.bind, Presentation.of_isIso_generators,
          GeneratingSections.ofEpi_I, Presentation.map_generators_I]
        exact ((hD ij.1).isFinite_presentation ij.2).isFiniteType_generators.finite
    }
    finite_relations := by
      have := ((hD ij.1).isFinite_presentation ij.2).finite_relations
      rw [show ((QuasicoherentData.bind M X hX D).presentation ij).relations.I =
          ((D ij.1).presentation ij.2).relations.I from by
        simp only [QuasicoherentData.bind, Presentation.of_isIso,
          GeneratingSections.ofEpi_I, Presentation.map_relations_I]]
      exact this
  }

/-- Glueing finite-type generators data: locally finite-type generators glue to a
globally finite-type generators datum. -/
lemma QuasicoherentData.bind_localGeneratorsData_isFiniteType
    {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (D : Π i, QuasicoherentData (M.over (X i)))
    (hD : ∀ (i : I) (j : (D i).I), ((D i).presentation j).generators.IsFiniteType) :
    (QuasicoherentData.bind M X hX D).localGeneratorsData.IsFiniteType where
  isFiniteType ij := {
    finite := by
      simp only [QuasicoherentData.localGeneratorsData_generators]
      have h := (hD ij.1 ij.2).finite
      rw [show ((QuasicoherentData.bind M X hX D).presentation ij).generators.I =
          ((D ij.1).presentation ij.2).generators.I from by
        simp only [QuasicoherentData.bind, Presentation.of_isIso_generators,
          GeneratingSections.ofEpi_I, Presentation.map_generators_I]]
      exact h }

/-- Local-to-global: if `M` restricted to each `X i` is finitely presented and the
`X i` form a covering, then `M` is finitely presented. -/
lemma IsFinitePresentation.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    [∀ i, IsFinitePresentation (M.over (X i))] :
    IsFinitePresentation M where
  exists_quasicoherentData := by
    have h : ∀ i, ∃ (q : QuasicoherentData (M.over (X i))), q.IsFinitePresentation :=
      fun i => IsFinitePresentation.exists_quasicoherentData (M.over (X i))
    choose D hD using h
    exact ⟨QuasicoherentData.bind M X hX D,
      QuasicoherentData.bind_isFinitePresentation M X hX D hD⟩

/-- Local-to-global (instance form): finite presentation locally implies finite type
globally on a covering. -/
lemma IsFiniteType.of_coversTop_of_isFinitePresentation {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    [∀ i, IsFinitePresentation (M.over (X i))] :
    IsFiniteType M := by
  have := IsFinitePresentation.of_coversTop M X hX
  infer_instance

/-- Same as `IsFiniteType.of_coversTop_of_isFinitePresentation`, taking the
finite-presentation hypothesis as an explicit argument rather than a typeclass. -/
lemma IsFiniteType.of_coversTop_of_isFinitePresentation' {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (hFP : ∀ i, IsFinitePresentation (M.over (X i))) :
    IsFiniteType M := by
  haveI : ∀ i, IsFinitePresentation (M.over (X i)) := hFP
  exact IsFiniteType.of_coversTop_of_isFinitePresentation M X hX

end bind_finite
