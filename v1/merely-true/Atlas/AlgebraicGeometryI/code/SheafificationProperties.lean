/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

open CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace Proposition15

/-- The sheafification adjunction: presheafification ⊣ inclusion of sheaves into
presheaves, instantiated for abelian-group-valued (pre)sheaves on a topological
space `X`. -/
noncomputable def sheafification_adjunction (X : TopCat.{u}) :
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⊣
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The sheafification functor is a left adjoint (instance form). -/
theorem sheafification_isLeftAdjoint (X : TopCat.{u}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).IsLeftAdjoint :=
  inferInstance

/-- **Universal property of sheafification (existence)**: any morphism `η : P → Q`
to a sheaf `Q` factors through the sheafification map `P → P⁺` via `sheafifyLift`. -/
theorem sheafification_universal_factorization
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C)
    {D : Type*} [Category.{u} D]
    [HasWeakSheafify J D]
    {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    toSheafify J P ≫ sheafifyLift J η hQ = η :=
  toSheafify_sheafifyLift J η hQ

/-- **Universal property of sheafification (uniqueness)**: the factorization
through the sheafification is unique. -/
theorem sheafification_universal_uniqueness
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C)
    {D : Type*} [Category.{u} D]
    [HasWeakSheafify J D]
    {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : sheafify J P ⟶ Q)
    (h : toSheafify J P ≫ γ = η) :
    γ = sheafifyLift J η hQ :=
  sheafifyLift_unique J η hQ γ h

/-- A presheaf that is already a sheaf is isomorphic to its sheafification. -/
theorem sheafification_iso_of_isSheaf
    {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C)
    {D : Type*} [Category.{u} D]
    [HasWeakSheafify J D]
    {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    IsIso (toSheafify J P) :=
  isIso_toSheafify J hP

/-- **Exactness of sheafification**: the sheafification functor preserves homology
(equivalently, finite limits and finite colimits) on abelian-group-valued
presheaves. -/
theorem sheafification_exact (X : TopCat.{u}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology := by
  set F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

  have hfl : PreservesFiniteLimits F := inferInstance

  have hpc : PreservesColimitsOfSize.{0, 0} F :=
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).leftAdjoint_preservesColimits

  have hfc : PreservesFiniteColimits F := hpc.preservesFiniteColimits

  exact ((F.exact_tfae.out 3 2).mp
    (show PreservesFiniteLimits F ∧ PreservesFiniteColimits F from ⟨hfl, hfc⟩))

/-- The composition "take underlying presheaf, then take stalk at `x`" preserves
homology. This is what makes "exactness can be checked on stalks" work for
sheaves of abelian groups. -/
theorem stalkFunctor_preservesHomology (X : TopCat.{u}) (x : X) :
    (Sheaf.forget AddCommGrpCat.{u} X ⋙
      Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesHomology := by
  set F := Sheaf.forget AddCommGrpCat.{u} X ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} x

  have hfl : PreservesFiniteLimits F := inferInstance

  have hpc : PreservesColimitsOfSize.{0, 0} F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  have hfc : PreservesFiniteColimits F := hpc.preservesFiniteColimits

  exact ((F.exact_tfae.out 3 2).mp
    (show PreservesFiniteLimits F ∧ PreservesFiniteColimits F from ⟨hfl, hfc⟩))

/-- **Exactness on stalks**: a short complex of sheaves of abelian groups on `X`
is exact if and only if its stalk at every `x ∈ X` is exact. -/
theorem exact_iff_stalkwise_exact (X : TopCat.{u})
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)) :
    S.Exact ↔ ∀ x : X,
      (S.map (Sheaf.forget AddCommGrpCat.{u} X ⋙
        Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact :=
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

end Proposition15
