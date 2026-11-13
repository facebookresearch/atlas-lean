/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Filtered.Basic

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]

/-- Filtered colimits commute with finite limits: the canonical comparison
`colim_K lim_J F ≅ lim_J colim_K F` is an isomorphism under the hypothesis that
the colimit functor preserves finite limits. -/
noncomputable def filteredColimit_finiteLimits_iso
    [HasLimitsOfShape J C] [HasColimitsOfShape K C]
    [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]
    (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.flip) :=
  colimitLimitIso F

/-- In the category of types, filtered colimits preserve finite limits. -/
noncomputable instance filteredColimit_preservesFiniteLimits_type
    [Small.{v, u₂} K] [IsFiltered K] :
    PreservesFiniteLimits (colim : (K ⥤ Type v) ⥤ _) :=
  filtered_colim_preservesFiniteLimits_of_types

/-- Filtered-colimit-vs-finite-limit isomorphism specialized to types. -/
noncomputable def filteredColimit_finiteLimits_iso_type
    [SmallCategory J] [FinCategory J]
    [Small.{v, u₂} K] [IsFiltered K]
    [HasLimitsOfShape J (Type v)] [HasColimitsOfShape K (Type v)]
    (F : J ⥤ K ⥤ Type v) : colimit (limit F) ≅ limit (colimit F.flip) :=
  colimitLimitIso F

/-- In a concrete category compatible with the forgetful functor, filtered
colimits commute with finite limits, generalizing the type-level statement. -/
noncomputable instance filteredColimit_preservesFiniteLimits_concrete
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
    [SmallCategory J] [FinCategory J]
    [Small.{v, u₂} K] [IsFiltered K]
    [HasLimitsOfShape J C] [HasColimitsOfShape K C]
    [ReflectsLimitsOfShape J (forget C)]
    [PreservesColimitsOfShape K (forget C)]
    [PreservesLimitsOfShape J (forget C)] :
    PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _) :=
  filtered_colim_preservesFiniteLimits

/-- Explicit description of the filtered-colimit/finite-limit isomorphism on the
cone components: `colim.ι ≫ iso ≫ lim.π = lim.π ≫ colim.ι`. -/
theorem filteredColimit_finiteLimits_iso_components
    [HasLimitsOfShape J C] [HasColimitsOfShape K C]
    [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]
    (F : J ⥤ K ⥤ C) (a : K) (b : J) :
    colimit.ι (limit F) a ≫ (filteredColimit_finiteLimits_iso F).hom ≫
      limit.π (colimit F.flip) b =
    (limit.π F b).app a ≫ (colimit.ι F.flip a).app b :=
  ι_colimitLimitIso_limit_π F a b
