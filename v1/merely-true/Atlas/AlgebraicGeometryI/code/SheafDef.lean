/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits
  TopologicalSpace TopologicalSpace.Opens Opposite

universe x

namespace TopCat.Presheaf

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {X : TopCat.{x}} (F : Presheaf C X)

/-- **Gluing axiom**: every compatible family `(sᵢ ∈ F(Uᵢ))` of local sections
admits a section on the union `⋃ Uᵢ` whose restrictions agree with `sᵢ`. -/
def SatisfiesGluing : Prop :=
  ∀ ⦃ι : Type x⦄ (U : ι → Opens X) (sf : ∀ i, ToType (F.obj (op (U i)))),
    F.IsCompatible U sf → ∃ s : ToType (F.obj (op (iSup U))), F.IsGluing U sf s

/-- **Locality axiom**: two sections of `F` over `⋃ Uᵢ` that agree on every `Uᵢ`
are equal. -/
def SatisfiesLocality : Prop :=
  ∀ ⦃ι : Type x⦄ (U : ι → Opens X)
    (s t : ToType (F.obj (op (iSup U)))),
    (∀ i, F.map (Opens.leSupr U i).op s = F.map (Opens.leSupr U i).op t) → s = t

/-- The "unique gluing" sheaf condition is equivalent to the conjunction of the
gluing and locality axioms. -/
theorem isSheafUniqueGluing_iff_gluing_and_locality :
    F.IsSheafUniqueGluing ↔ F.SatisfiesGluing ∧ F.SatisfiesLocality := by
  constructor
  · intro h
    refine ⟨fun ι U sf hcompat => ?_, fun ι U s t heq => ?_⟩
    ·
      obtain ⟨s, hs, _⟩ := h U sf hcompat
      exact ⟨s, hs⟩
    ·

      let sf := fun i => F.map (Opens.leSupr U i).op s
      have hcompat_sf : F.IsCompatible U sf := by
        intro i j
        simp only [sf, ← ConcreteCategory.comp_apply, ← F.map_comp]
        rfl
      obtain ⟨gl, _, huniq⟩ := h U sf hcompat_sf

      have hs : F.IsGluing U sf s := fun i => rfl
      have ht : F.IsGluing U sf t := by
        intro i; simp only [sf]; exact (heq i).symm
      exact (huniq s hs).trans (huniq t ht).symm
  ·
    intro ⟨hglue, hloc⟩ ι U sf hcompat
    obtain ⟨s, hs⟩ := hglue U sf hcompat
    exact ⟨s, hs, fun t ht => hloc U t s (fun i => by rw [ht i, hs i])⟩

section ConcreteComplete

variable [HasLimitsOfSize.{x, x} C] [(forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{x, x} (forget C)]

/-- The standard `IsSheaf` condition (limit-based) is equivalent to gluing +
locality in concrete categories with the appropriate limits. -/
theorem isSheaf_iff_gluing_and_locality :
    F.IsSheaf ↔ F.SatisfiesGluing ∧ F.SatisfiesLocality := by
  rw [isSheaf_iff_isSheafUniqueGluing, isSheafUniqueGluing_iff_gluing_and_locality]

/-- A sheaf satisfies the gluing axiom. -/
theorem _root_.TopCat.Sheaf.satisfiesGluing (ℱ : TopCat.Sheaf C X) :
    SatisfiesGluing ℱ.1 :=
  ((isSheaf_iff_gluing_and_locality ℱ.1).mp ℱ.2).1

/-- A sheaf satisfies the locality axiom. -/
theorem _root_.TopCat.Sheaf.satisfiesLocality (ℱ : TopCat.Sheaf C X) :
    SatisfiesLocality ℱ.1 :=
  ((isSheaf_iff_gluing_and_locality ℱ.1).mp ℱ.2).2

end ConcreteComplete

end TopCat.Presheaf
