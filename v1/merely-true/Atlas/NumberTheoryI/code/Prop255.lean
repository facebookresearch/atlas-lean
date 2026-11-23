/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.NumberTheoryI.code.DirectLimits

open scoped RestrictedProduct
open Filter Set Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

namespace RestrictedProduct

section XS_Definitions

variable (X : ι → Type*) (U : (i : ι) → Set (X i))

def XS (S : Finset ι) : Set ((i : ι) → X i) :=
  {x | ∀ i, i ∉ S → x i ∈ U i}

theorem XS_mono {S T : Finset ι} (hST : S ⊆ T) : XS X U S ⊆ XS X U T :=
  fun _ hx i hi => hx i (fun hS => hi (hST hS))

theorem mem_XS_of_restricted (x : Πʳ i, [X i, U i]) :
    ∃ S : Finset ι, (x : (i : ι) → X i) ∈ XS X U S := by
  have hfin := eventually_cofinite.mp x.2
  exact ⟨hfin.toFinset, fun i hi => by
    simp only [Finite.mem_toFinset, mem_setOf_eq, not_not] at hi; exact hi⟩

def supportFinset (x : Πʳ i, [X i, U i]) : Finset ι :=
  (eventually_cofinite.mp x.2).toFinset

theorem mem_XS_support (x : Πʳ i, [X i, U i]) :
    (x : (i : ι) → X i) ∈ XS X U (supportFinset X U x) := by
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, mem_setOf_eq, not_not] at hi; exact hi

theorem XS_mem_restricted {S : Finset ι} {x : (i : ι) → X i}
    (hx : x ∈ XS X U S) : ∀ᶠ i in cofinite, x i ∈ U i := by
  rw [eventually_cofinite]
  exact S.finite_toSet.subset (fun i hi => by
    simp only [mem_setOf_eq] at hi
    by_contra h; exact hi (hx i (by simpa using h)))

theorem supportFinset_le {T : Finset ι} {x : Πʳ i, [X i, U i]}
    (hx : (x : (i : ι) → X i) ∈ XS X U T) :
    supportFinset X U x ⊆ T := by
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, mem_setOf_eq] at hi
  by_contra hiT
  exact hi (hx i hiT)

end XS_Definitions

section DirectLimitConstruction

variable (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (U : (i : ι) → Set (X i))

def inclusionMap {S T : Finset ι} (h : S ⊆ T) :
    XS X U S → XS X U T :=
  fun ⟨x, hx⟩ => ⟨x, XS_mono X U h hx⟩

def transitionMaps :
    ∀ (S T : Finset ι), S ≤ T → XS X U S → XS X U T :=
  fun _ _ h => inclusionMap X U h

abbrev DirectLimitXS :=
  TopologicalSpace.DirectLimit.Space
    (fun S : Finset ι => XS X U S)
    (transitionMaps X U)

theorem cofinite_le_principal_compl (S : Finset ι) :
    cofinite ≤ principal ((↑S : Set ι)ᶜ) := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

end DirectLimitConstruction

section Homeomorphism

variable (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (U : (i : ι) → Set (X i))

open TopologicalSpace.DirectLimit in
def toDirectLimit (x : Πʳ i, [X i, U i]) : DirectLimitXS X U :=
  of (fun S : Finset ι => XS X U S) (transitionMaps X U)
    (supportFinset X U x) ⟨(x : (i : ι) → X i), mem_XS_support X U x⟩

open TopologicalSpace.DirectLimit in
noncomputable def fromDirectLimit : DirectLimitXS X U → Πʳ i, [X i, U i] :=
  lift (fun S : Finset ι => XS X U S) (transitionMaps X U)
    (fun S (x : ↥(XS X U S)) => ⟨x.val, XS_mem_restricted X U x.prop⟩)
    (fun S T h x => by simp only [transitionMaps, inclusionMap])


open TopologicalSpace.DirectLimit in
theorem toDirectLimit_fromDirectLimit (q : DirectLimitXS X U) :
    toDirectLimit X U (fromDirectLimit X U q) = q := by
  obtain ⟨⟨S, x⟩, rfl⟩ := @Quotient.exists_rep _ (directLimitSetoid _ _) q


  show toDirectLimit X U (fromDirectLimit X U (of _ _ S x)) = of _ _ S x
  have key : fromDirectLimit X U (of _ _ S x) = ⟨x.val, XS_mem_restricted X U x.prop⟩ := rfl
  rw [key]
  unfold toDirectLimit
  have h_le : supportFinset X U ⟨x.val, XS_mem_restricted X U x.prop⟩ ≤ S :=
    supportFinset_le X U x.prop
  exact (of_comp (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) h_le _).symm

def toChunk (S : Finset ι) (x : ↥(XS X U S)) :
    Πʳ i, [X i, U i]_[Filter.principal ((↑S : Set ι)ᶜ)] :=
  RestrictedProduct.mk x.val (by
    rw [Filter.eventually_principal]
    intro i hi
    exact x.prop i (by simpa using hi))

theorem continuous_toChunk (S : Finset ι) : Continuous (toChunk X U S) := by
  rw [RestrictedProduct.topologicalSpace_eq_of_principal]
  exact continuous_induced_rng.mpr continuous_subtype_val

open TopologicalSpace.DirectLimit in
theorem continuous_fromDirectLimit : Continuous (fromDirectLimit X U) := by
  apply lift_continuous
  intro S
  have h_filter : Filter.cofinite ≤ Filter.principal ((↑S : Set ι)ᶜ) :=
    cofinite_le_principal_compl S


  rw [show (fun x : ↥(XS X U S) => (⟨(x : (i : ι) → X i), XS_mem_restricted X U x.prop⟩ : Πʳ i, [X i, U i])) =
      RestrictedProduct.inclusion X U h_filter ∘ toChunk X U S from by
    ext x i; rfl]
  exact (RestrictedProduct.continuous_inclusion h_filter).comp (continuous_toChunk X U S)

theorem inclusion_mem_XS_of_principal {S : Set ι} (hS : Filter.cofinite ≤ Filter.principal S)
    (y : Πʳ i, [X i, U i]_[Filter.principal S]) :
    (RestrictedProduct.inclusion X U hS y : (i : ι) → X i) ∈
      XS X U (Set.Finite.toFinset (Filter.eventually_cofinite.mp (hS (Filter.mem_principal.mpr (Set.Subset.refl S))))) := by
  intro i hi
  have hy := y.2
  rw [Filter.eventually_principal] at hy
  apply hy
  by_contra h
  exact hi ((Set.Finite.mem_toFinset _).mpr h)

open TopologicalSpace.DirectLimit in
theorem continuous_toDirectLimit : Continuous (toDirectLimit X U) := by
  rw [RestrictedProduct.continuous_dom]
  intro S hS


  have hSc_fin : Set.Finite Sᶜ := by
    rw [← Filter.mem_cofinite]
    exact hS (Filter.mem_principal.mpr (Set.Subset.refl S))
  set T : Finset ι := hSc_fin.toFinset with hT_def


  have key : ∀ y : Πʳ i, [X i, U i]_[Filter.principal S],
      toDirectLimit X U (RestrictedProduct.inclusion X U hS y) =
        of (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) T
          ⟨(RestrictedProduct.inclusion X U hS y : (i : ι) → X i),
           inclusion_mem_XS_of_principal X U hS y⟩ := by
    intro y
    unfold toDirectLimit
    have h_le : supportFinset X U (RestrictedProduct.inclusion X U hS y) ≤ T :=
      supportFinset_le X U (inclusion_mem_XS_of_principal X U hS y)
    exact (of_comp (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) h_le _).symm

  have heq : toDirectLimit X U ∘ RestrictedProduct.inclusion X U hS =
      (fun y => of (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) T
        ⟨(RestrictedProduct.inclusion X U hS y : (i : ι) → X i),
         inclusion_mem_XS_of_principal X U hS y⟩) := by
    ext y; exact key y
  rw [heq]


  apply (of_continuous _ _ T).comp


  apply continuous_induced_rng.mpr


  rw [RestrictedProduct.topologicalSpace_eq_of_principal]
  exact continuous_subtype_val


end Homeomorphism

end RestrictedProduct


end
