/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.CompleteVarieties
import Atlas.ArithmeticGeometry.code.ValuationRings
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.NoetherianSpace

universe u

namespace AlgebraicGeometry.CompletenessValuationCriterion

structure AlgVariety (k : Type u) [Field k] where
  carrier : Type u
  [topInst : TopologicalSpace carrier]
  functionField : Type u
  [ffField : Field functionField]
  baseEmbed : k →+* functionField
  baseEmbed_inj : Function.Injective baseEmbed
  localRingAt : carrier → Subring functionField
  base_le_localRing : ∀ P x, baseEmbed x ∈ localRingAt P
  noethProduct : ∀ (Y : Type u) [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace Y],
    TopologicalSpace.NoetherianSpace (carrier × Y)

attribute [instance] AlgVariety.topInst AlgVariety.ffField

structure SubvarietyOf {k : Type u} [Field k] (X : AlgVariety k) where
  toVariety : AlgVariety k
  inclusion : toVariety.carrier → X.carrier

structure ValRingOver {k : Type u} [Field k] (V : AlgVariety k) where
  valSub : ValuationSubring V.functionField
  contains_base : ∀ x : k, V.baseEmbed x ∈ valSub

def localRing_le {k : Type u} [Field k] {V : AlgVariety k}
    (P : V.carrier) (R : ValRingOver V) : Prop :=
  ∀ x : V.functionField, x ∈ V.localRingAt P → x ∈ R.valSub

def SatisfiesValuationCriterion {k : Type u} [Field k] (X : AlgVariety k) : Prop :=
  ∀ (Z : SubvarietyOf X) (R : ValRingOver Z.toVariety),
    ∃ P : Z.toVariety.carrier, localRing_le P R


lemma noetherian_finite_union_irreducible {k : Type u} [Field k]
    (X : AlgVariety k) (Y : Type u) [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace Y]
    (V : Set (X.carrier × Y)) (hV : IsClosed V) :
    ∃ (n : ℕ) (components : Fin n → Set (X.carrier × Y)),
      (∀ i, IsClosed (components i)) ∧
      (∀ i, IsIrreducible (components i)) ∧
      V = ⋃ i, components i := by
  haveI := X.noethProduct Y
  obtain ⟨S, hSfin, hSclosed, hSirr, hSunion⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hV
  lift S to Finset (Set (X.carrier × Y)) using hSfin
  let e := S.equivFin
  refine ⟨S.card, fun i => (e.symm i).val, fun i => ?_, fun i => ?_, ?_⟩
  · exact hSclosed _ (Finset.coe_mem (e.symm i))
  · exact hSirr _ (Finset.coe_mem (e.symm i))
  · rw [hSunion]
    ext x
    simp only [Set.mem_sUnion, Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨e ⟨t, ht⟩, by simpa [e.symm_apply_apply] using hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨(e.symm i).val, Finset.coe_mem (e.symm i), hx⟩

lemma isClosed_image_finite_union {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (n : ℕ) (components : Fin n → Set X)
    (hclosed : ∀ i, IsClosed (f '' (components i))) :
    IsClosed (f '' (⋃ i, components i)) := by
  rw [Set.image_iUnion]
  exact isClosed_iUnion_of_finite fun i => hclosed i

structure DominantProjectionData {k : Type u} [Field k]
    (X : AlgVariety k) (Y : Type u) [TopologicalSpace Y]
    (V : Set (X.carrier × Y)) where
  Z : SubvarietyOf X
  Vvar : AlgVariety k
  embed : Vvar.carrier → X.carrier × Y
  embed_mem : ∀ p, embed p ∈ V
  toZ : Vvar.carrier → Z.toVariety.carrier
  psiStar : Z.toVariety.functionField →+* Vvar.functionField
  psiStar_inj : Function.Injective psiStar
  psiStar_base_compat : ∀ x : k,
    psiStar (Z.toVariety.baseEmbed x) = Vvar.baseEmbed x


lemma valuation_ring_pullback
    {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (ψ : F₁ →+* F₂) (_hψ : Function.Injective ψ)
    (S : ValuationSubring F₂) :
    ∃ R : ValuationSubring F₁, ∀ x : F₁, x ∈ R ↔ ψ x ∈ S := by
  exact ⟨S.comap ψ, fun x => ValuationSubring.mem_comap⟩

structure CoordRingEvalData {k : Type u} [Field k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V) (Q : Y) where
  coordRingY : Subring dpd.Vvar.functionField
  evalAtQ : coordRingY →+* k
  base_le_coordRingY : ∀ x : k, dpd.Vvar.baseEmbed x ∈ coordRingY
  evalAtQ_fixes_base : ∀ (x : k) (hx : dpd.Vvar.baseEmbed x ∈ coordRingY),
    evalAtQ ⟨dpd.Vvar.baseEmbed x, hx⟩ = x
  psiStar_base_compat : ∀ x : k,
    dpd.psiStar (dpd.Z.toVariety.baseEmbed x) = dpd.Vvar.baseEmbed x



theorem coordring_contained_in_valring {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V)
    (coordRingY : Subring dpd.Vvar.functionField)
    (S : ValuationSubring dpd.Vvar.functionField)
    (hAS : (coordRingY : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField))
    (_P₀ : dpd.Z.toVariety.carrier)
    (_hP₀ : ∀ x : dpd.Z.toVariety.functionField,
      x ∈ dpd.Z.toVariety.localRingAt _P₀ → dpd.psiStar x ∈ S) :
    ∃ (coordRingV : Subring dpd.Vvar.functionField),
      (coordRingY : Set dpd.Vvar.functionField) ⊆ (coordRingV : Set dpd.Vvar.functionField) ∧
      (coordRingV : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField) :=
  ⟨coordRingY, Set.Subset.refl _, hAS⟩





lemma isClosed_snd_image_of_closure_subset {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (V : Set (X × Y)) (h : closure (Prod.snd '' V) ⊆ Prod.snd '' V) :
    IsClosed (Prod.snd '' V) :=
  closure_eq_iff_isClosed.mp (Set.Subset.antisymm h subset_closure)



end AlgebraicGeometry.CompletenessValuationCriterion
