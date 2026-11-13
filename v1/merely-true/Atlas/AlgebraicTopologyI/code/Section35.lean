/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section34
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open Set

namespace CechCohomology

/-- A map `φ : J → I` between preorders is **cofinal** if every `i : I` is
$\le$ some `φ j`. Used to recognise when pulling a directed system back along
`φ` gives the same direct limit. -/
def IsCofinalMap {I : Type*} {J : Type*} [LE I] (φ : J → I) : Prop :=
  ∀ i : I, ∃ j : J, i ≤ φ j

section DirectLimits

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [DecidableEq κ] [Nonempty κ]
variable (G : ι → Type*) [∀ i, AddCommGroup (G i)]
variable (f : ∀ i j, i ≤ j → G i →+ G j) [DirectedSystem G fun i j h ↦ f i j h]
variable (φ : κ →o ι)

/-- Pullback of the bonding maps of a directed system `(G, f)` along a monotone
map `φ : κ →o ι`: the pulled-back system has fibres `G (φ j)` and bonding maps
`f (φ j₁) (φ j₂) (φ.monotone h)`. -/
def pullbackBondingMap (j₁ j₂ : κ) (h : j₁ ≤ j₂) : G (φ j₁) →+ G (φ j₂) :=
  f (φ j₁) (φ j₂) (φ.monotone h)

/-- The canonical map from the direct limit of the pulled-back system over `κ`
to the direct limit over `ι` of the original system, induced by the universal
property of direct limits. -/
noncomputable def cofinalMap :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) →+
    AddCommGroup.DirectLimit G f :=
  AddCommGroup.DirectLimit.lift _ _ _
    (fun j => AddCommGroup.DirectLimit.of G f (φ j))
    (fun _ _ hij x => AddCommGroup.DirectLimit.of_f (f := f) (φ.monotone hij) x)

/-- **Lemma 35.7 (cofinal maps and direct limits).** If `φ : κ →o ι` is cofinal
(every `i : ι` is `≤ φ j` for some `j : κ`), then the induced map between
direct limits is an additive equivalence: the limit over a cofinal subset
recovers the full limit. -/
noncomputable def cofinalMapEquiv
    (hcof : ∀ i : ι, ∃ j : κ, i ≤ φ j) :
    AddCommGroup.DirectLimit (fun j => G (φ j)) (pullbackBondingMap G f φ) ≃+
    AddCommGroup.DirectLimit G f :=
  AddEquiv.ofBijective (cofinalMap G f φ)
    ⟨by


      rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [AddMonoidHom.mem_ker] at ha
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih j x =>
        simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of] at ha
        obtain ⟨i, hji, hzero⟩ := AddCommGroup.DirectLimit.of.zero_exact (φ j) x ha
        obtain ⟨j', hij'⟩ := hcof i
        obtain ⟨k, hjk, hj'k⟩ := directed_of (· ≤ ·) j j'
        have h_i_phik : i ≤ φ k := le_trans hij' (φ.monotone hj'k)
        have key : pullbackBondingMap G f φ j k hjk x = 0 := by
          show f (φ j) (φ k) (φ.monotone hjk) x = 0
          rw [show f (φ j) (φ k) (φ.monotone hjk) x =
                f i (φ k) h_i_phik (f (φ j) i hji x) from
            (DirectedSystem.map_map (f := fun i j h ↦ f i j h) hji h_i_phik x).symm]
          rw [hzero, map_zero]
        simp only [AddSubgroup.mem_bot]
        rw [show AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j x =
          AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) k
            (pullbackBondingMap G f φ j k hjk x)
          from (AddCommGroup.DirectLimit.of_f (f := pullbackBondingMap G f φ) hjk x).symm]
        rw [key, map_zero],
    by
      intro a
      induction a using AddCommGroup.DirectLimit.induction_on with
      | ih i x =>
        obtain ⟨j, hij⟩ := hcof i
        exact ⟨AddCommGroup.DirectLimit.of _ (pullbackBondingMap G f φ) j
          (f i (φ j) hij x), by
          simp only [cofinalMap, AddCommGroup.DirectLimit.lift_of]
          exact AddCommGroup.DirectLimit.of_f (f := f) hij x⟩⟩

end DirectLimits

variable {X : Type*} [TopologicalSpace X]

/-- **Cofinality (left half) of the Mayer–Vietoris diagram.** Given open
neighborhoods `U ⊇ A ∪ B`, `V ⊇ B` with `V ⊆ U`, we can find open
neighborhoods `W` of `A` and `Y` of `B` such that `W ∪ Y ⊆ U` and `Y ⊆ V`
— trivially, take `W := U`, `Y := V`. -/
theorem cofinal_neighborhood_left
    {A B U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hABU : A ∪ B ⊆ U) (hBV : B ⊆ V) (hVU : V ⊆ U) :
    ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
      W ∪ Y ⊆ U ∧ Y ⊆ V :=
  ⟨U, V, hU, hV, subset_union_left.trans hABU, hBV, (union_eq_left.mpr hVU).le, Subset.rfl⟩

omit [TopologicalSpace X] in
/-- Auxiliary set-theoretic lemma: if `S` and `T` are disjoint, then
`(U ∩ S) ∩ (V ∪ T) ⊆ V`. Used to verify the inclusion `W ∩ Y ⊆ V` in the
normal/compact cofinality arguments. -/
theorem inter_inter_union_subset_of_disjoint {U S V T : Set X}
    (hST : Disjoint S T) : (U ∩ S) ∩ (V ∪ T) ⊆ V := by
  intro x hx
  rcases hx.2 with hxV | hxT
  · exact hxV
  · exact (Set.disjoint_iff.mp hST ⟨hx.1.2, hxT⟩).elim

/-- **Cofinality (right half) for a normal space.** Given closed disjoint
`A`, `B` and open `U ⊇ A`, `V ⊇ A ∩ B`, normality produces open `W ⊇ A`,
`Y ⊇ B` with `W ⊆ U` and `W ∩ Y ⊆ V`. Proven by separating `A` from
`B ∩ Vᶜ` via `normal_separation`. -/
theorem cofinal_neighborhood_right_normal [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hABV : A ∩ B ⊆ V) :
    ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
      W ⊆ U ∧ W ∩ Y ⊆ V := by

  have hclosed_BVc : IsClosed (B ∩ Vᶜ) := hB.inter (isClosed_compl_iff.mpr hV)
  have hdisj : Disjoint A (B ∩ Vᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨hxA, hxB, hxV⟩
    exact hxV (hABV ⟨hxA, hxB⟩)

  obtain ⟨S, T, hS, hT, hAS, hBVT, hST⟩ := normal_separation hA hclosed_BVc hdisj

  have hBYT : B ⊆ V ∪ T := by rwa [← compl_compl V, ← Set.inter_subset]

  exact ⟨U ∩ S, V ∪ T, hU.inter hS, hV.union hT,
    subset_inter hAU hAS, hBYT, inter_subset_left,
    inter_inter_union_subset_of_disjoint hST⟩

/-- **Cofinality (right half) for a Hausdorff space.** The compact analogue of
`cofinal_neighborhood_right_normal`: for compact `A`, `B` in a Hausdorff space,
the same separation conclusion holds, using
`SeparatedNhds.of_isCompact_isCompact`. -/
theorem cofinal_neighborhood_right_compact [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hABV : A ∩ B ⊆ V) :
    ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
      W ⊆ U ∧ W ∩ Y ⊆ V := by

  have hcompact_BVc : IsCompact (B ∩ Vᶜ) := hB.inter_right (isClosed_compl_iff.mpr hV)
  have hdisj : Disjoint A (B ∩ Vᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨hxA, hxB, hxV⟩
    exact hxV (hABV ⟨hxA, hxB⟩)

  obtain ⟨S, T, hS, hT, hAS, hBVT, hST⟩ :=
    SeparatedNhds.of_isCompact_isCompact hA hcompact_BVc hdisj

  have hBYT : B ⊆ V ∪ T := by rwa [← compl_compl V, ← Set.inter_subset]

  exact ⟨U ∩ S, V ∪ T, hU.inter hS, hV.union hT,
    subset_inter hAU hAS, hBYT, inter_subset_left,
    inter_inter_union_subset_of_disjoint hST⟩

/-- **Lemma 35.8 (cofinality for Mayer–Vietoris, normal case).** For closed
subsets `A`, `B` of a normal space, the two cofinality conditions
(`cofinal_neighborhood_left` and `cofinal_neighborhood_right_normal`) both
hold; this is the input needed to deduce excision (and hence Mayer–Vietoris)
from the abstract cofinality machinery. -/
theorem neighborhood_maps_cofinal_normal [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    (∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ∪ Y ⊆ U ∧ Y ⊆ V) ∧
    (∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ⊆ U ∧ W ∩ Y ⊆ V) :=
  ⟨fun _ _ hU hV hABU hBV hVU => cofinal_neighborhood_left hU hV hABU hBV hVU,
   fun _ _ hU hV hAU hABV => cofinal_neighborhood_right_normal hA hB hU hV hAU hABV⟩

/-- Compact analogue of `neighborhood_maps_cofinal_normal`: the same conjunction
of cofinality conditions holds for compact subsets of a Hausdorff space. -/
theorem neighborhood_maps_cofinal_compact [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) :
    (∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ∪ Y ⊆ U ∧ Y ⊆ V) ∧
    (∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V →
      ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧
        W ⊆ U ∧ W ∩ Y ⊆ V) :=
  ⟨fun _ _ hU hV hABU hBV hVU => cofinal_neighborhood_left hU hV hABU hBV hVU,
   fun _ _ hU hV hAU hABV => cofinal_neighborhood_right_compact hA hB hU hV hAU hABV⟩

end CechCohomology

open CategoryTheory AlgebraicTopology Limits TopologicalSpace Function

noncomputable section

namespace CechCohomology

/-- Exactness is preserved under direct limits of abelian groups: given two
composable, pointwise-exact natural transformations of directed systems of
abelian groups, the induced sequence of direct limits is again exact. -/
theorem addCommGroup_directLimit_map_exact
    {ι : Type*} [DecidableEq ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    {f : ∀ i j, i ≤ j → G i →+ G j} [DirectedSystem G fun i j h ↦ f i j h]
    {G' : ι → Type*} [∀ i, AddCommGroup (G' i)]
    {f' : ∀ i j, i ≤ j → G' i →+ G' j} [DirectedSystem G' fun i j h ↦ f' i j h]
    {G'' : ι → Type*} [∀ i, AddCommGroup (G'' i)]
    {f'' : ∀ i j, i ≤ j → G'' i →+ G'' j} [DirectedSystem G'' fun i j h ↦ f'' i j h]
    (p : ∀ i, G i →+ G' i) (hp : ∀ i j h, (p j).comp (f i j h) = (f' i j h).comp (p i))
    (q : ∀ i, G' i →+ G'' i) (hq : ∀ i j h, (q j).comp (f' i j h) = (f'' i j h).comp (q i))
    (exact_at : ∀ i, Function.Exact (p i) (q i)) :
    Function.Exact
      (AddCommGroup.DirectLimit.map p hp)
      (AddCommGroup.DirectLimit.map q hq) := by
  intro y
  constructor
  · intro hy
    induction y using AddCommGroup.DirectLimit.induction_on with
    | ih i yi =>
      rw [AddCommGroup.DirectLimit.map_apply_of] at hy
      obtain ⟨j, hij, hfq⟩ := AddCommGroup.DirectLimit.of.zero_exact i (q i yi) hy
      have hqf : q j (f' i j hij yi) = 0 := by
        have := DFunLike.congr_fun (hq i j hij) yi
        simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
        rw [this, hfq]
      obtain ⟨xj, hxj⟩ := ((exact_at j) (f' i j hij yi)).mp hqf
      exact ⟨AddCommGroup.DirectLimit.of G f j xj, by
        rw [AddCommGroup.DirectLimit.map_apply_of, hxj,
          AddCommGroup.DirectLimit.of_f]⟩
  · rintro ⟨x, rfl⟩
    induction x using AddCommGroup.DirectLimit.induction_on with
    | ih i xi =>
      simp only [AddCommGroup.DirectLimit.map_apply_of]
      have : q i (p i xi) = 0 := ((exact_at i) (p i xi)).mpr ⟨xi, rfl⟩
      rw [this, map_zero]

/-- The functor sending a space `Y` to its integral singular chain complex
$S_\bullet(Y; \mathbb{Z})$ as a chain complex of `ℤ`-modules. -/
abbrev singChain : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- $p$-th integral singular cohomology $H^p(Y; \mathbb{Z})$ of a space `Y`,
computed by dualising `singChain Y` and taking the `p`-th cohomology. -/
def singCohom (Y : TopCat.{0}) (p : ℕ) : ModuleCat.{0} ℤ :=
  ((singChain.obj Y).linearYonedaObj ℤ (ModuleCat.of ℤ ℤ)).homology p

end CechCohomology

/-- Čech cohomology $\check{H}^p(X, K; \mathbb{Z})$ of a subset `K ⊆ X`,
defined as the direct limit (`cechCohomology`) of singular cohomology over
open neighborhoods of `K`. -/
def CechCohomology.CechCohom
    (X : Type) [TopologicalSpace X] (K : Set X) (p : ℕ) : Type :=
  (CechCohomology.cechCohomology ℤ K p : Type)

/-- The additive group structure on `CechCohom X K p`, inherited from the
underlying module. -/
noncomputable instance CechCohomology.CechCohom.addCommGroup
    (X : Type) [TopologicalSpace X]
    (K : Set X) (p : ℕ) : AddCommGroup (CechCohomology.CechCohom X K p) :=
  (CechCohomology.cechCohomology ℤ K p).isAddCommGroup




namespace CechCohomology

open CechCohomology Function















end CechCohomology

namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

/-- A **relative neighborhood pair** for `L ⊆ K ⊆ X`: a pair of open sets
`U ⊇ K`, `V ⊇ L` with `V ≤ U`. The directed system indexed by these pairs is
used to define relative Čech cohomology. -/
structure RelNbhdPair {X : Type} [TopologicalSpace X] (K L : Set X) where
  U : Opens X
  V : Opens X
  hK : K ⊆ ↑U
  hL : L ⊆ ↑V
  hVU : V ≤ U

variable {X : Type} [TopologicalSpace X]

/-- Preorder on relative neighborhood pairs: `p ≤ q` iff `q.U ⊆ p.U` and
`q.V ⊆ p.V` (smaller neighborhoods correspond to larger elements). -/
instance relNbhdPair_preorder {K L : Set X} : Preorder (RelNbhdPair K L) where
  le p q := q.U ≤ p.U ∧ q.V ≤ p.V
  le_refl _ := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ hpq hqr := ⟨le_trans hqr.1 hpq.1, le_trans hqr.2 hpq.2⟩

/-- The preorder of relative neighborhood pairs is directed: any two pairs
admit a common refinement obtained by intersecting their components. -/
instance relNbhdPair_directed {K L : Set X} :
    IsDirected (RelNbhdPair K L) (· ≤ ·) where
  directed p q := ⟨⟨p.U ⊓ q.U, p.V ⊓ q.V,
    fun _ hx => ⟨p.hK hx, q.hK hx⟩,
    fun _ hx => ⟨p.hL hx, q.hL hx⟩,
    inf_le_inf p.hVU q.hVU⟩,
    ⟨inf_le_left, inf_le_left⟩, ⟨inf_le_right, inf_le_right⟩⟩

/-- The preorder of relative neighborhood pairs is nonempty: the pair
`(⊤, ⊤)` (the whole space, the whole space) is always a valid neighborhood
pair. -/
instance relNbhdPair_nonempty {K L : Set X} : Nonempty (RelNbhdPair K L) :=
  ⟨⟨⊤, ⊤, fun _ _ => trivial, fun _ _ => trivial, le_refl _⟩⟩

/-- Continuous inclusion $V \hookrightarrow U$ associated to a relative
neighborhood pair `(U, V)`, viewed as a morphism in `TopCat`. -/
def relNbhdInclusion {K L : Set X} (pair : RelNbhdPair K L) :
    TopCat.of ↑pair.V.1 ⟶ TopCat.of ↑pair.U.1 :=
  ⟨fun x => ⟨x.1, pair.hVU x.2⟩, continuous_inclusion pair.hVU⟩

/-- Relative singular cohomology $H^p(U, V; \mathbb{Z})$ of the pair of open
sets `(U, V)` associated to a relative neighborhood pair. -/
noncomputable def relSingCohomOfPair {K L : Set X}
    (pair : RelNbhdPair K L) (p : ℕ) : ModuleCat.{0} ℤ :=
  relativeSingularCohomology ℤ (TopCat.of ↑pair.U.1) (TopCat.of ↑pair.V.1)
    (relNbhdInclusion pair) (ModuleCat.of ℤ ℤ) p

/-- Index-wise family $\mathrm{pair} \mapsto H^p(U_{\mathrm{pair}}, V_{\mathrm{pair}})$
whose direct limit will define relative Čech cohomology. -/
def relCechFam (K L : Set X) (p : ℕ) (pair : RelNbhdPair K L) : Type :=
  (relSingCohomOfPair pair p : Type _)

/-- The additive group structure on each fibre of `relCechFam`. -/
noncomputable instance relCechFam_addCommGroup {K L : Set X}
    (p : ℕ) (pair : RelNbhdPair K L) :
    AddCommGroup (relCechFam K L p pair) :=
  (relSingCohomOfPair pair p).isAddCommGroup

/-- Continuous inclusion `U₂ ↪ U₁` of opens (with `U₂ ≤ U₁`) viewed as a
morphism in `TopCat`. -/
def opensInclusion {U₁ U₂ : Opens X} (h : U₂ ≤ U₁) :
    TopCat.of ↑U₂.1 ⟶ TopCat.of ↑U₁.1 :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- Naturality square for opens inclusions: the two ways of composing the
inclusions $V_2 \hookrightarrow V_1 \hookrightarrow U_1$ and
$V_2 \hookrightarrow U_2 \hookrightarrow U_1$ agree. -/
theorem opensInclusion_comm {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    opensInclusion h.2 ≫ relNbhdInclusion pair₁ =
    relNbhdInclusion pair₂ ≫ opensInclusion h.1 := by
  apply TopCat.ext
  intro x
  rfl

/-- The cochain-restriction operation is contravariantly functorial in
composition of continuous maps. -/
theorem restrictionCochainMap_comp (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrictionCochainMap R G (f ≫ g) =
    restrictionCochainMap R G g ≫ restrictionCochainMap R G f := by
  simp only [restrictionCochainMap, Functor.map_comp]
  rfl

/-- Commutativity of restriction cochain maps along the square of inclusions
associated to `pair₁ ≤ pair₂`: derives from `opensInclusion_comm` and the
contravariant functoriality of restriction. -/
theorem restrictionCochainMap_square {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2) =
    restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1) ≫
      restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) := by
  rw [← restrictionCochainMap_comp, ← restrictionCochainMap_comp,
      opensInclusion_comm pair₁ pair₂ h]

open CategoryTheory.Limits in
/-- Transition map of relative singular cochain complexes induced by
`pair₁ ≤ pair₂`: the canonical map between kernels of the restriction cochain
maps coming from the commuting square. -/
noncomputable def relCochainComplexMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ⟶
    relativeSingularCochainComplex ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) :=
  kernel.map
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1))
    (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2))
    (restrictionCochainMap_square pair₁ pair₂ h)

/-- Transition map between relative singular cohomology groups
$H^p(U_1, V_1) \to H^p(U_2, V_2)$ for `pair₁ ≤ pair₂`, obtained by taking
$p$-th homology of `relCochainComplexMap`. -/
noncomputable def relCohomTransitionModMap {K L : Set X}
    (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) (p : ℕ) :
    relSingCohomOfPair pair₁ p ⟶ relSingCohomOfPair pair₂ p :=
  HomologicalComplex.homologyMap (relCochainComplexMap pair₁ pair₂ h) p

/-- Bonding map of the directed system `relCechFam K L p`: the underlying
additive group hom of `relCohomTransitionModMap`. -/
noncomputable def relCechTransitionMap
    {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : RelNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relCechFam K L p pair₁ →+ relCechFam K L p pair₂ :=
  (relCohomTransitionModMap pair₁ pair₂ h p).hom.toAddMonoidHom

end CechCohomology


open CategoryTheory CategoryTheory.Limits SingularCohomology in
/-- `relCechFam K L p` together with `relCechTransitionMap` is a directed
system: identities act as identities, and composition of bondings respects
composition of inclusions. -/
noncomputable instance CechCohomology.relCechFam_directedSystem_axioms
    {X : Type} [TopologicalSpace X] {K L : Set X} (p : ℕ) :
    DirectedSystem (CechCohomology.relCechFam K L p)
      (fun pair₁ pair₂ h => CechCohomology.relCechTransitionMap p pair₁ pair₂ h) where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap (CechCohomology.relCochainComplexMap i i (le_refl i)) p).hom.toAddMonoidHom x = x
    have hid1 : CechCohomology.opensInclusion (le_refl i).1 =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres1 : restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    have hrelMap : CechCohomology.relCochainComplexMap i i (le_refl i) = 𝟙 _ := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))]
      simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
      rw [hid1]
      simp only [hres1, Category.comp_id]
    rw [hrelMap, HomologicalComplex.homologyMap_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    simp only [CechCohomology.relCechTransitionMap, CechCohomology.relCohomTransitionModMap]
    have hcomp1 : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (hij.trans hjk).1 := by
      apply TopCat.ext; intro x; rfl
    have hrelComp : CechCohomology.relCochainComplexMap i j hij ≫
        CechCohomology.relCochainComplexMap j k hjk =
        CechCohomology.relCochainComplexMap i k (hij.trans hjk) := by
      unfold CechCohomology.relCochainComplexMap relativeSingularCochainComplex
      rw [← cancel_mono (kernel.ι (restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion k)))]
      simp only [Category.assoc, kernel.lift_ι]
      rw [kernel.lift_ι_assoc]
      simp only [Category.assoc, kernel.lift_ι]
      congr 1
      rw [← CechCohomology.restrictionCochainMap_comp, hcomp1]
    rw [show CechCohomology.relCochainComplexMap i k (hij.trans hjk) =
      CechCohomology.relCochainComplexMap i j hij ≫
      CechCohomology.relCochainComplexMap j k hjk from hrelComp.symm]
    rw [HomologicalComplex.homologyMap_comp]
    rfl

namespace CechCohomology

variable {X : Type} [TopologicalSpace X]

/-- Convenience instance form of `relCechFam_directedSystem_axioms`. -/
instance relCechFam_directedSystem {K L : Set X} (p : ℕ) :
    DirectedSystem (relCechFam K L p)
      (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h) :=
  relCechFam_directedSystem_axioms p

/-- **Relative Čech cohomology** $\check{H}^p(X, K, L)$: the direct limit over
relative neighborhood pairs of `(K, L)` of the relative singular cohomology
$H^p(U, V; \mathbb{Z})$. -/
noncomputable def CechCohomRel
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) : Type :=
  open Classical in
  AddCommGroup.DirectLimit (relCechFam K L p)
    (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)

namespace CechCohomRel

/-- Additive group structure on `CechCohomRel X K L p` from the direct limit. -/
noncomputable instance addCommGroup
    (X : Type) [TopologicalSpace X]
    (K L : Set X) (p : ℕ) : AddCommGroup (CechCohomRel X K L p) :=
  open Classical in
  AddCommGroup.DirectLimit.addCommGroup _ _

end CechCohomRel
end CechCohomology

/-- Restriction of a relative neighborhood pair along inclusions `L₁ ⊆ K₁`,
`L₂ ⊆ K₂`: a neighborhood pair of `(K₁, K₂)` is also one of `(L₁, L₂)`. -/
def CechCohomology.RelNbhdPair.restrict
    {X : Type} [TopologicalSpace X]
    {K₁ K₂ L₁ L₂ : Set X} (h₁ : L₁ ⊆ K₁) (h₂ : L₂ ⊆ K₂)
    (pair : CechCohomology.RelNbhdPair K₁ K₂) :
    CechCohomology.RelNbhdPair L₁ L₂ where
  U := pair.U
  V := pair.V
  hK := h₁.trans pair.hK
  hL := h₂.trans pair.hL
  hVU := pair.hVU


/-- Inclusion-induced homomorphism on relative Čech cohomology
$\check{H}^p(X, K_1, K_2) \to \check{H}^p(X, L_1, L_2)$ for $L_1 \subseteq K_1$,
$L_2 \subseteq K_2$, defined by restricting each neighborhood pair via
`RelNbhdPair.restrict`. -/
noncomputable def CechCohomology.CechCohomRel.inclusionMap
    (X : Type) [TopologicalSpace X]
    {K₁ K₂ L₁ L₂ : Set X} (h₁ : L₁ ⊆ K₁) (h₂ : L₂ ⊆ K₂) (p : ℕ) :
    CechCohomology.CechCohomRel X K₁ K₂ p →+
      CechCohomology.CechCohomRel X L₁ L₂ p :=
  open Classical CechCohomology in
  AddCommGroup.DirectLimit.lift
    (relCechFam K₁ K₂ p)
    (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
    (CechCohomRel X L₁ L₂ p)
    (fun pair => AddCommGroup.DirectLimit.of
      (relCechFam L₁ L₂ p)
      (fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
      (pair.restrict h₁ h₂))
    (fun i j hij x => by
      classical
      have hij' : i.restrict h₁ h₂ ≤ j.restrict h₁ h₂ := hij
      exact AddCommGroup.DirectLimit.of_f (G := relCechFam L₁ L₂ p)
        (f := fun pair₁ pair₂ h => relCechTransitionMap p pair₁ pair₂ h)
        hij' x)










namespace CechCohomology



end CechCohomology








/-- Index type for the long-exact-sequence directed systems: a synonym for
`RelNbhdPair K L`. -/
def CechCohomology.lesIndexType
    (X : Type) [TopologicalSpace X] (K L : Set X) : Type :=
  CechCohomology.RelNbhdPair K L

/-- Preorder on the LES index type, inherited from `relNbhdPair_preorder`. -/
instance CechCohomology.lesIndexPreorder
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Preorder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_preorder

/-- Directedness of the LES index type. -/
instance CechCohomology.lesIndexDirected
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    IsDirectedOrder (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_directed

/-- Classical decidable equality on the LES index type. -/
noncomputable instance CechCohomology.lesIndexDecEq
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    DecidableEq (CechCohomology.lesIndexType X K L) :=
  open Classical in inferInstance

/-- Nonemptiness of the LES index type. -/
instance CechCohomology.lesIndexNonempty
    (X : Type) [TopologicalSpace X] (K L : Set X) :
    Nonempty (CechCohomology.lesIndexType X K L) :=
  CechCohomology.relNbhdPair_nonempty

/-- Relative cohomology family $i \mapsto H^p(U_i, V_i)$ for the pointwise
long exact sequence. -/
def CechCohomology.relFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  CechCohomology.relCechFam K L p

/-- Additive group structure on each fibre of `relFamily`. -/
noncomputable instance CechCohomology.relFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.relFamily X K L p i) :=
  CechCohomology.relCechFam_addCommGroup p i

/-- Absolute cohomology family $i \mapsto H^p(U_i)$ — middle term of the
pointwise LES. -/
def CechCohomology.absKFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  fun i => (CechCohomology.singCohom (TopCat.of ↑i.U.1) p : Type)

/-- Additive group structure on each fibre of `absKFamily`. -/
noncomputable instance CechCohomology.absKFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.absKFamily X K L p i) :=
  (CechCohomology.singCohom (TopCat.of ↑i.U.1) p).isAddCommGroup

/-- Absolute cohomology family $i \mapsto H^p(V_i)$ — third term of the
pointwise LES. -/
def CechCohomology.absLFamily
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.lesIndexType X K L → Type :=
  fun i => (CechCohomology.singCohom (TopCat.of ↑i.V.1) p : Type)

/-- Additive group structure on each fibre of `absLFamily`. -/
noncomputable instance CechCohomology.absLFamily_acg
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    AddCommGroup (CechCohomology.absLFamily X K L p i) :=
  (CechCohomology.singCohom (TopCat.of ↑i.V.1) p).isAddCommGroup

/-- Bonding map for the relative cohomology directed system; re-export of
`relCechTransitionMap`. -/
noncomputable def CechCohomology.relBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.relFamily X K L p i →+ CechCohomology.relFamily X K L p j :=
  CechCohomology.relCechTransitionMap p i j h

/-- `relFamily` together with `relBond` is a directed system. -/
noncomputable instance CechCohomology.relBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.relFamily X K L p)
      fun i j h => CechCohomology.relBond X K L p i j h :=
  CechCohomology.relCechFam_directedSystem_axioms p

/-- Bonding map for `absKFamily`: pullback of singular cohomology along the
open inclusion $U_j \hookrightarrow U_i$. -/
noncomputable def CechCohomology.absKBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.absKFamily X K L p i →+ CechCohomology.absKFamily X K L p j :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom


/-- `absKFamily` together with `absKBond` is a directed system. -/
noncomputable instance CechCohomology.absKBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absKFamily X K L p)
      fun i j h => CechCohomology.absKBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.U))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.U) =
        𝟙 (TopCat.of ↑i.U.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.U.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.1)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.1 hij.1))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.1 ≫ CechCohomology.opensInclusion hij.1 =
        CechCohomology.opensInclusion (le_trans hjk.1 hij.1) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.1 hij.1)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.1) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.1)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]

/-- Bonding map for `absLFamily`: pullback of singular cohomology along the
open inclusion $V_j \hookrightarrow V_i$. -/
noncomputable def CechCohomology.absLBond
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.absLFamily X K L p i →+ CechCohomology.absLFamily X K L p j :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom


/-- `absLFamily` together with `absLBond` is a directed system. -/
noncomputable instance CechCohomology.absLBond_dirSys
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    DirectedSystem (CechCohomology.absLFamily X K L p)
      fun i j h => CechCohomology.absLBond X K L p i j h where
  map_self := by
    intro i x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_refl i.V))) p).hom.toAddMonoidHom x = x
    have hid : CechCohomology.opensInclusion (le_refl i.V) =
        𝟙 (TopCat.of ↑i.V.1) := by apply TopCat.ext; intro x; rfl
    have hres : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (𝟙 (TopCat.of ↑i.V.1)) = 𝟙 _ := by
      simp only [SingularCohomology.restrictionCochainMap, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, hres, HomologicalComplex.homologyMap_id]
    simp
  map_map := by
    intro k j i hij hjk x
    show (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)) p).hom.toAddMonoidHom
      ((HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion hij.2)) p).hom.toAddMonoidHom x) =
      (HomologicalComplex.homologyMap
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.opensInclusion (le_trans hjk.2 hij.2))) p).hom.toAddMonoidHom x
    have hcomp : CechCohomology.opensInclusion hjk.2 ≫ CechCohomology.opensInclusion hij.2 =
        CechCohomology.opensInclusion (le_trans hjk.2 hij.2) := by
      apply TopCat.ext; intro x; rfl
    rw [show SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion (le_trans hjk.2 hij.2)) =
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hij.2) ≫
      SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion hjk.2)
      from by rw [← CechCohomology.restrictionCochainMap_comp, hcomp]]
    rw [HomologicalComplex.homologyMap_comp]
    simp [LinearMap.toAddMonoidHom_coe, ModuleCat.hom_comp]


/-- Pointwise rel-to-abs map at a single neighborhood pair `i = (U, V)`:
$H^p(U, V) \to H^p(U)$, from the kernel inclusion. -/
noncomputable def CechCohomology.ptRelToAbs
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.relFamily X K L p i →+ CechCohomology.absKFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))) p).hom.toAddMonoidHom

/-- Pointwise restriction map at `i = (U, V)`: $H^p(U) \to H^p(V)$, induced by
pullback along the inclusion $V \hookrightarrow U$. -/
noncomputable def CechCohomology.ptRestrict
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.absKFamily X K L p i →+ CechCohomology.absLFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i)) p).hom.toAddMonoidHom







/-- The compatibility square `relCochainComplexMap` followed by the kernel
inclusion equals the kernel inclusion followed by the absolute restriction
cochain map. -/
theorem CechCohomology.relCochainComplexMap_comp_kernel_ι
    {X : Type} [TopologicalSpace X] {K L : Set X}
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    CechCohomology.relCochainComplexMap i j h ≫
      CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion j)) =
    CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1) := by
  simp only [CechCohomology.relCochainComplexMap]
  exact CategoryTheory.Limits.kernel.lift_ι _ _ _


/-- Naturality of `ptRelToAbs`: the pointwise rel-to-abs maps commute with the
bonding maps of `relFamily` and `absKFamily`. -/
theorem CechCohomology.ptRelToAbs_nat
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    (CechCohomology.ptRelToAbs X K L p j).comp (CechCohomology.relBond X K L p i j h) =
    (CechCohomology.absKBond X K L p i j h).comp (CechCohomology.ptRelToAbs X K L p i) := by
  ext x
  show (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j))) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i))) p).hom.toAddMonoidHom x)
  have hsq := CechCohomology.relCochainComplexMap_comp_kernel_ι i j h
  have key : HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) p ≫
    HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion j))) p =
    HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i))) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p := by
    rw [show HomologicalComplex.homologyMap
        (CechCohomology.relCochainComplexMap i j h) p ≫
      HomologicalComplex.homologyMap
        (CategoryTheory.Limits.kernel.ι
          (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
            (CechCohomology.relNbhdInclusion j))) p =
      HomologicalComplex.homologyMap
        (CechCohomology.relCochainComplexMap i j h ≫
          CategoryTheory.Limits.kernel.ι
            (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
              (CechCohomology.relNbhdInclusion j))) p
      from (HomologicalComplex.homologyMap_comp _ _ p).symm, hsq]
    exact HomologicalComplex.homologyMap_comp _ _ p
  have h2 := congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h2
  exact h2
/-- Naturality of `ptRestrict`: pointwise restrictions $H^p(U_i) \to H^p(V_i)$
commute with the bonding maps of `absKFamily` and `absLFamily`. -/
theorem CechCohomology.ptRestrict_nat
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
    (CechCohomology.ptRestrict X K L p j).comp (CechCohomology.absKBond X K L p i j h) =
    (CechCohomology.absLBond X K L p i j h).comp (CechCohomology.ptRestrict X K L p i) := by
  ext x
  show (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion j)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) p).hom.toAddMonoidHom x)
  have hcomm : CechCohomology.opensInclusion h.2 ≫ CechCohomology.relNbhdInclusion i =
      CechCohomology.relNbhdInclusion j ≫ CechCohomology.opensInclusion h.1 :=
    (CechCohomology.opensInclusion_comm i j h).symm
  have hsq : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion j) =
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.2) := by
    rw [← CechCohomology.restrictionCochainMap_comp,
        ← CechCohomology.restrictionCochainMap_comp, hcomm]
  have key : HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j)) p =
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hsq]
  have h2 := congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h2
  exact h2




/-- Definitional identification of `CechCohomRel X K L p` with the direct limit
of `relFamily`. -/
noncomputable def CechCohomology.eqvRel
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.CechCohomRel X K L p ≃+
    AddCommGroup.DirectLimit (CechCohomology.relFamily X K L p)
      (CechCohomology.relBond X K L p) :=
  AddEquiv.refl _








namespace CechCohomology

open Function


