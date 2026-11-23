/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.Topology.Separation.Hausdorff
import Atlas.AlgebraicTopologyI.code.Section34

open CategoryTheory

noncomputable section

namespace PoincareDuality

variable (R : Type) [CommRing R]













/-- An $n$-manifold $M$ is `IsROriented` if it admits an $R$-orientation, i.e. a coherent
choice of local-homology generators. This is the prerequisite for talking about a
fundamental class and hence Poincaré duality with coefficients in $R$. -/
class IsROriented (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  isROrientable : OrientationHomology.IsROrientable n M R


















































section CechCohomologyDecreasingCompact
open Limits TopologicalSpace

variable (R : Type) [CommRing R]






end CechCohomologyDecreasingCompact













/-- Five-lemma for `ModuleCat R`: given a ladder of two horizontal 4-term exact sequences
with `α` epi, `β`, `δ` iso, `ε` mono, the middle map `γ` is an iso. Specialisation of the
abelian-category five lemma. -/
theorem fiveLemma_moduleCat_isIso
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : ModuleCat.{0} R}
    (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (f₄ : A₄ ⟶ A₅)
    (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃) (g₃ : B₃ ⟶ B₄) (g₄ : B₄ ⟶ B₅)
    (α : A₁ ⟶ B₁) (β : A₂ ⟶ B₂) (γ : A₃ ⟶ B₃) (δ : A₄ ⟶ B₄) (ε : A₅ ⟶ B₅)
    (sq₁ : f₁ ≫ β = α ≫ g₁) (sq₂ : f₂ ≫ γ = β ≫ g₂)
    (sq₃ : f₃ ≫ δ = γ ≫ g₃) (sq₄ : f₄ ≫ ε = δ ≫ g₄)
    (hexTopExact : (ComposableArrows.mk₄ f₁ f₂ f₃ f₄).Exact)
    (hexBotExact : (ComposableArrows.mk₄ g₁ g₂ g₃ g₄).Exact)
    (hα : Epi α) (hβ : IsIso β) (hδ : IsIso δ) (hε : Mono ε) :
    IsIso γ :=
  Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hexTopExact hexBotExact
    (ComposableArrows.homMk₄ α β γ δ ε sq₁ sq₂ sq₃ sq₄) hα hβ hδ hε











































































end PoincareDuality

end

open CategoryTheory TopologicalSpace Limits

namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

/-- An open neighbourhood of a set $K$: an open subset $U \subseteq \alpha$ together with
the inclusion $K \subseteq U$. The indexing category for the Čech-cohomology colimit. -/
structure OpenNhdsOfSet (K : Set α) where
  toOpens : Opens α
  subset_carrier : K ⊆ toOpens.carrier

namespace OpenNhdsOfSet
variable {K : Set α}

/-- Reverse-inclusion preorder: $U \le V$ iff $V \subseteq U$, so that the system of
neighbourhoods is directed downward. -/
instance : Preorder (OpenNhdsOfSet K) where
  le U V := V.toOpens ≤ U.toOpens
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := le_trans hbc hab

/-- $\alpha$ itself is always an open neighbourhood of $K$, so the type is nonempty. -/
instance : Nonempty (OpenNhdsOfSet K) := ⟨⟨⊤, Set.subset_univ K⟩⟩

/-- The preorder on open neighbourhoods is directed: any two neighbourhoods admit a common
refinement (their intersection). -/
instance : IsDirected (OpenNhdsOfSet K) (· ≤ ·) where
  directed U V :=
    ⟨⟨U.toOpens ⊓ V.toOpens,
      fun _ hx => ⟨U.subset_carrier hx, V.subset_carrier hx⟩⟩,
     (inf_le_left : U.toOpens ⊓ V.toOpens ≤ U.toOpens),
     (inf_le_right : U.toOpens ⊓ V.toOpens ≤ V.toOpens)⟩

/-- Forgetful functor `OpenNhdsOfSet K ⥤ (Opens α)ᵒᵖ` sending $U$ to its underlying open
set, contravariantly: the source for Čech-cohomology colimits over neighbourhoods of $K$. -/
def inclusionFunctorOp : OpenNhdsOfSet K ⥤ (Opens α)ᵒᵖ where
  obj U := Opposite.op U.toOpens
  map {_U _V} f := (homOfLE (leOfHom f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

end OpenNhdsOfSet

/-- An "indexed" open neighbourhood: a pair $(k, U)$ where $U$ is an open neighbourhood of
$A_k$. Used to interpolate between the colimits along the family $\{A_k\}$ and the colimit
along their intersection, in the proof of Lemma 37.2. -/
structure CombinedOpenNhds (A : ℕ → Set α) where
  idx : ℕ
  nhd : OpenNhdsOfSet (A idx)

namespace CombinedOpenNhds
variable {A : ℕ → Set α}

/-- Reverse-inclusion preorder on `CombinedOpenNhds`: $(k, U) \le (k', V)$ iff
$V \subseteq U$, ignoring the indices. -/
instance : Preorder (CombinedOpenNhds A) where
  le p q := q.nhd.toOpens ≤ p.nhd.toOpens
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := le_trans hbc hab

/-- The pair $(0, \top)$ is always a combined open neighbourhood, hence the type is
nonempty. -/
instance : Nonempty (CombinedOpenNhds A) := ⟨⟨0, ⟨⊤, Set.subset_univ _⟩⟩⟩

/-- For an antitone (decreasing) family of subsets $A_k$, the preorder on combined
neighbourhoods is directed: take a common refinement index and intersect the neighbourhoods. -/
@[reducible]
def isDirectedOfAntitone (hA : Antitone A) :
    IsDirected (CombinedOpenNhds A) (· ≤ ·) where
  directed p q :=
    ⟨⟨max p.idx q.idx,
      ⟨p.nhd.toOpens ⊓ q.nhd.toOpens,
       fun _ hx => ⟨p.nhd.subset_carrier (hA (le_max_left _ _) hx),
                     q.nhd.subset_carrier (hA (le_max_right _ _) hx)⟩⟩⟩,
     (inf_le_left : p.nhd.toOpens ⊓ q.nhd.toOpens ≤ p.nhd.toOpens),
     (inf_le_right : p.nhd.toOpens ⊓ q.nhd.toOpens ≤ q.nhd.toOpens)⟩

/-- Forgetful map from a combined open neighbourhood $(k, U)$ to an open neighbourhood of
the intersection $\bigcap_k A_k$: since $\bigcap_k A_k \subseteq A_k \subseteq U$. -/
def toNhdsInter (_hA : Antitone A) :
    CombinedOpenNhds A → OpenNhdsOfSet (⋂ k, A k) :=
  fun p => ⟨p.nhd.toOpens, Set.iInter_subset_of_subset p.idx p.nhd.subset_carrier⟩

/-- The forgetful map `toNhdsInter` is monotone with respect to the reverse-inclusion
preorders. -/
theorem toNhdsInter_monotone (hA : Antitone A) :
    Monotone (toNhdsInter hA) := fun _ _ h => h

/-- Cofinality of `toNhdsInter`: in a Hausdorff space, every open neighbourhood of the
intersection $\bigcap_k A_k$ of an antitone family of compacts $A_k$ contains some $A_k$,
giving a refinement coming from a combined open neighbourhood. -/
theorem toNhdsInter_cofinal [T2Space α]
    (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k)) :
    ∀ (V : OpenNhdsOfSet (⋂ k, A k)), ∃ (p : CombinedOpenNhds A),
      V ≤ toNhdsInter hA p := by
  intro V
  have hdir : Directed (· ⊇ ·) A :=
    fun i j => ⟨max i j, hA (le_max_left _ _), hA (le_max_right _ _)⟩
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hcpt
    (fun x hx => V.toOpens.isOpen.mem_nhds (V.subset_carrier hx))
  exact ⟨⟨k, ⟨V.toOpens, hk⟩⟩, le_refl _⟩

/-- Finality of `toNhdsInter` as a functor: cofinality plus monotonicity in a Hausdorff
space ensure that colimits along the combined index agree with colimits along open
neighbourhoods of the intersection. -/
theorem toNhdsInter_functor_final [T2Space α]
    (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k)) :
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    (toNhdsInter_monotone hA).functor.Final := by
  letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
  rw [Monotone.final_functor_iff]
  exact toNhdsInter_cofinal hA hcpt

/-- **Lemma 37.2 (categorical core).** In a Hausdorff space, for any presheaf $F$ on the
opens of $\alpha$ and an antitone family of compacts $A_k$ with intersection $A$, the colimit
of $F$ over open neighbourhoods of $A$ is canonically isomorphic to the colimit of $F$
along the combined index built from the $A_k$. -/
noncomputable def cechCohomology_colimit_iso [T2Space α]
    {C : Type*} [Category C]
    (A : ℕ → Set α) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (F : (Opens α)ᵒᵖ ⥤ C)
    [HasColimit (OpenNhdsOfSet.inclusionFunctorOp ⋙ F : OpenNhdsOfSet (⋂ k, A k) ⥤ C)] :
    let G := (OpenNhdsOfSet.inclusionFunctorOp ⋙ F : OpenNhdsOfSet (⋂ k, A k) ⥤ C)
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    letI : (toNhdsInter_monotone hA).functor.Final :=
      toNhdsInter_functor_final hA hcpt
    colimit ((toNhdsInter_monotone hA).functor ⋙ G) ≅ colimit G := by
  letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
  haveI : (toNhdsInter_monotone hA).functor.Final :=
    toNhdsInter_functor_final hA hcpt
  exact Functor.Final.colimitIso _ _

end CombinedOpenNhds

end OpenNhdsColimit

section CechCohomologySpecialization

variable {α : Type} [TopologicalSpace α]

namespace CombinedOpenNhds

variable {A : ℕ → Set α}

/-- `cechCohomology_colimit_iso` specialised to `C = ModuleCat.{0} R`, the variant used to
prove Lemma 37.2 in the Čech-cohomology setting. -/
noncomputable def cechCohomology_colimit_iso_cech [T2Space α]
    (R : Type) [CommRing R]
    (A : ℕ → Set α) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (F : (Opens α)ᵒᵖ ⥤ ModuleCat.{0} R)
    [HasColimit (OpenNhdsOfSet.inclusionFunctorOp ⋙ F :
      OpenNhdsOfSet (⋂ k, A k) ⥤ ModuleCat.{0} R)] :
    let G := (OpenNhdsOfSet.inclusionFunctorOp ⋙ F :
      OpenNhdsOfSet (⋂ k, A k) ⥤ ModuleCat.{0} R)
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    letI : (toNhdsInter_monotone hA).functor.Final :=
      toNhdsInter_functor_final hA hcpt
    colimit ((toNhdsInter_monotone hA).functor ⋙ G) ≅ colimit G :=
  cechCohomology_colimit_iso A hA hcpt F

end CombinedOpenNhds

end CechCohomologySpecialization

end PoincareDuality

namespace CapProduct

open PoincareDuality

variable (R : Type) [CommRing R]


end CapProduct

namespace PoincareDualityCompact

open CategoryTheory PoincareDuality



/-- An `IsROriented` instance in the outer namespace promotes to one in
`PoincareDuality.IsROriented`, which is the form used by `poincareDualityMap`. -/
instance isROriented_toPoincareDuality (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [h : IsROriented R n M] : PoincareDuality.IsROriented R n M :=
  ⟨h.isROrientable⟩





end PoincareDualityCompact

namespace PoincareDualityZMod2

open CategoryTheory AlgebraicTopology LinearMap SingularCohomology
open AlgebraicTopologyI PoincareDuality





end PoincareDualityZMod2
