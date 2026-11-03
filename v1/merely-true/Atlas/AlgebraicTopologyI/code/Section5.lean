/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible

import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Homology.AlternatingConst
import Atlas.AlgebraicTopologyI.code.ContractibleHomology

namespace HomotopyTheory

open ContinuousMap unitInterval

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Definition 5.1** (Homotopy). A homotopy from `f₀` to `f₁` is a continuous map
`h : X × I → Y` satisfying `h(x, 0) = f₀(x)` and `h(x, 1) = f₁(x)`. Here it is realized
as the Mathlib datum `ContinuousMap.Homotopy f₀ f₁`. -/
def Homotopy (f₀ f₁ : C(X, Y)) : Type _ :=
  ContinuousMap.Homotopy f₀ f₁

/-- The proposition that `f₀` and `f₁` are homotopic, written `f₀ ≃ f₁` in the textbook
(Definition 5.1). -/
def Homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  ContinuousMap.Homotopic f₀ f₁

end HomotopyTheory

open CategoryTheory

universe u₀

namespace HomotopyCategory

/-- The setoid on `C(X, Y)` for which two continuous maps are identified iff they are
homotopic. Used to form the morphisms of the homotopy category. -/
instance homotopicSetoid (X Y : TopCat.{u₀}) : Setoid C(X, Y) :=
  ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩

/-- **Definition 5.3** (Homotopy category). `HoTop` is the homotopy category of
topological spaces: same objects as `Top`, but with morphisms `Top(X, Y) / ≃` given by
homotopy classes of continuous maps. -/
def HoTop := TopCat.{u₀}

namespace HoTop

/-- An object of `HoTop` may be coerced to its underlying type. -/
instance : CoeSort HoTop.{u₀} (Type u₀) := ⟨fun X => X.carrier⟩

/-- The topology on the underlying type of an object of `HoTop`. -/
instance (X : HoTop.{u₀}) : TopologicalSpace X := X.str

/-- Bundle a topological space `X` as an object of the homotopy category `HoTop`. -/
def of (X : Type u₀) [TopologicalSpace X] : HoTop := TopCat.of X

/-- Categorical data on `HoTop`: morphisms `X ⟶ Y` are homotopy classes of continuous
maps, identities are the classes of `id`, and composition is induced from composition
of representatives (well-defined because homotopy is compatible with composition). -/
instance : CategoryStruct HoTop.{u₀} where
  Hom X Y := Quotient (homotopicSetoid X Y)
  id X := ⟦ContinuousMap.id X⟧
  comp := Quotient.map₂ (fun f g => g.comp f)
    (fun _ _ hf _ _ hg => hg.comp hf)

/-- `HoTop` is a category: composition is associative and the homotopy classes of
identities act as left and right units. -/
instance : Category HoTop.{u₀} where
  id_comp f := by
    induction f using Quotient.ind
    exact congr_arg (⟦·⟧) (ContinuousMap.id_comp _)
  comp_id f := by
    induction f using Quotient.ind
    exact congr_arg (⟦·⟧) (ContinuousMap.comp_id _)
  assoc f g h := by
    induction f using Quotient.ind
    induction g using Quotient.ind
    induction h using Quotient.ind
    exact congr_arg (⟦·⟧) (ContinuousMap.comp_assoc _ _ _)

end HoTop

end HomotopyCategory

namespace HomotopyTheory

/-- **Definition 5.6** (Contractible). A space `X` is contractible if the unique map
`X → *` is a homotopy equivalence; equivalently, `X` is homotopy equivalent to a point.
Realized here as Mathlib's `ContractibleSpace`. -/
abbrev IsContractible (X : Type*) [TopologicalSpace X] : Prop :=
  ContractibleSpace X

/-- **Definition 5.4** (Homotopy equivalence). A homotopy equivalence between `X` and
`Y` is a pair of continuous maps `f : X → Y` and `g : Y → X` with `g ∘ f ≃ idₓ` and
`f ∘ g ≃ id_Y`. Bundled here as Mathlib's `ContinuousMap.HomotopyEquiv`. -/
abbrev HomotopyEquivalence (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  ContinuousMap.HomotopyEquiv X Y

end HomotopyTheory

namespace HomotopyEquivalence

open ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` is a homotopy equivalence (Definition 5.4) iff there
exists `g : Y → X` such that `g ∘ f ≃ idₓ` and `f ∘ g ≃ id_Y`. -/
def IsHomotopyEquiv (f : C(X, Y)) : Prop :=
  ∃ g : C(Y, X), (g.comp f).Homotopic (ContinuousMap.id X) ∧
    (f.comp g).Homotopic (ContinuousMap.id Y)

end HomotopyEquivalence

namespace HomotopyInvariance

open CategoryTheory HomologicalComplex

universe v u

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V]
variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

/-- **Definition 5.9** (Chain homotopy). A chain homotopy between two chain maps
`f₀, f₁ : C → D` is a family of maps `h : Cₙ → Dₙ₊₁` such that `dh + hd = f₁ - f₀`.
Realized here as Mathlib's `Homotopy` of `HomologicalComplex` maps. -/
abbrev ChainHomotopy (f₀ f₁ : C ⟶ D) : Type _ := Homotopy f₀ f₁

variable {f₀ f₁ : C ⟶ D}

/-- **Lemma 5.10**. Chain-homotopic chain maps induce the same map on homology:
if `f₀, f₁ : C → D` are chain homotopic, then `H_n(f₀) = H_n(f₁)`. -/
theorem chainHomotopy_homologyMap_eq (h : ChainHomotopy f₀ f₁) (i : ι)
    [C.HasHomology i] [D.HasHomology i] :
    homologyMap f₀ i = homologyMap f₁ i :=
  Homotopy.homologyMap_eq h i

namespace ChainHomotopy

end ChainHomotopy

/-- A chain homotopy equivalence between chain complexes `C` and `D` induces an
isomorphism on `i`-th homology (a consequence of Lemma 5.10). -/
noncomputable def homotopyEquivHomologyIso
    (e : HomotopyEquiv C D) (i : ι)
    [C.HasHomology i] [D.HasHomology i] :
    C.homology i ≅ D.homology i where
  hom := homologyMap e.hom i
  inv := homologyMap e.inv i
  hom_inv_id := by
    rw [← homologyMap_comp,
      chainHomotopy_homologyMap_eq e.homotopyHomInvId,
      homologyMap_id]
  inv_hom_id := by
    rw [← homologyMap_comp,
      chainHomotopy_homologyMap_eq e.homotopyInvHomId,
      homologyMap_id]

universe w₁ v₁ u₁

/-- **Theorem 5.2** (Homotopy invariance of homology). Homotopic continuous maps
`f, g : X → Y` induce the same map on singular homology. Combined with Proposition 5.11
(homotopic maps yield chain-homotopic chain maps) and Lemma 5.10 (chain-homotopic maps
induce the same homology map). -/
theorem homotopy_invariance_of_homology
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Limits.HasCoproducts.{w₁} C]
    [CategoryWithHomology C]
    {X Y : TopCat.{w₁}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map f =
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map g := by
  simp only [AlgebraicTopology.singularHomologyFunctor, Functor.comp_obj,
    Functor.whiskeringRight_obj_obj, Functor.comp_map]
  rw [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyFunctor_map]
  exact H.congr_homologyMap_singularChainComplexFunctor R n

end HomotopyInvariance

namespace HomotopyTheory

open CategoryTheory AlgebraicTopology HomologicalComplex Limits

/-- **Corollary 5.5**. A homotopy equivalence of topological spaces `X ≃ Y` induces an
isomorphism on `n`-th singular homology (with coefficients in `R`). -/
noncomputable def homotopyEquivHomologyIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y)
    {C : Type*} [Category C] [HasCoproducts.{0} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of Y) := by
  let F := ((singularHomologyFunctor C n).obj R)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨F.map f, F.map g, ?_, ?_⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨H⟩ := e.left_inv
    have hfg : f ≫ g = TopCat.ofHom (e.invFun.comp e.toFun) := by ext; rfl
    have hid : 𝟙 (TopCat.of X) = TopCat.ofHom (ContinuousMap.id X) := by ext; rfl
    rw [hfg, hid]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨H⟩ := e.right_inv
    have hgf : g ≫ f = TopCat.ofHom (e.toFun.comp e.invFun) := by ext; rfl
    have hid : 𝟙 (TopCat.of Y) = TopCat.ofHom (ContinuousMap.id Y) := by ext; rfl
    rw [hgf, hid]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R n

end HomotopyTheory

namespace DeformationRetract

open unitInterval ContinuousMap

universe u

variable {X : Type u} [TopologicalSpace X]

/-- **Definition 5.8** (Deformation retract). An inclusion `A ↪ X` is a deformation
retract if there is a continuous map `h : X × I → X` such that `h(x, 0) = x`,
`h(x, 1) ∈ A` for all `x`, and `h(a, t) = a` for all `a ∈ A` and `t ∈ I`. This is
packaged as a retract `X → X` landing in `A` together with a relative homotopy from the
identity to the retract, fixing `A` pointwise. -/
structure IsDeformationRetract (A : Set X) where
  retract : C(X, X)
  retract_mem : ∀ x, retract x ∈ A
  homotopy : HomotopyRel (ContinuousMap.id X) retract A

end DeformationRetract

namespace HomotopyTheory

/-- **Definition 5.12** (Star-shaped). A subset `s ⊆ E` is star-shaped with respect to
`b ∈ s` if for every `x ∈ s` the segment `{tb + (1-t)x : t ∈ [0,1]}` lies in `s`.
Realized as Mathlib's `StarConvex ℝ b s`. -/
abbrev IsStarShaped {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (b : E) (s : Set E) : Prop :=
  StarConvex ℝ b s

end HomotopyTheory

namespace HomotopyTheory

open CategoryTheory AlgebraicTopology HomologicalComplex Limits

/-- The continuous self-map of `X` constant at the point `b ∈ X`. -/
def topConstAt {X : TopCat.{0}} (b : X) : X ⟶ X :=
  ⟨fun _ => b, continuous_const⟩

/-- The unique continuous projection `X → *` to the one-point space. -/
def topProjToPoint (X : TopCat.{0}) : X ⟶ TopCat.of PUnit :=
  ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The continuous inclusion `* → X` of the one-point space picking out `b ∈ X`. -/
def topInclFromPoint {X : TopCat.{0}} (b : X) : TopCat.of PUnit ⟶ X :=
  ⟨fun _ => b, continuous_const⟩

/-- **Corollary 5.7** (positive-degree part). If `X` is contractible then `H_n(X) = 0`
for all `n ≠ 0`. Proved by factoring the identity through a point and using homotopy
invariance plus the vanishing of higher homology of a point. -/
theorem isZero_singularHomology_of_contractibleSpace
    {C : Type*} [Category C] [HasCoproducts.{0} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) (hn : n ≠ 0) (X : TopCat.{0}) [ContractibleSpace X] :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  obtain ⟨b, ⟨H⟩⟩ := id_nullhomotopic X
  rw [IsZero.iff_id_eq_zero]
  rw [← CategoryTheory.Functor.map_id ((singularHomologyFunctor C n).obj R) X]
  have htpy : TopCat.Homotopy (𝟙 X) (topConstAt b) := H
  show homologyMap (((singularChainComplexFunctor C).obj R).map (𝟙 X)) n = 0
  rw [htpy.congr_homologyMap_singularChainComplexFunctor R n]
  rw [show topConstAt b = topProjToPoint X ≫ topInclFromPoint b from by ext; rfl]
  rw [CategoryTheory.Functor.map_comp, homologyMap_comp]
  have hZ : IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R (TopCat.of PUnit) hn
  have h1 : homologyMap (((singularChainComplexFunctor C).obj R).map (topInclFromPoint b)) n = 0 :=
    hZ.eq_zero_of_src _
  simp only [h1, Limits.comp_zero]

/-- A homotopy equivalence of topological spaces `X ≃ Y` lifts to a chain homotopy
equivalence of singular chain complexes. This is the chain-level form of Corollary 5.5,
combining Theorem 5.2 / Proposition 5.11 with the definition of homotopy equivalence. -/
noncomputable def singularChainHomotopyEquivOfHomotopyEquiv
    {C : Type*} [Category C] [HasCoproducts.{0} C] [Preadditive C]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (R : C) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of X))
      (((singularChainComplexFunctor C).obj R).obj (TopCat.of Y)) := by
  let F := ((singularChainComplexFunctor C).obj R)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have H_left : TopCat.Homotopy (f ≫ g) (CategoryStruct.id (TopCat.of X)) :=
    Classical.choice e.left_inv
  have H_right : TopCat.Homotopy (g ≫ f) (CategoryStruct.id (TopCat.of Y)) :=
    Classical.choice e.right_inv
  exact
    { hom := F.map f
      inv := F.map g
      homotopyHomInvId :=
        (_root_.Homotopy.ofEq (F.map_comp f g).symm).trans
          ((H_left.singularChainComplexFunctorObjMap R).trans
            (_root_.Homotopy.ofEq (F.map_id (TopCat.of X))))
      homotopyInvHomId :=
        (_root_.Homotopy.ofEq (F.map_comp g f).symm).trans
          ((H_right.singularChainComplexFunctorObjMap R).trans
            (_root_.Homotopy.ofEq (F.map_id (TopCat.of Y)))) }

/-- **Proposition 5.13**. For a nonempty star-shaped subset `s` of a real topological
vector space, the singular chain complex `S_*(s; ℤ)` is chain-homotopy equivalent to the
chain complex `ℤ` concentrated in degree zero. Combines contractibility of `s` with the
chain-level homotopy invariance and identification of `S_*(*)` with `ℤ`. -/
noncomputable def starShaped_singularHomology
    {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    {s : Set E} {b : E} (hstar : StarConvex ℝ b s) (hne : s.Nonempty) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of ↥s))
      ((ChainComplex.single₀ AddCommGrpCat).obj (AddCommGrpCat.of ℤ)) := by
  letI : ContractibleSpace ↥s := hstar.contractibleSpace hne

  let e := Classical.choice (ContractibleSpace.hequiv_unit ↥s)
  let step1 := singularChainHomotopyEquivOfHomotopyEquiv e (AddCommGrpCat.of ℤ)

  let iso1 := singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    AddCommGrpCat (AddCommGrpCat.of ℤ) (TopCat.of Unit)

  let step3 := ChainComplex.alternatingConstHomotopyEquiv
    (∐ fun _ : (TopCat.of Unit) ↦ (AddCommGrpCat.of ℤ))

  let iso2 := (ChainComplex.single₀ AddCommGrpCat).mapIso
    (coproductUniqueIso (fun _ : (TopCat.of Unit) ↦ (AddCommGrpCat.of ℤ)))
  exact step1.trans ((HomotopyEquiv.ofIso iso1).trans (step3.trans (HomotopyEquiv.ofIso iso2)))

end HomotopyTheory

namespace HomotopyInvariance

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe v' u' w'

/-- **Proposition 5.11**. A homotopy `H : f₀ ≃ f₁` between continuous maps `X → Y`
determines a natural chain homotopy between the induced chain maps
`f₀*, f₁* : S_*(X) → S_*(Y)`. -/
noncomputable def singularChainHomotopy_of_homotopy
    {C : Type u'} [Category.{v'} C] [Preadditive C] [HasCoproducts.{w'} C]
    {X Y : TopCat.{w'}} {f₀ f₁ : X ⟶ Y}
    (H : TopCat.Homotopy f₀ f₁) (R : C) :
    Homotopy (((singularChainComplexFunctor C).obj R).map f₀)
      (((singularChainComplexFunctor C).obj R).map f₁) :=
  H.singularChainComplexFunctorObjMap R

/-- The "nonempty" form of Proposition 5.11: there exists a chain homotopy between the
induced chain maps `f₀*, f₁* : S_*(X) → S_*(Y)` whenever `f₀` and `f₁` are homotopic. -/
theorem nonempty_singularChainHomotopy_of_homotopy
    {C : Type u'} [Category.{v'} C] [Preadditive C] [HasCoproducts.{w'} C]
    {X Y : TopCat.{w'}} {f₀ f₁ : X ⟶ Y}
    (H : TopCat.Homotopy f₀ f₁) (R : C) :
    Nonempty (Homotopy (((singularChainComplexFunctor C).obj R).map f₀)
      (((singularChainComplexFunctor C).obj R).map f₁)) :=
  ⟨singularChainHomotopy_of_homotopy H R⟩

end HomotopyInvariance
