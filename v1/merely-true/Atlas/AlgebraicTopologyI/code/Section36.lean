/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker

open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory

noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The singular chain complex `S_*(Y; R)` of a topological space `Y` with
coefficients in the commutative ring `R`, viewed as a chain complex of
`R`-modules indexed by `ℕ`. -/
abbrev singChainCx (Y : TopCat.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj Y

/-- The continuous inclusion `A ↪ X` of a subset `A ⊆ X` as a morphism in `TopCat`,
given by the subtype valuation map. -/
def subtypeIncl (X : TopCat.{0}) (A : Set X) : TopCat.of A ⟶ X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The chain map `S_*(A; R) → S_*(X; R)` induced by the inclusion of a
subspace `A ⊆ X` into `X`. -/
def inclChainMap (X : TopCat.{0}) (A : Set X) :
    singChainCx R (TopCat.of A) ⟶ singChainCx R X :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
    (subtypeIncl X A)

/-- The relative singular chain complex `S_*(X, A; R)`, defined as the cokernel
of the inclusion-induced chain map `S_*(A; R) → S_*(X; R)`. -/
def relSingChainCx (X : TopCat.{0}) (A : Set X) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel (inclChainMap R X A)

/-- The relative singular homology `H_n(X, A; R)`, defined as the `n`-th homology
of the relative singular chain complex. -/
def relSingularHomology (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.{0} R :=
  (relSingChainCx R X A).homology n

/-- The absolute singular homology `H_n(X; R)`, the `n`-th homology of the
singular chain complex. -/
def absSingularHomology (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  (singChainCx R X).homology n

/-- The Čech cohomology `Ȟ^p(K; R)` of a subset `K ⊆ X`, obtained as the direct
limit of the singular cohomologies of open neighbourhoods of `K`. -/
def cechCohomology
    (X : TopCat.{0}) (K : Set X) (p : ℕ) : ModuleCat.{0} R :=
  CechCohomology.cechCohomology R K p

/-- A pair `(U, V)` of open neighbourhoods with `K ⊆ U`, `L ⊆ V` and `V ⊆ U`,
indexing the directed system used to define relative Čech cohomology
`Ȟ^p(K, L; R)`. -/
structure OpenNbhdPair {X : Type} [TopologicalSpace X] (K L : Set X) where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  hK : K ⊆ ↑U
  hL : L ⊆ ↑V
  hVU : V ≤ U

/-- The reverse-inclusion preorder on `OpenNbhdPair K L`: a pair `p` is smaller
than `q` when `q.U ⊆ p.U` and `q.V ⊆ p.V`. This makes the family of pairs into
a directed system as the neighbourhoods shrink down to `(K, L)`. -/
instance openNbhdPair_preorder {X : Type} [TopologicalSpace X] {K L : Set X} :
    Preorder (OpenNbhdPair K L) where
  le p q := q.U ≤ p.U ∧ q.V ≤ p.V
  le_refl p := ⟨le_refl _, le_refl _⟩
  le_trans p q r hpq hqr := ⟨le_trans hqr.1 hpq.1, le_trans hqr.2 hpq.2⟩

/-- The inclusion `V ↪ U` of opens `V ≤ U` as a morphism in `TopCat`. -/
def opensInclusion {X : TopCat.{0}} (U V : TopologicalSpace.Opens X) (h : V ≤ U) :
    TopCat.of ↑V.1 ⟶ TopCat.of ↑U.1 :=
  ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- The relative singular cohomology `H^p(U, V; R)` of an `OpenNbhdPair (U, V)`,
constructed as the `p`-th cohomology of the kernel of the cochain restriction
`S^*(U; R) → S^*(V; R)`. -/
def relCohomOfPair {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p : ℕ) : ModuleCat.{0} R := by
  classical
  let G := ModuleCat.of R R
  let restrictMap :=
    (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
      (((((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj G).map
          (opensInclusion pair.U pair.V pair.hVU))).op)
  exact (kernel restrictMap).homology p

/-- The underlying type of `relCohomOfPair`, exposed as a `Type` to serve as
the type-theoretic family for the direct-limit construction of relative
Čech cohomology. -/
def relCechFamily {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) : Type :=
  (relCohomOfPair R pair p : Type _)

/-- Transport the additive commutative group structure from `relCohomOfPair`
to its underlying type `relCechFamily`. -/
instance relCechFamily_addCommGroup {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    AddCommGroup (relCechFamily R p pair) :=
  (relCohomOfPair R pair p).isAddCommGroup

/-- Transport the `R`-module structure from `relCohomOfPair` to its underlying
type `relCechFamily`. -/
instance relCechFamily_module {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    Module R (relCechFamily R p pair) :=
  (relCohomOfPair R pair p).isModule

/-- The transition map `relCohomOfPair pair₁ p → relCohomOfPair pair₂ p` in the
directed system of open neighbourhood pairs, induced by restriction of cochains
along the inclusions `pair₂.U ⊆ pair₁.U` and `pair₂.V ⊆ pair₁.V`. -/
def relCechTransition {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relCechFamily R p pair₁ →ₗ[R] relCechFamily R p pair₂ := by
  classical

  let G := ModuleCat.of R R
  let F := (singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj G
  let L' := ((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)
  let U := HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)


  let restrictMap₁ := U.map ((L'.map (F.map (opensInclusion pair₁.U pair₁.V pair₁.hVU))).op)
  let restrictMap₂ := U.map ((L'.map (F.map (opensInclusion pair₂.U pair₂.V pair₂.hVU))).op)

  let pU := U.map ((L'.map (F.map (opensInclusion pair₁.U pair₂.U h.1))).op)
  let qV := U.map ((L'.map (F.map (opensInclusion pair₁.V pair₂.V h.2))).op)

  have comm : restrictMap₁ ≫ qV = pU ≫ restrictMap₂ := by
    simp only [restrictMap₁, restrictMap₂, pU, qV]
    simp only [← U.map_comp, ← op_comp, ← L'.map_comp, ← F.map_comp]


    have : opensInclusion pair₁.V pair₂.V h.2 ≫ opensInclusion pair₁.U pair₁.V pair₁.hVU =
        opensInclusion pair₂.U pair₂.V pair₂.hVU ≫ opensInclusion pair₁.U pair₂.U h.1 := by
      ext ⟨x, hx⟩; rfl
    rw [this]

  exact (HomologicalComplex.homologyMap
    (kernel.map restrictMap₁ restrictMap₂ pU qV comm) p).hom


/-- The relative Čech cohomology `Ȟ^p(K, L; R)`, defined as the direct limit
of the relative singular cohomologies `H^p(U, V; R)` over the cofinal system
of `OpenNbhdPair`s shrinking down to `(K, L)`. -/
def cechCohomologyRel
    (X : TopCat.{0}) (K L : Set X) (p : ℕ) : ModuleCat.{0} R := by
  classical
  exact ModuleCat.of R (Module.DirectLimit
    (relCechFamily (R := R) (X := X) (K := K) (L := L) p)
    (fun pair₁ pair₂ h => relCechTransition R p pair₁ pair₂ h))

/-- The subset `(X - K) ∩ (X - L) ⊆ X - L`, encoded as the preimage of `Kᶜ`
inside the subspace `Lᶜ`. -/
def complementInComplement (X : TopCat.{0}) (K L : Set X) :
    Set (TopCat.of (Lᶜ : Set X)) :=
  Subtype.val ⁻¹' (Kᶜ : Set X)

/-- Extract the open neighbourhood of `K` from an `OpenNbhdPair K L`. -/
def pairToNbhdK {X : Type} [TopologicalSpace X] {K L : Set X}
    (pair : OpenNbhdPair K L) : CechCohomology.OpenNeighborhoods K :=
  ⟨pair.U, pair.hK⟩

/-- Extract the open neighbourhood of `L` from an `OpenNbhdPair K L`. -/
def pairToNbhdL {X : Type} [TopologicalSpace X] {K L : Set X}
    (pair : OpenNbhdPair K L) : CechCohomology.OpenNeighborhoods L :=
  ⟨pair.V, pair.hL⟩


/-- For a single neighbourhood pair, the map from the relative cohomology
`H^p(U, V; R)` to absolute Čech cohomology `Ȟ^p(K; R)`, obtained by forgetting
the relativity (via the kernel inclusion) and then injecting into the
direct limit. -/
def nbhdRestrictToLimit {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) :
    relCechFamily R p pair →ₗ[R]
      (CechCohomology.cechCohomology R K p : Type _) := by
  classical
  let G := ModuleCat.of R R

  let rMap := SingularCohomology.restrictionCochainMap R G
    (opensInclusion pair.U pair.V pair.hVU)


  let forgetful : relCechFamily R p pair →ₗ[R]
      CechCohomology.cechFamily R K p (pairToNbhdK pair) :=
    (HomologicalComplex.homologyMap (kernel.ι rMap) p).hom

  let intoLimit := Module.DirectLimit.of R _
    (CechCohomology.cechFamily R K p)
    (fun U V h => CechCohomology.cechTransition R K p U V h)
    (pairToNbhdK pair)
  exact intoLimit.comp forgetful





/-- For an open neighbourhood `U` of `K`, the map from the cohomology of `U` to
the Čech cohomology of `L`, defined to be the natural injection into the direct
limit when `L ⊆ K` (so `U` is also a neighbourhood of `L`), and zero otherwise. -/
def nbhdToSubspaceViaLimit {X : TopCat.{0}} {K : Set X} (L : Set X)
    (p : ℕ) (U : CechCohomology.OpenNeighborhoods K) :
    CechCohomology.cechFamily R K p U →ₗ[R]
      (CechCohomology.cechCohomology R L p : Type _) := by
  classical
  by_cases hLK : L ⊆ K
  · have hLU : L ⊆ ↑U.1 := fun x hx => U.2 (hLK hx)
    exact Module.DirectLimit.of R _
      (CechCohomology.cechFamily R L p)
      (fun V₁ V₂ h => CechCohomology.cechTransition R L p V₁ V₂ h)
      ⟨U.1, hLU⟩
  · exact 0










/-- The inclusion `A ↪ B` of one subset into another (with `A ⊆ B`), as a
morphism in `TopCat`. -/
def subsetInclusion (X : TopCat.{0}) (A B : Set X) (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- The inclusion `A ↪ X` factors through `A ↪ B ↪ X` whenever `A ⊆ B`. -/
lemma subtypeIncl_factor (X : TopCat.{0}) (A B : Set X) (h : A ⊆ B) :
    subtypeIncl X A = subsetInclusion X A B h ≫ subtypeIncl X B := by
  apply ConcreteCategory.hom_ext
  intro ⟨x, hx⟩
  rfl

/-- The natural map `(X - L) ∩ (X - K) ↪ X - K` viewed as a morphism in
`TopCat`. -/
def complToComplement (X : TopCat.{0}) (K L : Set X) :
    TopCat.of (complementInComplement X K L) ⟶ TopCat.of (Kᶜ : Set X) :=
  ⟨fun ⟨⟨x, _⟩, hxK⟩ => ⟨x, hxK⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the square of inclusions
`(Lᶜ ∩ Kᶜ) ↪ Lᶜ ↪ X` and `(Lᶜ ∩ Kᶜ) ↪ Kᶜ ↪ X` in `TopCat`. -/
lemma tripleIncl_comm_topcat (X : TopCat.{0}) (K L : Set X) :
    subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫
      subtypeIncl X Lᶜ =
    complToComplement X K L ≫ subtypeIncl X Kᶜ := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- The chain-level version of `tripleIncl_comm_topcat`: the corresponding
square of chain maps between singular chain complexes commutes. -/
lemma tripleIncl_comm_chain (X : TopCat.{0}) (K L : Set X) :
    inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (subtypeIncl X Lᶜ) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (complToComplement X K L) ≫
      inclChainMap R X Kᶜ := by
  simp only [inclChainMap, ← Functor.map_comp, tripleIncl_comm_topcat X K L]

/-- The induced chain map on relative singular chain complexes,
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(X, Kᶜ; R)`, coming from the inclusions of the
triple `(Lᶜ ∩ Kᶜ) ⊆ Lᶜ ⊆ X` and `(Lᶜ ∩ Kᶜ) ⊆ Kᶜ ⊆ X`. -/
def tripleInclChainMap (X : TopCat.{0}) (K L : Set X) :
    relSingChainCx R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) ⟶
    relSingChainCx R X Kᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (complToComplement X K L))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (subtypeIncl X Lᶜ))
    (tripleIncl_comm_chain R X K L)

/-- The induced map on relative homology,
`H_q(Lᶜ, Lᶜ ∩ Kᶜ; R) → H_q(X, Kᶜ; R)`, coming from the inclusion of pairs
`(Lᶜ, Lᶜ ∩ Kᶜ) → (X, Kᶜ)`. -/
def homolTripleInclusion
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R (TopCat.of (Lᶜ : Set X))
      (complementInComplement X K L) q ⟶
      relSingularHomology R X Kᶜ q :=
  HomologicalComplex.homologyMap (tripleInclChainMap R X K L) q

/-- Compatibility square needed to define the restriction chain map
`S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)` when `Kᶜ ⊆ Lᶜ`. -/
lemma restriction_comm_chain (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    inclChainMap R X Kᶜ ≫ 𝟙 _ =
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (subsetInclusion X Kᶜ Lᶜ h) ≫ inclChainMap R X Lᶜ := by
  simp only [Category.comp_id, inclChainMap, ← Functor.map_comp,
    subtypeIncl_factor X Kᶜ Lᶜ h]

/-- The chain map between relative singular chain complexes
`S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)`, induced by enlarging the relative subspace
from `Kᶜ` to `Lᶜ` (assuming `Kᶜ ⊆ Lᶜ`, i.e. `L ⊆ K`). -/
def restrictionChainMap (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    relSingChainCx R X Kᶜ ⟶ relSingChainCx R X Lᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (subsetInclusion X Kᶜ Lᶜ h))
    (𝟙 _)
    (restriction_comm_chain R X K L h)

/-- The restriction map `H_q(X, Kᶜ; R) → H_q(X, Lᶜ; R)` induced by enlarging
the relative subspace from `Kᶜ` to `Lᶜ` (defined to be zero if `Kᶜ ⊄ Lᶜ`). -/
def homolRestriction
    (X : TopCat.{0}) (K L : Set X) (q : ℕ) :
    relSingularHomology R X Kᶜ q ⟶ relSingularHomology R X Lᶜ q := by
  classical
  exact if h : (Kᶜ : Set X) ⊆ Lᶜ
    then HomologicalComplex.homologyMap (restrictionChainMap R X K L h) q
    else 0

/-- The composition `tripleInclChainMap ≫ restrictionChainMap` vanishes,
expressing the chain-level exactness needed to obtain the short exact
sequence of relative chain complexes for the triple `(X, Lᶜ, Kᶜ)`. -/
lemma tripleInclChainMap_comp_restrictionChainMap_eq_zero
    (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    tripleInclChainMap R X K L ≫ restrictionChainMap R X K L h = 0 := by
  simp only [tripleInclChainMap, restrictionChainMap, relSingChainCx]

  apply coequalizer.hom_ext
  simp only [cokernel.π_desc_assoc, comp_zero, Category.assoc]


  rw [cokernel.π_desc]
  simp only [Category.id_comp]


  show inclChainMap R X Lᶜ ≫ cokernel.π (inclChainMap R X Lᶜ) = 0
  exact cokernel.condition _

/-- The short complex of relative singular chain complexes for the triple
`(X, Lᶜ, Kᶜ)`, namely
`S_*(Lᶜ, Lᶜ ∩ Kᶜ; R) → S_*(X, Kᶜ; R) → S_*(X, Lᶜ; R)`. -/
def tripleShortComplex (X : TopCat.{0}) (K L : Set X) (h : (Kᶜ : Set X) ⊆ Lᶜ) :
    ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk
    (tripleInclChainMap R X K L)
    (restrictionChainMap R X K L h)
    (tripleInclChainMap_comp_restrictionChainMap_eq_zero R X K L h)


















/-- The inclusion `U ↪ X` of an open subspace into `X`, in `TopCat`. -/
def excisionOpenIncl (X : TopCat.{0}) (U : TopologicalSpace.Opens X) :
    TopCat.of ↑U.1 ⟶ X :=
  subtypeIncl X U.1

/-- The inclusion `U ∩ Kᶜ ↪ Kᶜ` of subspaces of `X`, used to set up the
excision map for the pair `(X, Kᶜ)` relative to an open neighbourhood of `K`. -/
def excisionSubspaceIncl (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑U.1)) ⟶ TopCat.of (Kᶜ : Set X) :=
  ⟨fun ⟨⟨x, _⟩, hxK⟩ => ⟨x, hxK⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the chain-level square used to build the excision map
of pairs `(U, U ∩ Kᶜ) → (X, Kᶜ)`. -/
lemma excisionPairIncl_comm (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    inclChainMap R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (excisionOpenIncl X U) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (excisionSubspaceIncl X K U) ≫
      inclChainMap R X Kᶜ := by
  simp only [inclChainMap, ← Functor.map_comp]
  congr 1 <;> { apply ConcreteCategory.hom_ext; intro ⟨⟨x, _⟩, hxK⟩; rfl }

/-- The relative chain map `S_*(U, U ∩ Kᶜ; R) → S_*(X, Kᶜ; R)` induced by the
inclusion of pairs `(U, U ∩ Kᶜ) → (X, Kᶜ)`; this is the chain-level excision
map. -/
def excisionPairChainMap (X : TopCat.{0}) (K : Set X) (U : TopologicalSpace.Opens X) :
    relSingChainCx R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R X Kᶜ :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (excisionSubspaceIncl X K U))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (excisionOpenIncl X U))
    (excisionPairIncl_comm R X K U)

/-- The induced map on relative homology
`H_n(U, U ∩ Kᶜ; R) → H_n(X, Kᶜ; R)` coming from the excision inclusion of
pairs. -/
def excisionForwardHomol (X : TopCat.{0}) (K : Set X)
    (U : TopologicalSpace.Opens X) (n : ℕ) :
    relSingularHomology R (TopCat.of ↑U.1) (Subtype.val ⁻¹' Kᶜ) n ⟶
    relSingularHomology R X Kᶜ n :=
  HomologicalComplex.homologyMap (excisionPairChainMap R X K U) n







/-- The inclusion `U \ L ↪ Lᶜ` as a morphism in `TopCat`, used to compare
`(U \ L, (U \ L) ∩ Kᶜ)` with `(Lᶜ, Lᶜ ∩ Kᶜ)`. -/
def localityBigIncl (X : TopCat.{0}) {K : Set X} (L : Set X)
    (pair : OpenNbhdPair K L) :
    TopCat.of ↑(pair.U.1 \ L) ⟶ TopCat.of (Lᶜ : Set X) :=
  ⟨fun ⟨x, hx⟩ => ⟨x, hx.2⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- The inclusion `(U \ L) ∩ Kᶜ ↪ Lᶜ ∩ Kᶜ`, viewed as a morphism in `TopCat`
between the relativizing subspaces. -/
def localitySubIncl (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair.U.1 \ L))) ⟶
    TopCat.of (complementInComplement X K L) :=
  ⟨fun ⟨⟨x, hxUL⟩, hxK⟩ => ⟨⟨x, hxUL.2⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Commutativity of the square of inclusions relating the pair
`(U \ L, (U \ L) ∩ Kᶜ)` to `(Lᶜ, Lᶜ ∩ Kᶜ)`, in `TopCat`. -/
lemma localityIncl_comm_topcat (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    subtypeIncl (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      localityBigIncl X L pair =
    localitySubIncl X K L pair ≫
      subtypeIncl (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- Chain-level version of `localityIncl_comm_topcat`: the induced square of
chain maps between singular chain complexes commutes. -/
lemma localityIncl_comm_chain (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    inclChainMap R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (localityBigIncl X L pair) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (localitySubIncl X K L pair) ≫
      inclChainMap R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) := by
  simp only [inclChainMap, ← Functor.map_comp, localityIncl_comm_topcat X K L pair]

/-- The induced map of relative singular chain complexes
`S_*(U \ L, (U \ L) ∩ Kᶜ; R) → S_*(Lᶜ, Lᶜ ∩ Kᶜ; R)` coming from the
inclusions of pairs. -/
def localityInclChainMap (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) :
    relSingChainCx R (TopCat.of ↑(pair.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of (Lᶜ : Set X)) (complementInComplement X K L) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (localitySubIncl X K L pair))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (localityBigIncl X L pair))
    (localityIncl_comm_chain R X K L pair)

/-- The induced map on relative homology
`H_q(U \ L, (U \ L) ∩ Kᶜ; R) → H_q(Lᶜ, Lᶜ ∩ Kᶜ; R)`, which is the second
ingredient (after excision) of the local construction of the fully relative
cap product. -/
def localityForwardHomol
    (X : TopCat.{0}) (K L : Set X)
    (pair : OpenNbhdPair K L) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑(pair.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of (Lᶜ : Set X))
        (complementInComplement X K L) q : Type _) :=
  (HomologicalComplex.homologyMap (localityInclChainMap R X K L pair) q).hom




/-- The induced map of "relativizing" subspaces between two nested
neighbourhood pairs at the `n`-side: `U₂ ∩ Kᶜ ↪ U₁ ∩ Kᶜ` (recall the pair
preorder is reversed, so `pair₁ ≤ pair₂` means `U₂ ⊆ U₁`). -/
def nbhdSubIncl_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑pair₂.U.1)) ⟶
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑pair₁.U.1)) :=
  ⟨fun ⟨⟨x, hxU₂⟩, hxK⟩ => ⟨⟨x, h.1 hxU₂⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Compatibility square in `TopCat` between subspace and open inclusions for
nested neighbourhood pairs, on the `n`-side. -/
lemma nbhdIncl_comm_topcat_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    subtypeIncl (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ≫
      opensInclusion pair₁.U pair₂.U h.1 =
    nbhdSubIncl_n pair₁ pair₂ h ≫
      subtypeIncl (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _⟩, _⟩
  rfl

/-- Chain-level version of `nbhdIncl_comm_topcat_n`: the corresponding square
of chain maps commutes. -/
lemma nbhdIncl_comm_chain_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    inclChainMap R (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (opensInclusion pair₁.U pair₂.U h.1) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdSubIncl_n pair₁ pair₂ h) ≫
      inclChainMap R (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) := by
  simp only [inclChainMap, ← Functor.map_comp, nbhdIncl_comm_topcat_n pair₁ pair₂ h]

/-- The chain map between relative chain complexes
`S_*(U₂, U₂ ∩ Kᶜ) → S_*(U₁, U₁ ∩ Kᶜ)` induced by passing to a smaller pair
(on the `n`-side). -/
def nbhdInclChainMap_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relSingChainCx R (TopCat.of ↑pair₂.U.1) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of ↑pair₁.U.1) (Subtype.val ⁻¹' Kᶜ) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdSubIncl_n pair₁ pair₂ h))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (opensInclusion pair₁.U pair₂.U h.1))
    (nbhdIncl_comm_chain_n R pair₁ pair₂ h)


/-- The map on relative homology
`H_n(U₂, U₂ ∩ Kᶜ; R) → H_n(U₁, U₁ ∩ Kᶜ; R)` induced by passing to a smaller
pair (on the `n`-side). -/
def nbhdHomologyInclusion_n
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (n : ℕ) :
    (relSingularHomology R (TopCat.of ↑pair₂.U.1)
      (Subtype.val ⁻¹' Kᶜ) n : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑pair₁.U.1)
        (Subtype.val ⁻¹' Kᶜ) n : Type _) :=
  (HomologicalComplex.homologyMap (nbhdInclChainMap_n R pair₁ pair₂ h) n).hom

/-- The inclusion `U₂ \ L ↪ U₁ \ L` for two nested neighbourhood pairs,
as a morphism in `TopCat`. -/
def nbhdBigIncl_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of ↑(pair₂.U.1 \ L) ⟶ TopCat.of ↑(pair₁.U.1 \ L) :=
  ⟨fun ⟨x, hx⟩ => ⟨x, h.1 hx.1, hx.2⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩

/-- The inclusion `(U₂ \ L) ∩ Kᶜ ↪ (U₁ \ L) ∩ Kᶜ` for two nested neighbourhood
pairs, as a morphism in `TopCat` (on the `q`-side). -/
def nbhdSubIncl_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair₂.U.1 \ L))) ⟶
    TopCat.of (Subtype.val ⁻¹' Kᶜ : Set (TopCat.of ↑(pair₁.U.1 \ L))) :=
  ⟨fun ⟨⟨x, hx⟩, hxK⟩ => ⟨⟨x, h.1 hx.1, hx.2⟩, hxK⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- Compatibility square in `TopCat` between subspace and big-pair inclusions
for nested neighbourhood pairs, on the `q`-side. -/
lemma nbhdIncl_comm_topcat_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    subtypeIncl (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      nbhdBigIncl_q pair₁ pair₂ h =
    nbhdSubIncl_q pair₁ pair₂ h ≫
      subtypeIncl (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
  apply ConcreteCategory.hom_ext
  intro ⟨⟨x, _, _⟩, _⟩
  rfl

/-- Chain-level version of `nbhdIncl_comm_topcat_q`: the corresponding square
of chain maps commutes on the `q`-side. -/
lemma nbhdIncl_comm_chain_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    inclChainMap R (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ≫
      ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdBigIncl_q pair₁ pair₂ h) =
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
        (nbhdSubIncl_q pair₁ pair₂ h) ≫
      inclChainMap R (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) := by
  simp only [inclChainMap, ← Functor.map_comp, nbhdIncl_comm_topcat_q pair₁ pair₂ h]

/-- The chain map between relative chain complexes
`S_*(U₂ \ L, (U₂ \ L) ∩ Kᶜ) → S_*(U₁ \ L, (U₁ \ L) ∩ Kᶜ)` induced by passing
to a smaller pair (on the `q`-side). -/
def nbhdInclChainMap_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) :
    relSingChainCx R (TopCat.of ↑(pair₂.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) ⟶
    relSingChainCx R (TopCat.of ↑(pair₁.U.1 \ L)) (Subtype.val ⁻¹' Kᶜ) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdSubIncl_q pair₁ pair₂ h))
    (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
      (nbhdBigIncl_q pair₁ pair₂ h))
    (nbhdIncl_comm_chain_q R pair₁ pair₂ h)


/-- The map on relative homology
`H_q(U₂ \ L, (U₂ \ L) ∩ Kᶜ; R) → H_q(U₁ \ L, (U₁ \ L) ∩ Kᶜ; R)` induced by
passing to a smaller pair (on the `q`-side). -/
def nbhdHomologyInclusion_q
    {X : TopCat.{0}} {K L : Set X}
    (pair₁ pair₂ : OpenNbhdPair K L) (h : pair₁ ≤ pair₂) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑(pair₂.U.1 \ L))
      (Subtype.val ⁻¹' Kᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R (TopCat.of ↑(pair₁.U.1 \ L))
        (Subtype.val ⁻¹' Kᶜ) q : Type _) :=
  (HomologicalComplex.homologyMap (nbhdInclChainMap_q R pair₁ pair₂ h) q).hom


































/-- The natural map `H_n(X; R) → H_n(X, Kᶜ; R)` from absolute to relative
singular homology, induced by the cokernel projection of the relativizing
chain map. -/
def absToRelHomol
    (X : TopCat.{0}) (K : Set X) (n : ℕ) :
    absSingularHomology R X n ⟶ relSingularHomology R X Kᶜ n :=
  HomologicalComplex.homologyMap (cokernel.π (inclChainMap R X Kᶜ)) n




































end FullyRelativeCapProduct

open Set FullyRelativeCapProduct

/-- The standing hypothesis for the Čech/singular Mayer–Vietoris compatibility
theorem: either `X` is a normal space and `A, B` are closed in `X`, or `X` is
Hausdorff and `A, B` are compact. -/
def MayerVietorisHypothesis (X : Type*) [TopologicalSpace X]
    (A B : Set X) : Prop :=
  (NormalSpace X ∧ IsClosed A ∧ IsClosed B) ∨
  (T2Space X ∧ IsCompact A ∧ IsCompact B)

/-- Data witnessing the Čech/singular Mayer–Vietoris compatibility ladder of
Theorem 36.2: a Mayer–Vietoris sequence in Čech cohomology of `A, B, A ∪ B,
A ∩ B`, a Mayer–Vietoris sequence in relative singular homology of their
complements, exactness of both sequences, "cap rungs" connecting them indexed
by subsets `S ∈ {A, B, A ∪ B, A ∩ B}` for each `(p, q)` with `p + q = n`, and
three commutative squares expressing compatibility with the union-to-sum,
sum-to-intersection, and connecting morphisms. -/
structure MayerVietorisLadder (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) where

  topUnionToSum : ∀ p : ℕ,
    (cechCohomology R X (A ∪ B) p ⟶
      cechCohomology R X A p ⊞ cechCohomology R X B p)
  topSumToInter : ∀ p : ℕ,
    (cechCohomology R X A p ⊞ cechCohomology R X B p ⟶
      cechCohomology R X (A ∩ B) p)
  topConnecting : ∀ p : ℕ,
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1))

  botUnionToSum : ∀ q : ℕ,
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q)
  botSumToInter : ∀ q : ℕ,
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q)
  botConnecting : ∀ q : ℕ,
    (relSingularHomology R X (A ∩ B)ᶜ q ⟶ relSingularHomology R X (A ∪ B)ᶜ (q - 1))
  capRung : ∀ (p q : ℕ) (S : Set X), p + q = n →
    (cechCohomology R X S p ⟶ relSingularHomology R X Sᶜ q)

  top_exact_sum : ∀ p : ℕ, Function.Exact
    (topUnionToSum p).hom (topSumToInter p).hom
  top_exact_inter : ∀ p : ℕ, Function.Exact
    (topSumToInter p).hom (topConnecting p).hom
  top_exact_union : ∀ p : ℕ, Function.Exact
    (topConnecting p).hom (topUnionToSum (p + 1)).hom

  bot_exact_sum : ∀ q : ℕ, Function.Exact
    (botUnionToSum q).hom (botSumToInter q).hom
  bot_exact_inter : ∀ q : ℕ, Function.Exact
    (botSumToInter q).hom (botConnecting q).hom
  bot_exact_union : ∀ q : ℕ, Function.Exact
    (botConnecting q).hom (botUnionToSum (q - 1)).hom

  comm_sq1 : ∀ (p q : ℕ) (hpq : p + q = n),
    capRung p q (A ∪ B) hpq ≫ botUnionToSum q =
      topUnionToSum p ≫ Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq)
  comm_sq2 : ∀ (p q : ℕ) (hpq : p + q = n),
    Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq) ≫ botSumToInter q =
      topSumToInter p ≫ capRung p q (A ∩ B) hpq
  comm_sq3 : ∀ (p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n),
    topConnecting p ≫ capRung (p + 1) (q - 1) (A ∪ B) hpq' =
      capRung p q (A ∩ B) hpq ≫ botConnecting q

/-- Abstract data of a Mayer–Vietoris long exact sequence in Čech cohomology
for the cover `A, B` of `A ∪ B`: a union-to-sum map, a sum-to-intersection
map, a degree-raising connecting morphism, and the three exactness conditions
making the resulting sequence long exact. -/
structure CechMVSequence (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) where
  unionToSum : ∀ p : ℕ,
    (cechCohomology R X (A ∪ B) p ⟶
      cechCohomology R X A p ⊞ cechCohomology R X B p)
  sumToInter : ∀ p : ℕ,
    (cechCohomology R X A p ⊞ cechCohomology R X B p ⟶
      cechCohomology R X (A ∩ B) p)
  connecting : ∀ p : ℕ,
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1))
  exact_sum : ∀ p : ℕ, Function.Exact
    (unionToSum p).hom (sumToInter p).hom
  exact_inter : ∀ p : ℕ, Function.Exact
    (sumToInter p).hom (connecting p).hom
  exact_union : ∀ p : ℕ, Function.Exact
    (connecting p).hom (unionToSum (p + 1)).hom

/-- Abstract data of a Mayer–Vietoris long exact sequence in relative singular
homology for the cover `A, B` of `A ∪ B` (taken in the complements): a
union-to-sum map, a sum-to-intersection map, a degree-lowering connecting
morphism, and the three exactness conditions. -/
structure SingularMVSequence (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) where
  unionToSum : ∀ q : ℕ,
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q)
  sumToInter : ∀ q : ℕ,
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q)
  connecting : ∀ q : ℕ,
    (relSingularHomology R X (A ∩ B)ᶜ q ⟶ relSingularHomology R X (A ∪ B)ᶜ (q - 1))
  exact_sum : ∀ q : ℕ, Function.Exact
    (unionToSum q).hom (sumToInter q).hom
  exact_inter : ∀ q : ℕ, Function.Exact
    (sumToInter q).hom (connecting q).hom
  exact_union : ∀ q : ℕ, Function.Exact
    (connecting q).hom (unionToSum (q - 1)).hom

/-- The "cap rung" data connecting a Čech Mayer–Vietoris sequence to a
singular Mayer–Vietoris sequence in the presence of a fixed homology class
`x_union ∈ H_n(X, (A ∪ B)ᶜ)`: cap product maps for each subset
`S ∈ {A, B, A ∪ B, A ∩ B}` and `(p, q)` with `p + q = n`, plus the three
commutative squares expressing Mayer–Vietoris naturality. -/
structure MVCapProductData (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n)
    (cechMV : CechMVSequence R X A B)
    (singMV : SingularMVSequence R X A B) where
  capRung : ∀ (p q : ℕ) (S : Set X), p + q = n →
    (cechCohomology R X S p ⟶ relSingularHomology R X Sᶜ q)
  comm_sq1 : ∀ (p q : ℕ) (hpq : p + q = n),
    capRung p q (A ∪ B) hpq ≫ singMV.unionToSum q =
      cechMV.unionToSum p ≫
        Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq)
  comm_sq2 : ∀ (p q : ℕ) (hpq : p + q = n),
    Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq) ≫
      singMV.sumToInter q =
      cechMV.sumToInter p ≫ capRung p q (A ∩ B) hpq
  comm_sq3 : ∀ (p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n),
    cechMV.connecting p ≫ capRung (p + 1) (q - 1) (A ∪ B) hpq' =
      capRung p q (A ∩ B) hpq ≫ singMV.connecting q



















/-- The Mayer–Vietoris union-to-sum map in relative singular homology of the
complements, `H_q(X, (A ∪ B)ᶜ) → H_q(X, Aᶜ) ⊕ H_q(X, Bᶜ)`, given by pairing
the two restriction maps. -/
def singularMV_unionToSum
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (_hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q) :=
  biprod.lift
    (homolRestriction R X (A ∪ B) A q)
    (homolRestriction R X (A ∪ B) B q)


/-- The Mayer–Vietoris sum-to-intersection map in relative singular homology
of the complements, `H_q(X, Aᶜ) ⊕ H_q(X, Bᶜ) → H_q(X, (A ∩ B)ᶜ)`, given by
the difference of the restriction maps. -/
def singularMV_sumToInter
    (R : Type) [CommRing R] (X : TopCat.{0}) (A B : Set X)
    (_hyp : MayerVietorisHypothesis X A B) (q : ℕ) :
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q) :=
  biprod.desc
    (homolRestriction R X A (A ∩ B) q)
    (-(homolRestriction R X B (A ∩ B) q))



















/-- The map induced on relative singular homology by the inclusion of a
neighbourhood `U` of `S` into `X`: `H_q(U, Sᶜ ∩ U) → H_q(X, Sᶜ)`. -/
def inclusionForwardHomol
    (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X)
    (U : CechCohomology.OpenNeighborhoods S) (q : ℕ) :
    (relSingularHomology R (TopCat.of ↑U.1.1)
      (Subtype.val ⁻¹' Sᶜ) q : Type _) →ₗ[R]
      (relSingularHomology R X Sᶜ q : Type _) :=
  (excisionForwardHomol R X S U.1 q).hom




























