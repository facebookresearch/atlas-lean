/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section32
import Atlas.AlgebraicTopologyI.code.Lemma32_4
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.LocallyConstant.Basic

open Topology MulAction CategoryTheory TopologicalSpace

namespace CoveringSpaces

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-- (Definition 31.1) A continuous map `p : E → B` is a *covering space* if every point
preimage is discrete and every `b ∈ B` has a neighborhood `V` so that `p⁻¹(V)` splits
homeomorphically as `V × p⁻¹(b)` over `V`. Defined here as `IsCoveringMap p`. -/
def IsCoveringSpace (p : E → B) : Prop :=
  IsCoveringMap p

/-- (Definition 31.3) The action of a group `π` on a space `X` is *principal*
(equivalently, totally discontinuous) if every `x` has a neighborhood `U` such that
`gU ∩ U ≠ ∅` forces `g = 1`. -/
def IsPrincipalAction (π : Type*) (X : Type*) [Group π] [TopologicalSpace X]
    [MulAction π X] : Prop :=
  ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : π, ((g • ·) '' U ∩ U).Nonempty → g = 1

variable {π : Type*} {X : Type*} [Group π] [TopologicalSpace X] [MulAction π X]
  [ContinuousConstSMul π X]

/-- Packaging of a principal action as a `IsQuotientCoveringMap` for the orbit
projection, used to derive that the orbit projection is a covering map. -/
theorem IsPrincipalAction.isQuotientCoveringMap (h : IsPrincipalAction π X) :
    IsQuotientCoveringMap (Quotient.mk (orbitRel π X)) π where
  toIsQuotientMap := isQuotientMap_quotient_mk'
  continuous_const_smul := ContinuousConstSMul.continuous_const_smul
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint := h

/-- (Lemma 31.4) If `π` acts principally on `X` then the orbit projection
`X → π\X` is a covering space. -/
theorem isCoveringMap_orbitProjection_of_principalAction (h : IsPrincipalAction π X) :
    IsCoveringMap (Quotient.mk (orbitRel π X)) :=
  h.isQuotientCoveringMap.isCoveringMap

/-- (Theorem 31.5, Unique path lifting) For any covering space `p : E → B`, path
`γ : I → B` in the base, and `e ∈ E` with `p e = γ 0`, there is a unique lift
`Γ : I → E` with `p ∘ Γ = γ` and `Γ 0 = e`. -/
theorem unique_path_lifting {p : E → B} (hp : IsCoveringMap p)
    (γ : C(↑unitInterval, B)) (e : E) (he : γ 0 = p e) :
    ∃! Γ : C(↑unitInterval, E), p ∘ ⇑Γ = ⇑γ ∧ Γ 0 = e := by
  refine ⟨hp.liftPath γ e he, ⟨hp.liftPath_lifts γ e he, hp.liftPath_zero γ e he⟩, ?_⟩
  intro Γ' ⟨hΓ'_lifts, hΓ'_zero⟩
  exact (hp.eq_liftPath_iff' he).mpr ⟨hΓ'_lifts, hΓ'_zero⟩

universe u

noncomputable section

/-- A typeclass asserting that `B` is path connected and *semi-locally simply connected*:
every point has arbitrarily small neighborhoods `V` whose loops at the basepoint become
null-homotopic in `B`. Hypothesis used in the classification of covering spaces. -/
class IsSemiLocallySimplyConnected (B : Type u) [TopologicalSpace B] : Prop where
  pathConnected : PathConnectedSpace B
  semilocal : ∀ (b : B) (U : Set B), U ∈ nhds b →
    ∃ V : Set B, V ∈ nhds b ∧ V ⊆ U ∧
      ∀ (hb : b ∈ V) (γ : Path (⟨b, hb⟩ : V) ⟨b, hb⟩),
        Path.Homotopic (γ.map continuous_subtype_val) (Path.refl b)

/-- The data of a covering space over a fixed base `B`: a total space `E` together with
its topology, a continuous projection `proj : E → B`, and a proof that `proj` is a
covering map. -/
structure CoveringSpaceOver (B : Type u) [TopologicalSpace B] where
  E : Type u
  topE : TopologicalSpace E
  proj : E → B
  continuous_proj : @Continuous E B topE _ proj
  isCoveringMap : @IsCoveringMap E B topE _ proj

/-- A morphism of covering spaces over `B`: a continuous map between the total spaces
that commutes with the projections. -/
structure CoveringSpaceOver.Hom {B : Type u} [TopologicalSpace B]
    (E₁ E₂ : CoveringSpaceOver B) where
  toFun : E₁.E → E₂.E
  continuous_toFun : @Continuous E₁.E E₂.E E₁.topE E₂.topE toFun
  proj_comm : E₂.proj ∘ toFun = E₁.proj

/-- The category `Cov_B` of covering spaces over `B`, with morphisms given by
projection-preserving continuous maps. -/
instance coveringSpaceOverCategory {B : Type u} [TopologicalSpace B] :
    Category (CoveringSpaceOver B) where
  Hom := CoveringSpaceOver.Hom
  id E := {
    toFun := id
    continuous_toFun := @continuous_id E.E E.topE
    proj_comm := rfl
  }
  comp {X Y Z} f g := {
    toFun := g.toFun ∘ f.toFun
    continuous_toFun := @Continuous.comp X.E Y.E Z.E X.topE Y.topE Z.topE
      (f := f.toFun) (g := g.toFun) g.continuous_toFun f.continuous_toFun
    proj_comm := by
      ext x
      have h1 := congr_fun g.proj_comm (f.toFun x)
      have h2 := congr_fun f.proj_comm x
      simp only [Function.comp] at h1 h2 ⊢
      rw [h1, h2]
  }

/-- The monodromy action of `π₁(B, b)` on the fiber `p⁻¹(b)`, realised as a group
homomorphism into the endomorphism monoid of the fiber under the monodromy functor. -/
def fiberAction {B : Type u} [TopologicalSpace B] (b : B)
    {E : Type u} [TopologicalSpace E] {p : E → B}
    (cov : IsCoveringMap p) : FundamentalGroup B b →*
    End (cov.monodromyFunctor.obj (FundamentalGroupoid.mk b)) where
  toFun g := cov.monodromyFunctor.map g
  map_one' := cov.monodromyFunctor.map_id _
  map_mul' a c := by
    simp only [End.mul_def]
    exact cov.monodromyFunctor.map_comp c a

/-- The fiber of a covering space over `b` packaged as a `π₁(B, b)`-set via the monodromy
action. -/
def fiberActionObj {B : Type u} [TopologicalSpace B] (b : B)
    (covSpace : CoveringSpaceOver B) : Action (Type u) (FundamentalGroup B b) where
  V := @IsCoveringMap.monodromyFunctor covSpace.E B covSpace.topE _ covSpace.proj
    covSpace.isCoveringMap |>.obj (FundamentalGroupoid.mk b)
  ρ := @fiberAction B _ b covSpace.E covSpace.topE covSpace.proj covSpace.isCoveringMap

/-- A morphism of covering spaces over `B'` commutes with path lifting: postcomposing the
lift of a path in `E₁` by the morphism `f : E₁ → E₂` gives the lift of the same path
starting at `f e`. -/
lemma liftPath_comp_covMorphism
    {E₁ : Type u} {E₂ : Type u} {B' : Type u}
    {t₁ : TopologicalSpace E₁} {t₂ : TopologicalSpace E₂} [TopologicalSpace B']
    {p₁ : E₁ → B'} {p₂ : E₂ → B'}
    (cov₁ : @IsCoveringMap _ _ t₁ _ p₁) (cov₂ : @IsCoveringMap _ _ t₂ _ p₂)
    (f : E₁ → E₂) (hf_cont : @Continuous _ _ t₁ t₂ f) (hf_comm : p₂ ∘ f = p₁)
    (γ : C(↑unitInterval, B')) (e : E₁) (he : γ 0 = p₁ e) :
    (@ContinuousMap.mk _ _ t₁ t₂ f hf_cont).comp (cov₁.liftPath γ e he) =
      cov₂.liftPath γ (f e)
        (show γ 0 = p₂ (f e) by rw [he, ← congr_fun hf_comm e]; rfl) := by
  apply (cov₂.eq_liftPath_iff' _).mpr
  refine ⟨?_, ?_⟩
  · ext t
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Function.comp]
    have h := congr_fun (cov₁.liftPath_lifts γ e he) t
    simp only [Function.comp] at h
    have hc := congr_fun hf_comm (cov₁.liftPath γ e he t)
    simp only [Function.comp] at hc
    rw [hc, h]
  · simp [ContinuousMap.comp_apply, ContinuousMap.coe_mk, cov₁.liftPath_zero]

/-- Equivariance of the fiber map induced by a morphism of covering spaces: the map
`f : E₁ → E₂` intertwines the monodromy actions of `π₁(B', b)` on the fibers
`p₁⁻¹(b)` and `p₂⁻¹(b)`. -/
lemma fiberMap_monodromy_comm
    {E₁ : Type u} {E₂ : Type u} {B' : Type u}
    {t₁ : TopologicalSpace E₁} {t₂ : TopologicalSpace E₂} [TopologicalSpace B']
    {p₁ : E₁ → B'} {p₂ : E₂ → B'}
    (cov₁ : @IsCoveringMap _ _ t₁ _ p₁) (cov₂ : @IsCoveringMap _ _ t₂ _ p₂)
    (f : E₁ → E₂) (hf_cont : @Continuous _ _ t₁ t₂ f) (hf_comm : p₂ ∘ f = p₁)
    {b : B'} (γ : Path.Homotopic.Quotient b b) (e : p₁ ⁻¹' {b}) :
    f (@IsCoveringMap.monodromy _ _ t₁ _ _ cov₁ (x := b) (y := b) γ e).val =
      (@IsCoveringMap.monodromy _ _ t₂ _ _ cov₂ (x := b) (y := b) γ
        ⟨f e.val, by
          have := e.prop
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢
          have h := congr_fun hf_comm e.val
          simp only [Function.comp] at h
          rw [h, this]⟩).val := by
  obtain ⟨γ_path, rfl⟩ := Quotient.exists_rep γ
  unfold IsCoveringMap.monodromy
  simp only [Quotient.lift_mk]
  have he_eq : (↑γ_path : C(↑unitInterval, B')) 0 = p₁ e.val := by
    show γ_path 0 = p₁ e.val
    rw [γ_path.source]
    exact (Set.mem_preimage.mp e.prop : p₁ e.val = b).symm
  have key := liftPath_comp_covMorphism cov₁ cov₂ f hf_cont hf_comm (↑γ_path) e.val he_eq
  have h := congr_fun (congrArg DFunLike.coe key) 1
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk] at h
  convert h using 2

/-- The "take the fiber at `b`" functor `Cov_B → π₁(B, b)-Set` sending a covering space
to its fiber equipped with the monodromy action, and a morphism to its restriction
between fibers. -/
def fiberFunctor {B : Type u} [TopologicalSpace B] (b : B) :
    CoveringSpaceOver B ⥤ Action (Type u) (FundamentalGroup B b) where
  obj := fiberActionObj b
  map {E₁ E₂} f :=
    { hom := fun e =>
        ⟨f.toFun e.val, by
          have := e.prop
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢
          have h := congr_fun f.proj_comm e.val
          simp only [Function.comp] at h
          rw [h, this]⟩
      comm := fun g => by
        ext ⟨e, he⟩
        apply Subtype.ext
        simp only [types_comp_apply, fiberActionObj, fiberAction]
        exact fiberMap_monodromy_comm E₁.isCoveringMap E₂.isCoveringMap
          f.toFun f.continuous_toFun f.proj_comm g ⟨e, he⟩ }
  map_id X := by
    apply Action.Hom.ext
    funext ⟨e, he⟩
    apply Subtype.ext
    rfl
  map_comp {X Y Z} f g := by
    apply Action.Hom.ext
    funext ⟨e, he⟩
    apply Subtype.ext
    rfl




end

end CoveringSpaces

open CategoryTheory AlgebraicTopology SingularCohomology Limits

noncomputable section

namespace OrientationHomology

/-- The singular chain complex functor `Top → Ch_*(ModuleCat R)` with coefficients in
`R`, obtained by tensoring the integral singular chain complex with `R`. -/
abbrev singularChainFunctor (R : Type) [CommRing R] :
    TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} R) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)

/-- The inclusion of a subspace `A ⊆ M` as a morphism in `TopCat`. -/
def subsetIncl (M : Type) [TopologicalSpace M] (A : Set M) :
    TopCat.of A ⟶ TopCat.of M :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The relative singular chain complex `S_*(M, A; R)`, defined as the cokernel of the
chain map induced by the inclusion `A ↪ M`. -/
def relativeChainComplex (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (A : Set M) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel ((singularChainFunctor R).map (subsetIncl M A))

/-- The relative singular homology module `H_n(M, A; R)` of the pair `(M, A)`. -/
def relativeHomologyModule (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] (A : Set M) :
    ModuleCat.{0} R :=
  (relativeChainComplex R M A).homology n

/-- The local homology module `H_n(M, M − {x}; R)` at the point `x`; the stalk of the
orientation sheaf in degree `n`. -/
def localHomologyModule (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] (x : M) :
    ModuleCat.{0} R :=
  relativeHomologyModule R n M ({x}ᶜ)

/-- The inclusion `A ↪ B` as a morphism in `TopCat`, given `A ⊆ B`. -/
def subsetToSubset (M : Type) [TopologicalSpace M]
    (A B : Set M) (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  ⟨fun a => ⟨a.1, h a.2⟩, continuous_inclusion h⟩

/-- For `A ⊆ B`, the natural chain map between the relative chain complexes
`S_*(M, A; R) → S_*(M, B; R)` induced by the inclusion of subcomplexes. -/
def restrictionChainMap (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (A B : Set M) (h : A ⊆ B) :
    relativeChainComplex R M A ⟶ relativeChainComplex R M B := by
  apply cokernel.map _ _
    ((singularChainFunctor R).map (subsetToSubset M A B h)) (𝟙 _)
  simp only [Category.comp_id]
  show (singularChainFunctor R).map (subsetIncl M A) =
    (singularChainFunctor R).map (subsetToSubset M A B h) ≫
    (singularChainFunctor R).map (subsetIncl M B)
  rw [← Functor.map_comp]; congr 1

/-- The induced map on relative homology `H_n(M, A; R) → H_n(M, B; R)` for `A ⊆ B`. -/
def restrictionHomologyMap (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (A B : Set M) (h : A ⊆ B) :
    relativeHomologyModule R n M A ⟶ relativeHomologyModule R n M B :=
  HomologicalComplex.homologyMap (restrictionChainMap R M A B h) n

/-- The restriction map `H_n(M, M − U; R) → H_n(M, M − {y}; R) = (o_M)_y` from a
"compatible class over `U`" to its local-homology value at any point `y ∈ U`. -/
def restrictToPoint (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (U : Set M) (y : M) (hy : y ∈ U) :
    relativeHomologyModule R n M Uᶜ ⟶ localHomologyModule R n M y :=
  restrictionHomologyMap R n M Uᶜ {y}ᶜ
    (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy))

/-- A choice of local-homology element at each point is *locally compatible* if every
point has an open neighborhood `U` and a relative-homology class on `(M, M − U)` that
restricts to the chosen element at every point of `U`. -/
def IsLocallyCompatibleSection (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M]
    (μ : (x : M) → ↥(localHomologyModule R n M x)) : Prop :=
  ∀ x : M, ∃ (U : Set M) (_ : IsOpen U) (_ : x ∈ U)
    (α : ↥(relativeHomologyModule R n M Uᶜ)),
    ∀ (y : M) (hy : y ∈ U),
      (restrictToPoint R n M U y hy).hom α = μ y

/-- The `R`-module `Γ(M; o_M ⊗ R)` of (not-necessarily continuous) sections of the
orientation sheaf with `R`-coefficients, given here as the product of the local-homology
fibers. -/
def orientationSectionModule (R : Type) [CommRing R] (n : ℕ) (M : Type)
    [TopologicalSpace M] : ModuleCat.{0} R :=
  ModuleCat.of R (∀ x : M, ↥(localHomologyModule R n M x))

/-- The comparison map `j : H_n(M; R) → Γ(M; o_M ⊗ R)` of the Orientation Theorem,
sending a homology class to the family of its restrictions to each local-homology
fiber. -/
def orientationComparisonMap (R : Type) [CommRing R] (n : ℕ) (M : Type)
    [TopologicalSpace M] :
    relativeHomologyModule R n M ∅ →ₗ[R] (∀ x : M, ↥(localHomologyModule R n M x)) where
  toFun a x := (restrictionHomologyMap R n M ∅ {x}ᶜ (Set.empty_subset _)).hom a
  map_add' a b := funext fun x =>
    map_add (restrictionHomologyMap R n M ∅ {x}ᶜ (Set.empty_subset _)).hom a b
  map_smul' r a := funext fun x =>
    map_smul (restrictionHomologyMap R n M ∅ {x}ᶜ (Set.empty_subset _)).hom r a

/-- (Definition 31.8) An *`R`-orientation* of an `n`-manifold `M`: a choice of
generator `μ x` in each local-homology module `H_n(M, M − {x}; R)`, depending locally
compatibly on `x`. Equivalently, a section of the unit twisted local system
`(o_M ⊗ R)^×`. -/
structure ROrientation (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (R : Type) [CommRing R] where
  μ : (x : M) → ↥(localHomologyModule R n M x)
  generates : ∀ x : M, Submodule.span R {μ x} = ⊤
  locallyCompatible : ∀ x : M, ∃ (U : Set M) (_ : IsOpen U) (_ : x ∈ U)
      (α : ↥(relativeHomologyModule R n M Uᶜ)),
      ∀ (y : M) (hy : y ∈ U),
        (restrictToPoint R n M U y hy).hom α = μ y

/-- The manifold `M` is *`R`-orientable* if it admits some `R`-orientation. -/
def IsROrientable (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (R : Type) [CommRing R] : Prop :=
  Nonempty (ROrientation n M R)

/-- The submodule `R[2] := {r ∈ R : 2r = 0}` of `2`-torsion elements of `R`. -/
abbrev twoTorsion (R : Type) [CommRing R] : Submodule R R :=
  Submodule.torsionBy R R (2 : R)


/-- Absolute singular homology agrees with relative homology against the empty subspace,
`H_n(M; R) ≅ H_n(M, ∅; R)`. -/
def singularHomology_iso_relativeHomology_empty (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] :
    singularHomologyModule R (TopCat.of M) n ≅ relativeHomologyModule R n M ∅ := by


  show ((singularChainFunctor R).obj (TopCat.of M)).homology n ≅
    (cokernel ((singularChainFunctor R).map (subsetIncl M ∅))).homology n

  have hf : (singularChainFunctor R).map (subsetIncl M ∅) = 0 := by
    haveI : IsEmpty (↥(∅ : Set M)) := Set.isEmpty_coe_sort.mpr rfl
    haveI : TotallyDisconnectedSpace (↥(∅ : Set M)) := inferInstance
    have hZ : IsZero ((singularChainFunctor R).obj (TopCat.of (↥(∅ : Set M)))) := by
      apply IsZero.of_iso _ (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat.{0} R) (ModuleCat.of R R) (TopCat.of (↥(∅ : Set M))))
      have hCoprod : IsZero (∐ fun _ : (↥(∅ : Set M)) ↦ (ModuleCat.of R R)) := by
        rw [IsZero.iff_id_eq_zero]; ext ⟨j, hj⟩; exact absurd hj (by simp)
      rw [IsZero.iff_id_eq_zero]; ext i : 1
      simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply]
      exact hCoprod.eq_zero_of_src (𝟙 _) ▸ rfl
    exact hZ.eq_zero_of_src _

  have iso_chain : cokernel ((singularChainFunctor R).map (subsetIncl M ∅)) ≅
      (singularChainFunctor R).obj (TopCat.of M) := by
    rw [hf]
    exact cokernelZeroIsoTarget
  exact ((HomologicalComplex.homologyFunctor _ _ n).mapIso iso_chain).symm



















/-- If `N` is `R`-linearly isomorphic to `R` and `v ∈ N` spans `N`, then `v` has trivial
annihilator: `r • v = 0` implies `r = 0`. -/
lemma annihilator_trivial_of_span_top_iso_R
    {R : Type} [CommRing R] {N : ModuleCat.{0} R}
    (e : N ≅ ModuleCat.of R R)
    {v : ↥N} (hgen : Submodule.span R {v} = ⊤)
    {r : R} (hr : r • v = 0) : r = 0 := by

  set w := e.hom.hom v
  have hw : r * w = 0 := by
    have h := congr_arg e.hom.hom hr
    rw [map_smul, map_zero] at h
    rwa [Algebra.id.smul_eq_mul] at h
  have hgen_w : Submodule.span R {w} = ⊤ := by
    rw [Submodule.span_singleton_eq_top_iff]
    intro z
    have hsurj : Function.Surjective e.hom.hom := by
      intro y; exact ⟨e.inv.hom y, congr_fun (congrArg DFunLike.coe
        (congr_arg ModuleCat.Hom.hom e.inv_hom_id)) y⟩
    obtain ⟨v', hv'⟩ := hsurj z
    obtain ⟨s, hs⟩ := (Submodule.span_singleton_eq_top_iff R v).mp hgen v'
    exact ⟨s, by rw [← hv', ← hs, map_smul]⟩

  rw [Submodule.span_singleton_eq_top_iff] at hgen_w
  obtain ⟨s, hs⟩ := hgen_w 1

  have hs' : s * w = 1 := by rwa [Algebra.id.smul_eq_mul] at hs


  calc r = r * 1 := (mul_one r).symm
    _ = r * (s * w) := by rw [hs']
    _ = (r * s) * w := (mul_assoc r s w).symm
    _ = (s * r) * w := by rw [mul_comm r s]
    _ = s * (r * w) := mul_assoc s r w
    _ = s * 0 := by rw [hw]
    _ = 0 := mul_zero s













end OrientationHomology

namespace LocalCoefficientSystems

/-- A *local coefficient system of `R`-modules over `B`*: a functor from the
fundamental groupoid of `B` to `R`-modules. -/
abbrev LocalCoefficientSystem (B : Type*) [TopologicalSpace B]
    (R : Type*) [CommRing R] :=
  FundamentalGroupoid B ⥤ ModuleCat.{0} R

noncomputable section

/-- The representation of `π₁(B, b)` on the fiber `F(b)` of a local coefficient
system `F`. -/
def fiberRepresentation {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B)
    (F : LocalCoefficientSystem B R) :
    Representation R (FundamentalGroup B b)
      (F.obj (FundamentalGroupoid.mk b)) where
  toFun g := (F.map g).hom
  map_one' := by
    have h : (1 : FundamentalGroup B b) = 𝟙 (FundamentalGroupoid.mk b) := End.one_def
    rw [h, F.map_id]; ext; rfl
  map_mul' g₁ g₂ := by
    have h : (g₁ * g₂ : FundamentalGroup B b) = (g₂ ≫ g₁ : End (FundamentalGroupoid.mk b)) :=
      End.mul_def g₁ g₂
    rw [h, F.map_comp]; ext; rfl

/-- A natural transformation `η : F → G` of local coefficient systems restricts on
fibers to an intertwining map between the corresponding `π₁(B, b)`-representations. -/
def fiberIntertwiningMap {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B)
    {F G : LocalCoefficientSystem B R} (η : F ⟶ G) :
    (fiberRepresentation R b F).IntertwiningMap (fiberRepresentation R b G) :=
  Representation.IntertwiningMap.mk (η.app (FundamentalGroupoid.mk b)).hom (fun g => by
    ext x
    simp only [fiberRepresentation, LinearMap.comp_apply]
    exact congr_fun (congrArg DFunLike.coe
      (congr_arg ModuleCat.Hom.hom (η.naturality g))) x)

/-- The functor sending a local coefficient system to its fiber at `b` as an object of
`Rep R (π₁(B, b))`. -/
def fiberToRep {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B) :
    LocalCoefficientSystem B R ⥤ Rep.{0} R (FundamentalGroup B b) where
  obj F := Rep.of (fiberRepresentation R b F)
  map η := Rep.ofHom (fiberIntertwiningMap R b η)
  map_id F := by apply Rep.hom_ext; ext; rfl
  map_comp {F G H} η θ := by apply Rep.hom_ext; ext; rfl

/-- The composite "fiber" functor from local coefficient systems on `B` to modules over
the group algebra `R[π₁(B, b)]`. -/
def fiberFunctor {B : Type*} [TopologicalSpace B]
    (R : Type*) [CommRing R] (b : B) :
    LocalCoefficientSystem B R ⥤
      ModuleCat.{0} (MonoidAlgebra R (FundamentalGroup B b)) :=
  fiberToRep R b ⋙ Rep.toModuleMonoidAlgebra




end

end LocalCoefficientSystems
