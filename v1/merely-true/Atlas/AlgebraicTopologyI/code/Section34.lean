/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section31
import Atlas.AlgebraicTopologyI.code.Section33

import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology

noncomputable section

namespace CechCohomology

/-- **Regular-neighborhood condition** (Section 34, Čech-cohomology setup).
For a directed system of `R`-modules `(G i)` with structure maps and a
compatible collection of maps `g i : G i →ₗ[R] P` to a target module `P`,
the system satisfies the regular-neighborhood condition when each index
`i` is dominated by some `j ≥ i` for which `g j` is a *bijection*.  This
abstract criterion captures the geometric situation where, for a compact
subset `K ⊂ X`, the cohomology of every sufficiently small open
neighborhood already agrees with the cohomology of `K`, and is the key
hypothesis allowing the direct-limit (Čech) cohomology to be identified
with a single representative. -/
def RegularNeighborhoodCondition
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P) : Prop :=
  ∀ i, ∃ j, i ≤ j ∧ Function.Bijective (g j)

/-- **Direct-limit isomorphism under the regular-neighborhood condition**
(Section 34).  If a compatible collection of maps `g i : G i → P` from a
directed system satisfies `RegularNeighborhoodCondition`, then the
canonical map `Module.DirectLimit.lift … g` from the colimit `colim G` to
`P` is *bijective*.  Geometrically, this lets us identify the Čech
cohomology of `K` (the colimit over neighborhoods) with the singular
cohomology of any sufficiently small regular neighborhood.  Surjectivity
follows from one bijective level, injectivity from the cofinality of such
levels. -/
theorem cech_cohomology_iso_of_regular_neighborhood_condition
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
    [DirectedSystem G (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hreg : RegularNeighborhoodCondition g) :
    Function.Bijective (Module.DirectLimit.lift R ι G f g hg) := by


  constructor
  ·


    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    simp only [Module.DirectLimit.lift_of] at hz
    obtain ⟨j, hij, hbij⟩ := hreg i
    have h1 : g j (f i j hij x) = 0 := by rw [hg]; exact hz
    have hfx : f i j hij x = 0 := hbij.1 (by rw [h1, map_zero])
    rw [Submodule.mem_bot]
    have : Module.DirectLimit.of R ι G f i x =
        Module.DirectLimit.of R ι G f j (f i j hij x) := by
      rw [Module.DirectLimit.of_f]
    rw [this, hfx, map_zero]
  ·


    intro x
    obtain ⟨i⟩ : Nonempty ι := inferInstance
    obtain ⟨j, _, hbij⟩ := hreg i
    obtain ⟨y, hy⟩ := hbij.2 x
    exact ⟨Module.DirectLimit.of R ι G f j y, by simp [hy]⟩

/-- **Linear equivalence form of the direct-limit isomorphism.**  Packaging
of `cech_cohomology_iso_of_regular_neighborhood_condition` as an honest
`R`-linear equivalence `Module.DirectLimit G f ≃ₗ[R] P` whenever the
`RegularNeighborhoodCondition` holds.  This is the form used downstream
when identifying Čech cohomology of a compact set with the singular
cohomology of a neighborhood. -/
def cechCohomologyLinearEquiv
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
    [DirectedSystem G (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hreg : RegularNeighborhoodCondition g) :
    Module.DirectLimit G f ≃ₗ[R] P :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift R ι G f g hg)
    (cech_cohomology_iso_of_regular_neighborhood_condition g hg hreg)

/-- **Open neighborhoods of a subset `K ⊂ X`.**  The type of pairs
`(U, hKU)` consisting of an open set `U : Opens X` together with a proof
that `K ⊆ U`.  Ordered by *reverse inclusion* (smaller neighborhoods are
"larger" in the poset), this indexes the directed system whose colimit
defines the Čech cohomology of `K`. -/
def OpenNeighborhoods {X : Type*} [TopologicalSpace X] (K : Set X) : Type _ :=
  { U : Opens X // K ⊆ U.1 }

/-- The reverse-inclusion preorder on open neighborhoods of `K`: `U ≤ V`
means `V ⊆ U`.  This is the standard convention so that "smaller
neighborhoods" come later, making the system *directed downward* and
inducing the correct directed colimit on cohomology. -/
instance openNeighborhoods_preorder {X : Type*} [TopologicalSpace X] (K : Set X) :
    Preorder (OpenNeighborhoods K) where
  le U V := V.1 ≤ U.1
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := le_trans h2 h1

/-- The poset of open neighborhoods of `K` is directed: any two
neighborhoods `U` and `V` are both refined by their intersection `U ∩ V`,
which is again open and still contains `K`. -/
instance openNeighborhoods_directed {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsDirected (OpenNeighborhoods K) (· ≤ ·) where
  directed U V := by
    refine ⟨⟨U.1 ⊓ V.1, ?_⟩, ?_, ?_⟩
    · intro x hx; exact ⟨U.2 hx, V.2 hx⟩
    · show U.1 ⊓ V.1 ≤ U.1; exact inf_le_left
    · show U.1 ⊓ V.1 ≤ V.1; exact inf_le_right

/-- The poset of open neighborhoods of `K` is nonempty: the ambient space
`X = ⊤` is always an open neighborhood of `K`. -/
instance openNeighborhoods_nonempty {X : Type*} [TopologicalSpace X] (K : Set X) :
    Nonempty (OpenNeighborhoods K) :=
  ⟨⟨⊤, fun _ _ => trivial⟩⟩

/-- **Neighborhood-retract property** of a subset `X ⊂ ℝⁿ`.  `X` is a
neighborhood retract when there exists an open neighborhood `U ⊇ X` and a
continuous retraction `r : U → X` (i.e. `r` restricted to `X` is the
identity).  Compact ANRs in `ℝⁿ` (in particular all compact topological
manifolds and CW complexes) have this property, which is the geometric
input that lets the Čech cohomology of `X` be computed by the singular
cohomology of a neighborhood. -/
def IsNeighborhoodRetract {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (_ : IsOpen U) (hXU : X ⊆ U)
    (r : ↥U → ↥X), Continuous r ∧ ∀ (x : ↥X), r ⟨x.1, hXU x.2⟩ = x

/-- **Inclusion of one neighborhood into a larger one.**  For two open
neighborhoods `U ≤ V` of `K` (so `V ⊆ U` in the reverse-inclusion
convention), the underlying-set inclusion `V ↪ U` is a morphism in `TopCat`.
This is the morphism whose restriction induces the structure map in the
directed system of cochain complexes used to define Čech cohomology. -/
def nbhdInclusion {X : Type*} [TopologicalSpace X] {K : Set X}
    {U V : OpenNeighborhoods K} (h : U ≤ V) : TopCat.of ↥V.1.1 ⟶ TopCat.of ↥U.1.1 :=
  ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- **Singular cohomology of a neighborhood `U` of `K`** in degree `p`,
with coefficients in `R`, packaged as a `ModuleCat R`.  This is the
typewise object that lives at index `U` in the directed system whose
colimit defines `cechCohomology R K p`. -/
def nbhdSingCohom (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] {K : Set X}
    (U : OpenNeighborhoods K) (p : ℕ) : ModuleCat.{0} R :=
  singularCohomology R (TopCat.of ↥U.1.1) (ModuleCat.of R R) p

/-- The underlying-type version of `nbhdSingCohom`, used so that the
direct-limit machinery (which works on plain types with `Module` structure)
can be applied to the family `U ↦ H^p(U; R)`. -/
def cechFamily (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) : Type :=
  (nbhdSingCohom R U p : Type _)

/-- Inherited abelian-group structure on each level of the Čech family,
forwarded from the `ModuleCat`-valued `nbhdSingCohom`. -/
instance cechFamily_addCommGroup (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) :
    AddCommGroup (cechFamily R K p U) :=
  (nbhdSingCohom R U p).isAddCommGroup

/-- Inherited `R`-module structure on each level of the Čech family,
forwarded from the `ModuleCat R`-valued `nbhdSingCohom`. -/
instance cechFamily_module (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) :
    Module R (cechFamily R K p U) :=
  (nbhdSingCohom R U p).isModule

/-- **Transition map in the Čech directed system.**  For `U ≤ V` (i.e.
`V ⊆ U`), the inclusion `V ↪ U` induces a restriction map on singular
cochain complexes, and the resulting map on cohomology is the structure
map `cechFamily R K p U →ₗ[R] cechFamily R K p V` of the directed system
whose colimit is `cechCohomology R K p`. -/
def cechTransition (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U V : OpenNeighborhoods K) (h : U ≤ V) :
    cechFamily R K p U →ₗ[R] cechFamily R K p V :=
  (HomologicalComplex.homologyMap
    (restrictionCochainMap R (ModuleCat.of R R) (nbhdInclusion h)) p).hom

/-- **Definition 34.4 (Čech cohomology of a subset).**  The Čech
cohomology `Ȟ^p(K; R)` of a subset `K ⊂ X` with coefficients in `R` is
defined as the *directed colimit* over all open neighborhoods `U ⊇ K` of
the singular cohomologies `H^p(U; R)`, with structure maps given by
restriction along the inclusions `V ↪ U` of smaller neighborhoods.  This
agrees with the singular cohomology of `K` whenever `K` is a sufficiently
nice subset (e.g. compact ENR), via the regular-neighborhood criterion. -/
def cechCohomology (R : Type) [CommRing R]
    {X : Type} [TopologicalSpace X] (K : Set X) (p : ℕ) : ModuleCat.{0} R := by
  classical
  exact ModuleCat.of R (Module.DirectLimit (cechFamily R K p)
    (fun U V h => cechTransition R K p U V h))

/-- **An open cover of a topological space `Y`.**  Data of a collection of
open subsets `members ⊂ Opens Y` whose union is all of `Y`.  The set of
open covers, ordered by *refinement*, indexes the directed system used in
the Čech-cover (nerve) construction of Čech cohomology — an alternative,
combinatorial description that agrees with the neighborhood definition
for sufficiently nice spaces. -/
structure OpenCover (Y : Type) [TopologicalSpace Y] where
  members : Set (Opens Y)
  covers : ∀ y : Y, ∃ U ∈ members, y ∈ (U : Set Y)

/-- **Refinement of open covers.**  `𝒱.Refines 𝒰` means every member of
`𝒱` is contained in some member of `𝒰`; equivalently, `𝒱` is "finer"
than `𝒰`.  This is the order on `OpenCover Y` used to form the directed
system computing nerve cohomology. -/
def OpenCover.Refines {Y : Type} [TopologicalSpace Y]
    (𝒱 𝒰 : OpenCover Y) : Prop :=
  ∀ V ∈ 𝒱.members, ∃ U ∈ 𝒰.members, (V : Set Y) ⊆ U

/-- The preorder on `OpenCover Y` where `𝒰 ≤ 𝒱` iff `𝒱` refines `𝒰`.
Reflexivity is the trivial self-refinement; transitivity composes
witnesses. -/
instance openCoverPreorder {Y : Type} [TopologicalSpace Y] :
    Preorder (OpenCover Y) where
  le 𝒰 𝒱 := 𝒱.Refines 𝒰
  le_refl 𝒰 := fun V hV => ⟨V, hV, le_refl _⟩
  le_trans _ _ _ h1 h2 := by
    intro W hW
    obtain ⟨V, hV, hWV⟩ := h2 W hW
    obtain ⟨U, hU, hVU⟩ := h1 V hV
    exact ⟨U, hU, hWV.trans hVU⟩














/-- **Topological version of the regular-neighborhood condition.**  A
specialization of `RegularNeighborhoodCondition` to the index category of
`OpenNeighborhoods K`: every neighborhood `U ⊇ K` admits a smaller
neighborhood `V ⊆ U` for which the comparison map `g V` is a bijection.
This is the form actually used to conclude that Čech cohomology equals
the cohomology of a sufficiently small regular neighborhood. -/
def TopologicalRegularNeighborhoodCondition
    {X : Type*} [TopologicalSpace X] {K : Set X}
    {R : Type*} [CommRing R]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P) : Prop :=
  ∀ U : OpenNeighborhoods K, ∃ V : OpenNeighborhoods K, U ≤ V ∧ Function.Bijective (g V)

/-- **Čech-cohomology isomorphism in the topological setting.**  For a
closed subset `K` of `X` and a compatible system `g U : H U → P` of maps
from a directed system indexed by open neighborhoods of `K`, the
condition `TopologicalRegularNeighborhoodCondition` implies that the
induced map from the colimit (the Čech cohomology) to `P` is a
bijection.  This is the central technical lemma used to identify
`Ȟ^p(K)` with the cohomology of a regular neighborhood. -/
theorem topological_cech_cohomology_iso
    {X : Type*} [TopologicalSpace X] {K : Set X} (_hK : IsClosed K)
    {R : Type*} [CommRing R] [DecidableEq (OpenNeighborhoods K)]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {ρ : ∀ U V : OpenNeighborhoods K, U ≤ V → H U →ₗ[R] H V}
    [DirectedSystem H (ρ · · ·)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P)
    (hcompat : ∀ U V (h : U ≤ V) x, g V (ρ U V h x) = g U x)
    (hreg : TopologicalRegularNeighborhoodCondition g) :
    Function.Bijective (Module.DirectLimit.lift R (OpenNeighborhoods K) H ρ g hcompat) :=
  cech_cohomology_iso_of_regular_neighborhood_condition g hcompat hreg

/-- **Linear-equivalence form of the topological Čech isomorphism.**
Packages `topological_cech_cohomology_iso` as an honest linear
equivalence `Module.DirectLimit H ρ ≃ₗ[R] P`. -/
def topologicalCechCohomologyLinearEquiv
    {X : Type*} [TopologicalSpace X] {K : Set X} (_hK : IsClosed K)
    {R : Type*} [CommRing R] [DecidableEq (OpenNeighborhoods K)]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {ρ : ∀ U V : OpenNeighborhoods K, U ≤ V → H U →ₗ[R] H V}
    [DirectedSystem H (ρ · · ·)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P)
    (hcompat : ∀ U V (h : U ≤ V) x, g V (ρ U V h x) = g U x)
    (hreg : TopologicalRegularNeighborhoodCondition g) :
    Module.DirectLimit H ρ ≃ₗ[R] P :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift R (OpenNeighborhoods K) H ρ g hcompat)
    (topological_cech_cohomology_iso _hK g hcompat hreg)

end CechCohomology

namespace CapProduct

variable (R : Type) [CommRing R]

/-- **Abstract cap-product pairing** (Section 34).  A bundled
specification of a cap-product: three `R`-modules (`CohomGrp`, the
"cohomology group" acting; and two "relative homology groups" `RelHomGrpN`
and `RelHomGrpQ`) together with a bilinear pairing
`cap : CohomGrp →ₗ[R] RelHomGrpN →ₗ[R] RelHomGrpQ`.  This abstracts the
algebraic structure of the cap product `H^p(Y; R) ⊗ H_{p+q}(Y, A) → H_q(Y, A)`
so that the projection-and-excision proof of Lemma 34.3 works at the level
of an axiomatic interface, free of singular-cohomology specifics. -/
structure CapProductPairing (R : Type) [CommRing R] where
  CohomGrp : Type
  [instCohomACG : AddCommGroup CohomGrp]
  [instCohomMod : Module R CohomGrp]
  RelHomGrpN : Type
  [instRelHomNACG : AddCommGroup RelHomGrpN]
  [instRelHomNMod : Module R RelHomGrpN]
  RelHomGrpQ : Type
  [instRelHomQACG : AddCommGroup RelHomGrpQ]
  [instRelHomQMod : Module R RelHomGrpQ]
  cap : CohomGrp →ₗ[R] RelHomGrpN →ₗ[R] RelHomGrpQ

attribute [instance] CapProductPairing.instCohomACG CapProductPairing.instCohomMod
  CapProductPairing.instRelHomNACG CapProductPairing.instRelHomNMod
  CapProductPairing.instRelHomQACG CapProductPairing.instRelHomQMod

/-- **Geometrically situated cap-product pairing.**  A
`CapProductPairing` tagged with the data of an open set `Y` and a subset
`K ⊆ Y` in some ambient space `X`; this provides the geometric context
(open set, compact subset, etc.) needed for the excision-and-projection
argument used in Lemma 34.3. -/
structure CapProductPairingOf (R : Type) [CommRing R]
    {X : Type*} [TopologicalSpace X] (Y K : Set X) (hY : IsOpen Y) (hK : K ⊆ Y)
    extends CapProductPairing R

/-- **Abstract excision data.**  When `V ⊆ U` are two open subsets both
containing `K`, the inclusion-induced relative-homology maps
`H_*(V, V \ K) → H_*(U, U \ K)` are isomorphisms (excision); the
`ExcisionData` bundles the *inverse* linear maps as opaque morphisms,
without yet requiring them to be specific singular-homology
isomorphisms.  This is what lets the abstract Lemma 34.3 talk about
excision without proving it. -/
structure ExcisionData (R : Type) [CommRing R]
    {X : Type*} [TopologicalSpace X] {K U V : Set X}
    (hK : IsClosed K) (hVU : V ⊆ U)
    (pairU : CapProductPairing R) (pairV : CapProductPairing R) where
  excInvN : pairU.RelHomGrpN →ₗ[R] pairV.RelHomGrpN
  excInvQ : pairU.RelHomGrpQ →ₗ[R] pairV.RelHomGrpQ

/-- **Abstract projection formula.**  For two cap-product pairings
`pairY, pairZ` representing the cap products on a "smaller" space `Y` and
a "larger" space `Z`, this structure bundles a pullback on cohomology
together with pushforwards on the two relative-homology groups, such that
the diagram `f_*(f^*b ⌢ x) = b ⌢ f_*x` commutes.  This is the algebraic
content of the projection (naturality) formula for the cap product. -/
structure ProjectionFormula (R : Type) [CommRing R]
    (pairY pairZ : CapProductPairing R) where
  pullback : pairZ.CohomGrp →ₗ[R] pairY.CohomGrp
  pushforwardN : pairY.RelHomGrpN →ₗ[R] pairZ.RelHomGrpN
  pushforwardQ : pairY.RelHomGrpQ →ₗ[R] pairZ.RelHomGrpQ
  formula : ∀ (b : pairZ.CohomGrp) (x : pairY.RelHomGrpN),
    pushforwardQ (pairY.cap (pullback b) x) = pairZ.cap b (pushforwardN x)

end CapProduct

namespace CapProduct

variable (R : Type) [CommRing R]

/-- **Abstract form of Lemma 34.3 (cap product commutes with
restriction).**  Given two cap-product pairings on neighborhoods `V ⊆ U`
of `K`, an abstract projection formula linking them, and excision data
witnessing the isomorphism `H_*(V, V \ K) ≃ H_*(U, U \ K)`, the
following diagram commutes: capping in `U` and then excising equals
restricting in cohomology and capping in `V`.  This is the algebraic
skeleton used to prove that the cap product passes to the Čech-cohomology
colimit. -/
theorem cap_product_restriction_commutes_abstract
    {X : Type*} [TopologicalSpace X] {K U V : Set X}
    (hK : IsClosed K) (hU : IsOpen U) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVU : V ⊆ U)
    (pairU : CapProductPairingOf R U K hU (hKV.trans hVU))
    (pairV : CapProductPairingOf R V K hV hKV)
    (ι : ProjectionFormula R pairV.toCapProductPairing pairU.toCapProductPairing)
    (exc : ExcisionData R hK hVU pairU.toCapProductPairing pairV.toCapProductPairing)
    (hexcN : Function.RightInverse exc.excInvN ι.pushforwardN)
    (hexcQ : Function.LeftInverse exc.excInvQ ι.pushforwardQ)
    (b : pairU.CohomGrp) (x : pairU.RelHomGrpN) :
    exc.excInvQ (pairU.cap b x) = pairV.cap (ι.pullback b) (exc.excInvN x) := by

  have h_push_inv : ι.pushforwardN (exc.excInvN x) = x := hexcN x
  have h_proj := ι.formula b (exc.excInvN x)
  rw [h_push_inv] at h_proj


  rw [← h_proj]
  exact hexcQ _

/-- **Relative singular homology** `H_n(Y, A; R)`, packaged as a
`ModuleCat R`.  Defined as the homology in degree `n` of the *cokernel*
chain complex `C_*(Y) / C_*(A)`, where the inclusion `A ↪ Y` induces a
chain map between singular-chain complexes.  This is the standard
"relative chain complex" construction. -/
noncomputable def relativeSingularHomologyModule
    (R : Type) [CommRing R] (Y : TopCat.{0}) (A : Set Y) (n : ℕ) : ModuleCat.{0} R :=
  let incl : TopCat.of A ⟶ Y := ⟨Subtype.val, continuous_subtype_val⟩
  let chainMap := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).map incl
  (CategoryTheory.Limits.cokernel chainMap).homology n





/-- **Pushforward map on relative singular homology.**  A continuous map
`f : Y → Z` with `f(A) ⊆ B` induces a chain map of relative chain
complexes and hence a linear map `H_n(Y, A) → H_n(Z, B)`.  When `f` does
*not* send `A` into `B`, the convention here is to return the zero map
(so the definition is total). -/
def relativePushforwardMap
    (R : Type) [CommRing R] {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (A : Set Y) (B : Set Z) (n : ℕ) :
    (relativeSingularHomologyModule R Y A n : Type) →ₗ[R]
    (relativeSingularHomologyModule R Z B n : Type) := by
  classical
  by_cases hf : Set.MapsTo f A B
  · let f_A : TopCat.of A ⟶ TopCat.of B :=
      ⟨fun a => ⟨f a.val, hf a.property⟩, by fun_prop⟩
    let SCF := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R))
    have comm : SCF.map (show TopCat.of A ⟶ Y from ⟨Subtype.val, continuous_subtype_val⟩) ≫
        SCF.map f =
        SCF.map f_A ≫
        SCF.map (show TopCat.of B ⟶ Z from ⟨Subtype.val, continuous_subtype_val⟩) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
    exact (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.map _ _ (SCF.map f_A) (SCF.map f) comm) n).hom
  · exact 0
















open Simplicial in

/-- **Front face of a `(p+q)`-simplex.**  The "first-`(p+1)`-vertices"
inclusion `[p] ↪ [p+q]` of simplicial objects, sending `i ↦ i`.
Geometrically, restricts a `(p+q)`-simplex to the affine face spanned by
its first `p+1` vertices.  Used as the front-cup half of the cap-product
chain-level formula `(β ⌢ σ) = β(front)·back`. -/
def frontFace (p q : ℕ) : (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun i => Fin.castLE (by omega) i, fun _ _ h => h⟩

open Simplicial in
/-- **Back face of a `(p+q)`-simplex.**  The "last-`(q+1)`-vertices"
inclusion `[q] ↪ [p+q]`, sending `j ↦ j + p`.  Restricts a
`(p+q)`-simplex to the affine face spanned by its last `q+1` vertices.
This is the back-cup half of the cap-product chain-level formula. -/
def backFace (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun j => ⟨j.val + p, by omega⟩,
    fun a b (h : a ≤ b) => show a.val + p ≤ b.val + p by omega⟩

/-- **Singular chain complex of a topological space.**  Abbreviation for
the singular chain complex `C_*(X; R)` of `X` with coefficients in `R`,
viewed as a chain complex of `ModuleCat R`-objects indexed by `ℕ`.
Computed via Mathlib's `singularChainComplexFunctor`. -/
abbrev singularChainCx (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

/-- **The set of singular `n`-simplices of `X`.**  Continuous maps
`Δⁿ → X`, i.e. the `n`-cells of `Sing(X)`.  This is the underlying index
type for the free `R`-module of singular `n`-chains. -/
abbrev singularSimplices (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

open CategoryTheory.Limits in
/-- **The free simplicial `R`-module on the singular simplicial set of
`X`.**  Levelwise: the free `R`-module on `singularSimplices X n`.  Its
associated (alternating-sum) chain complex is the usual singular chain
complex `singularChainCx R X`. -/
abbrev freeSimplicialModule (R : Type) [CommRing R] (X : TopCat.{0}) :
    SimplicialObject (ModuleCat.{0} R) :=
  ((SimplicialObject.whiskering (Type 0) (ModuleCat.{0} R)).obj
    (sigmaConst.obj (ModuleCat.of R R))).obj (TopCat.toSSet.obj X)

open CategoryTheory.Limits in
/-- **Compatibility of face maps with the augmentation.**  Both face
maps `δ 0` and `δ 1` of the free simplicial module, when composed with
the augmentation `C_0 → R` collapsing each 0-simplex to `1`, yield the
augmentation on 1-simplices (which simply collapses each 1-simplex to
`1`).  This is the basic identity behind the augmentation chain map. -/
lemma freeSimplicialModule_δ_comp_aug (R : Type) [CommRing R] (X : TopCat.{0}) (i : Fin 2) :
    (freeSimplicialModule R X).δ i ≫
      Limits.Sigma.desc (fun (_ : singularSimplices X 0) => 𝟙 (ModuleCat.of R R)) =
    Limits.Sigma.desc (fun (_ : singularSimplices X 1) => 𝟙 (ModuleCat.of R R)) := by
  have hδ : (freeSimplicialModule R X).δ i =
    (sigmaConst.obj (ModuleCat.of R R)).map ((TopCat.toSSet.obj X).δ i) := rfl
  rw [hδ, sigmaConst_obj_map]
  apply Sigma.hom_ext
  intro σ
  simp [Sigma.ι_comp_map'_assoc, Sigma.ι_desc]

open CategoryTheory.Limits in
open Simplicial CategoryTheory.Limits in
/-- **Cap product at the chain level.**  For a `p`-cochain
`β : C_p(X) → R` and a singular `(p+q)`-simplex `σ`, the cap product
`β ⌢ σ` is defined as `β(σ ∘ frontFace) · (σ ∘ backFace)`, a singular
`q`-simplex (or rather, an element of `C_q(X)`).  This is the standard
chain-level cap product, expressed here in the language of free modules
on simplices. -/
def capProductChainMap (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (β : (singularChainCx R X).X p ⟶ ModuleCat.of R R) :
    (singularChainCx R X).X (p + q) ⟶ (singularChainCx R X).X q :=
  Sigma.desc (fun (σ : singularSimplices X (p + q)) =>
    let σ_front : singularSimplices X p :=
      (TopCat.toSSet.obj X).map (frontFace p q).op σ
    let σ_back : singularSimplices X q :=
      (TopCat.toSSet.obj X).map (backFace p q).op σ


    (Sigma.ι (fun (_ : singularSimplices X p) => ModuleCat.of R R) σ_front ≫ β) ≫
      Sigma.ι (fun (_ : singularSimplices X q) => ModuleCat.of R R) σ_back)










/-- **Kronecker pairing** `⟨·, ·⟩ : H^n(X; R) × H_n(X; R) → R`.
The classical evaluation pairing of a singular `n`-cochain on an
`n`-cycle, descended to cohomology/homology.  Re-exposed here from
Mathlib's `SingularCohomology.kroneckerPairing` for use in
`augmentation_cap_eq_kronecker` and the adjointness formula for cup/cap. -/
def kroneckerPairing
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X n : Type) →ₗ[R] R :=
  SingularCohomology.kroneckerPairing R X n


/-- **Augmentation** `ε : H_0(X; R) → R`.  The map descended from the
chain-level augmentation `C_0(X) → R` (which collapses each 0-simplex to
`1`).  Equal to the unique map induced by `X → pt` on `H_0`, and equal
to `1 ⌢ ·` ↦ `1` via the unit relation. -/
def augmentation (R : Type) [CommRing R] (X : TopCat.{0}) :
    (SingularCohomology.singularHomologyModule R X 0 : Type) →ₗ[R] R :=
  (augmentationH0 R X).hom


/-- **Pushforward on singular homology**, `f_* : H_n(X; R) → H_n(Y; R)`.
Functoriality of singular homology in the topological space, as a
`ModuleCat`-morphism.  Used in the projection formula for the cap
product. -/
def pushforwardMap' (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    SingularCohomology.singularHomologyModule R X n ⟶
    SingularCohomology.singularHomologyModule R Y n :=
  ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).map f

/-- **Pullback on singular cohomology**, `f^* : H^n(Y; R) → H^n(X; R)`.
Contravariant functoriality of singular cohomology in the topological
space.  Used in the projection formula for the cap product. -/
def pullbackMap
    (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (SingularCohomology.singularCohomology R Y (ModuleCat.of R R) n : Type) →ₗ[R]
    (SingularCohomology.singularCohomology R X (ModuleCat.of R R) n : Type) :=
  (SingularCohomology.singularCohomologyMap R f n).hom



























end CapProduct

namespace PoincareDualityCompact

open CategoryTheory

/-- **`R`-orientability of an `n`-manifold `M`.**  A typeclass wrapping
`OrientationHomology.IsROrientable n M R`: there exists a continuous
choice of local generators of `H_n(M, M ∖ {x}; R) ≅ R` over all `x ∈ M`.
This is the standard hypothesis for compact Poincaré duality with
coefficients in `R`. -/
class IsROriented (R : Type) [CommRing R] (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  isROrientable : OrientationHomology.IsROrientable n M R






end PoincareDualityCompact

namespace CechCohomology




end CechCohomology
