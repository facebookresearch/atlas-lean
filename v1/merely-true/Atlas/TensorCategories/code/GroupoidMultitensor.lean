/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi

set_option maxHeartbeats 800000

open CategoryTheory

universe u v w

namespace GroupoidMultitensor

/-- A finite groupoid presented combinatorially as objects `Obj`, morphisms `Mor`, source/target
maps, composition (defined when `tgt g = src h`), identity, and inverse, all subject to the
expected groupoid relations. -/
structure FiniteGroupoidData where
  Obj : Type u
  Mor : Type v
  [finObj : Fintype Obj]
  [finMor : Fintype Mor]
  [decEqObj : DecidableEq Obj]
  [decEqMor : DecidableEq Mor]
  src : Mor → Obj
  tgt : Mor → Obj
  comp : (g h : Mor) → tgt g = src h → Mor
  id : Obj → Mor
  inv : Mor → Mor
  src_id : ∀ x, src (id x) = x
  tgt_id : ∀ x, tgt (id x) = x
  src_comp : ∀ g h (p : tgt g = src h), src (comp g h p) = src g
  tgt_comp : ∀ g h (p : tgt g = src h), tgt (comp g h p) = tgt h
  src_inv : ∀ g, src (inv g) = tgt g
  tgt_inv : ∀ g, tgt (inv g) = src g

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor
attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

/-- The groupoid `G` has a single object (its object set has cardinality `1`). -/
def FiniteGroupoidData.IsSingleObject (G : FiniteGroupoidData) : Prop :=
  Fintype.card G.Obj = 1

/-- The number of objects of the finite groupoid `G`. -/
noncomputable def FiniteGroupoidData.numObjects (G : FiniteGroupoidData) : ℕ :=
  Fintype.card G.Obj

/-- The subtype of morphisms of `G` between two specified objects. -/
def FiniteGroupoidData.MorBetween (G : FiniteGroupoidData) (x y : G.Obj) : Type v :=
  { g : G.Mor // G.src g = y ∧ G.tgt g = x }

/-- The identity-morphism map `Obj → Mor` of a groupoid is injective. -/
theorem FiniteGroupoidData.id_injective (G : FiniteGroupoidData) :
    Function.Injective G.id := by
  intro x y h
  have hx := G.src_id x
  have hy := G.src_id y
  rw [h] at hx
  rw [← hx, hy]

/-- The image of the identity map: the set of identity morphisms, one per object. -/
def FiniteGroupoidData.unitComponents (G : FiniteGroupoidData) : Finset G.Mor :=
  Finset.univ.image G.id

/-- The groupoid has a single connected component contributing to the unit, i.e. only one
identity morphism. -/
def FiniteGroupoidData.HasSimpleUnit (G : FiniteGroupoidData) : Prop :=
  G.unitComponents.card = 1

/-- The cardinality of `unitComponents` equals the number of objects of `G`. -/
theorem FiniteGroupoidData.unitComponents_card (G : FiniteGroupoidData) :
    G.unitComponents.card = Fintype.card G.Obj := by
  simp [unitComponents, Finset.card_image_of_injective _ G.id_injective]

/-- The algebra of endomorphisms of the unit object for the groupoid-graded `k`-vector space
category: pointwise scalars indexed by objects of `G`. -/
abbrev FiniteGroupoidData.EndUnit (G : FiniteGroupoidData) (k : Type w) [Field k] :=
  G.Obj → k

/-- The dimension of `EndUnit` equals the number of objects of `G`. -/
theorem FiniteGroupoidData.finrank_endUnit (G : FiniteGroupoidData) (k : Type w) [Field k] :
    Module.finrank k (G.EndUnit k) = Fintype.card G.Obj :=
  Module.finrank_pi k

/-- The endomorphism algebra of the unit has dimension `1` iff the groupoid has a single
object — the criterion separating tensor from multitensor categories. -/
theorem FiniteGroupoidData.endUnit_iso_k_iff_singleObject (G : FiniteGroupoidData)
    (k : Type w) [Field k] :
    Module.finrank k (G.EndUnit k) = 1 ↔ G.IsSingleObject := by
  unfold IsSingleObject
  rw [G.finrank_endUnit k]

/-- If `G` has a single object, `EndUnit k` is `k`-linearly equivalent to `k`. -/
noncomputable def FiniteGroupoidData.endUnitLinearEquivOfSingleObject
    (G : FiniteGroupoidData) (k : Type w) [Field k]
    (h : G.IsSingleObject) : G.EndUnit k ≃ₗ[k] k := by
  have : Nonempty (Unique G.Obj) := Fintype.card_eq_one_iff_nonempty_unique.mp h
  letI := this.some
  exact LinearEquiv.funUnique G.Obj k k

/-- If `G` has a single object, `EndUnit k` is `k`-algebra-equivalent to `k`. -/
noncomputable def FiniteGroupoidData.endUnitAlgEquivOfSingleObject
    (G : FiniteGroupoidData) (k : Type w) [Field k]
    (h : G.IsSingleObject) : G.EndUnit k ≃ₐ[k] k := by
  have : Nonempty (Unique G.Obj) := Fintype.card_eq_one_iff_nonempty_unique.mp h
  letI := this.some
  exact AlgEquiv.funUnique k G.Obj k

/-- If `G` has more than one object, `EndUnit k` has dimension greater than one. -/
theorem FiniteGroupoidData.endUnit_dim_gt_one_of_multipleObjects
    (G : FiniteGroupoidData) (k : Type w) [Field k]
    (h : 1 < Fintype.card G.Obj) :
    1 < Module.finrank k (G.EndUnit k) := by
  rw [G.finrank_endUnit k]
  exact h

/-- View a finite group as the single-object groupoid whose morphisms are the group elements. -/
def groupAsGroupoidData (G : Type u) [Group G] [Fintype G] [DecidableEq G] :
    FiniteGroupoidData.{0, u} where
  Obj := Unit
  Mor := G
  src := fun _ => ()
  tgt := fun _ => ()
  comp := fun g h _ => g * h
  id := fun _ => 1
  inv := fun g => g⁻¹
  src_id := fun _ => rfl
  tgt_id := fun _ => rfl
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun _ _ _ => rfl
  src_inv := fun _ => rfl
  tgt_inv := fun _ => rfl

/-- The pair groupoid on a finite set `X`: objects are points of `X`, with a unique morphism
between any two of them. -/
def pairGroupoidData (X : Type u) [Fintype X] [DecidableEq X] :
    FiniteGroupoidData.{u, u} where
  Obj := X
  Mor := X × X
  src := Prod.fst
  tgt := Prod.snd
  comp := fun g h _ => (g.1, h.2)
  id := fun x => (x, x)
  inv := fun g => (g.2, g.1)
  src_id := fun _ => rfl
  tgt_id := fun _ => rfl
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun _ _ _ => rfl
  src_inv := fun _ => rfl
  tgt_inv := fun _ => rfl

/-- The transformation groupoid `X ⋊ G` associated with a finite group acting on a finite set:
objects are points of `X`, morphisms are pairs `(g, x)` from `x` to `g • x`. -/
def transformationGroupoidData (G : Type u) (X : Type u)
    [Group G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]
    [MulAction G X] :
    FiniteGroupoidData.{u, u} where
  Obj := X
  Mor := G × X
  src := fun p => p.2
  tgt := fun p => p.1 • p.2
  comp := fun g h _ => (h.1 * g.1, g.2)
  id := fun x => (1, x)
  inv := fun p => (p.1⁻¹, p.1 • p.2)
  src_id := fun _ => rfl
  tgt_id := fun x => by simp
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun g h p => by
    simp only
    rw [mul_smul, p]
  src_inv := fun _ => rfl
  tgt_inv := fun p => by simp

/-- A groupoid-graded vector space: assignment of a `k`-vector space to each morphism of `G`.
The categories of such gradings model multitensor categories arising from groupoids. -/
structure GroupoidGradedVecData (k : Type w) [Field k]
    (G : FiniteGroupoidData.{u, v}) where
  component : G.Mor → Type w
  [instAddCommMonoid : ∀ g, AddCommMonoid (component g)]
  [instModule : ∀ g, Module k (component g)]

attribute [instance] GroupoidGradedVecData.instAddCommMonoid GroupoidGradedVecData.instModule

/-- A morphism `g` is a unit-component iff it equals some identity morphism `G.id x`. -/
def GroupoidGradedVecData.isUnitComponent (G : FiniteGroupoidData) (g : G.Mor) : Prop :=
  ∃ x : G.Obj, g = G.id x

/-- Grading shift for the dual object: invert the morphism. -/
def GroupoidGradedVecData.dualGrading (G : FiniteGroupoidData) (g : G.Mor) : G.Mor :=
  G.inv g

/-- Category structure on `GroupoidGradedVecData k G`: a morphism is a family of `k`-linear
maps between the components indexed by morphisms of `G`. -/
@[reducible]
def ggvCategoryInstance (k : Type w) [Field k] (G : FiniteGroupoidData.{u, v}) :
    Category.{max v w} (GroupoidGradedVecData k G) where
  Hom V W := ∀ g : G.Mor, V.component g →ₗ[k] W.component g
  id V g := LinearMap.id
  comp f g h := (g h).comp (f h)
  id_comp f := by funext g; simp [LinearMap.comp_id]
  comp_id f := by funext g; simp [LinearMap.id_comp]
  assoc f g h := by funext i; rfl


/-- Matrix-valued vector space data: a `k`-vector space `component i j` assigned to each
`(i, j)` index pair in `Fin n × Fin n`. -/
structure MatrixVecData (k : Type w) [Field k] (n : ℕ) where
  component : Fin n → Fin n → Type w
  [instAddCommMonoid : ∀ i j, AddCommMonoid (component i j)]
  [instModule : ∀ i j, Module k (component i j)]

attribute [instance] MatrixVecData.instAddCommMonoid MatrixVecData.instModule

/-- Category structure on `MatrixVecData k n`: morphisms are entrywise linear maps. -/
@[reducible]
def matVecCategoryInstance (k : Type w) [Field k] (n : ℕ) :
    Category.{w} (MatrixVecData k n) where
  Hom V W := ∀ i j, V.component i j →ₗ[k] W.component i j
  id V i j := LinearMap.id
  comp f g i j := (g i j).comp (f i j)
  id_comp f := by funext i j; simp [LinearMap.comp_id]
  comp_id f := by funext i j; simp [LinearMap.id_comp]
  assoc f g h := by funext i j; rfl


/-- The product of `m` matrix-group-graded vector space datas: for each `i` we have a matrix
indexed by `Fin (n i) × Fin (n i)` further graded by elements of `G i`. -/
structure ProductMatrixGroupVecData (k : Type w) [Field k]
    {m : ℕ}
    (n : Fin m → ℕ)
    (G : (i : Fin m) → Type w)
    [∀ i, Group (G i)]
    [∀ i, Fintype (G i)]
    [∀ i, DecidableEq (G i)] where
  component : (i : Fin m) → Fin (n i) → Fin (n i) → G i → Type w
  [instAddCommMonoid : ∀ i j₁ j₂ g, AddCommMonoid (component i j₁ j₂ g)]
  [instModule : ∀ i j₁ j₂ g, Module k (component i j₁ j₂ g)]

attribute [instance] ProductMatrixGroupVecData.instAddCommMonoid
attribute [instance] ProductMatrixGroupVecData.instModule

/-- Category structure on `ProductMatrixGroupVecData` with componentwise linear maps. -/
@[reducible]
def pmgvCategoryInstance (k : Type w) [Field k]
    {m : ℕ} (n : Fin m → ℕ)
    (G : (i : Fin m) → Type w)
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] :
    Category.{w} (ProductMatrixGroupVecData k n G) where
  Hom V W := ∀ (i : Fin m) (j₁ j₂ : Fin (n i)) (g : G i),
    V.component i j₁ j₂ g →ₗ[k] W.component i j₁ j₂ g
  id V i j₁ j₂ g := LinearMap.id
  comp f h i j₁ j₂ g := (h i j₁ j₂ g).comp (f i j₁ j₂ g)
  id_comp f := by funext i j₁ j₂ g; simp [LinearMap.comp_id]
  comp_id f := by funext i j₁ j₂ g; simp [LinearMap.id_comp]
  assoc f g h := by funext i j₁ j₂ gg; rfl


/-- Two monoidal categories `C` and `D` are monoidally equivalent if there is an equivalence
between them whose forward functor carries a lax monoidal structure. -/
def AreMonoidallyEquivalent
    (C : Type*) (catC : Category C) (monC : @MonoidalCategory C catC)
    (D : Type*) (catD : Category D) (monD : @MonoidalCategory D catD) : Prop :=
  ∃ (E : @Equivalence C D catC catD),
    Nonempty (@Functor.LaxMonoidal C catC monC D catD monD E.functor)



/-- The grading set indexing the `(x, y)` component subcategory: morphisms in `G` from `y` to `x`. -/
def componentSubcategoryGrading (G : FiniteGroupoidData) (x y : G.Obj) :=
  G.MorBetween x y

/-- Bridge from a Mathlib `Groupoid` instance with finite Hom sets to `FiniteGroupoidData`. -/
noncomputable def fromMathlibGroupoid (X : Type u) [Fintype X] [DecidableEq X]
    [CategoryTheory.Groupoid X]
    [∀ (x y : X), Fintype (x ⟶ y)]
    [∀ (x y : X), DecidableEq (x ⟶ y)] :
    FiniteGroupoidData.{u, max u v} where
  Obj := X
  Mor := Σ (p : X × X), (p.1 ⟶ p.2)
  finObj := inferInstance
  finMor := inferInstance
  decEqObj := inferInstance
  decEqMor := inferInstance
  src := fun g => g.1.1
  tgt := fun g => g.1.2
  comp := fun g h p => by
    refine ⟨(g.1.1, h.1.2), ?_⟩
    have : g.1.2 = h.1.1 := p
    exact g.2 ≫ (this ▸ h.2)
  id := fun x => ⟨(x, x), 𝟙 x⟩
  inv := fun g => ⟨(g.1.2, g.1.1), CategoryTheory.Groupoid.inv g.2⟩
  src_id := fun _ => rfl
  tgt_id := fun _ => rfl
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun _ _ _ => rfl
  src_inv := fun _ => rfl
  tgt_inv := fun _ => rfl

end GroupoidMultitensor
