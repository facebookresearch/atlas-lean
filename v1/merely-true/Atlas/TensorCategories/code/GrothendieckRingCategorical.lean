/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.GrothendieckRing
import Atlas.TensorCategories.code.TensorCategoryDef
import Atlas.TensorCategories.code.Prop_1_45_10

open CategoryTheory MonoidalCategory Limits Finset
open TensorCategories

universe v u

/-- Categorical fusion data for a `κ`-linear abelian rigid monoidal category `C`: a finite
indexing of representatives `S i` of simples, fusion coefficients `N`, duality involution,
and Jordan-Hölder multiplicities `mult` compatible with the unit, tensor product and
isomorphisms. -/
class CategoricalFusionData (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C] where
  ι : Type
  [ι_fintype : Fintype ι]
  [ι_deceq : DecidableEq ι]
  S : ι → C
  S_simple : ∀ i, Simple (S i)
  S_complete : ∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ S i)
  S_distinct : ∀ i j, Nonempty (S i ≅ S j) → i = j
  unitIdx : ι
  unitIso : Nonempty (S unitIdx ≅ 𝟙_ C)
  N : ι → ι → ι → ℕ
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  N_unit_mul : ∀ j k, N unitIdx j k = if j = k then 1 else 0
  N_mul_unit : ∀ i k, N i unitIdx k = if i = k then 1 else 0
  N_duality : ∀ i j, N i j unitIdx = if j = star i then 1 else 0
  N_assoc : ∀ i j m l, ∑ p : ι, N i j p * N p m l = ∑ p : ι, N j m p * N i p l
  N_star_transpose : ∀ i j k, N i j k = N (star i) k j
  N_eq_finrank : ∀ i j k, N i j k = Module.finrank κ (S k ⟶ (S i ⊗ S j))
  mult : C → ι → ℕ
  mult_simple : ∀ i j, mult (S i) j = if i = j then 1 else 0
  mult_unit : ∀ j, mult (𝟙_ C) j = if j = unitIdx then 1 else 0
  mult_tensor : ∀ (X Y : C) (l : ι),
    mult (X ⊗ Y) l = ∑ i : ι, ∑ j : ι, mult X i * mult Y j * N i j l
  mult_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → ∀ i, mult X i = mult Y i
  mult_nontrivial : ∀ (X : C), ∃ i, 0 < mult X i

namespace CategoricalFusionData

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]
variable [cfd : CategoricalFusionData κ C]


attribute [reducible, instance] CategoricalFusionData.ι_fintype CategoricalFusionData.ι_deceq

/-- The combinatorial `FusionRing` (Definition 1.42.2 / Proposition 1.42.4) extracted from
the categorical fusion data on `C`. -/
def toFusionRing : FusionRing cfd.ι where
  unit := cfd.unitIdx
  N := cfd.N
  star := cfd.star
  star_star := cfd.star_star
  unit_mul := cfd.N_unit_mul
  mul_unit := cfd.N_mul_unit
  duality := cfd.N_duality
  assoc := cfd.N_assoc
  N_star_transpose := cfd.N_star_transpose

/-- Abbreviation for the underlying additive group `K₀` of the Grothendieck ring obtained
from the categorical fusion data on `C`. -/
abbrev GrothendieckRingK0 : Type :=
  FusionRing.GrRingOf (toFusionRing (κ := κ) (C := C))

/-- Ring structure on `GrothendieckRingK0`, inherited from the fusion ring construction. -/
instance grothendieckRingK0_ring : Ring (GrothendieckRingK0 (κ := κ) (C := C)) :=
  FusionRing.GrRingOf.instRing

/-- The basis class in the Grothendieck ring corresponding to the simple object `S i`. -/
def basisClass (i : cfd.ι) : GrothendieckRingK0 (κ := κ) (C := C) :=
  ⟨FusionRing.basisVec i⟩

/-- The coefficient at `l` of the product of two basis classes equals the fusion coefficient
`N i j l`. -/
theorem basisClass_mul_coeff (i j l : cfd.ι) :
    (basisClass (κ := κ) (C := C) i * basisClass j).coeff l = (cfd.N i j l : ℤ) := by
  show FusionRing.grMul (toFusionRing (κ := κ) (C := C))
    (FusionRing.basisVec i) (FusionRing.basisVec j) l = (cfd.N i j l : ℤ)
  simp only [FusionRing.grMul, FusionRing.basisVec, toFusionRing]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

end CategoricalFusionData

namespace RepZ2Categorical

open FusionRing

/-- Fusion coefficients for `Rep(ℤ/2)`: a one-dimensional Hom space iff `i + j ≡ k (mod 2)`. -/
def N_categorical (i j k : Fin 2) : ℕ :=
  if (i.val + j.val) % 2 = k.val then 1 else 0

end RepZ2Categorical

namespace FusionCategoryBridge

open CategoricalFusionData FusionRing

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]
variable [cfd : CategoricalFusionData κ C]

/-- Alternative name for the basis class of the simple `S i` in the Grothendieck ring,
used by the fusion-category bridge. -/
def simpleClass (i : cfd.ι) : GrRingOf (toFusionRing (κ := κ) (C := C)) :=
  ⟨basisVec i⟩

/-- Coefficient formula for products of simple classes via the fusion-category bridge. -/
theorem simpleClass_mul_coeff (i j l : cfd.ι) :
    (simpleClass (κ := κ) (C := C) i * simpleClass j).coeff l = (cfd.N i j l : ℤ) := by
  show grMul (toFusionRing (κ := κ) (C := C)) (basisVec i) (basisVec j) l = (cfd.N i j l : ℤ)
  simp only [grMul, basisVec, toFusionRing]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']

end FusionCategoryBridge

/-- Definition 1.42.2(1): A based ring on the basis `ι`: fusion coefficients, a unit subset
`I₀`, an involution `star`, associativity, and the duality / antiautomorphism axioms. -/
structure BasedRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l
  sum_I₀_mul_left : ∀ j k, (∑ s ∈ I₀, N s j k) = if j = k then 1 else 0
  sum_I₀_mul_right : ∀ i k, (∑ s ∈ I₀, N i s k) = if i = k then 1 else 0
  duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)

/-- A based ring is unital (Definition 1.42.2(2)) if `1` itself belongs to the basis,
i.e. `I₀` is a singleton. -/
def BasedRing.IsUnital {ι : Type*} [DecidableEq ι] [Fintype ι]
    (B : BasedRing ι) : Prop :=
  ∃ u : ι, B.I₀ = {u}

/-- A `UnitalBasedRing` is a based ring together with a distinguished basis element `unitElem`
which is the unique element of `I₀`. -/
structure UnitalBasedRing (ι : Type*) [DecidableEq ι] [Fintype ι]
    extends BasedRing ι where
  unitElem : ι
  I₀_eq_singleton : I₀ = {unitElem}

/-- Categorical multitensor data for a `κ`-linear monoidal preadditive category `C`: a finite
set of representatives `S i` of simples together with fusion coefficients `N`, a unit set `I₀`,
involution and the based-ring axioms. Used to model multitensor (not necessarily tensor)
categories. -/
class CategoricalMultitensorData (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C]
    [MonoidalCategory C] [MonoidalPreadditive C] where
  ι : Type
  [ι_fintype : Fintype ι]
  [ι_deceq : DecidableEq ι]
  S : ι → C
  S_simple : ∀ i, Simple (S i)
  N : ι → ι → ι → ℕ
  N_eq_finrank : ∀ i j k, N i j k = Module.finrank κ (S k ⟶ (S i ⊗ S j))
  I₀ : Finset ι
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  N_assoc : ∀ i j m l, ∑ p : ι, N i j p * N p m l = ∑ p : ι, N j m p * N i p l
  N_sum_I₀_mul_left : ∀ j k, (∑ p ∈ I₀, N p j k) = if j = k then 1 else 0
  N_sum_I₀_mul_right : ∀ i k, (∑ p ∈ I₀, N i p k) = if i = k then 1 else 0
  N_duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  N_star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)

namespace CategoricalMultitensorData

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C]
  [MonoidalCategory C] [MonoidalPreadditive C]
variable [cmd : CategoricalMultitensorData κ C]


attribute [reducible, instance] CategoricalMultitensorData.ι_fintype
  CategoricalMultitensorData.ι_deceq

/-- Extract a `BasedRing` from `CategoricalMultitensorData`, realising the Grothendieck
based ring of a multitensor category. -/
def toBasedRing : BasedRing cmd.ι where
  N := cmd.N
  I₀ := cmd.I₀
  star := cmd.star
  star_star := cmd.star_star
  assoc := cmd.N_assoc
  sum_I₀_mul_left := cmd.N_sum_I₀_mul_left
  sum_I₀_mul_right := cmd.N_sum_I₀_mul_right
  duality_trace := cmd.N_duality_trace
  star_anti := cmd.N_star_anti

end CategoricalMultitensorData
