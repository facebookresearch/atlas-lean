/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.Group

set_option maxHeartbeats 800000

open CategoryTheory

universe u v

/-- A 3-cocycle on a monoid `G` with values in a commutative monoid `A`:
a function `ω : G × G × G → A` satisfying the cocycle identity used to
twist the associator of the pointed monoidal category `Vec_G^ω`. -/
structure GroupCocycle3 (G : Type u) [Monoid G] (A : Type v) [CommMonoid A] where
  toFun : G → G → G → A
  cocycle_cond : ∀ g₁ g₂ g₃ g₄ : G,
    toFun (g₁ * g₂) g₃ g₄ * toFun g₁ g₂ (g₃ * g₄) =
    toFun g₁ g₂ g₃ * toFun g₁ (g₂ * g₃) g₄ * toFun g₂ g₃ g₄

/-- Coerce a `GroupCocycle3` to its underlying function `G → G → G → A`. -/
instance {G : Type u} [Monoid G] {A : Type v} [CommMonoid A] :
    CoeFun (GroupCocycle3 G A) (fun _ => G → G → G → A) :=
  ⟨GroupCocycle3.toFun⟩

/-- Extensionality for 3-cocycles: equality of `toFun` implies equality. -/
@[ext]
theorem GroupCocycle3.ext {G : Type u} [Monoid G] {A : Type v} [CommMonoid A]
    {ω₁ ω₂ : GroupCocycle3 G A} (h : ω₁.toFun = ω₂.toFun) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; congr

/-- A normalised 3-cocycle: a `GroupCocycle3` satisfying
`ω(g, 1, h) = 1` for all `g, h ∈ G`. -/
structure NormalizedGroupCocycle3 (G : Type u) [Monoid G] (A : Type v) [CommMonoid A]
    extends GroupCocycle3 G A where
  normalized : ∀ g h : G, toFun g 1 h = 1

/-- The trivial 3-cocycle, constantly equal to `1`. -/
def GroupCocycle3.trivial (G : Type u) [Monoid G] (A : Type v) [CommMonoid A] :
    GroupCocycle3 G A where
  toFun _ _ _ := 1
  cocycle_cond _ _ _ _ := by simp

/-- The trivial normalised 3-cocycle, constantly equal to `1`. -/
def NormalizedGroupCocycle3.trivial (G : Type u) [Monoid G] (A : Type v) [CommMonoid A] :
    NormalizedGroupCocycle3 G A where
  toGroupCocycle3 := GroupCocycle3.trivial G A
  normalized _ _ := rfl

/-- Objects of the twisted pointed monoidal category `Vec_G^ω`: a single
homogeneous component indexed by an element `val : G`. -/
@[ext]
structure CG (G : Type u) (A : Type v) [Monoid G] [CommGroup A]
    (_ω : NormalizedGroupCocycle3 G A) where
  val : G

/-- A morphism `X ⟶ Y` in `Vec_G^ω` exists only when `X.val = Y.val`,
and is the data of a single nonzero scalar `val : A`. -/
structure CG.Hom {G : Type u} {A : Type v} [Monoid G] [CommGroup A]
    {ω : NormalizedGroupCocycle3 G A} (X Y : CG G A ω) : Type v where
  val : A
  eq : X.val = Y.val

namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]
variable {ω : NormalizedGroupCocycle3 G A}

/-- Extensionality for `CG.Hom`: morphisms are determined by their
underlying scalar `val`. -/
@[ext]
theorem Hom.ext {X Y : CG G A ω} {f f' : CG.Hom X Y} (hv : f.val = f'.val) : f = f' := by
  cases f; cases f'; congr

/-- Category instance on `CG G A ω`: composition multiplies the
underlying scalars and identity morphisms have scalar `1`. -/
instance instCategory : Category (CG G A ω) where
  Hom := CG.Hom
  id _ := ⟨1, rfl⟩
  comp f f' := ⟨f.val * f'.val, f.eq.trans f'.eq⟩
  id_comp _ := Hom.ext (one_mul _)
  comp_id _ := Hom.ext (mul_one _)
  assoc _ _ _ := Hom.ext (mul_assoc _ _ _)


/-- Underlying scalar of the composition of morphisms in `CG G A ω`. -/
@[simp] theorem comp_val {X Y Z : CG G A ω} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val * g.val := rfl
/-- The underlying scalar of the identity morphism is `1`. -/
@[simp] theorem id_val (X : CG G A ω) : (𝟙 X : X ⟶ X).val = 1 := rfl

/-- Tensor product of objects in `CG G A ω`: degrees multiply. -/
abbrev tensorObj' (X Y : CG G A ω) : CG G A ω := ⟨X.val * Y.val⟩

/-- Tensor product of morphisms in `CG G A ω`: scalars multiply. -/
abbrev tensorHom' {X₁ X₂ Y₁ Y₂ : CG G A ω} (f : X₁ ⟶ X₂) (f' : Y₁ ⟶ Y₂) :
    tensorObj' X₁ Y₁ ⟶ tensorObj' X₂ Y₂ :=
  ⟨f.val * f'.val, by simp [f.eq, f'.eq]⟩

/-- The monoidal unit object in `CG G A ω` lives in degree `1`. -/
abbrev unit' : CG G A ω := ⟨1⟩

/-- The associator in the twisted category `CG G A ω`, with structure
constant `ω(X.val, Y.val, Z.val)` on each component. -/
def twistedAssociator' (X Y Z : CG G A ω) :
    tensorObj' (tensorObj' X Y) Z ≅ tensorObj' X (tensorObj' Y Z) where
  hom := ⟨ω.toFun X.val Y.val Z.val, by simp [mul_assoc]⟩
  inv := ⟨(ω.toFun X.val Y.val Z.val)⁻¹, by simp [mul_assoc]⟩
  hom_inv_id := Hom.ext (mul_inv_cancel _)
  inv_hom_id := Hom.ext (inv_mul_cancel _)

/-- The forward scalar of the twisted associator is `ω(X, Y, Z)`. -/
@[simp] theorem twistedAssociator'_hom_val (X Y Z : CG G A ω) :
    (twistedAssociator' X Y Z).hom.val = ω.toFun X.val Y.val Z.val := rfl
/-- The inverse scalar of the twisted associator is `ω(X, Y, Z)⁻¹`. -/
@[simp] theorem twistedAssociator'_inv_val (X Y Z : CG G A ω) :
    (twistedAssociator' X Y Z).inv.val = (ω.toFun X.val Y.val Z.val)⁻¹ := rfl

/-- Left unit isomorphism `1 ⊗ X ≅ X` in `CG G A ω`. -/
def leftUnitor' (X : CG G A ω) : tensorObj' unit' X ≅ X where
  hom := ⟨1, by simp⟩
  inv := ⟨1, by simp⟩
  hom_inv_id := Hom.ext (mul_one _)
  inv_hom_id := Hom.ext (mul_one _)

/-- The underlying scalar of the left unitor in `CG G A ω` is `1`. -/
@[simp] theorem leftUnitor'_hom_val (X : CG G A ω) :
    (leftUnitor' X).hom.val = 1 := rfl

/-- Right unit isomorphism `X ⊗ 1 ≅ X` in `CG G A ω`. -/
def rightUnitor' (X : CG G A ω) : tensorObj' X unit' ≅ X where
  hom := ⟨1, by simp⟩
  inv := ⟨1, by simp⟩
  hom_inv_id := Hom.ext (mul_one _)
  inv_hom_id := Hom.ext (mul_one _)

/-- The underlying scalar of the right unitor in `CG G A ω` is `1`. -/
@[simp] theorem rightUnitor'_hom_val (X : CG G A ω) :
    (rightUnitor' X).hom.val = 1 := rfl

/-- Monoidal-category structure data on `CG G A ω`: tensor product,
unit, associator, and unitors as defined above. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (CG G A ω) where
  tensorObj := tensorObj'
  whiskerLeft X _ _ f := tensorHom' (𝟙 X) f
  whiskerRight f Y := tensorHom' f (𝟙 Y)
  tensorHom := tensorHom'
  tensorUnit := unit'
  associator := twistedAssociator'
  leftUnitor := leftUnitor'
  rightUnitor := rightUnitor'

/-- `CG G A ω` is a monoidal category: the pentagon axiom follows from
the cocycle identity of `ω` and the triangle axiom from normalisation.
This is the construction of `Vec_G^ω` (EGNO §1.7). -/
instance monoidalCategory : MonoidalCategory (CG G A ω) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => Hom.ext (show (1 : A) * 1 = 1 from by simp))
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => Hom.ext (by
      show f₁.val * f₂.val * (g₁.val * g₂.val) = (f₁.val * g₁.val) * (f₂.val * g₂.val)
      simp [mul_comm, mul_left_comm]))
    (associator_naturality := fun f₁ f₂ f₃ => Hom.ext (by
      show (f₁.val * f₂.val) * f₃.val * ω.toFun _ _ _ =
           ω.toFun _ _ _ * (f₁.val * (f₂.val * f₃.val))
      rw [f₁.eq, f₂.eq, f₃.eq]; simp [mul_comm, mul_left_comm]))
    (leftUnitor_naturality := fun f => Hom.ext (by
      show 1 * f.val * 1 = 1 * f.val; simp))
    (rightUnitor_naturality := fun f => Hom.ext (by
      show f.val * 1 * 1 = 1 * f.val; simp))
    (pentagon := fun W X Y Z => Hom.ext (by
      show ω.toFun W.val X.val Y.val * 1 *
           (ω.toFun W.val (X.val * Y.val) Z.val *
           (1 * ω.toFun X.val Y.val Z.val)) =
           ω.toFun (W.val * X.val) Y.val Z.val *
           ω.toFun W.val X.val (Y.val * Z.val)
      simp only [mul_one, one_mul]
      have h := (ω.cocycle_cond W.val X.val Y.val Z.val).symm
      rw [mul_assoc] at h; exact h))
    (triangle := fun X Y => Hom.ext (by
      show ω.toFun X.val 1 Y.val * (1 * 1) = 1 * 1; simp [ω.normalized]))

end CG

section Rigidity

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]
variable {ω : NormalizedGroupCocycle3 G A}

/-- Dual object of `X = ⟨g⟩` in `CG G A ω`, namely `⟨g⁻¹⟩`. -/
def CG.dualObj (X : CG G A ω) : CG G A ω := ⟨X.val⁻¹⟩

/-- A normalised 3-cocycle is also normalised in the rightmost slot:
`ω(g, h, 1) = 1`. -/
lemma NormalizedGroupCocycle3.normalized_right
    (ω : NormalizedGroupCocycle3 G A) (g h : G) : ω.toFun g h 1 = 1 := by
  have hc := ω.cocycle_cond g h 1 1
  simp only [mul_one] at hc
  rw [ω.normalized (g * h) 1, ω.normalized h 1] at hc
  simp only [one_mul, mul_one] at hc
  have : ω.toFun g h 1 * ω.toFun g h 1 = ω.toFun g h 1 * 1 := by
    rw [mul_one]; exact hc.symm
  exact mul_left_cancel this

/-- A normalised 3-cocycle is also normalised in the leftmost slot:
`ω(1, g, h) = 1`. -/
lemma NormalizedGroupCocycle3.normalized_left
    (ω : NormalizedGroupCocycle3 G A) (g h : G) : ω.toFun 1 g h = 1 := by
  have hc := ω.cocycle_cond 1 1 g h
  simp only [one_mul] at hc
  rw [ω.normalized 1 (g * h), ω.normalized 1 g] at hc
  simp only [one_mul, mul_one] at hc
  have : ω.toFun 1 g h * ω.toFun 1 g h = ω.toFun 1 g h * 1 := by
    rw [mul_one]; exact hc.symm
  exact mul_left_cancel this

/-- Specialised cocycle identity used in the rigidity proof:
`ω(g, g⁻¹, g) · ω(g⁻¹, g, g⁻¹) = 1`. -/
lemma NormalizedGroupCocycle3.cocycle_inv_cancel
    (ω : NormalizedGroupCocycle3 G A) (g : G) :
    ω.toFun g g⁻¹ g * ω.toFun g⁻¹ g g⁻¹ = 1 := by
  have hc := ω.cocycle_cond g g⁻¹ g g⁻¹
  simp only [mul_inv_cancel, inv_mul_cancel] at hc
  rw [ω.normalized_left g g⁻¹, ω.normalized_right g g⁻¹, ω.normalized g g⁻¹] at hc
  simp only [mul_one] at hc
  exact hc.symm

/-- The evaluation morphism `Xᘁ ⊗ X ⟶ 𝟙` in `CG G A ω`, given by the scalar
`ω(g, g⁻¹, g)⁻¹` where `g = X.val`. -/
def CG.evalMorphism (X : CG G A ω) :
    CG.tensorObj' (CG.dualObj X) X ⟶ CG.unit' where
  val := (ω.toFun X.val X.val⁻¹ X.val)⁻¹
  eq := by simp [CG.dualObj]

/-- The coevaluation morphism `𝟙 ⟶ X ⊗ Xᘁ` in `CG G A ω`, given by the
scalar `1`. -/
def CG.coevMorphism (X : CG G A ω) :
    CG.unit' ⟶ CG.tensorObj' X (CG.dualObj X) where
  val := 1
  eq := by simp [CG.dualObj]

/-- Each object `X` of `CG G A ω` has an exact pairing with its dual
`Xᘁ = ⟨g⁻¹⟩`, exhibiting `CG G A ω` as a rigid monoidal category. -/
noncomputable instance CG.exactPairing (X : CG G A ω) :
    ExactPairing X (CG.dualObj X) where
  coevaluation' := CG.coevMorphism X
  evaluation' := CG.evalMorphism X
  coevaluation_evaluation' := by
    apply CG.Hom.ext


    show 1 * 1 * ((ω.toFun X.val⁻¹ X.val X.val⁻¹)⁻¹ *
      ((ω.toFun X.val X.val⁻¹ X.val)⁻¹ * 1)) = 1 * 1
    simp only [one_mul, mul_one]
    rw [← mul_inv]
    rw [inv_eq_one]
    have := ω.cocycle_inv_cancel X.val
    rw [mul_comm] at this
    exact this
  evaluation_coevaluation' := by
    apply CG.Hom.ext


    show 1 * 1 * (ω.toFun X.val X.val⁻¹ X.val *
      (1 * (ω.toFun X.val X.val⁻¹ X.val)⁻¹)) = 1 * 1
    simp [mul_inv_cancel]

end Rigidity
