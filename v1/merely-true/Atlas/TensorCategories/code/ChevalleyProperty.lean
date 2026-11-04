/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.SemisimpleMultitensor

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

section ChevalleyProperty

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A monoidal category `C` has the Chevalley property if the tensor product of two
semisimple objects is again semisimple (so the full subcategory of semisimple objects is a
monoidal subcategory). -/
class HasChevalleyProperty : Prop where
  tensor_semisimple : ∀ (X Y : C),
    IsSemisimpleObject C X → IsSemisimpleObject C Y → IsSemisimpleObject C (X ⊗ Y)

/-- Definition 1.31.1 (named restatement): the Chevalley property for a tensor category. -/
def Definition_1_31_1_ChevalleyProperty : Prop :=
  HasChevalleyProperty C

/-- Definition 1.31.1: the Chevalley property for a tensor category, expressed as a
proposition. -/
def Definition_1_31_1 : Prop :=
  HasChevalleyProperty C

end ChevalleyProperty

section Pointed

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A monoidal category is pointed in this Atlas formulation if every simple object has a
tensor inverse, i.e. is invertible. -/
class IsPointedTensorCategory : Prop where
  simple_has_inverse : ∀ (X : C) [Simple X],
    ∃ (Y : C), Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C)



end Pointed

section TensorBiproductDist

end TensorBiproductDist

section Pointed2

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]


end Pointed2

section SemisimpleChevalley

end SemisimpleChevalley

section LoewyLength

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A length-`n` semisimple filtration of an object `X`: a tuple of `n` semisimple objects
intended as the associated graded pieces of a filtration of `X`. -/
structure SemisimpleFiltration (X : C) (n : ℕ) where
  gradedPiece : Fin n → C
  gradedPiece_semisimple : ∀ i, IsSemisimpleObject C (gradedPiece i)

/-- Abstract data witnessing the existence of a Loewy length function on `C`: every object
admits some semisimple filtration of positive length, filtrations are functorial in tensor
products with multiplicative compatible length, and biproducts of semisimple objects are
semisimple. -/
structure LoewyLengthData where
  hasSemisimpleFiltration : C → ℕ → Prop
  hasSemisimpleFiltration_dec : ∀ (X : C), DecidablePred (hasSemisimpleFiltration X)
  hasSemisimpleFiltration_exists : ∀ (X : C), ∃ n, hasSemisimpleFiltration X n
  hasSemisimpleFiltration_pos : ∀ (X : C) (n : ℕ),
    hasSemisimpleFiltration X n → 1 ≤ n
  toFiltration : ∀ (X : C) (n : ℕ),
    hasSemisimpleFiltration X n → SemisimpleFiltration C X n
  filtration_tensor :
    ∀ (X Y : C) (m n : ℕ) (_ : m ≥ 1) (_ : n ≥ 1)
    (fX : SemisimpleFiltration C X m) (fY : SemisimpleFiltration C Y n),
    ∃ (candidateGradedPieces : Fin (m + n - 1) → C),

      (∀ (r : Fin (m + n - 1)),
        ∃ (k : ℕ) (pairs : Fin k → C) (hb : HasBiproduct pairs),
          (∀ p, ∃ (i : Fin m) (j : Fin n),
            pairs p = fX.gradedPiece i ⊗ fY.gradedPiece j) ∧
          Nonempty (candidateGradedPieces r ≅ @biproduct _ _ _ _ pairs hb)) ∧

      ((∀ r, IsSemisimpleObject C (candidateGradedPieces r)) →
        hasSemisimpleFiltration (X ⊗ Y) (m + n - 1))
  semisimple_biproduct : ∀ {k : ℕ} (f : Fin k → C) (hb : HasBiproduct f),
    (∀ i, IsSemisimpleObject C (f i)) →
    IsSemisimpleObject C (@biproduct _ _ _ _ f hb)

variable {C}

/-- The Loewy length `Lw(X)` of an object `X`, defined as the smallest `n` for which a
semisimple filtration of length `n` exists. -/
def LoewyLengthData.loewyLength (LD : LoewyLengthData C) (X : C) : ℕ :=
  @Nat.find _ (LD.hasSemisimpleFiltration_dec X) (LD.hasSemisimpleFiltration_exists X)

/-- The Loewy length of `X` is attained: there is a semisimple filtration of length
`LD.loewyLength X`. -/
theorem LoewyLengthData.loewyLength_spec (LD : LoewyLengthData C) (X : C) :
    LD.hasSemisimpleFiltration X (LD.loewyLength X) :=
  @Nat.find_spec _ (LD.hasSemisimpleFiltration_dec X)
    (LD.hasSemisimpleFiltration_exists X)

/-- If `X` admits a semisimple filtration of length `n`, then `loewyLength X ≤ n`. -/
theorem LoewyLengthData.loewyLength_le (LD : LoewyLengthData C) (X : C) (n : ℕ)
    (h : LD.hasSemisimpleFiltration X n) : LD.loewyLength X ≤ n :=
  @Nat.find_le _ _ (LD.hasSemisimpleFiltration_dec X)
    (LD.hasSemisimpleFiltration_exists X) h

/-- The Loewy length is always at least `1`. -/
theorem LoewyLengthData.loewyLength_pos (LD : LoewyLengthData C) (X : C) :
    1 ≤ LD.loewyLength X :=
  LD.hasSemisimpleFiltration_pos X _ (LD.loewyLength_spec X)

/-- Proposition 1.31.3 (key inequality): under the Chevalley property, the Loewy length is
subadditive on tensor products with a `- 1` shift: `Lw(X ⊗ Y) ≤ Lw(X) + Lw(Y) - 1`. -/
theorem LoewyLengthData.loewyLength_tensor_le [hChev : HasChevalleyProperty C]
    (LD : LoewyLengthData C) (X Y : C) :
    LD.loewyLength (X ⊗ Y) ≤ LD.loewyLength X + LD.loewyLength Y - 1 := by

  have hX := LD.loewyLength_spec X
  have hY := LD.loewyLength_spec Y
  have hXpos := LD.loewyLength_pos X
  have hYpos := LD.loewyLength_pos Y
  let fX := LD.toFiltration X _ hX
  let fY := LD.toFiltration Y _ hY


  obtain ⟨candidateGP, hdecomp, hvalid⟩ :=
    LD.filtration_tensor X Y _ _ hXpos hYpos fX fY


  have hss : ∀ r, IsSemisimpleObject C (candidateGP r) := by
    intro r

    obtain ⟨k, pairs, hb, hpairs_are_tensors, ⟨iso_r⟩⟩ := hdecomp r

    have hpairs_ss : ∀ p, IsSemisimpleObject C (pairs p) := by
      intro p
      obtain ⟨i, j, heq⟩ := hpairs_are_tensors p
      rw [heq]
      exact hChev.tensor_semisimple _ _
        (fX.gradedPiece_semisimple i) (fY.gradedPiece_semisimple j)

    exact isSemisimpleObject_of_iso iso_r (LD.semisimple_biproduct pairs hb hpairs_ss)

  exact LD.loewyLength_le _ _ (hvalid hss)

/-- Reformulation of the Loewy length tensor inequality avoiding truncated subtraction:
`Lw(X ⊗ Y) + 1 ≤ Lw(X) + Lw(Y)`. -/
theorem LoewyLengthData.loewyLength_tensor_le' [HasChevalleyProperty C]
    (LD : LoewyLengthData C) (X Y : C) :
    LD.loewyLength (X ⊗ Y) + 1 ≤ LD.loewyLength X + LD.loewyLength Y := by
  have h := LD.loewyLength_tensor_le X Y
  have hX := LD.loewyLength_pos X
  have hY := LD.loewyLength_pos Y
  omega

/-- Proposition 1.31.3: In a tensor category with the Chevalley property, the Loewy length
satisfies `Lw(X ⊗ Y) ≤ Lw(X) + Lw(Y) - 1`. -/
theorem Proposition_1_31_3 [HasChevalleyProperty C]
    (LD : LoewyLengthData C) (X Y : C) :
    LD.loewyLength (X ⊗ Y) ≤ LD.loewyLength X + LD.loewyLength Y - 1 :=
  LD.loewyLength_tensor_le X Y

/-- In a semisimple category every object is already semisimple, so the Loewy length data
is trivially given by length `1` filtrations. -/
def loewyLengthDataOfSemisimple [IsSemisimpleCategory C] : LoewyLengthData C where
  hasSemisimpleFiltration := fun _ n => n ≥ 1
  hasSemisimpleFiltration_dec := fun _ => inferInstance
  hasSemisimpleFiltration_exists := fun _ => ⟨1, le_refl 1⟩
  hasSemisimpleFiltration_pos := fun _ _ h => h
  toFiltration := fun X n _ =>
    { gradedPiece := fun _ => X
      gradedPiece_semisimple := fun _ => IsSemisimpleCategory.semisimple X }
  filtration_tensor := fun X Y m n hm hn fX fY => by
    have hmn : m + n - 1 ≥ 1 := by omega

    set T := fX.gradedPiece ⟨0, by omega⟩ ⊗ fY.gradedPiece ⟨0, by omega⟩

    let pairs : Fin 1 → C := fun _ => T
    refine ⟨fun _ => T,
      fun r => ⟨1, pairs, inferInstance,
        fun _ => ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩,
        ⟨(biproductUniqueIso pairs).symm⟩⟩,
      fun _ => hmn⟩
  semisimple_biproduct := fun _ _ _ => IsSemisimpleCategory.semisimple _

/-- Tensor-product compatibility for a coradical-style Loewy length: the filtration is a
"Hopf algebra filtration" in the sense of Corollary 1.31.5 if `loewyLength (X ⊗ Y)` is
controlled by the sum of the Loewy lengths of `X` and `Y`. -/
structure IsHopfAlgebraFiltration (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] [HasChevalleyProperty C]
    (LD : LoewyLengthData C) : Prop where
  filtration_tensor_compat :
    ∀ (X Y : C) (i j : ℕ),
      LD.loewyLength X ≤ i → LD.loewyLength Y ≤ j →
      LD.loewyLength (X ⊗ Y) ≤ i + j

/-- Helper toward Corollary 1.31.5: in any tensor category with the Chevalley property, the
Loewy length data automatically forms a Hopf algebra filtration on objects, since `loewy
length` is multiplicatively well-behaved on tensor products. -/
theorem pointed_coradicalFiltration_isHopfAlgebraFiltration
    [hChev : HasChevalleyProperty C]
    (LD : LoewyLengthData C) :
    IsHopfAlgebraFiltration C LD where
  filtration_tensor_compat := by
    intro X Y i j hi hj
    have h := LD.loewyLength_tensor_le X Y
    have hX := LD.loewyLength_pos X
    have hY := LD.loewyLength_pos Y
    omega

/-- A Hopf algebra filtration is "full" if it is also preserved by taking right duals,
matching `S(H_i) = H_i` in Corollary 1.31.5. -/
structure IsFullHopfAlgebraFiltration (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasZeroMorphisms C] [HasChevalleyProperty C]
    (LD : LoewyLengthData C) : Prop extends IsHopfAlgebraFiltration C LD where
  dual_preserves_filtration :
    ∀ (X : C) [HasRightDual X] (n : ℕ),
      LD.loewyLength X ≤ n ↔ LD.loewyLength (HasRightDual.rightDual (X := X)) ≤ n



end LoewyLength

end CategoryTheory
