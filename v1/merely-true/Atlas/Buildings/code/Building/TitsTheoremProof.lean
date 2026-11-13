/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptIsCoxeterProof
import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.IsCoxeterCharacterized
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.ThinFolding
import Atlas.Buildings.code.ChamberComplex.GalleryTypes.WallCrossing
import Mathlib.GroupTheory.Coxeter.Length

open ChamberComplex AptIsCoxeterProof

variable {V : Type*} [DecidableEq V]

namespace TitsTheoremProof

/-- For adjacent chambers, the sufficient-foldings hypothesis yields a folding
fixing $C$ and sending $C'$ to $C$. -/
theorem sufficient_foldings_fix_fold
    (cc : ChamberComplex V) (hsf : HasSufficientFoldings cc)
    (C C' : Finset V) (hadj : cc.toSimplicialComplex.Adjacent C C') :
    ∃ (f : Folding cc), C.image f.morph.toFun = C ∧ C'.image f.morph.toFun = C := by
  obtain ⟨f, _, hfC, hfC', _, _⟩ := hsf C C' hadj
  exact ⟨f, hfC, hfC'⟩

/-- Dual to `sufficient_foldings_fix_fold`: a folding fixing $C'$ and sending
$C$ to $C'$. -/
theorem sufficient_foldings_fold_fix
    (cc : ChamberComplex V) (hsf : HasSufficientFoldings cc)
    (C C' : Finset V) (hadj : cc.toSimplicialComplex.Adjacent C C') :
    ∃ (f' : Folding cc), C'.image f'.morph.toFun = C' ∧ C.image f'.morph.toFun = C' := by
  obtain ⟨_, f', _, _, hf'C', hf'C⟩ := hsf C C' hadj
  exact ⟨f', hf'C', hf'C⟩

/-- A wall reflection is involutive: $s(s(v)) = v$ for every vertex $v$. -/
theorem wallReflection_involutive (cc : ChamberComplex V) (s : WallReflection cc) :
    ∀ v, s.refl (s.refl v) = v :=
  s.refl_involutive

/-- A simple generator $s_i$ of a Coxeter group is not the identity. -/
theorem simple_ne_one {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (i : B) :
    M.toCoxeterSystem.simple i ≠ 1 := by
  intro h
  have := M.toCoxeterSystem.length_simple i
  rw [h, CoxeterSystem.length_one] at this
  omega

/-- Each simple generator is its own inverse: $s_i^{-1} = s_i$. -/
theorem simple_inv {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (i : B) :
    (M.toCoxeterSystem.simple i)⁻¹ = M.toCoxeterSystem.simple i :=
  M.toCoxeterSystem.inv_simple i

/-- Right multiplication by a simple generator moves any element: $w s_i \ne w$. -/
theorem mul_simple_ne_self {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (w : M.Group) (i : B) :
    w * M.toCoxeterSystem.simple i ≠ w := by
  intro h
  have : M.toCoxeterSystem.simple i = 1 := by
    have := mul_left_cancel (a := w) (b := M.toCoxeterSystem.simple i) (c := 1)
    rw [mul_one] at this
    exact this h
  exact simple_ne_one M i this

/-- Chamber-adjacency in a Coxeter complex is invariant under left
multiplication by any group element. -/
theorem chamberAdjacent_left_mul {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (g w w' : M.Group)
    (hadj : CoxeterComplex.ChamberAdjacent M w w') :
    CoxeterComplex.ChamberAdjacent M (g * w) (g * w') := by
  obtain ⟨hne, i, hi⟩ := hadj
  constructor
  · intro heq; exact hne (mul_left_cancel heq)
  · exact ⟨i, by rw [hi, mul_assoc]⟩

/-- The chambers $w$ and $w s_i$ are chamber-adjacent in the Coxeter complex. -/
theorem chamberAdjacent_mul_simple {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (w : M.Group) (i : B) :
    CoxeterComplex.ChamberAdjacent M w (w * M.toCoxeterSystem.simple i) := by
  constructor
  · exact Ne.symm (mul_simple_ne_self M w i)
  · exact ⟨i, rfl⟩

/-- The gallery path realizing the word $s_{i_1} \dots s_{i_n}$ starting from
$w$: the list $[w, w s_{i_1}, w s_{i_1} s_{i_2}, \dots]$. -/
def galleryPath {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (w : M.Group) : List B → List M.Group
  | [] => [w]
  | i :: rest => w :: galleryPath M (w * M.toCoxeterSystem.simple i) rest

/-- The gallery path is non-empty. -/
theorem galleryPath_nonempty {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (w : M.Group) (word : List B) :
    galleryPath M w word ≠ [] := by
  cases word <;> simp [galleryPath]

/-- Every gallery path is a valid gallery in the Coxeter complex (consecutive
chambers are chamber-adjacent). -/
theorem word_gallery_isGallery {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) :
    ∀ (word : List B) (w : M.Group),
    CoxeterComplex.IsGallery M (galleryPath M w word) := by
  intro word
  induction word with
  | nil => intro w; exact trivial
  | cons i rest ih =>
    intro w
    show CoxeterComplex.IsGallery M (w :: galleryPath M (w * M.toCoxeterSystem.simple i) rest)
    cases rest with
    | nil =>
      show CoxeterComplex.ChamberAdjacent M w (w * M.toCoxeterSystem.simple i) ∧ True
      exact ⟨chamberAdjacent_mul_simple M w i, trivial⟩
    | cons j rest' =>
      show CoxeterComplex.ChamberAdjacent M w (w * M.toCoxeterSystem.simple i) ∧
        CoxeterComplex.IsGallery M (galleryPath M (w * M.toCoxeterSystem.simple i) (j :: rest'))
      exact ⟨chamberAdjacent_mul_simple M w i, ih (w * M.toCoxeterSystem.simple i)⟩

/-- Accumulated word product: starting from $w$, multiply right by each
simple generator $s_i$ in the word. -/
def wordProduct {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) (w : M.Group) : List B → M.Group
  | [] => w
  | i :: rest => wordProduct M (w * M.toCoxeterSystem.simple i) rest

/-- The last chamber of the gallery path equals the word product. -/
theorem galleryPath_last {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) :
    ∀ (word : List B) (w : M.Group),
    (galleryPath M w word).getLast (galleryPath_nonempty M w word) =
    wordProduct M w word := by
  intro word
  induction word with
  | nil => intro w; simp [galleryPath, wordProduct]
  | cons i rest ih =>
    intro w
    simp only [galleryPath, wordProduct]
    have hne : galleryPath M (w * M.toCoxeterSystem.simple i) rest ≠ [] :=
      galleryPath_nonempty M _ rest
    rw [List.getLast_cons (by exact hne)]
    exact ih (w * M.toCoxeterSystem.simple i)

end TitsTheoremProof
