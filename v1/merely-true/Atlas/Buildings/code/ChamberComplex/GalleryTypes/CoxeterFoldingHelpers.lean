/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Folding
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import Mathlib.GroupTheory.Coxeter.Length

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

section GroupLevel

variable {B_idx : Type*} (M : CoxeterMatrix B_idx)

/-- The group-level half-apartment map for simple reflection $s_i$: returns $w$ if multiplication
by $s_i$ on the left lengthens $w$, and $s_i w$ otherwise. -/
noncomputable def coxeterHalfGroupMap (i : B_idx) (w : M.Group) : M.Group :=
  let cs := M.toCoxeterSystem
  if cs.length (cs.simple i * w) > cs.length w then w
  else cs.simple i * w

/-- The half-apartment map $\text{coxeterHalfGroupMap}_i$ is idempotent on the Coxeter group. -/
theorem coxeterHalfGroupMap_idempotent (i : B_idx) (w : M.Group) :
    coxeterHalfGroupMap M i (coxeterHalfGroupMap M i w) = coxeterHalfGroupMap M i w := by
  unfold coxeterHalfGroupMap
  simp only
  set cs := M.toCoxeterSystem
  set s := cs.simple i
  by_cases h1 : cs.length (s * w) > cs.length w
  · simp only [h1, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    rw [cs.simple_mul_simple_cancel_left i]
    have hne := cs.length_simple_mul_ne w i
    have hlt : cs.length (s * w) < cs.length w :=
      lt_of_le_of_ne (Nat.not_lt.mp h1) hne
    simp only [show cs.length w > cs.length (s * w) from hlt, ↓reduceIte]

end GroupLevel

section ChamberLevel

variable {B_idx : Type*}

/-- Lift `coxeterHalfGroupMap` from the Coxeter group to the chamber complex along a labelling
$\varphi$: maps chamber $E$ to a chamber whose $\varphi$-image equals the half-apartment image of
$\varphi(E)$. -/
noncomputable def coxeterHalfChamberMap
    (K : ChamberComplex V)
    (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
    (i : B_idx) (E : Finset V) : Finset V :=
  let cs := M.toCoxeterSystem
  let w := φ E
  if cs.length (cs.simple i * w) > cs.length w then E
  else (hsurj (cs.simple i * w)).choose

/-- The chamber-level half map intertwines with the group-level map along $\varphi$:
$\varphi(\text{coxeterHalfChamberMap}\ i\ E) = \text{coxeterHalfGroupMap}\ i\ (\varphi(E))$. -/
theorem coxeterHalfChamberMap_spec
    (K : ChamberComplex V)
    (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
    (i : B_idx) (E : Finset V) :
    φ (coxeterHalfChamberMap K M φ hsurj i E) = coxeterHalfGroupMap M i (φ E) := by
  unfold coxeterHalfChamberMap coxeterHalfGroupMap
  simp only
  split_ifs with h
  · rfl
  · exact (hsurj (M.toCoxeterSystem.simple i * φ E)).choose_spec.2

/-- The chamber-level half map preserves maximality (chambers go to chambers). -/
theorem coxeterHalfChamberMap_maximal
    (K : ChamberComplex V)
    (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
    (i : B_idx) (E : Finset V)
    (hE : K.toSimplicialComplex.IsMaximal E) :
    K.toSimplicialComplex.IsMaximal (coxeterHalfChamberMap K M φ hsurj i E) := by
  unfold coxeterHalfChamberMap
  simp only
  split_ifs with h
  · exact hE
  · exact (hsurj (M.toCoxeterSystem.simple i * φ E)).choose_spec.1

end ChamberLevel

end ChamberComplex
