/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.DifferentialForms

set_option autoImplicit false

/-- Trivial differential-form scaffolding: every degree's space of forms is the singleton
`PUnit`, providing a degenerate witness for the DFS API. -/
@[reducible]
def TrivialΩ : ℕ → Type* := fun _ => PUnit

/-- Trivial vector-field space: the singleton `PUnit`, the partner of `TrivialΩ`. -/
@[reducible]
def TrivialVF : Type* := PUnit

/-- The trivial `DifferentialFormSpace` instance on `TrivialΩ` / `TrivialVF`: all operations
return the unique element of `PUnit` and all axioms hold by `Subsingleton.elim`. -/
noncomputable instance trivialDFS : DifferentialFormSpace TrivialΩ TrivialVF where
  instAddCommGroup := fun _ => inferInstanceAs (AddCommGroup PUnit)
  instModule := fun _ => inferInstanceAs (Module ℝ PUnit)
  fMul := fun _ _ => PUnit.unit
  wedge1 := fun _ _ => PUnit.unit
  d := fun _ => PUnit.unit
  ι := fun _ {_} _ => PUnit.unit
  L := fun _ {_} _ => PUnit.unit
  d_add := by intros; exact Subsingleton.elim _ _
  d_smul := by intros; exact Subsingleton.elim _ _
  d_squared := by intros; exact Subsingleton.elim _ _
  d_fMul := by intros; exact Subsingleton.elim _ _
  fMul_add_left := by intros; exact Subsingleton.elim _ _
  fMul_add_right := by intros; exact Subsingleton.elim _ _
  fMul_smul := by intros; exact Subsingleton.elim _ _
  wedge1_add_right := by intros; exact Subsingleton.elim _ _
  wedge1_smul_right := by intros; exact Subsingleton.elim _ _
  ι_add := by intros; exact Subsingleton.elim _ _
  ι_smul := by intros; exact Subsingleton.elim _ _
  ι_fMul := by intros; exact Subsingleton.elim _ _
  ι_wedge1 := by intros; exact Subsingleton.elim _ _
  ι_squared := by intros; exact Subsingleton.elim _ _
  ι_ι_anticomm := by intros; exact Subsingleton.elim _ _

  L_add := by intros; exact Subsingleton.elim _ _
  L_smul := by intros; exact Subsingleton.elim _ _
  L_zero_eq_ι_d := by intros; exact Subsingleton.elim _ _
  L_comm_d := by intros; exact Subsingleton.elim _ _
  L_fMul := by intros; exact Subsingleton.elim _ _
  ext_fdα := by intros; exact Subsingleton.elim _ _
  ι_one_form_nondegenerate := by intros; exact Subsingleton.elim _ _
  ι_two_form_nondegenerate := by intros; exact Subsingleton.elim _ _
