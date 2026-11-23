/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.GLn
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.CompleteLattice.Finset

namespace GLnBuilding

open Submodule Module

variable (k : Type*) [Field k] (n : ℕ)

/-- Convert a basis $b$ of $k^n$ into a frame by taking lines $L_i = k \cdot b_i$. -/
noncomputable def frameOfBasis (b : Basis (Fin n) k (Vec k n)) : Frame k n where
  lines i := k ∙ b i
  one_dim i := finrank_span_singleton (b.ne_zero i)
  indep := b.linearIndependent.iSupIndep_span_singleton
  spanning := by
    rw [← span_range_eq_iSup]
    exact b.span_eq

/-- The $i$-th line of `frameOfBasis b` is $k \cdot b_i$, by definition. -/
theorem frameOfBasis_lines (b : Basis (Fin n) k (Vec k n)) (i : Fin n) :
    (frameOfBasis k n b).lines i = k ∙ b i := rfl

/-- Any proper non-zero subspace $V \subseteq k^n$ admits an adapted frame: there exists a
frame $F$ for which $V = \bigoplus_{i \in S} L_i$ for some $S \subseteq \mathrm{Fin}\ n$,
constructed by extending a basis of $V$ by a basis of a complement. -/
theorem adapted_frame_of_single_subspace
    (V : Submodule k (Vec k n)) (_hbot : V ≠ ⊥) (_htop : V ≠ ⊤) :
    ∃ F : Frame k n, F.IsCompatible k n V := by

  obtain ⟨W, hVW⟩ := V.exists_isCompl

  set d := finrank k V with hd_def
  set e := finrank k W with he_def
  have hde : d + e = n := by
    have := Submodule.finrank_add_eq_of_isCompl hVW
    rw [finrank_fin_fun] at this; exact this

  have bV : Basis (Fin d) k V := finBasis k V
  have bW : Basis (Fin e) k W := finBasis k W

  let bVW := bV.prod bW
  let bAll := bVW.map (prodEquivOfIsCompl V W hVW)

  let idx : Fin d ⊕ Fin e ≃ Fin n := finSumFinEquiv.trans (finCongr hde)
  let b := bAll.reindex idx

  use frameOfBasis k n b

  use Finset.image (fun i : Fin d => idx (Sum.inl i)) Finset.univ

  rw [Finset.iSup_finset_image]
  simp only [Finset.mem_univ, iSup_true]

  have key : ∀ j : Fin d, b (idx (Sum.inl j)) = V.subtype (bV j) := by
    intro j
    simp [b, bAll, bVW, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply,
      prodEquivOfIsCompl]

  simp_rw [frameOfBasis_lines, key]


  rw [← span_range_eq_iSup]
  rw [show (fun j => V.subtype (bV j)) = V.subtype ∘ bV from rfl]
  rw [Set.range_comp, Submodule.span_image, bV.span_eq]
  exact (map_subtype_top V).symm

end GLnBuilding
