/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers
import Atlas.Buildings.code.CoxeterGroup.DeletionWordRelation
import Mathlib.GroupTheory.Coxeter.Basic

open CoxeterSystemFromDeletion Function Set

namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- Compatibility of the canonical homomorphism with word products: $\varphi$
sends the abstract product of a word in simple generators to the concrete
product of the same word under $\mathtt{gen}$. -/
lemma deletionCanonicalHom_map_word_prod
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (word : List B) :
    let M := deletionCoxeterMatrix gen hgen_inv hgen_ne
    let φ := deletionCanonicalHom gen hgen_inv hgen_ne
    φ ((word.map M.simple).prod) = (word.map gen).prod := by
  intro M φ
  rw [map_list_prod]
  congr 1
  rw [List.map_map]
  congr 1
  ext s
  exact deletionCanonicalHom_apply_simple gen hgen_inv hgen_ne s



end CoxeterSystemFromDeletion
