/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- Corollary 18.4 (Nakayama, set form): for a local Noetherian ring $R$ with maximal ideal $\mathfrak{m}$ and a subset $s \subseteq \mathfrak{m}$, the elements of $s$ generate $\mathfrak{m}$ as an ideal iff their images in the cotangent space $\mathfrak{m}/\mathfrak{m}^2$ span it as an $R/\mathfrak{m}$-vector space. -/
theorem Ideal.generators_iff_cotangent_span
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (s : Set (IsLocalRing.maximalIdeal R)) :
    Ideal.span (Subtype.val '' s) = IsLocalRing.maximalIdeal R ↔
      Submodule.span (IsLocalRing.ResidueField R)
        ((IsLocalRing.maximalIdeal R).toCotangent '' s) = ⊤ := by
  rw [← Ideal.submodule_span_eq, Submodule.span_val_image_eq_iff,
    IsLocalRing.CotangentSpace.span_image_eq_top_iff]

/-- Finite-tuple version of Corollary 18.4: for $t_1, \dots, t_n \in \mathfrak{m}$ in a local Noetherian ring, the $t_i$ generate $\mathfrak{m}$ iff their images generate $\mathfrak{m}/\mathfrak{m}^2$ as an $R/\mathfrak{m}$-vector space. -/
theorem Ideal.generators_iff_cotangent_span_fin
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (t : Fin n → IsLocalRing.maximalIdeal R) :
    Ideal.span (Set.range (fun i => (t i : R))) = IsLocalRing.maximalIdeal R ↔
      Submodule.span (IsLocalRing.ResidueField R)
        (Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (t i))) = ⊤ := by
  rw [show Set.range (fun i => (t i : R)) = Subtype.val '' (Set.range t) from by
      ext x; simp [Set.mem_image, Set.mem_range],
    show Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (t i)) =
      (IsLocalRing.maximalIdeal R).toCotangent '' (Set.range t) from by
      ext x; simp [Set.mem_image, Set.mem_range]]
  exact Ideal.generators_iff_cotangent_span R (Set.range t)
