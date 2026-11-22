/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

namespace Garrett


/-- For a reflexive bilinear form `B`, vanishing of the orthogonal complement of `⊤`
implies nondegeneracy. -/
theorem nondegenerate_of_orthogonal_top_eq_bot
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V)
    (href : B.IsRefl)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :
    B.Nondegenerate :=
  href.nondegenerate_iff_separatingLeft.mpr
    (LinearMap.separatingLeft_iff_ker_eq_bot.mpr
      (by rwa [LinearMap.BilinForm.orthogonal_top_eq_ker href] at hnd))

/-- Converse of `nondegenerate_of_orthogonal_top_eq_bot`: a reflexive nondegenerate
form has trivial orthogonal complement of `⊤`. -/
theorem orthogonal_top_eq_bot_of_nondegenerate
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V)
    (href : B.IsRefl)
    (hnd : B.Nondegenerate) :
    LinearMap.BilinForm.orthogonal B ⊤ = ⊥ := by
  rw [LinearMap.BilinForm.orthogonal_top_eq_ker href]
  exact hnd.ker_eq_bot

/-- If `x` is anisotropic for `B` (i.e. not orthogonal to itself), then `k ∙ x` and
its orthogonal complement are complementary subspaces. -/
theorem isCompl_span_singleton_orthogonal
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V)
    {x : V} (hx : ¬ LinearMap.BilinForm.IsOrtho B x x) :
    IsCompl (k ∙ x) (LinearMap.BilinForm.orthogonal B (k ∙ x)) :=
  LinearMap.BilinForm.isCompl_span_singleton_orthogonal hx

/-- The restriction of a reflexive nondegenerate form `B` to the orthogonal
complement of a span of a single anisotropic vector remains nondegenerate. -/
theorem restrict_nondegenerate_orthogonal_spanSingleton
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V)
    (href : B.IsRefl)
    (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
    {x : V} (hx : ¬ LinearMap.BilinForm.IsOrtho B x x) :
    (LinearMap.BilinForm.restrict B
      (LinearMap.BilinForm.orthogonal B (k ∙ x))).Nondegenerate :=
  LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B
    (nondegenerate_of_orthogonal_top_eq_bot B href hnd) href hx


variable {k : Type*} [Field k]
         {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- For a reflexive form on a finite-dimensional space, a subspace `S` on which `B`
restricts nondegenerately is complementary to its orthogonal complement. -/
theorem orthogonal_isCompl_of_restrict_nondegenerate
    (B : LinearMap.BilinForm k V)
    (href : ∀ x y : V, B x y = 0 → B y x = 0)
    (S : Submodule k V)
    (hS : (LinearMap.BilinForm.restrict B S).Nondegenerate) :
    IsCompl S (LinearMap.BilinForm.orthogonal B S) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate href hS

end Garrett
