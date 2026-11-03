/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

universe u

namespace SerreDualityStatement

/-- Abstract vector-space-level model of a smooth complete curve over `k`:
locally free sheaves with finite-dimensional global sections and `H¹`,
together with a Serre dual involution and distinguished `O_X`, `K_X`. -/
structure SmoothCompleteCurveVS (k : Type u) [Field k] where
  LocallyFreeSheaf : Type u
  globalSections : LocallyFreeSheaf → Type u
  globalSections_addCommGroup : ∀ E, AddCommGroup (globalSections E)
  globalSections_module : ∀ E, Module k (globalSections E)
  globalSections_finiteDimensional : ∀ E, Module.Finite k (globalSections E)
  H1 : LocallyFreeSheaf → Type u
  H1_addCommGroup : ∀ E, AddCommGroup (H1 E)
  H1_module : ∀ E, Module k (H1 E)
  H1_finiteDimensional : ∀ E, Module.Finite k (H1 E)
  serreDual : LocallyFreeSheaf → LocallyFreeSheaf
  canonicalSheaf : LocallyFreeSheaf
  structureSheaf : LocallyFreeSheaf
  serreDual_globalSections_equiv : ∀ E,
    globalSections (serreDual (serreDual E)) ≃ₗ[k] globalSections E
  serreDual_H1_equiv : ∀ E,
    H1 (serreDual (serreDual E)) ≃ₗ[k] H1 E

variable {k : Type u} [Field k]

attribute [instance] SmoothCompleteCurveVS.globalSections_addCommGroup
attribute [instance] SmoothCompleteCurveVS.globalSections_module
attribute [instance] SmoothCompleteCurveVS.globalSections_finiteDimensional
attribute [instance] SmoothCompleteCurveVS.H1_addCommGroup
attribute [instance] SmoothCompleteCurveVS.H1_module
attribute [instance] SmoothCompleteCurveVS.H1_finiteDimensional




end SerreDualityStatement
