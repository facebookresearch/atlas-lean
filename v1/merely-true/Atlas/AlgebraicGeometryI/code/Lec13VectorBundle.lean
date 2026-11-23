/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.AffineSpace

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

/-- Definition 28 (Lec 13): a morphism `f : X → Y` is a vector bundle of rank `n` if
there is an open cover `{Uᵢ}` of `Y` such that, over each `Uᵢ`, `f` is isomorphic
(over `Uᵢ`) to the trivial affine bundle `𝔸(Fin n; Uᵢ) → Uᵢ`. -/
def IsVectorBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∃ (ι : Type u) (U : ι → Y.Opens), (⨆ i, U i = ⊤) ∧
    ∀ i, ∃ (e : (f ⁻¹ᵁ (U i)).toScheme ≅ 𝔸(Fin n; ↑(U i))),
      e.hom ≫ (𝔸(Fin n; ↑(U i)) ↘ ↑(U i)) = f ∣_ (U i)

/-- A sheaf of `O_X`-modules `ℱ` is locally free of rank `r` if `X` admits an open
cover `{Uᵢ}` such that `ℱ|_{Uᵢ}` is isomorphic to the free `O_{Uᵢ}`-module of rank `r`.
This is the sheaf counterpart of `IsVectorBundle`. -/
def IsLocallyFreeSheaf {X : Scheme.{u}} (ℱ : X.Modules) (r : ℕ) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens),
    (⨆ i, U i = ⊤) ∧
    ∀ i, Nonempty (ℱ.restrict (U i).ι ≅
      SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin r)))

end
