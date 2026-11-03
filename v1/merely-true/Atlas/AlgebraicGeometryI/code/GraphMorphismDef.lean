/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated

set_option maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}

/-- Graph morphism `Γ_f : X → X ×_S Y` of a morphism `f : X → Y` over `S`,
defined by `(𝟙 X, f)` via the pullback universal property (Def 18, Lec 7). -/
def graphMorphism (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) (w : sX = f ≫ sY) :
    X ⟶ pullback sX sY :=
  pullback.lift (𝟙 X) f (by rw [Category.id_comp, w])

variable (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) (w : sX = f ≫ sY)

/-- First projection of the graph morphism is the identity on `X`. -/
@[simp]
lemma graphMorphism_fst :
    graphMorphism f sX sY w ≫ pullback.fst sX sY = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- Second projection of the graph morphism is `f`. -/
@[simp]
lemma graphMorphism_snd :
    graphMorphism f sX sY w ≫ pullback.snd sX sY = f :=
  pullback.lift_snd _ _ _

/-- The graph morphism is a split monomorphism, with `pullback.fst` as retraction. -/
instance graphMorphism_isSplitMono :
    IsSplitMono (graphMorphism f sX sY w) :=
  ⟨⟨⟨pullback.fst sX sY, graphMorphism_fst f sX sY w⟩⟩⟩

/-- As a split mono, the graph morphism is in particular a monomorphism. -/
instance graphMorphism_mono :
    Mono (graphMorphism f sX sY w) :=
  IsSplitMono.mono _

/-- The graph of the identity morphism is the diagonal `Δ_{X/S}`. -/
lemma graphMorphism_id (sX : X ⟶ S) :
    graphMorphism (𝟙 X) sX sX (Category.id_comp sX) = pullback.diagonal sX := by
  unfold graphMorphism pullback.diagonal
  congr 1

/-- If the target `Y → S` is separated, the graph morphism is a closed immersion. -/
instance graphMorphism_isClosedImmersion [IsSeparated sY] :
    IsClosedImmersion (graphMorphism f sX sY w) := by
  subst w
  unfold graphMorphism
  convert (inferInstance : IsClosedImmersion (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ sY))))

end AlgebraicGeometry
