/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Module AlgebraicGeometry

universe u

namespace ArithmeticGeometry

/-- A curve over a field $k$: an integral scheme equipped with a smooth proper structure morphism to $\mathrm{Spec}(k)$ of relative dimension $1$. -/
structure Curve_k (k : Type u) [Field k] where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ Spec (.of k)
  [isIntegral : IsIntegral toScheme]
  [isProper : IsProper structureMorphism]
  [isSmooth : SmoothOfRelativeDimension 1 structureMorphism]

attribute [instance] Curve_k.isIntegral Curve_k.isProper Curve_k.isSmooth

/-- A function field of one variable over $k$: a finitely generated extension $F/k$ of transcendence degree $1$ in which $k$ is algebraically closed in $F$. -/
class FunctionField_k (k : Type*) (F : Type*) [Field k] [Field F] [Algebra k F] where
  finitelyGenerated : (⊤ : IntermediateField k F).FG
  transcendenceDegreeOne : ∃ (x : F), Transcendental k x ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) F
  algClosedInF : ∀ (x : F), IsAlgebraic k x → x ∈ (⊥ : IntermediateField k F)


namespace FunctionField_k

variable {k : Type*} [Field k]
variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

/-- The degree of a morphism of function fields $\varphi : F_2 \to F_1$: the degree $[F_1 : \varphi(F_2)]$ of $F_1$ over the image. -/
def Morphism.degree (φ : F₂ →+* F₁) : ℕ :=
  Module.finrank φ.fieldRange F₁


end FunctionField_k

end ArithmeticGeometry

end
