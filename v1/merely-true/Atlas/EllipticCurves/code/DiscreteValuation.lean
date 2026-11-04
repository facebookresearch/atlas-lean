/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-- A discrete valuation on a field $F$, i.e. a surjective homomorphism $v : F^\times \to
\mathbb{Z}$ satisfying $v(x+y) \geq \min(v(x), v(y))$ (Definition 23.4). Packaged as a
Mathlib `Valuation` valued in $\mathbb{Z}_\infty$ together with a rank-one discreteness
hypothesis. -/
structure DiscreteValuation (F : Type*) [Field F] where
  val : Valuation F (WithZero (Multiplicative ℤ))
  [discrete : Valuation.IsRankOneDiscrete val]

attribute [instance] DiscreteValuation.discrete

namespace DiscreteValuation

variable {F : Type*} [Field F] (v : DiscreteValuation F)

/-- The valuation subring $R = \{x \in F : v(x) \geq 0\}$ of a discrete valuation. -/
def valuationSubring : ValuationSubring F :=
  v.val.valuationSubring

/-- The underlying subring of $F$ associated to a discrete valuation. -/
def valuationRing : Subring F :=
  v.valuationSubring.toSubring

/-- The unique maximal ideal $\mathfrak{m} = \{x \in R : v(x) \geq 1\}$ of the valuation ring. -/
noncomputable def maximalIdeal : Ideal v.valuationSubring :=
  IsLocalRing.maximalIdeal v.valuationSubring

/-- An element $u \in F$ is a uniformizer for $v$ when $v(u) = 1$. -/
def IsUniformizerOf (u : F) : Prop :=
  v.val.IsUniformizer u

/-- The valuation ring of a discrete valuation is a principal ideal domain (Definition 23.4). -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing v.valuationSubring :=
  Valuation.valuationSubring_isPrincipalIdealRing v.val

end DiscreteValuation
