/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped Classical

namespace ProjectionIncidence

/-- A line in `ℝ²`, encoded as a nonempty affine subspace of dimension `1`. -/
structure Line2 where
  carrier : AffineSubspace ℝ (Fin 2 → ℝ)
  dim_eq : Module.finrank ℝ carrier.direction = 1
  nonempty : (carrier : Set (Fin 2 → ℝ)).Nonempty

/-- A point `p ∈ ℝ²` belongs to a line `l : Line2` iff it lies in the underlying
affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier

/-- The number of incidences `I(X, L) = #{(x, ℓ) ∈ X × L : x ∈ ℓ}` between a finite
set of points `X ⊆ ℝ²` and a finite set of lines `L`. -/
def incidenceCount (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) : ℕ :=
  ((X ×ˢ L).filter fun p => p.1 ∈ p.2).card

end ProjectionIncidence
