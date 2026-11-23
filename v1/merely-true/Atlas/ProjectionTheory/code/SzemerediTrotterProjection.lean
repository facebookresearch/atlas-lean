/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.SzemerediTrotter

open Finset Real Set

namespace SzemerediTrotterProjection

/-- The orthogonal projection $\pi_\theta(p) = p_1 \cos\theta + p_2 \sin\theta$ of a
point $p \in \mathbb{R}^2$ in direction $\theta$, written in product form. -/
noncomputable def orthProj (θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * cos θ + p.2 * sin θ

/-- The image $\pi_\theta(X) \subset \mathbb{R}$ of a finite set $X \subset \mathbb{R}^2$
under the direction-$\theta$ projection. -/
noncomputable def projImage (θ : ℝ) (X : Finset (ℝ × ℝ)) : Finset ℝ :=
  X.image (orthProj θ)

/-- The set $D = D(X, S) \subset [0, \pi)$ of directions $\theta$ along which the
projection $\pi_\theta(X)$ has small image, $|\pi_\theta(X)| \le S$. -/
noncomputable def smallProjDirections (X : Finset (ℝ × ℝ)) (S : ℕ) : Set ℝ :=
  {θ : ℝ | θ ∈ Ico 0 π ∧ (projImage θ X).card ≤ S}





end SzemerediTrotterProjection

namespace SzemerediTrotter
open Classical


end SzemerediTrotter
