/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Complex ZMod

noncomputable section

namespace ProjectionTheory

/-- Projection $\pi_p f : \mathbb{Z}_p \to \mathbb{C}$ onto the subspace indexed by
$\mathbb{Z}_p$: at residue $a$ it sums $f(n)$ over those $n \in [N]$ with $n \equiv a \pmod p$.
A companion definition expressing the dictionary $\widehat{\pi_V f}(\xi) = \hat f(\xi)$
for $V = \mathbb{Z}_p$. -/
def modProjection (N p : ℕ) (f : Fin N → ℂ) (a : ZMod p) : ℂ :=
  ∑ n : Fin N, if ((n : ℕ) : ZMod p) = a then f n else 0

end ProjectionTheory
