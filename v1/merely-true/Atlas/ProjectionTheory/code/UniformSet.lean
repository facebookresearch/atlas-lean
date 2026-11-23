/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset

namespace UniformSet

variable {d : ℕ}

/-- `cubeOf N m j p` returns the coordinates of the dyadic cube at scale `Δ^j = N^{-j}`
(working in the grid `{0, …, N^m - 1}^d`) that contains the lattice point `p`.
Each coordinate is obtained by dividing `p i` by `N^(m - j)`, i.e. by truncating the
last `m - j` base-`N` digits. -/
def cubeOf (N m j : ℕ) (p : Fin d → ℕ) : Fin d → ℕ :=
  fun i => p i / N ^ (m - j)

/-- The branching count `|Q ∩ X|^*_{Δ^{j+1}}`: the number of distinct
sub-cubes at scale `Δ^{j+1}` that are needed to cover the points of `X`
lying inside the scale-`Δ^j` cube `Q`. Formally, it counts the image of
`X ∩ Q` under the next finer cube map `cubeOf N m (j + 1)`. -/
noncomputable def subcubeCovering (N m j d : ℕ)
    (X : Finset (Fin d → ℕ)) (Q : Fin d → ℕ) : ℕ :=
  ((X.filter (fun p => cubeOf N m j p = Q)).image (cubeOf N m (j + 1))).card

/-- `IsUniform N m d X` says that the set `X ⊂ {0, …, N^m - 1}^d` is
`(Δ, m)`-uniform with `Δ = 1/N`: for every scale `j < m`, there is a single
"branching factor" `R_j` such that **every** non-empty scale-`Δ^j` cube
`Q` of `X` is split into exactly `R_j` non-empty scale-`Δ^{j+1}` sub-cubes
(`|Q ∩ X|^*_{Δ^{j+1}} = R_j`). -/
def IsUniform (N m d : ℕ) (X : Finset (Fin d → ℕ)) : Prop :=
  ∀ j : ℕ, j < m →
    ∃ R : ℕ, ∀ Q : Fin d → ℕ,
      (X.filter (fun p => cubeOf N m j p = Q)).Nonempty →
      subcubeCovering N m j d X Q = R

end UniformSet
