/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.StrongIsometryExt
import Mathlib.GroupTheory.Coxeter.Length

set_option maxHeartbeats 400000

variable {V : Type*} [DecidableEq V]

/-- The gallery distance between two chambers $C, D$ in a building equals the
Coxeter length of their $W$-valued distance $\delta(C, D)$. -/
theorem galleryDist_eq_coxeterLength
    {V : Type*} [DecidableEq V]
    {b : Building V}
    (δW : Building.WValuedDist b)
    (C D : Finset V) :
    galleryDist b.toChamberComplex.toSimplicialComplex C D =
    δW.coxeterMatrix.toCoxeterSystem.length (δW.delta C D) :=
  δW.galleryDist_eq_length C D

/-- If two pairs of chambers have the same $W$-valued distance, then they have
the same gallery distance. -/
theorem delta_eq_imp_galleryDist_eq
    {b : Building V}
    (δW : Building.WValuedDist b)
    (C D C' D' : Finset V) :
    δW.delta C D = δW.delta C' D' →
    galleryDist b.toChamberComplex.toSimplicialComplex C D =
    galleryDist b.toChamberComplex.toSimplicialComplex C' D' := by
  intro h
  rw [galleryDist_eq_coxeterLength δW C D, galleryDist_eq_coxeterLength δW C' D', h]

