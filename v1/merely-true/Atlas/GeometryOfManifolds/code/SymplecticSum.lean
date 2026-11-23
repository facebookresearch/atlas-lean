/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.LefschetzPencils

set_option autoImplicit false

open DifferentialFormSpace


/-- Data describing a symplectic sum (Definition 3): the differential-form structure
on the connected sum of two symplectic manifolds glued along a codimension-2
symplectic submanifold, here aliased to the underlying `FiberSum.DFS` structure. -/
abbrev SymplecticSumData := @FiberSum.DFS
