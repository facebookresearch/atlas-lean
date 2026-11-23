/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

set_option maxHeartbeats 400000 in
/-- Corollary 16 (cf. Thm 12.1): for any module `M` over a commutative ring
`R`, the associated sheaf `M̃` on `Spec R` is quasicoherent, exhibiting the
tilde functor as landing in quasicoherent sheaves. -/
theorem tilde_isQuasicoherent_cor16 {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance
