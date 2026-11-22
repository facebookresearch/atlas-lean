/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

namespace InnerProductSpaces

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

theorem exists_orthonormal_basis :
    Nonempty (OrthonormalBasis (Fin (Module.finrank 𝕜 V)) 𝕜 V) :=
  ⟨stdOrthonormalBasis 𝕜 V⟩
