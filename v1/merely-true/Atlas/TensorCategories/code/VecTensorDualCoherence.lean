/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.TensorCategories.code.VecDualMapBridge

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Module Category

universe u

noncomputable section

namespace VecTensorDualCoherence

variable (k : Type u) [Field k]

/-- The canonical double-dual isomorphism `V ≅ (V*)*` in `FGModuleCat k`, packaged
from the linear-algebraic evaluation equivalence on finite-dimensional vector spaces. -/
noncomputable def vecDoubleDualIso (V : FGModuleCat k) : V ≅ (Vᘁ)ᘁ :=
  (Module.evalEquiv k V).toFGModuleCatIso

/-- The tensor-coherence isomorphism `(V*)* ⊗ (W*)* ≅ ((V ⊗ W)*)*` in `FGModuleCat k`,
assembled from the double-dual isos on `V`, `W`, and `V ⊗ W`. -/
noncomputable def vecTensorCoherenceIso (V W : FGModuleCat k) :
    (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : FGModuleCat k)ᘁ : FGModuleCat k)ᘁ :=
  (MonoidalCategory.tensorIso (vecDoubleDualIso k V).symm (vecDoubleDualIso k W).symm) ≪≫
    (vecDoubleDualIso k (V ⊗ W))

end VecTensorDualCoherence

end
