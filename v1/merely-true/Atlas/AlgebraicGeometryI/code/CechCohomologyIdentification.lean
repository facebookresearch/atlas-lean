/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.TateCechInfra

noncomputable section

universe v

namespace CechCohomologyIdentification

variable {k : Type*} [Field k]
















/-- The integer-valued cohomology dimensions stored in `CechSheafData` agree definitionally with
the actual Čech cohomology of the Tate duality setup. -/
theorem serre_duality_identification_is_rfl
    (D : TateCechInfra.CechSheafData k) :

    D.h0_EK = ↑(Module.finrank k ↥D.setup.dual.cechH0) ∧

    D.h1_E = ↑(Module.finrank k D.setup.cechH1) :=
  ⟨rfl, rfl⟩

end CechCohomologyIdentification

end
