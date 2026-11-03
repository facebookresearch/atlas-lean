/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.SphericalBuilding.FinsetGapCorrespondenceProof

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Cascade of constructions assembling the thin-apartment property unconditionally for
$n \ge 2$: from the finset gap and frame–finset correspondence, derive a submodule gap
insertion, then a frame gap filler, then a panel-gap, a direct panel extension, and finally
the full `ThinApartmentHyp`. -/
noncomputable def thinApartmentHypComposed (hn2 : 2 ≤ n) : ThinApartmentHyp k n :=

  thinApartmentHyp k n

    (panelExtensionOfDirect k n

      (directPanelExtensionOfGap k n

        (panelGapOfFrameGapFiller k n

          (frameGapFillerOfGapInsertion k n

            (submoduleGapInsertionOfSubHyps k n

              (frameFinsetCorrespondenceHyp k n)

              (finsetChainGapHyp n hn2))))))

end GLnBuilding
