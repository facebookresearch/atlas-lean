/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Atlas.HighDimensionalStatistics.code.Chapter2.Thm_2_2
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_3
import Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_4
import Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_9
import Atlas.HighDimensionalStatistics.code.Chapter10.Schwartz_Repr
import Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props
import Atlas.HighDimensionalStatistics.code.Chapter12.MicrolocalAnalysis
import Atlas.HighDimensionalStatistics.code.Chapter16.Props


/-- Sentinel value confirming that the per-chapter top-level files for
the Rigollet "High-Dimensional Statistics" formalization all compile and link
together via the imports above. -/
def Rigollet.buildOk : Bool := true
