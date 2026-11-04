/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6
import Atlas.HighDimensionalStatistics.code.Chapter1.Cor_1_7
import Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_8
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_11

open MeasureTheory ProbabilityTheory

/-- Short alias for Theorem 1.6: any finite linear combination of independent
sub-Gaussian random variables is again sub-Gaussian, with variance proxy
scaled by the sum of squared coefficients. -/
abbrev thm_1_6 := @theorem_1_6_subgaussian_vector

/-- Short alias for the upper-tail part of Corollary 1.7: tail bound for a
weighted sum of independent sub-Gaussian variables. -/
abbrev cor_1_7_upper := @corollary_1_7_upper_tail

/-- Short alias for the lower-tail part of Corollary 1.7: lower-tail bound for
a weighted sum of independent sub-Gaussian variables. -/
abbrev cor_1_7_lower := @corollary_1_7_lower_tail

/-- Short alias for Corollary 1.7 (combined two-sided form): both upper and
lower tail bounds for a weighted sum of independent sub-Gaussian variables. -/
abbrev cor_1_7 := @corollary_1_7_linear_combination_tail

/-- Short alias for the MGF form of Hoeffding's lemma (Lemma 1.8): the moment
generating function bound `E[e^{sX}] ≤ exp(s²(b-a)²/8)` for centered bounded
random variables. -/
abbrev lemma_1_8_mgf := @hoeffding_mgf_bound

/-- Short alias for Hoeffding's lemma (Lemma 1.8): a centered random variable
taking values in `[a,b]` is sub-Gaussian with variance proxy `(b-a)²/4`. -/
abbrev lemma_1_8 := @lemma_1_8_hoeffding
