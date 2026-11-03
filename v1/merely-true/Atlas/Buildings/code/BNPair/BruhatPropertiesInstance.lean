/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.CellCoverProof
import Atlas.Buildings.code.BNPair.CellInvProof
import Atlas.Buildings.code.BNPair.CellDisjointProof
import Atlas.Buildings.code.BNPair.CellMulParabolicProof
import Atlas.Buildings.code.BNPair.CellMulFiniteProof
import Atlas.Buildings.code.CoxeterGroup.ParabolicInjective
import Atlas.Buildings.code.BNPair.SubgroupOverBProof
import Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import Atlas.Buildings.code.BNPair.ConjugatorProof
import Atlas.Buildings.code.BNPair.ParabolicDefs

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} [DecidableEq B_idx] [Fintype B_idx]
  {M : CoxeterMatrix B_idx}

/-- Assemble the full `BruhatProperties` bundle (cell cover/disjointness/inversion/multiplication
within parabolics, conjugator targeting, finiteness) for a BN-pair from its axioms. -/
noncomputable def BNPair.BruhatProperties.fromAxioms
    (bp : BNPair G M) (ax : BNPairAxioms bp) : BNPair.BruhatProperties bp where
  cell_disjoint := CellDisjoint.cell_disjoint_from_bnpair bp ax
  cell_cover := CellCover.cell_cover_from_bnpair bp ax
  cell_inv := fun w g hg => BNPair.cell_inv_from_bnpair bp w g hg
  cell_mul_in_parabolic := CellMulParabolic.cell_mul_in_parabolic_from_bnpair bp ax
  parabolicW_injective := fun S₁ S₂ h =>
    M.toCoxeterSystem.parabolicSubgroup_injective S₁ S₂ h
  subgroup_over_B_eq_parabolic := SubgroupOverB.subgroup_over_B_eq_parabolic_from_bnpair bp ax
  normalizer_in_parabolic := NormalizerParabolic.normalizer_in_parabolic_from_bnpair bp ax
  conjugator_in_target := ConjugatorProof.conjugator_in_target_from_bnpair bp ax
  cell_mul_finite := CellMulFinite.cell_mul_finite_from_bnpair bp ax
