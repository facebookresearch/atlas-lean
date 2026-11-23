/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers
import Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.Assembly
import Mathlib.GroupTheory.Coxeter.Basic

open Finset BigOperators CoxeterGroup

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The family of reflections $\sigma_s \in GL(\mathbb{R}^B)$ satisfies the
Coxeter braid relations, so it satisfies the lifting hypothesis for $M$. -/
theorem sigmaLinearEquiv_isLiftable (M : CoxeterMatrix B) :
    M.IsLiftable (fun s => sigmaLinearEquiv M s) := by
  intro s t

  ext v : 1

  simp only [LinearEquiv.coe_one, id_eq, LinearEquiv.coe_pow]

  have hcoe : ⇑(sigmaLinearEquiv M s * sigmaLinearEquiv M t) =
      fun w => sigma M s (sigma M t w) := rfl
  rw [hcoe]

  by_cases hm : M.M s t = 0
  · simp [hm]
  · exact (braidRelationHyp M).braid_power_eq_one s t hm v

/-- The geometric representation of $W$: the group homomorphism from $W$ to
$GL(\mathbb{R}^B)$ sending each simple reflection $s_i$ to $\sigma_{s_i}$. -/
noncomputable def coxeterRepresentation (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) :
    W →* ((B → ℝ) ≃ₗ[ℝ] (B → ℝ)) :=
  cs.lift ⟨fun s => sigmaLinearEquiv M s, sigmaLinearEquiv_isLiftable M⟩

/-- The geometric representation sends a simple generator $s_i$ to the
corresponding reflection $\sigma_{s_i}$ as a linear equivalence. -/
@[simp]
theorem coxeterRepresentation_simple (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (s : B) :
    coxeterRepresentation M cs (cs.simple s) = sigmaLinearEquiv M s :=
  cs.lift_apply_simple (sigmaLinearEquiv_isLiftable M) s

/-- The action of $\rho(\mathtt{wordProd}\,\omega)$ on a vector $v$ is exactly
the iterated reflection $\sigma_{s_{i_1}} \cdots \sigma_{s_{i_k}}(v)$
encoded by $\mathtt{wordSigma}$. -/
theorem coxeterRepresentation_wordProd_apply (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (word : List B) (v : B → ℝ) :
    (coxeterRepresentation M cs (cs.wordProd word)) v = wordSigma M word v := by
  induction word with
  | nil =>
    simp [CoxeterSystem.wordProd_nil, wordSigma_nil, map_one, LinearEquiv.coe_one]
  | cons s rest ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul]

    show (coxeterRepresentation M cs (cs.simple s) *
          coxeterRepresentation M cs (cs.wordProd rest)) v = _

    simp only [LinearEquiv.mul_apply]
    rw [coxeterRepresentation_simple]

    simp only [sigmaLinearEquiv_apply, ih]

    rfl

end CoxeterGroup
