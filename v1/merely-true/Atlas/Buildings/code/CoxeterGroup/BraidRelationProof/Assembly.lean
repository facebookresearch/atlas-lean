/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers

open Finset BigOperators Real

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The braid relation for $e_s$: $(\sigma_s\sigma_t)^{m(s,t)} (e_s) = e_s$. -/
lemma rotation_power_e_s (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    (fun w => sigma M s (sigma M t w))^[M.M s t] (e s) = e s := by
  ext u
  rw [iter_e_s_formula M s t (M.M s t) u]
  rw [seqA_at_m M s t hst hm, seqB_at_m M s t hst hm]
  simp

/-- The braid relation for $e_t$: $(\sigma_s\sigma_t)^{m(s,t)} (e_t) = e_t$. -/
lemma rotation_power_e_t (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    (fun w => sigma M s (sigma M t w))^[M.M s t] (e t) = e t := by
  ext u
  rw [iter_e_t_formula M s t (M.M s t) u]
  rw [seqC_at_m M s t hst hm, seqD_at_m M s t hst hm]
  simp


omit [DecidableEq B] [Fintype B] in
/-- For $s \ne t$ and finite $m(s,t)$, the matrix entry satisfies
$B_{s,t}^2 < 1$. -/
lemma formVal_sq_lt_one (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    formVal M s t ^ 2 < 1 := by
  have hm2 := m_ge_two M s t hst hm
  simp only [formVal, if_neg hm]
  rw [neg_sq]
  have hm_pos : (0 : ℝ) < (M.M s t : ℝ) := by positivity
  have hangle_pos : 0 < π / (M.M s t : ℝ) := div_pos Real.pi_pos hm_pos
  have hangle_lt_pi : π / (M.M s t : ℝ) < π := by
    rw [div_lt_iff₀ hm_pos]
    calc π = π * 1 := by ring
      _ < π * (M.M s t : ℝ) := by
          apply mul_lt_mul_of_pos_left _ Real.pi_pos
          exact_mod_cast show 1 < M.M s t by omega
  have hsin_pos : 0 < sin (π / (M.M s t : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt_pi
  rw [Real.cos_sq']
  linarith [sq_pos_of_pos hsin_pos]

omit [DecidableEq B] [Fintype B] in
/-- $1 - B_{s,t}^2 \ne 0$, so the orthogonal projection used below is
well-defined. -/
lemma one_sub_formVal_sq_ne_zero (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    1 - formVal M s t ^ 2 ≠ 0 := by
  linarith [formVal_sq_lt_one M s t hst hm]

/-- The coefficient $\alpha$ in the decomposition $v = \alpha e_s + \beta e_t +
w$ where $w$ is $B$-orthogonal to both $e_s$ and $e_t$. -/
noncomputable def decompAlpha (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) : ℝ :=
  (bilinForm M v (e s) - formVal M s t * bilinForm M v (e t)) /
  (1 - formVal M s t ^ 2)

/-- The coefficient $\beta$ in the orthogonal decomposition of $v$ along
$e_s, e_t$, complementary to $\alpha$. -/
noncomputable def decompBeta (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) : ℝ :=
  (bilinForm M v (e t) - formVal M s t * bilinForm M v (e s)) /
  (1 - formVal M s t ^ 2)

/-- The orthogonal complement $w = v - \alpha e_s - \beta e_t$ of $v$ in the
$(e_s, e_t)$-plane. -/
noncomputable def decompW (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) : B → ℝ :=
  v - decompAlpha M s t v • e s - decompBeta M s t v • e t

/-- The decomposition identity:
$v = \alpha e_s + \beta e_t + w$. -/
theorem decomp_eq (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) :
    v = decompAlpha M s t v • e s + decompBeta M s t v • e t + decompW M s t v := by
  simp only [decompW]
  ext u; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The component $w$ is $B$-orthogonal to $e_s$. -/
theorem decomp_ortho_s (M : CoxeterMatrix B) (s t : B) (v : B → ℝ)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    bilinForm M (decompW M s t v) (e s) = 0 := by
  simp only [decompW]
  have heq : v - decompAlpha M s t v • e s - decompBeta M s t v • e t =
    v + (- decompAlpha M s t v) • e s + (- decompBeta M s t v) • e t := by
    ext u; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq, bilinForm_add_left, bilinForm_add_left, bilinForm_smul_left, bilinForm_smul_left,
      bilinForm_e_e, bilinForm_e_e, formVal_diag, formVal_symm M t s]
  simp only [decompAlpha, decompBeta]
  have hne := one_sub_formVal_sq_ne_zero M s t hst hm
  field_simp; ring

/-- The component $w$ is $B$-orthogonal to $e_t$. -/
theorem decomp_ortho_t (M : CoxeterMatrix B) (s t : B) (v : B → ℝ)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) :
    bilinForm M (decompW M s t v) (e t) = 0 := by
  simp only [decompW]
  have heq : v - decompAlpha M s t v • e s - decompBeta M s t v • e t =
    v + (- decompAlpha M s t v) • e s + (- decompBeta M s t v) • e t := by
    ext u; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq, bilinForm_add_left, bilinForm_add_left, bilinForm_smul_left, bilinForm_smul_left,
      bilinForm_e_e, bilinForm_e_e, formVal_diag]
  simp only [decompAlpha, decompBeta]
  have hne := one_sub_formVal_sq_ne_zero M s t hst hm
  field_simp; ring


/-- For $s \ne t$ with finite Coxeter order $m(s,t)$, the geometric
representation satisfies the braid relation $(\sigma_s \sigma_t)^{m(s,t)} v =
v$ on every vector $v$. -/
theorem braid_power_ne (M : CoxeterMatrix B) (s t : B)
    (hst : s ≠ t) (hm : M.M s t ≠ 0) (v : B → ℝ) :
    (fun w => sigma M s (sigma M t w))^[M.M s t] v = v := by
  set α' := decompAlpha M s t v
  set β := decompBeta M s t v
  set w := decompW M s t v
  have hv : v = α' • e s + β • e t + w := decomp_eq M s t v
  have hws : bilinForm M w (e s) = 0 := decomp_ortho_s M s t v hst hm
  have hwt : bilinForm M w (e t) = 0 := decomp_ortho_t M s t v hst hm
  conv_lhs => rw [hv]
  rw [show α' • e s + β • e t + w = (α' • e s + β • e t) + w from by
    ext u; simp [Pi.add_apply, Pi.smul_apply]]
  rw [iterate_sigma_comp_add, iterate_sigma_comp_fixes_orthogonal M s t _ w hws hwt,
      iterate_sigma_comp_add, iterate_sigma_comp_smul, iterate_sigma_comp_smul,
      rotation_power_e_s M s t hst hm, rotation_power_e_t M s t hst hm, ← hv]

/-- The braid relation hypothesis holds on the geometric representation: for
every pair $s, t$ with finite Coxeter order, $(\sigma_s\sigma_t)^{m(s,t)}$ is
the identity on $\mathbb{R}^B$. -/
noncomputable def braidRelationHyp (M : CoxeterMatrix B) : BraidRelationHyp M where
  braid_power_eq_one := by
    intro s t hm v
    by_cases hst : s = t
    · subst hst
      have hm1 : M.M s s = 1 := M.diagonal s
      simp [sigma_involution]
    · exact braid_power_ne M s t hst hm v

end CoxeterGroup
