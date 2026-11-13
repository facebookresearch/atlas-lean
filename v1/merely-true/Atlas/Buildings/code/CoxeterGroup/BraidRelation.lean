/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- If $v$ is $B$-orthogonal to $e_s$, then the reflection $\sigma_s$ fixes
$v$: $\sigma_s(v) = v$. -/
theorem sigma_fixes_orthogonal (M : CoxeterMatrix B) (s : B) (v : B → ℝ)
    (h : bilinForm M v (e s) = 0) :
    sigma M s v = v := by
  ext t
  simp only [sigma, h]
  ring


/-- If $v$ is $B$-orthogonal to both $e_s$ and $e_t$, then
$\sigma_s \sigma_t$ fixes $v$. -/
theorem sigma_comp_fixes_orthogonal (M : CoxeterMatrix B) (s t : B) (v : B → ℝ)
    (hs : bilinForm M v (e s) = 0) (ht : bilinForm M v (e t) = 0) :
    sigma M s (sigma M t v) = v := by
  rw [sigma_fixes_orthogonal M t v ht, sigma_fixes_orthogonal M s v hs]

/-- Explicit formula for $\sigma_s \sigma_t$ applied to $e_s$ in terms of the
matrix entry $B_{s,t}$. -/
theorem sigma_comp_e_s (M : CoxeterMatrix B) (s t : B) :
    sigma M s (sigma M t (e s)) =
    fun u => (4 * formVal M s t ^ 2 - 1) * e s u - 2 * formVal M s t * e t u := by

  rw [sigma_e_other M t s]


  rw [show (fun u => e s u - 2 * formVal M s t * e t u) =
    e s + (-2 * formVal M s t) • e t from by
    ext u; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring]
  rw [sigma_add, sigma_smul]

  rw [sigma_e_self, sigma_e_other M s t]
  ext u
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [formVal_symm M t s]
  ring

/-- Explicit formula for $\sigma_s \sigma_t$ applied to $e_t$. -/
theorem sigma_comp_e_t (M : CoxeterMatrix B) (s t : B) :
    sigma M s (sigma M t (e t)) =
    fun u => 2 * formVal M s t * e s u - e t u := by

  have h1 : sigma M t (e t) = fun u => -(e t u) := sigma_e_self M t
  rw [h1]

  rw [show (fun u => -(e t u)) = (-1 : ℝ) • e t from by
    ext u; simp [Pi.smul_apply, smul_eq_mul]]
  rw [sigma_smul, sigma_e_other M s t]
  ext u
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [formVal_symm M t s]
  ring


/-- The braid relation hypothesis on the geometric representation: for every
pair $s, t$ with finite Coxeter order $m(s,t)$, the composition
$\sigma_s \sigma_t$ has order dividing $m(s,t)$ on the representation. -/
structure BraidRelationHyp (M : CoxeterMatrix B) where
  braid_power_eq_one : ∀ (s t : B), M.M s t ≠ 0 →
    ∀ (v : B → ℝ), (fun w => sigma M s (sigma M t w))^[M.M s t] v = v

end CoxeterGroup
