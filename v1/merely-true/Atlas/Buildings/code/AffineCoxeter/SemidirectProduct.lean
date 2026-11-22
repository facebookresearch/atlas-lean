/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.AffineWeylGroups

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- The translation subgroup $T \subseteq W$ is **normal** in the affine Weyl group $W$. -/
theorem translationSubgroup_normal :
    (W.TranslationSubgroup.subgroupOf W.group).Normal := by
  constructor
  intro ⟨n, hn_W⟩ hn_mem ⟨g, hg_W⟩
  simp only [Subgroup.mem_subgroupOf] at hn_mem ⊢
  simp only [AffineReflectionGroup.TranslationSubgroup, Subgroup.mem_inf,
    MonoidHom.mem_ker] at hn_mem ⊢
  exact ⟨W.group.mul_mem (W.group.mul_mem hg_W hn_W) (W.group.inv_mem hg_W),
    by simp [hn_mem.2]⟩

/-- The **stabilizer subgroup** $W_x = \{g \in W : g \cdot x = x\}$ of a point $x \in E$. -/
def Stabilizer (x : E) : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {g ∈ W.group | g x = x}
  mul_mem' := by
    intro a b ⟨ha_W, ha_fix⟩ ⟨hb_W, hb_fix⟩
    exact ⟨W.group.mul_mem ha_W hb_W, by change a (b x) = x; rw [hb_fix, ha_fix]⟩
  one_mem' := ⟨W.group.one_mem, rfl⟩
  inv_mem' := by
    intro a ⟨ha_W, ha_fix⟩
    refine ⟨W.group.inv_mem ha_W, ?_⟩
    show a⁻¹ x = x
    calc a⁻¹ x = a⁻¹ (a x) := by rw [ha_fix]
      _ = (a⁻¹ * a) x := rfl
      _ = (1 : E ≃ᵃⁱ[ℝ] E) x := by rw [inv_mul_cancel]
      _ = x := rfl

/-- The stabilizer $W_x$ is a subgroup of $W$. -/
theorem stabilizer_le_group (x : E) : W.Stabilizer x ≤ W.group :=
  fun _ hg => hg.1

/-- The linear part map sends the stabilizer $W_x$ **surjectively** onto the finite linear part
group $\overline W$: for any $\overline w \in \overline W$ there is $g \in W_x$ with linear part $\overline w$.
This is the key surjectivity used in the semidirect-product decomposition. -/
theorem stabilizer_surjects_unconditional (x : E) (hx : W.SpecialPoint x) :
    ∀ wbar ∈ W.LinearPartGroup, ∃ g ∈ W.Stabilizer x, linearPartHom g = wbar := by
  intro wbar hwbar

  set R := {s : E ≃ᵃⁱ[ℝ] E | s ∈ W.group ∧ ∃ η ∈ W.arrangement.hyperplanes,
    (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1} with hR_def

  set S_img := (W.Stabilizer x).map linearPartHom with hS_img_def

  suffices wbar ∈ S_img by
    obtain ⟨g, hg, rfl⟩ := this
    exact ⟨g, hg, rfl⟩

  have hLinPart : W.LinearPartGroup = Subgroup.closure (linearPartHom '' R) := by
    unfold LinearPartGroup
    rw [W.generated_by_reflections]
    exact MonoidHom.map_closure linearPartHom R

  rw [hLinPart] at hwbar
  apply (Subgroup.closure_le S_img).mpr _ hwbar

  rintro _ ⟨s, ⟨hs_group, η, hη_arr, h_fix, h_inv⟩, rfl⟩


  obtain ⟨η', hη'_arr, ⟨t, h_par⟩, hx_carrier⟩ := hx η hη_arr

  obtain ⟨s', hs'_group, h_fix', h_inv', _⟩ := W.has_reflection η' hη'_arr

  have hs'_stab : s' ∈ W.Stabilizer x := ⟨hs'_group, h_fix' x hx_carrier⟩

  have ht_ne : t ≠ 0 := by
    intro ht0
    have : η'.normal = (0 : ℝ) • η.normal := by rw [← ht0, h_par]
    simp at this
    exact η'.normal_ne_zero this

  have h_par_rev : ∃ t' : ℝ, η.normal = t' • η'.normal := by
    refine ⟨1/t, ?_⟩
    rw [h_par, smul_smul, one_div, inv_mul_cancel₀ ht_ne, one_smul]

  have h_same_lin : linearPartHom s' = linearPartHom s :=
    W.parallel_reflections_same_linear_part s' hs'_group s hs_group
      η' hη'_arr η hη_arr h_fix' h_inv' h_fix h_inv h_par_rev

  rw [← h_same_lin]
  exact ⟨s', hs'_stab, rfl⟩

/-- **Semidirect product decomposition** $W = T \rtimes W_x$: every $w \in W$ factors uniquely as
$w = t \cdot s$ with $t \in T$ a translation and $s \in W_x$ a stabilizer element of a special point $x$. -/
theorem semidirect_product_decomposition (x : E)
    (hx : W.SpecialPoint x)
    (hgen : ∀ wbar ∈ W.LinearPartGroup,
      ∃ g ∈ W.Stabilizer x, linearPartHom g = wbar) :
    ∀ w ∈ W.group,
      ∃ t ∈ W.TranslationSubgroup, ∃ s ∈ W.Stabilizer x,
        w = t * s := by
  intro w hw
  have hw_lin : linearPartHom w ∈ W.LinearPartGroup := ⟨w, hw, rfl⟩
  obtain ⟨s, hs_stab, hs_lin⟩ := hgen _ hw_lin
  refine ⟨w * s⁻¹, ?_, s, hs_stab, ?_⟩
  · constructor
    · exact W.group.mul_mem hw (W.group.inv_mem (W.stabilizer_le_group x hs_stab))
    · show w * s⁻¹ ∈ linearPartHom.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs_lin, mul_inv_cancel]
  · group

/-- **Unconditional form of the semidirect product decomposition** $W = T \rtimes W_x$:
combines `semidirect_product_decomposition` with the surjectivity `stabilizer_surjects_unconditional`. -/
theorem semidirect_product_decomposition_unconditional (x : E)
    (hx : W.SpecialPoint x) :
    ∀ w ∈ W.group,
      ∃ t ∈ W.TranslationSubgroup, ∃ s ∈ W.Stabilizer x,
        w = t * s :=
  W.semidirect_product_decomposition x hx (W.stabilizer_surjects_unconditional x hx)

end AffineReflectionGroup
