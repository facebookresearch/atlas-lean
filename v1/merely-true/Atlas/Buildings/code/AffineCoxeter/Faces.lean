/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.AffineCriterion
import Atlas.Buildings.code.AffineCoxeter.TitsConeCorollary

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup TitsCone

namespace AffineCoxeterFaces

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The affine reflection hyperplane $H_{s} \cap E$ obtained by intersecting the Coxeter wall
$H_s = \{x : x_s = 0\}$ with the affine hyperplane $E = \{x : \langle v_0, x\rangle = 1\}$. -/
def affineReflectionHyperplane (M : CoxeterMatrix B) (v₀ : B → ℝ) (s : B) :
    Set (B → ℝ) :=
  coxeterWall M s ∩ affineHyperplane M v₀

/-- The arrangement of affine reflection hyperplanes in $E$: one hyperplane $\{y : \langle\alpha, y\rangle = 0\} \cap E$
for each positive root $\alpha \in \Phi^+$. -/
def affineHyperplaneSystem (M : CoxeterMatrix B) [inst : RootSystemData M]
    (v₀ : B → ℝ) : Set (Set (B → ℝ)) :=
  {η | ∃ α ∈ inst.Φpos, η = {y : B → ℝ | pairing α y = 0} ∩ affineHyperplane M v₀}

/-- The origin $0$ does not lie on the affine hyperplane $E = \{x : \sum_s v_0(s) x_s = 1\}$
when $v_0 > 0$, since the equation evaluates to $0 \ne 1$ at $x = 0$. -/
lemma zero_not_mem_affineHyperplane [Nonempty B]
    (M : CoxeterMatrix B) (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0) :
    (0 : B → ℝ) ∉ affineHyperplane M v₀ := by
  intro h
  simp only [affineHyperplane, Set.mem_setOf_eq] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  linarith

/-- Corollary: any point on the affine hyperplane $E$ is nonzero. -/
lemma ne_zero_of_mem_affineHyperplane [Nonempty B]
    (M : CoxeterMatrix B) (v₀ : B → ℝ) (hv₀_pos : ∀ s, v₀ s > 0)
    (x : B → ℝ) (hx : x ∈ affineHyperplane M v₀) :
    x ≠ 0 := by
  intro heq
  rw [heq] at hx
  exact zero_not_mem_affineHyperplane M v₀ hv₀_pos hx

/-- The affine hyperplane $E$ lies inside $\mathcal U \setminus \{0\}$ when $v_0$ is in the radical
of the Coxeter form; i.e. $E \subseteq \mathcal U \setminus \{0\}$. -/
lemma mem_titsCone_sdiff_zero_of_mem_E [Nonempty B]
    (M : CoxeterMatrix B) [RootSystemData M]
    (hAff : IsAffineCoxeter M) (v₀ : B → ℝ)
    (hv₀_pos : ∀ s, v₀ s > 0)
    (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
    (x : B → ℝ) (hx : x ∈ affineHyperplane M v₀) :
    x ∈ titsConeSet M \ {0} := by
  refine Set.mem_diff_singleton.mpr ⟨?_, ?_⟩
  · exact affineHyperplane_subset_titsCone M hAff v₀ hv₀_pos hv₀_rad hx
  · exact ne_zero_of_mem_affineHyperplane M v₀ hv₀_pos x hx

/-- The **affine face** of type $I \subseteq B$: intersection of the Tits face $F_I$ with the
affine hyperplane $E$. -/
def affineFace (M : CoxeterMatrix B) (v₀ : B → ℝ) (I : Finset B) :
    Set (B → ℝ) :=
  titsFaceDual M I ∩ affineHyperplane M v₀

/-- The **affine fundamental chamber** $C \cap E$: the strict fundamental chamber for $W$ acting
on $E$. -/
def affineFundamentalChamber (M : CoxeterMatrix B) (v₀ : B → ℝ) :
    Set (B → ℝ) :=
  titsFundamentalChamber M ∩ affineHyperplane M v₀



/-- The vertex of $\overline{C \cap E}$ opposite to the wall $H_{s_0}$: the codimension-$(|B|-1)$
face $F_{\{s_0\}^c} \cap E$. -/
def vertexMapToE (M : CoxeterMatrix B) (v₀ : B → ℝ)
    (s₀ : B) : Set (B → ℝ) :=
  titsFaceDual M ({s₀}ᶜ) ∩ affineHyperplane M v₀


/-- Face order: $I \le J$ means the affine face $F_J \cap E$ is contained in the closure of $F_I \cap E$,
i.e. $F_J \cap E$ is a face of $F_I \cap E$. -/
def affineFaceLE (M : CoxeterMatrix B) (v₀ : B → ℝ)
    (I J : Finset B) : Prop :=
  affineFace M v₀ J ⊆ closure (affineFace M v₀ I)

end AffineCoxeterFaces
