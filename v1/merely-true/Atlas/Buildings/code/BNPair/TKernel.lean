/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
variable (bp : BNPair G M)


/-- The action of $N$ on the standard apartment $W$ by left translation: $n \cdot w =
\pi(n) \cdot w$. -/
def BNPair.apartmentActionFun (n : bp.N) (w : M.Group) : M.Group :=
  bp.π n * w

/-- Elements of $T = B \cap N$ act trivially on the apartment $W$: $\pi(t) = 1$ for $t \in T$,
hence $t \cdot w = w$ for every $w \in W$. -/
theorem BNPair.T_acts_trivially_on_apartment (n : bp.N) (hn : (n : G) ∈ bp.T)
    (w : M.Group) : bp.apartmentActionFun n w = w := by
  simp [BNPair.apartmentActionFun, (bp.π_ker n).mpr hn]


/-- **T-kernel lemma (§5.2):** the torus $T$, viewed as a subgroup of $N$, coincides with
the kernel of the projection $\pi : N \to W$. Equivalently $T = \pi^{-1}(1)$. -/
theorem BNPair.T_subgroupOf_eq_ker : bp.T.subgroupOf bp.N = bp.π.ker := by
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  exact (bp.π_ker ⟨x, hx⟩).symm

/-- $T$ is normal in $N$, since $T = \ker \pi$ as a subgroup of $N$. -/
instance BNPair.T_normal_in_N : (bp.T.subgroupOf bp.N).Normal := by
  rw [bp.T_subgroupOf_eq_ker]
  exact MonoidHom.normal_ker bp.π


/-- The induced homomorphism $N/T \to W$ obtained by descending $\pi : N \to W$ through
its kernel $T$. -/
noncomputable def BNPair.quotientToW :
    bp.N ⧸ (bp.T.subgroupOf bp.N) →* M.Group :=
  QuotientGroup.lift _ bp.π (by
    intro x hx
    simp [Subgroup.mem_subgroupOf] at hx
    exact (bp.π_ker x).mpr hx)

/-- $N/T \to W$ is injective: its kernel equals $T/T = 1$. -/
theorem BNPair.quotientToW_injective :
    Function.Injective (bp.quotientToW) := by
  unfold BNPair.quotientToW
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [QuotientGroup.ker_lift]
  rw [← bp.T_subgroupOf_eq_ker]
  exact QuotientGroup.map_mk'_self _

/-- $N/T \to W$ is surjective, since $\pi : N \to W$ is already surjective. -/
theorem BNPair.quotientToW_surjective :
    Function.Surjective (bp.quotientToW) := by
  intro w
  obtain ⟨n, hn⟩ := bp.π_surj w
  exact ⟨QuotientGroup.mk n, by simp [BNPair.quotientToW, hn]⟩

/-- $N/T \to W$ is bijective. -/
theorem BNPair.quotientToW_bijective :
    Function.Bijective (bp.quotientToW) :=
  ⟨bp.quotientToW_injective, bp.quotientToW_surjective⟩

/-- **The isomorphism $N/T \cong W$.** Packages `quotientToW` and its bijectivity into a
group isomorphism, identifying the Weyl group $W$ of the Coxeter system with the
quotient $N/T$ of the BN-pair. -/
noncomputable def BNPair.quotientIso :
    bp.N ⧸ (bp.T.subgroupOf bp.N) ≃* M.Group :=
  MulEquiv.ofBijective bp.quotientToW bp.quotientToW_bijective
