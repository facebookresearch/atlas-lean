/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.Zorn

namespace HahnBanach

variable {K : Type*} {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A Hamel basis of a vector space $V$ over a field $K$ is a subset $H \subseteq V$ that is
linearly independent and whose $K$-linear span is all of $V$. Equivalently, every element of
$V$ can be written uniquely as a finite $K$-linear combination of elements of $H$. -/
def IsHamelBasis (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (H : Set V) : Prop :=
  LinearIndependent K ((↑) : H → V) ∧ Submodule.span K H = ⊤

/-- **Zorn's lemma.** If every chain in a nonempty partially ordered set $\alpha$ has an
upper bound, then $\alpha$ contains a maximal element. -/
theorem zorns_lemma {α : Type*} [Preorder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
    ∃ m : α, IsMax m :=
  zorn_le h

section HahnBanachTheorem

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

set_option backward.isDefEq.respectTransparency false in
/-- **Hahn-Banach theorem.** Let $V$ be a normed vector space and $M \subseteq V$ a subspace.
Any bounded linear functional $f : M \to \mathbb{K}$ extends to a bounded linear functional
$F : V \to \mathbb{K}$ with the same operator norm, $\|F\| = \|f\|$. -/
theorem hahn_banach_theorem (M : Subspace 𝕜 V) (f : M →L[𝕜] 𝕜) :
    ∃ F : V →L[𝕜] 𝕜, (∀ m : M, F m = f m) ∧ ‖F‖ = ‖f‖ :=
  exists_extension_norm_eq M f

end HahnBanachTheorem

section DualVectorApplication

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- For any nonzero vector $v$ in a normed space $V$, there exists a bounded linear
functional $f \in V'$ with $\|f\| = 1$ and $f(v) = \|v\|$. -/
theorem exists_norm_one_functional_achieving_norm (v : V) (hv : v ≠ 0) :
    ∃ f : V →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f v = ↑‖v‖ :=
  exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)

end DualVectorApplication

end HahnBanach

namespace HahnBanach

noncomputable section

open Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **One-step Hahn-Banach extension.** Let $V$ be a normed space, $M \subseteq V$ a subspace,
and $f : M \to \mathbb{K}$ a bounded linear functional with $\|f(m)\| \le C \|m\|$ for all
$m \in M$. If $x_0 \notin M$, then there exists a bounded linear functional $g$ on the
strictly larger subspace $M'' = M + \mathbb{K} \cdot x_0$ extending $f$ and satisfying
the same bound $\|g(v)\| \le C \|v\|$ for all $v \in M''$. -/
theorem hahn_banach_one_step_extension_bound
    (M : Subspace 𝕜 E) (f : ↥M →L[𝕜] 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (hf_bound : ∀ m : M, ‖f m‖ ≤ C * ‖(m : E)‖)
    (x₀ : E) (hx₀ : x₀ ∉ M) :
    ∃ g : ↥(M ⊔ 𝕜 ∙ x₀) →L[𝕜] 𝕜,
      (∀ m : M, g ⟨↑m, mem_sup_left m.2⟩ = f m) ∧
      (∀ v : ↥(M ⊔ 𝕜 ∙ x₀), ‖g v‖ ≤ C * ‖(v : E)‖) ∧
      M < M ⊔ 𝕜 ∙ x₀ := by
  obtain ⟨G, hG_ext, hG_norm⟩ := exists_extension_norm_eq M f
  let M' := M ⊔ 𝕜 ∙ x₀
  let g : ↥M' →L[𝕜] 𝕜 := G.comp M'.subtypeL
  refine ⟨g, ?_, ?_, ?_⟩
  · intro m
    simp only [g, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact hG_ext m
  · intro v
    simp only [g, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    have hG_le : ‖G‖ ≤ C := by
      rw [hG_norm]
      exact ContinuousLinearMap.opNorm_le_bound f hC hf_bound
    calc ‖G (v : E)‖ ≤ ‖G‖ * ‖(v : E)‖ := G.le_opNorm (v : E)
      _ ≤ C * ‖(v : E)‖ := mul_le_mul_of_nonneg_right hG_le (norm_nonneg _)
  · apply lt_of_le_of_ne le_sup_left
    intro h
    apply hx₀
    have : x₀ ∈ (M ⊔ 𝕜 ∙ x₀ : Submodule 𝕜 E) := mem_sup_right (mem_span_singleton_self x₀)
    rwa [← h] at this

end
