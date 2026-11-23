/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open scoped InnerProductSpace

namespace OrthonormalBases

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def IsOrthonormalSequence (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (φ : ℕ → E) : Prop :=
  Orthonormal 𝕜 φ

theorem IsOrthonormalSequence.norm_eq_one {φ : ℕ → E} (h : IsOrthonormalSequence 𝕜 φ)
    (n : ℕ) : ‖φ n‖ = 1 :=
  h.1 n

theorem IsOrthonormalSequence.inner_eq_zero {φ : ℕ → E} (h : IsOrthonormalSequence 𝕜 φ)
    {n m : ℕ} (hne : n ≠ m) : ⟪φ n, φ m⟫_𝕜 = 0 :=
  h.2 hne

end OrthonormalBases

end

noncomputable section

open Filter Topology

open scoped InnerProductSpace

namespace OrthonormalBases

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {α : Type*} {l : Filter α}

theorem inner_tendsto_of_tendsto {u v : α → E} {a b : E}
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b)) :
    Tendsto (fun n => ⟪u n, v n⟫_𝕜) l (𝓝 ⟪a, b⟫_𝕜) :=
  hu.inner hv

end OrthonormalBases

end

noncomputable section

open scoped InnerProductSpace
open Submodule

namespace OrthonormalBases

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {φ : ℕ → E}

theorem hasSum_inner_smul_of_dense_span (hφ : Orthonormal 𝕜 φ)
    (ha : (span 𝕜 (Set.range φ)).topologicalClosure = ⊤) (f : E) :
    HasSum (fun n => @inner 𝕜 _ _ (φ n) f • φ n) f := by
  let b := HilbertBasis.mk hφ ha.ge
  have hb : (b : ℕ → E) = φ := HilbertBasis.coe_mk hφ ha.ge
  have := b.hasSum_repr f
  simp only [b.repr_apply_apply] at this
  rwa [hb] at this

theorem parseval_of_dense_span (hφ : Orthonormal 𝕜 φ)
    (ha : (span 𝕜 (Set.range φ)).topologicalClosure = ⊤) (f : E) :
    HasSum (fun n => ‖@inner 𝕜 _ _ (φ n) f‖ ^ 2) (‖f‖ ^ 2) := by
  let b := HilbertBasis.mk hφ ha.ge
  have hb : (b : ℕ → E) = φ := HilbertBasis.coe_mk hφ ha.ge
  have h1 := b.hasSum_inner_mul_inner f f
  have h2 := (RCLike.reCLM (K := 𝕜)).hasSum h1
  simp only [RCLike.reCLM_apply] at h2
  simp_rw [show ∀ n, RCLike.re (@inner 𝕜 _ _ f (b n) * @inner 𝕜 _ _ (b n) f) =
      ‖@inner 𝕜 _ _ (b n) f‖ ^ 2 from fun n => by
    rw [inner_mul_symm_re_eq_norm, norm_mul, sq]
    congr 1
    rw [← RCLike.norm_conj (@inner 𝕜 _ _ f (b n))]
    congr 1
    exact inner_conj_symm (𝕜 := 𝕜) (b n) f, hb] at h2
  rwa [inner_self_eq_norm_sq (𝕜 := 𝕜)] at h2

omit [CompleteSpace E] in
theorem dense_span_of_hasSum_inner_smul
    (hc : ∀ f : E, HasSum (fun n => @inner 𝕜 _ _ (φ n) f • φ n) f) :
    (span 𝕜 (Set.range φ)).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro f _
  apply mem_closure_of_tendsto (hc f)
  apply Filter.Eventually.of_forall
  intro s
  apply sum_mem
  intro n _
  apply smul_mem
  exact subset_span ⟨n, rfl⟩

theorem dense_span_of_parseval
    (hb : ∀ f : E, HasSum (fun n => ‖@inner 𝕜 _ _ (φ n) f‖ ^ 2) (‖f‖ ^ 2)) :
    (span 𝕜 (Set.range φ)).topologicalClosure = ⊤ := by
  rw [← orthogonal_orthogonal_eq_closure, orthogonal_eq_top_iff, eq_bot_iff]
  intro f hf
  rw [mem_bot]
  have h_inner_zero : ∀ n, @inner 𝕜 _ _ (φ n) f = 0 := fun n =>
    hf (φ n) (subset_span ⟨n, rfl⟩)
  have h_parseval := hb f
  simp only [h_inner_zero, norm_zero, sq, mul_zero] at h_parseval
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg f, h_parseval.unique hasSum_zero])

end OrthonormalBases

end

noncomputable section

open scoped InnerProductSpace

namespace OrthonormalBases

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {φ : ℕ → E}

omit [CompleteSpace E] in
theorem inner_hasSum_of_orthonormal_series (hφ : Orthonormal 𝕜 φ)
    {a b : ℕ → 𝕜} {u v : E}
    (hu : HasSum (fun n => a n • φ n) u)
    (hv : HasSum (fun n => b n • φ n) v) :
    HasSum (fun n => starRingEnd 𝕜 (a n) * b n) (⟪u, v⟫_𝕜) := by
  show Filter.Tendsto (fun s => ∑ n ∈ s, starRingEnd 𝕜 (a n) * b n)
      (SummationFilter.unconditional ℕ).filter (nhds (⟪u, v⟫_𝕜))
  exact (hu.inner hv).congr fun s => hφ.inner_sum a b s

end OrthonormalBases

end

namespace HilbertSpace

class IsHilbertSpace (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] : Prop

end HilbertSpace
