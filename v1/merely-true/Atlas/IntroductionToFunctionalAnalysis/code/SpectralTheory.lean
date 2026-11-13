/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Function Set Filter Bornology Metric Pointwise Topology

namespace SpectralTheory

section AdjointOperator

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Let $H$ be a Hilbert space, and let $A : H \to H$ be a bounded linear operator.
Then $(\operatorname{Ran}(A))^\perp = \operatorname{Null}(A^\ast)$: the orthogonal
complement of the range of $A$ equals the kernel of its adjoint. -/
theorem range_orthogonal_eq_ker_adjoint (A : H →L[𝕜] H) :
    (LinearMap.range A.toLinearMap).orthogonal =
      LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap :=
  ContinuousLinearMap.orthogonal_range A

end AdjointOperator

section SelfAdjointOperator

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A bounded linear operator $T : H \to H$ on a Hilbert space is *self-adjoint*
if $T = T^\ast$. This is a wrapper around Mathlib's `IsSelfAdjoint`. -/
def IsSelfAdjointOperator (T : H →L[𝕜] H) : Prop := IsSelfAdjoint T

/-- If $T \in \mathcal{B}(H)$ is a self-adjoint operator (i.e. $T = T^\ast$), then
$\langle Tu, u\rangle \in \mathbb{R}$ for every $u \in H$, and the operator norm
satisfies $\|T\| = \sup_{\|x\| = 1} |\langle Tx, x\rangle|$, expressed here in terms
of the Rayleigh quotient. -/
theorem IsSelfAdjointOperator.inner_real_and_norm_eq_iSup_rayleighQuotient
    {T : H →L[𝕜] H} (hT : IsSelfAdjointOperator T) :
    (∀ u : H, ∃ r : ℝ, @inner 𝕜 H _ (T u) u = (r : 𝕜)) ∧
    ‖T‖ = ⨆ x : H, |T.rayleighQuotient x| := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  exact ⟨fun u => ⟨T.reApplyInnerSelf u, (hsym.coe_reApplyInnerSelf_apply u).symm⟩,
         T.norm_eq_iSup_rayleighQuotient hsym⟩

end SelfAdjointOperator

section EigenvalueProperties

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

open Module End

/-- Characterization of eigenvalues: for $T \in \mathcal{B}(H)$ and $\mu \in \mathbb{K}$,
$\mu$ is an eigenvalue of $T$ if and only if there exists a nonzero vector $u \in H$
(the associated eigenvector) such that $Tu = \mu u$. -/
theorem hasEigenvalue_iff_exists_ne_zero (T : H →L[𝕜] H) (μ : 𝕜) :
    HasEigenvalue (T.toLinearMap) μ ↔ ∃ u ≠ (0 : H), T u = μ • u := by
  rw [hasEigenvalue_iff, Submodule.ne_bot_iff]
  simp only [mem_eigenspace_iff]
  exact ⟨fun ⟨x, hx, hne⟩ => ⟨x, hne, hx⟩, fun ⟨x, hne, hx⟩ => ⟨x, hx, hne⟩⟩

end EigenvalueProperties

/-- Heine–Borel for finite-dimensional normed spaces over $\mathbb{R}$ or $\mathbb{C}$:
a subset $s \subseteq E$ is compact if and only if it is closed and bounded. -/
theorem isCompact_iff_isClosed_bounded
    (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (s : Set E) : IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s := by
  haveI : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  exact Metric.isCompact_iff_isClosed_bounded

/-- In a metric space $X$, a subset $K \subseteq X$ is compact if and only if it is
sequentially compact: every sequence in $K$ has a subsequence converging to an
element of $K$. -/
theorem isCompact_iff_seqCompact_metric {X : Type*} [PseudoMetricSpace X] (K : Set X) :
    IsCompact K ↔ IsSeqCompact K :=
  isCompact_iff_isSeqCompact

section FredholmAlternative

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

open Module End

omit [CompleteSpace H] in
/-- Auxiliary lemma: the kernel of $\mu I - T$ coincides with the eigenspace of $T$
associated to the eigenvalue $\mu$. -/
lemma ker_smul_id_sub_eq_eigenspace (T : H →L[𝕜] H) (μ : 𝕜) :
    LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap =
    Module.End.eigenspace (T.toLinearMap) μ := by
  ext x; simp [Module.End.eigenspace, LinearMap.mem_ker, sub_eq_zero]; exact ⟨Eq.symm, Eq.symm⟩

set_option maxHeartbeats 800000 in
/-- **Fredholm alternative.** Let $A = A^\ast \in \mathcal{B}(H)$ be a self-adjoint
compact operator, and let $\mu \in \mathbb{K} \setminus \{0\}$. Then
$\operatorname{Range}(\mu I - A)$ is closed (equal to $\operatorname{Null}(\mu I - A)^\perp$),
and either $\mu I - A$ is bijective, or its kernel — the eigenspace of $A$ associated
to $\mu$ — is nontrivial and finite-dimensional. -/
theorem fredholm_alternative_full
    {T : H →L[𝕜] H} (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    LinearMap.range (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap =
      (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap).orthogonal ∧
    (Function.Bijective (μ • (ContinuousLinearMap.id 𝕜 H) - T) ∨
      (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap ≠ ⊥ ∧
       FiniteDimensional 𝕜 (LinearMap.ker (μ • (ContinuousLinearMap.id 𝕜 H) - T).toLinearMap))) := by
  set S := μ • (ContinuousLinearMap.id 𝕜 H) - T
  have hSN : IsStarNormal S := by
    constructor; have hT' : star T = T := hsa
    simp only [S, star_sub, star_smul, hT', ContinuousLinearMap.star_eq_adjoint,
               ContinuousLinearMap.adjoint_id]
    ext x; simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
               map_sub, map_smul]; module
  have hort : (LinearMap.range S.toLinearMap).orthogonal = LinearMap.ker S.toLinearMap :=
    ContinuousLinearMap.IsStarNormal.orthogonal_range hSN
  have hKcomplete : CompleteSpace (LinearMap.ker S.toLinearMap)ᗮ :=
    (Submodule.isClosed_orthogonal _).completeSpace_coe
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet hT hμ with heig | hres
  · constructor
    · apply le_antisymm
      · intro y hy; rw [Submodule.mem_orthogonal']
        intro z hz
        have hz' : z ∈ (LinearMap.range S.toLinearMap).orthogonal := hort ▸ hz
        exact inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal' _ _).mp hz' y hy)
      · intro y hy
        have hTinv : ∀ x ∈ (LinearMap.ker S.toLinearMap)ᗮ,
            T x ∈ (LinearMap.ker S.toLinearMap)ᗮ := by
          intro x hx; rw [Submodule.mem_orthogonal'] at hx ⊢; intro z hz
          have hTz : T z = μ • z := (sub_eq_zero.mp (LinearMap.mem_ker.mp hz)).symm
          rw [← ContinuousLinearMap.adjoint_inner_right T x z, hsa.adjoint_eq, hTz,
              inner_smul_right, hx z hz, mul_zero]
        let T' : (LinearMap.ker S.toLinearMap)ᗮ →L[𝕜] (LinearMap.ker S.toLinearMap)ᗮ :=
          { toLinearMap := T.toLinearMap.restrict hTinv
            cont := Continuous.subtype_mk (T.continuous.comp continuous_subtype_val) _ }
        have hT'_compact : IsCompactOperator (T' : _ → _) := hT.restrict' hTinv
        have hT'_no_eig : ¬HasEigenvalue (T'.toLinearMap : End 𝕜 _) μ := by
          intro h; rw [hasEigenvalue_iff, Submodule.ne_bot_iff] at h
          obtain ⟨⟨v, hv_mem⟩, hv_eig, hv_ne⟩ := h
          have hTv : T v = μ • v := by
            have := congr_arg Subtype.val (mem_eigenspace_iff.mp hv_eig)
            simpa [T', LinearMap.restrict_apply] using this
          have hv_ker : (v : H) ∈ LinearMap.ker S.toLinearMap := by
            rw [LinearMap.mem_ker]; show μ • v - T v = 0; rw [hTv, sub_self]
          have hmem : v ∈ (LinearMap.ker S.toLinearMap) ⊓ (LinearMap.ker S.toLinearMap)ᗮ :=
            ⟨hv_ker, hv_mem⟩
          rw [Submodule.inf_orthogonal_eq_bot] at hmem
          exact hv_ne (Subtype.ext ((Submodule.mem_bot 𝕜).mp hmem))
        have hres := (@IsCompactOperator.hasEigenvalue_or_mem_resolventSet
          𝕜 _ _ _ _ T' μ hKcomplete hT'_compact hμ).resolve_left hT'_no_eig
        rw [spectrum.mem_resolventSet_iff] at hres
        have hbij := (@ContinuousLinearMap.isUnit_iff_bijective 𝕜 _
          (LinearMap.ker S.toLinearMap)ᗮ _ _ hKcomplete).mp hres
        obtain ⟨b, hb⟩ := hbij.2 ⟨y, hy⟩
        rw [LinearMap.mem_range]
        refine ⟨(b : H), ?_⟩
        have hb_val := congr_arg Subtype.val hb
        simp only [ContinuousLinearMap.sub_apply] at hb_val
        show μ • (b : H) - T (b : H) = y
        have hT'_val : ↑(T' b) = T (↑b : H) := by simp [T', LinearMap.restrict_apply]
        rw [← hT'_val]; exact hb_val
    · right; rw [ker_smul_id_sub_eq_eigenspace]
      exact ⟨hasEigenvalue_iff.mp heig,
             ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ⟩
  · rw [spectrum.mem_resolventSet_iff, ContinuousLinearMap.isUnit_iff_bijective] at hres
    have hbij : Function.Bijective (S : H → H) := by convert hres using 1
    exact ⟨by rw [LinearMap.range_eq_top.mpr hbij.2, LinearMap.ker_eq_bot.mpr hbij.1,
               Submodule.bot_orthogonal_eq_top],
           Or.inl hbij⟩

end FredholmAlternative


section SpectralDecomposition

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

open Module End

set_option maxHeartbeats 800000 in
/-- **Spectral theorem for compact self-adjoint operators (range decomposition form).**
Let $A = A^\ast \in \mathcal{B}(H)$ be a compact self-adjoint operator on a Hilbert
space $H$. Then:
(1) the closure of the span of all nonzero eigenspaces of $A$ equals the closure of
$\operatorname{Range}(A)$;
(2) $\overline{\operatorname{Range}(A)}$ and $\operatorname{Null}(A)$ are complementary
closed subspaces of $H$; and
(3) the family of eigenspaces of $A$ is an orthogonal family. -/
theorem spectral_theorem_range_decomposition {T : H →L[𝕜] H}
    (hT : IsCompactOperator (T : H → H)) (hsa : IsSelfAdjoint T) :

    (⨆ (μ : 𝕜) (_ : μ ≠ 0), (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H)).topologicalClosure =
      (LinearMap.range T.toLinearMap).topologicalClosure ∧

    IsCompl (LinearMap.range T.toLinearMap).topologicalClosure (LinearMap.ker T.toLinearMap) ∧

    OrthogonalFamily 𝕜 (fun μ : 𝕜 => eigenspace (T : End 𝕜 H) μ)
      (fun μ => (eigenspace (T : End 𝕜 H) μ).subtypeₗᵢ) := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  have hSN : IsStarNormal T := hsa.isStarNormal
  have hort_range : (LinearMap.range T.toLinearMap)ᗮ = LinearMap.ker T.toLinearMap :=
    ContinuousLinearMap.IsStarNormal.orthogonal_range hSN
  have h_span := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hsym

  have h_ort_nonzero : (⨆ (μ : 𝕜) (_ : μ ≠ 0),
      (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H))ᗮ = LinearMap.ker T.toLinearMap := by
    apply le_antisymm
    ·
      intro x hx
      have hTx_bot : T x ∈ (⨆ μ, eigenspace (T : End 𝕜 H) μ)ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro y hy
        exact Submodule.iSup_induction (p := fun μ => eigenspace (T : End 𝕜 H) μ)
          (motive := fun v => @inner 𝕜 H _ (T x) v = 0) hy
          (fun μ v hv => by
            have hTv := mem_eigenspace_iff.mp hv
            change @inner 𝕜 H _ ((T : H →ₗ[𝕜] H) x) v = 0
            rw [hsym x v, hTv, inner_smul_right]
            by_cases hμ : μ = 0
            · simp [hμ]
            · have hv_mem : v ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0),
                  (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H) :=
                Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ hv)
              have := (Submodule.mem_orthogonal' _ _).mp hx v hv_mem
              rw [this, mul_zero])
          (inner_zero_right _)
          (fun a b ha hb => by
            show @inner 𝕜 H _ (T x) (a + b) = 0
            rw [inner_add_right, ha, hb, add_zero])
      rw [h_span, Submodule.mem_bot] at hTx_bot
      exact LinearMap.mem_ker.mpr hTx_bot
    ·
      intro x hx
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hx_eig : x ∈ eigenspace (T : End 𝕜 H) 0 := by
        simp [LinearMap.mem_ker.mp hx]
      exact Submodule.iSup_induction
        (p := fun μ => ⨆ (_ : μ ≠ 0), eigenspace (T : End 𝕜 H) μ)
        (motive := fun v => @inner 𝕜 H _ x v = 0) hy
        (fun μ v hv => by
          by_cases hμ : μ = 0
          · subst hμ; simp at hv; rw [hv, inner_zero_right]
          · have hv' : v ∈ eigenspace (T : End 𝕜 H) μ := by
              simp only [ne_eq, hμ, not_false_eq_true, iSup_true] at hv; exact hv
            exact hsym.orthogonalFamily_eigenspaces (Ne.symm hμ) ⟨x, hx_eig⟩ ⟨v, hv'⟩)
        (inner_zero_right _)
        (fun a b ha hb => by
          show @inner 𝕜 H _ x (a + b) = 0
          rw [inner_add_right, ha, hb, add_zero])
  refine ⟨?_, ?_, hsym.orthogonalFamily_eigenspaces⟩
  ·
    have h1 : (⨆ (μ : 𝕜) (_ : μ ≠ 0),
        (eigenspace (T : End 𝕜 H) μ : Submodule 𝕜 H))ᗮ = (LinearMap.range T.toLinearMap)ᗮ := by
      rw [h_ort_nonzero, hort_range]
    rw [← Submodule.orthogonal_orthogonal_eq_closure, h1,
        Submodule.orthogonal_orthogonal_eq_closure]
  ·
    have hort_closure : (LinearMap.range T.toLinearMap).topologicalClosure.orthogonal =
        LinearMap.ker T.toLinearMap := by
      rw [Submodule.orthogonal_closure, hort_range]
    haveI : CompleteSpace (LinearMap.range T.toLinearMap).topologicalClosure :=
      (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    rw [← hort_closure]
    exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

end SpectralDecomposition

section SpectrumBounds

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Auxiliary lemma: for $t \in \mathbb{R}$ and a nonzero vector $x$, the Rayleigh
quotient of $tI - T$ at $x$ equals $t$ minus the Rayleigh quotient of $T$ at $x$. -/
lemma rayleighQuotient_algebraMap_sub (T : H →L[𝕜] H) (t : ℝ) (x : H) (hx : x ≠ 0) :
    ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T).rayleighQuotient x =
      t - T.rayleighQuotient x := by
  unfold ContinuousLinearMap.rayleighQuotient ContinuousLinearMap.reApplyInnerSelf
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.algebraMap_apply]
  rw [inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal]
  have h_re_inner : RCLike.re ((↑t : 𝕜) * @inner 𝕜 H _ x x) = t * ‖x‖ ^ 2 := by
    rw [RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, inner_self_eq_norm_sq (𝕜 := 𝕜)]
    simp
  rw [h_re_inner]
  have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

set_option maxHeartbeats 1600000 in
/-- The spectrum of a self-adjoint operator $T \in \mathcal{B}(H)$ is bounded by the
Rayleigh quotient: for every $\mu \in \operatorname{Spec}(T)$,
$\inf_{x} \langle Tx, x\rangle / \|x\|^2 \le \operatorname{Re}\mu
\le \sup_{x} \langle Tx, x\rangle / \|x\|^2$. -/
theorem selfAdjoint_spectrum_subset_Icc [Nontrivial H]
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {mu : 𝕜} (hmu : mu ∈ spectrum 𝕜 T) :
    ⨅ x : H, T.rayleighQuotient x ≤ RCLike.re mu ∧
    RCLike.re mu ≤ ⨆ x : H, T.rayleighQuotient x := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hrq_bdd : BddAbove (Set.range T.rayleighQuotient) :=
    ⟨‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).2⟩
  have hrq_bdd_below : BddBelow (Set.range T.rayleighQuotient) :=
    ⟨-‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1⟩
  set M := ⨆ x : H, T.rayleighQuotient x
  set m := ⨅ x : H, T.rayleighQuotient x
  have hm_le : ∀ x, m ≤ T.rayleighQuotient x := fun x => ciInf_le hrq_bdd_below x
  have hle_M : ∀ x, T.rayleighQuotient x ≤ M := fun x => le_ciSup hrq_bdd x
  have hshift : ∀ r : 𝕜, ‖r - mu‖ ≤ ‖(algebraMap 𝕜 (H →L[𝕜] H)) r - T‖ := fun r =>
    spectrum.norm_le_norm_of_mem (by
      rw [← spectrum.singleton_sub_eq]; exact Set.sub_mem_sub (Set.mem_singleton r) hmu)
  have h_norm_le : ∀ (t : ℝ), m ≤ t → t ≤ M →
      ‖(algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T‖ ≤ M - m := by
    intro t ht_m ht_M
    have hsa_S : IsSelfAdjoint ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T) := by
      have hsa_scalar : IsSelfAdjoint ((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜)) :=
        IsSelfAdjoint.algebraMap _ (by rw [isSelfAdjoint_iff, RCLike.star_def, RCLike.conj_ofReal])
      exact hsa_scalar.sub hT
    have hsym_S := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa_S
    rw [((algebraMap 𝕜 (H →L[𝕜] H)) (↑t : 𝕜) - T).norm_eq_iSup_rayleighQuotient hsym_S]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simp [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
      linarith
    · rw [rayleighQuotient_algebraMap_sub T t x hx]
      rw [abs_le]
      exact ⟨by linarith [hle_M x], by linarith [hm_le x]⟩
  have h_lower : m ≤ RCLike.re mu := by
    have h1 : ‖(↑M : 𝕜) - mu‖ ≤ M - m :=
      (hshift (↑M : 𝕜)).trans (h_norm_le M (le_trans (hm_le 0) (hle_M 0)) le_rfl)
    have h2 : M - RCLike.re mu ≤ ‖(↑M : 𝕜) - mu‖ := by
      have : RCLike.re ((↑M : 𝕜) - mu) = M - RCLike.re mu := by
        simp [map_sub, RCLike.ofReal_re]
      linarith [RCLike.abs_re_le_norm ((↑M : 𝕜) - mu), le_abs_self (RCLike.re ((↑M : 𝕜) - mu))]
    linarith
  have h_upper : RCLike.re mu ≤ M := by
    have h1 : ‖(↑m : 𝕜) - mu‖ ≤ M - m :=
      (hshift (↑m : 𝕜)).trans (h_norm_le m le_rfl (le_trans (hm_le 0) (hle_M 0)))
    have h2 : RCLike.re mu - m ≤ ‖(↑m : 𝕜) - mu‖ := by
      have : RCLike.re ((↑m : 𝕜) - mu) = m - RCLike.re mu := by
        simp [map_sub, RCLike.ofReal_re]
      linarith [RCLike.abs_re_le_norm ((↑m : 𝕜) - mu), neg_abs_le (RCLike.re ((↑m : 𝕜) - mu))]
    linarith
  exact ⟨h_lower, h_upper⟩

end SpectrumBounds

set_option maxHeartbeats 3200000 in
/-- Let $A = A^\ast \in \mathcal{B}(H)$ be a self-adjoint operator. Then $A$ is
*positive* — i.e. $\langle Au, u\rangle \ge 0$ for all $u \in H$ — if and only if
$\operatorname{Spec}(A) \subseteq [0, \infty)$. -/
theorem positive_iff_spectrum_nonneg {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [Nontrivial H] (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) :
    (∀ u : H, 0 ≤ T.reApplyInnerSelf u) ↔
    (∀ μ ∈ spectrum 𝕜 T, 0 ≤ RCLike.re μ) := by
  have hsym : (T : H →ₗ[𝕜] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hrq_bdd : BddAbove (Set.range T.rayleighQuotient) :=
    ⟨‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).2⟩
  have hrq_bdd_below : BddBelow (Set.range T.rayleighQuotient) :=
    ⟨-‖T‖, by rintro _ ⟨x, rfl⟩; exact (abs_le.mp (T.rayleighQuotient_le_norm x)).1⟩
  set M := ⨆ x : H, T.rayleighQuotient x
  set m := ⨅ x : H, T.rayleighQuotient x
  have hm_le : ∀ x, m ≤ T.rayleighQuotient x := fun x => ciInf_le hrq_bdd_below x
  have hle_M : ∀ x, T.rayleighQuotient x ≤ M := fun x => le_ciSup hrq_bdd x
  constructor
  ·
    intro hpos μ hμ
    have hrq_nonneg : ∀ x : H, 0 ≤ T.rayleighQuotient x := fun x =>
      div_nonneg (hpos x) (sq_nonneg _)
    have h_m_nonneg : (0 : ℝ) ≤ m := le_ciInf hrq_nonneg
    exact le_trans h_m_nonneg (selfAdjoint_spectrum_subset_Icc T hT hμ).1
  ·
    intro hspec u
    by_cases hu : u = 0
    · subst hu
      simp only [ContinuousLinearMap.reApplyInnerSelf, map_zero, inner_zero_left, map_zero, le_refl]
    ·
      have hreq : T.reApplyInnerSelf u = T.rayleighQuotient u * ‖u‖ ^ 2 := by
        simp only [ContinuousLinearMap.rayleighQuotient]
        field_simp [norm_ne_zero_iff.mpr hu]
      rw [hreq]
      apply mul_nonneg _ (sq_nonneg _)
      suffices hm_nonneg : 0 ≤ m from le_trans hm_nonneg (hm_le u)


      by_contra h_m_neg
      push_neg at h_m_neg
      set S := (algebraMap 𝕜 (H →L[𝕜] H)) (↑M : 𝕜) - T
      have hS_sa : IsSelfAdjoint S :=
        (IsSelfAdjoint.algebraMap _
          (by rw [isSelfAdjoint_iff, RCLike.star_def, RCLike.conj_ofReal])).sub hT
      have hS_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS_sa
      have hS_rq_nonneg : ∀ x : H, 0 ≤ S.rayleighQuotient x := by
        intro x
        by_cases hx : x = 0
        · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
        · have : S.rayleighQuotient x = M - T.rayleighQuotient x :=
            rayleighQuotient_algebraMap_sub T M x hx
          rw [this]; linarith [hle_M x]
      have hS_ne : S ≠ 0 := by
        intro hS_eq
        have hS_zero : (S : H →L[𝕜] H) = 0 := hS_eq
        have hT_scalar : T = (algebraMap 𝕜 (H →L[𝕜] H)) (↑M : 𝕜) := by
          have h : S = (algebraMap 𝕜 (H →L[𝕜] H)) (↑M : 𝕜) - T := rfl
          rw [hS_zero, eq_comm, sub_eq_zero] at h; exact h.symm
        have hM_in_spec : (↑M : 𝕜) ∈ spectrum 𝕜 T := by
          rw [hT_scalar, spectrum.mem_iff]; simp only [sub_self, not_isUnit_zero, not_false_eq_true]
        have hM_nonneg : (0 : ℝ) ≤ M := by
          have := hspec _ hM_in_spec; rwa [RCLike.ofReal_re] at this
        have hm_ge_zero : (0 : ℝ) ≤ m := by
          apply le_ciInf; intro x
          by_cases hx : x = 0
          · rw [hx, ContinuousLinearMap.rayleighQuotient_apply_zero]
          · have hSrq : S.rayleighQuotient x = M - T.rayleighQuotient x :=
              rayleighQuotient_algebraMap_sub T M x hx
            have hSrq_zero : S.rayleighQuotient x = 0 := by
              rw [show S = 0 from hS_zero]; exact ContinuousLinearMap.rayleighQuotient_zero_apply x
            linarith
        linarith
      have hS_spec_nonneg : ∀ ν ∈ spectrum 𝕜 S, 0 ≤ RCLike.re ν := by
        intro ν hν
        exact le_trans (le_ciInf hS_rq_nonneg) (selfAdjoint_spectrum_subset_Icc S hS_sa hν).1
      have hS_neg_not_mem : (↑(-‖S‖) : 𝕜) ∉ spectrum 𝕜 S := by
        intro h_mem
        have := hS_spec_nonneg _ h_mem
        rw [RCLike.ofReal_re] at this; linarith [norm_pos_iff.mpr hS_ne]
      have hS_norm_mem : (↑‖S‖ : 𝕜) ∈ spectrum 𝕜 S := by
        have h_or : (algebraMap ℝ 𝕜 ‖S‖) ∈ spectrum 𝕜 S ∨
            (algebraMap ℝ 𝕜 (-‖S‖)) ∈ spectrum 𝕜 S := by
          simp_rw [spectrum, Set.mem_compl_iff, map_neg]
          by_contra! h
          obtain ⟨c, hc0, hc⟩ := S.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
          linarith [S.norm_eq_iSup_rayleighQuotient hS_sym, ciSup_le hc]
        rcases h_or with h1 | h2
        · convert h1 using 1
        · exfalso; apply hS_neg_not_mem; convert h2 using 1
      have hM_sub_norm_mem : (↑(M - ‖S‖) : 𝕜) ∈ spectrum 𝕜 T := by
        have h_in_S := hS_norm_mem
        rw [← spectrum.singleton_sub_eq] at h_in_S
        obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.mp h_in_S
        rw [Set.mem_singleton_iff] at ha; subst ha
        convert hb using 1
        have heq : (↑M : 𝕜) - b = (↑‖S‖ : 𝕜) := hab
        have hre := congr_arg RCLike.re heq
        have him := congr_arg RCLike.im heq
        simp only [map_sub, RCLike.ofReal_re, RCLike.ofReal_im] at hre him
        exact RCLike.ext (by simp only [RCLike.ofReal_re]; linarith)
          (by simp only [RCLike.ofReal_im]; linarith)
      have hS_le_M : ‖S‖ ≤ M := by
        have := hspec _ hM_sub_norm_mem; rw [RCLike.ofReal_re] at this; linarith
      have hS_gt_M : M < ‖S‖ := by
        rw [S.norm_eq_iSup_rayleighQuotient hS_sym]
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : H, T.rayleighQuotient x₀ < 0 := by
          by_contra h_all; push_neg at h_all; linarith [le_ciInf h_all]
        have hx₀_ne : x₀ ≠ 0 := by
          intro h; rw [h, ContinuousLinearMap.rayleighQuotient_apply_zero] at hx₀; linarith
        have hS_rq_x₀ : S.rayleighQuotient x₀ = M - T.rayleighQuotient x₀ :=
          rayleighQuotient_algebraMap_sub T M x₀ hx₀_ne
        have hS_rq_gt : M < |S.rayleighQuotient x₀| := by
          rw [hS_rq_x₀, abs_of_nonneg (by linarith [hle_M x₀])]; linarith
        exact lt_of_lt_of_le hS_rq_gt
          (le_ciSup ⟨‖S‖, by rintro _ ⟨x, rfl⟩; exact S.rayleighQuotient_le_norm x⟩ x₀)
      linarith

section InvertibleOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The space of invertible bounded linear operators
$GL(H) = \{T \in \mathcal{B}(H) : T \text{ invertible}\}$
is an open subset of $\mathcal{B}(H)$. -/
theorem isOpen_invertible_operators :
    IsOpen { T : H →L[𝕜] H | Function.Bijective T } := by
  have h : { T : H →L[𝕜] H | Function.Bijective T } = { T : H →L[𝕜] H | IsUnit T } := by
    ext T
    exact ContinuousLinearMap.isUnit_iff_bijective.symm
  rw [h]
  exact Units.isOpen

end InvertibleOperators

section GreensSqrt

open MeasureTheory

/-- The Hilbert space $L^2([0,1])$ of square-integrable real-valued functions on
the unit interval, equipped with the restriction of Lebesgue measure to $[0,1]$. -/
noncomputable abbrev L2UnitInterval :=
  Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The $k$-th orthonormal sine basis function on $[0,1]$:
$u_k(x) = \sqrt{2} \sin(k\pi x)$.
These form an orthonormal eigenbasis of the Green's operator with Dirichlet
boundary conditions on the unit interval. -/
noncomputable def sineBasisFun (k : ℕ+) : ℝ → ℝ :=
  fun x => Real.sqrt 2 * Real.sin (↑k * Real.pi * x)

/-- The $k$-th eigenvalue of the Green's operator on $[0,1]$ with Dirichlet
boundary conditions: $\lambda_k = \dfrac{1}{k^2 \pi^2}$. -/
noncomputable def greensEigenvalue (k : ℕ+) : ℝ := 1 / ((k : ℝ) ^ 2 * Real.pi ^ 2)

/-- The square root of the $k$-th eigenvalue of the Green's operator,
$\sqrt{\lambda_k} = \dfrac{1}{k\pi}$. This is the $k$-th eigenvalue of $A^{1/2}$. -/
noncomputable def greensEigenvalueSqrt (k : ℕ+) : ℝ := 1 / ((k : ℝ) * Real.pi)

/-- The square root $A^{1/2}$ of the Green's operator, defined via its action on the
orthonormal eigenbasis $\{b_k\}$: if $f = \sum_k c_k\, b_k$ where
$c_k = \langle b_k, f\rangle$, then
$A^{1/2} f = \sum_k \frac{1}{k\pi}\, c_k\, b_k$. -/
noncomputable def greensOperatorSqrt (b : HilbertBasis ℕ+ ℝ L2UnitInterval) :
    L2UnitInterval → L2UnitInterval :=
  fun f => ∑' (k : ℕ+), (greensEigenvalueSqrt k * inner (𝕜 := ℝ) (b k) f) • b k

/-- The Green's kernel for the Dirichlet Laplacian on $[0,1]$:
$G(x,t) = \min(x,t)\,(1 - \max(x,t))$.
The Green's operator $f \mapsto \int_0^1 G(x,t) f(t)\,dt$ is the inverse of
$-\frac{d^2}{dx^2}$ subject to $u(0)=u(1)=0$. -/
noncomputable def greensKernel (x t : ℝ) : ℝ :=
  min x t * (1 - max x t)


/-- Key computation showing that the sine basis functions are eigenfunctions of the
Green's operator: for $x \in [0,1]$,
$\int_0^1 G(x,t)\, u_k(t)\, dt = \lambda_k\, u_k(x)$,
where $G$ is the Green's kernel, $u_k(x) = \sqrt{2}\sin(k\pi x)$ and
$\lambda_k = 1/(k^2\pi^2)$. -/
lemma greens_kernel_integral_sine_eq (k : ℕ+) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ t in (0:ℝ)..1, (greensKernel x t) * (sineBasisFun k t) =
      greensEigenvalue k * sineBasisFun k x := by
  simp only [greensKernel, sineBasisFun, greensEigenvalue]
  set a := (↑k : ℝ) * Real.pi with ha_def
  have ha : a ≠ 0 := mul_ne_zero (Nat.cast_pos.mpr k.pos).ne' Real.pi_ne_zero
  have hcont : Continuous (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t))) :=
    ((continuous_const.min continuous_id).mul
      (continuous_const.sub (continuous_const.max continuous_id))).mul
      (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
  rw [show (↑k : ℝ) * Real.pi * x = a * x from by rw [ha_def]]
  rw [show (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin ((↑k : ℝ) * Real.pi * t))) =
      (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t))) from by
    ext t; rw [ha_def]]
  rw [(intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 x) (hcont.intervalIntegrable x 1)).symm]

  have hleft_congr : Set.EqOn (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t)))
      (fun t => (1 - x) * Real.sqrt 2 * (t * Real.sin (a * t))) (Set.uIcc 0 x) := by
    intro t ht; simp only [Set.uIcc_of_le hx0] at ht
    simp [min_eq_right ht.2, max_eq_left ht.2]; ring
  have hright_congr : Set.EqOn (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t)))
      (fun t => x * Real.sqrt 2 * ((1 - t) * Real.sin (a * t))) (Set.uIcc x 1) := by
    intro t ht; simp only [Set.uIcc_of_le hx1] at ht
    simp [min_eq_left ht.1, max_eq_right ht.1]; ring
  rw [intervalIntegral.integral_congr hleft_congr, intervalIntegral.integral_congr hright_congr]

  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

  have hI1 : ∫ t in (0:ℝ)..x, t * Real.sin (a * t) =
      Real.sin (a * x) / a ^ 2 - x * Real.cos (a * x) / a := by
    have hasD : ∀ t ∈ Set.uIcc 0 x, HasDerivAt
        (fun t => Real.sin (a * t) / a ^ 2 - t * Real.cos (a * t) / a)
        (t * Real.sin (a * t)) t := by
      intro t _
      have hd : HasDerivAt (fun t => a * t) a t := by
        have := (hasDerivAt_id t).const_mul a; simp only [mul_one] at this; exact this
      have hh1 : HasDerivAt (fun t => Real.sin (a * t) / a ^ 2) (Real.cos (a * t) / a) t := by
        convert hd.sin.div_const (a ^ 2) using 1; field_simp
      have hh2 : HasDerivAt (fun t => t * Real.cos (a * t) / a)
          (Real.cos (a * t) / a - t * Real.sin (a * t)) t := by
        convert ((hasDerivAt_id t).mul hd.cos).div_const a using 1
        simp only [id, one_mul, neg_mul]; field_simp; ring
      convert hh1.sub hh2 using 1; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hasD
      ((continuous_id.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 x)]
    simp [Real.sin_zero, Real.cos_zero]

  have hI2 : ∫ t in x..(1:ℝ), (1 - t) * Real.sin (a * t) =
      -Real.sin a / a ^ 2 + Real.cos (a * x) / a +
        Real.sin (a * x) / a ^ 2 - x * Real.cos (a * x) / a := by
    have hasD : ∀ t ∈ Set.uIcc x 1, HasDerivAt
        (fun t => -Real.cos (a * t) / a - Real.sin (a * t) / a ^ 2 + t * Real.cos (a * t) / a)
        ((1 - t) * Real.sin (a * t)) t := by
      intro t _
      have hd : HasDerivAt (fun t => a * t) a t := by
        have := (hasDerivAt_id t).const_mul a; simp only [mul_one] at this; exact this
      have h1 : HasDerivAt (fun t => -Real.cos (a * t) / a) (Real.sin (a * t)) t := by
        convert (hd.cos.neg).div_const a using 1; field_simp
      have h2 : HasDerivAt (fun t => Real.sin (a * t) / a ^ 2) (Real.cos (a * t) / a) t := by
        convert hd.sin.div_const (a ^ 2) using 1; field_simp
      have h3 : HasDerivAt (fun t => t * Real.cos (a * t) / a)
          (Real.cos (a * t) / a - t * Real.sin (a * t)) t := by
        convert ((hasDerivAt_id t).mul hd.cos).div_const a using 1
        simp only [id, one_mul, neg_mul]; field_simp; ring
      convert (h1.sub h2).add h3 using 1; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hasD
      (((continuous_const.sub continuous_id).mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable x 1)]
    ring
  rw [hI1, hI2]

  have hsin_a : Real.sin a = 0 := by
    rw [ha_def]; exact_mod_cast Real.sin_nat_mul_pi ↑k
  rw [hsin_a, neg_zero, zero_div, zero_add]
  field_simp
  ring

/-- Spectral decomposition of the Green's operator on $L^2([0,1])$.
If $A$ is the self-adjoint operator on $L^2([0,1])$ given by the Green's kernel
$Af(x) = \int_0^1 G(x,t)\, f(t)\, dt$, and $\{b_k\}_{k \in \mathbb{N}^+}$ is the
Hilbert basis of sine functions $b_k(x) = \sqrt{2}\sin(k\pi x)$, then:
* $\mathrm{Null}(A) = \{0\}$;
* each $b_k$ is an eigenvector with eigenvalue $\lambda_k = 1/(k^2\pi^2)$;
* every $f \in L^2([0,1])$ satisfies
  $Af = \sum_{k=1}^\infty \lambda_k\, \langle b_k, f\rangle\, b_k$. -/
theorem greens_operator_eigendecomposition
    (A : Module.End ℝ L2UnitInterval)
    (b : HilbertBasis ℕ+ ℝ L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hb : ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t)) :
    LinearMap.ker A = ⊥ ∧
    (∀ k : ℕ+, A.HasEigenvector (greensEigenvalue k) (b k)) ∧
    ∀ f : L2UnitInterval,
      A f = ∑' k : ℕ+, (greensEigenvalue k * @inner ℝ _ _ (b k) f) • (b k) := by

  have heig : ∀ k : ℕ+, A (b k) = greensEigenvalue k • (b k) := by
    intro k
    apply Lp.ext
    set μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    have hIntEq : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        ∫ t in Set.Icc (0:ℝ) 1, greensKernel x t * sineBasisFun k t =
        greensEigenvalue k * sineBasisFun k x := by
      intro x hx0 hx1
      have hconv : ∫ t in Set.Icc (0:ℝ) 1, greensKernel x t * sineBasisFun k t =
          ∫ t in (0:ℝ)..1, greensKernel x t * sineBasisFun k t := by
        rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1)]
        exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm
      rw [hconv]
      exact greens_kernel_integral_sine_eq k x hx0 hx1
    have hAeq := hA_greens (b k)
    have hb_ae := hb k
    have hintegral_eq : ∀ᵐ x ∂μ,
        (fun x => ∫ t in Set.Icc (0:ℝ) 1, greensKernel x t * (↑↑(b k) : ℝ → ℝ) t) x =
        (fun x => ∫ t in Set.Icc (0:ℝ) 1, greensKernel x t * sineBasisFun k t) x := by
      have hae_vol : ∀ᵐ t ∂volume, t ∈ Set.Icc (0:ℝ) 1 →
          (↑↑(b k) : ℝ → ℝ) t = sineBasisFun k t := by
        rw [← ae_restrict_iff' measurableSet_Icc]; exact hb_ae
      exact Filter.Eventually.of_forall fun x =>
        setIntegral_congr_ae measurableSet_Icc
          (hae_vol.mono fun t ht hmem => by rw [ht hmem])
    have heigval_eq : ∀ᵐ x ∂μ,
        (fun x => ∫ t in Set.Icc (0:ℝ) 1, greensKernel x t * sineBasisFun k t) x =
        (fun x => greensEigenvalue k * sineBasisFun k x) x := by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun x hx => hIntEq x hx.1 hx.2
    have hsmul_eq : ∀ᵐ x ∂μ,
        (fun x => greensEigenvalue k * sineBasisFun k x) x =
        (fun x => greensEigenvalue k * (↑↑(b k) : ℝ → ℝ) x) x := by
      exact hb_ae.symm.mono fun x hx => by simp [hx]
    have hsmul_coeFn : (↑↑(greensEigenvalue k • b k) : ℝ → ℝ) =ᶠ[ae μ]
        fun x => greensEigenvalue k * (↑↑(b k) : ℝ → ℝ) x := by
      exact (Lp.coeFn_smul (greensEigenvalue k) (b k)).mono fun x hx => by
        simp [Pi.smul_apply, smul_eq_mul] at hx; exact hx
    calc (↑↑(A (b k)) : ℝ → ℝ)
        =ᶠ[ae μ] fun x => ∫ t in Set.Icc (0:ℝ) 1, greensKernel x t * (↑↑(b k) : ℝ → ℝ) t := hAeq
      _ =ᶠ[ae μ] fun x => ∫ t in Set.Icc (0:ℝ) 1, greensKernel x t * sineBasisFun k t := hintegral_eq
      _ =ᶠ[ae μ] fun x => greensEigenvalue k * sineBasisFun k x := heigval_eq
      _ =ᶠ[ae μ] fun x => greensEigenvalue k * (↑↑(b k) : ℝ → ℝ) x := hsmul_eq
      _ =ᶠ[ae μ] ↑↑(greensEigenvalue k • b k) := hsmul_coeFn.symm
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have hcoeff : ∀ k : ℕ+, @inner ℝ _ _ (b k) f = (0 : ℝ) := by
      intro k
      have hne : greensEigenvalue k ≠ 0 := by
        unfold greensEigenvalue; apply div_ne_zero one_ne_zero
        apply mul_ne_zero; positivity; positivity
      have h1 : @inner ℝ _ _ (A f) (b k) = @inner ℝ _ _ f (A (b k)) := hA_sa f (b k)
      rw [hf, heig k] at h1
      simp only [map_zero, inner_zero_left, inner_smul_right] at h1
      have h2 : @inner ℝ _ _ f (b k) = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact absurd h hne
        · exact h
      rw [real_inner_comm] at h2; exact h2
    have hinj := b.repr.injective
    apply hinj; ext k
    simp only [HilbertBasis.repr_apply_apply, hcoeff k, map_zero]; rfl
  ·
    intro k
    rw [Module.End.hasEigenvector_iff]
    exact ⟨Module.End.mem_eigenspace_iff.mpr (heig k), b.orthonormal.ne_zero k⟩
  ·
    intro f
    have hcoeff : ∀ j : ℕ+,
        @inner ℝ _ _ (b j) (A f) = greensEigenvalue j * @inner ℝ _ _ (b j) f := by
      intro j
      have h1 : @inner ℝ _ _ (b j) (A f) = @inner ℝ _ _ (A f) (b j) := real_inner_comm _ _
      rw [h1, hA_sa f (b j), heig j, real_inner_smul_right, real_inner_comm]
    have hexpand : HasSum (fun j => @inner ℝ _ _ (b j) (A f) • b j) (A f) := by
      have h := b.hasSum_repr (A f)
      simp_rw [HilbertBasis.repr_apply_apply] at h
      exact h
    rw [hexpand.tsum_eq.symm]
    congr 1
    ext j
    rw [hcoeff j]

end GreensSqrt




/-- Uniqueness for the Sturm-Liouville Dirichlet problem on $[0,1]$:
any two $C^2$ solutions $u_1, u_2$ of $-u'' + Vu = f$ on $[0,1]$ with the Dirichlet
boundary conditions $u(0) = u(1) = 0$ (where $V \geq 0$ is continuous) must agree on $[0,1]$.
The proof uses the convexity of $u^2$ when $u'' = V u$ with $V \geq 0$. -/
theorem sturm_liouville_uniqueness
    (V : C(Set.Icc (0 : ℝ) 1, ℝ)) (hV : ∀ x : Set.Icc (0 : ℝ) 1, 0 ≤ V x)
    (f : C(Set.Icc (0 : ℝ) 1, ℝ))
    (u₁ u₂ : ℝ → ℝ)
    (h₁ : ContDiffOn ℝ 2 u₁ (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1, -(iteratedDerivWithin 2 u₁ (Set.Icc 0 1) x) +
        V ⟨x, hx⟩ * u₁ x = f ⟨x, hx⟩) ∧
      u₁ 0 = 0 ∧ u₁ 1 = 0)
    (h₂ : ContDiffOn ℝ 2 u₂ (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1, -(iteratedDerivWithin 2 u₂ (Set.Icc 0 1) x) +
        V ⟨x, hx⟩ * u₂ x = f ⟨x, hx⟩) ∧
      u₂ 0 = 0 ∧ u₂ 1 = 0) :
    Set.EqOn u₁ u₂ (Set.Icc 0 1) := by
  obtain ⟨h₁_smooth, h₁_ode, h₁_bc0, h₁_bc1⟩ := h₁
  obtain ⟨h₂_smooth, h₂_ode, h₂_bc0, h₂_bc1⟩ := h₂
  set u : ℝ → ℝ := u₁ - u₂ with hu_def
  have hu0 : u 0 = 0 := by simp [hu_def, Pi.sub_apply, h₁_bc0, h₂_bc0]
  have hu1 : u 1 = 0 := by simp [hu_def, Pi.sub_apply, h₁_bc1, h₂_bc1]
  have hu_smooth : ContDiffOn ℝ 2 u (Icc 0 1) := h₁_smooth.sub h₂_smooth

  have hu_ode : ∀ x : ℝ, ∀ hx : x ∈ Icc (0:ℝ) 1,
      iteratedDerivWithin 2 u (Icc 0 1) x = V ⟨x, hx⟩ * u x := by
    intro x hx
    have h_sub := iteratedDerivWithin_sub hx uniqueDiffOn_Icc_zero_one
      (h₁_smooth.contDiffWithinAt (hx := hx)) (h₂_smooth.contDiffWithinAt (hx := hx))
    simp only [hu_def, Pi.sub_apply] at h_sub ⊢
    have eq1 := h₁_ode x hx
    have eq2 := h₂_ode x hx
    linarith

  have hg_conv : ConvexOn ℝ (Icc 0 1) (fun x => (u x) ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (f' := fun x => 2 * u x * deriv u x)
      (f'' := fun x => 2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x)
    · exact hu_smooth.continuousOn.pow 2
    · intro x hx
      rw [interior_Icc] at hx
      have hu_at : ContDiffAt ℝ 2 u x := hu_smooth.contDiffAt (Icc_mem_nhds hx.1 hx.2)
      have hd : HasDerivAt u (deriv u x) x :=
        (hu_at.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt
      have h : HasDerivAt (fun t => (u t) ^ 2) (2 * u x * deriv u x) x := by
        convert hd.pow 2 using 1; norm_num
      exact h.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hu_at : ContDiffAt ℝ 2 u x := hu_smooth.contDiffAt (Icc_mem_nhds hx.1 hx.2)
      have hdu : HasDerivAt u (deriv u x) x :=
        (hu_at.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt
      have hddu : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        ((hu_at.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
          (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasDerivAt
      have h1 : HasDerivAt (fun t => 2 * u t) (2 * deriv u x) x := hdu.const_mul 2
      have h2 := h1.mul hddu
      have h3 : HasDerivAt (fun t => 2 * u t * deriv u t)
          (2 * (deriv u x) ^ 2 + 2 * u x * deriv (deriv u) x) x := by convert h2 using 1; ring
      exact h3.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
      have hu_at : ContDiffAt ℝ 2 u x := hu_smooth.contDiffAt (Icc_mem_nhds hx.1 hx.2)
      have h_dd : deriv (deriv u) x = V ⟨x, hx'⟩ * u x := by
        have h1 := hu_ode x hx'
        have h2 : iteratedDerivWithin 2 u (Icc 0 1) x = iteratedDeriv 2 u x :=
          iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one hu_at hx'
        have h3 : iteratedDeriv 2 u x = deriv^[2] u x := congr_fun iteratedDeriv_eq_iterate x
        simp only [iterate_succ, comp, iterate_zero, id] at h3
        linarith
      rw [h_dd]
      nlinarith [sq_nonneg (deriv u x), sq_nonneg (u x), hV ⟨x, hx'⟩]

  intro x hx
  have hux_eq : u x = 0 := by
    have hg0 : (u 0) ^ 2 = 0 := by rw [hu0]; ring
    have hg1 : (u 1) ^ 2 = 0 := by rw [hu1]; ring
    have h_le : (u x) ^ 2 ≤ 0 := by
      have h01 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.mpr (by norm_num)
      have h11 : (1:ℝ) ∈ Icc (0:ℝ) 1 := right_mem_Icc.mpr (by norm_num)
      have hx0 : (0:ℝ) ≤ 1 - x := by linarith [hx.2]
      have hx1 : (0:ℝ) ≤ x := hx.1
      have hsum : (1 - x) + x = 1 := by ring
      have key := hg_conv.2 h01 h11 hx0 hx1 hsum
      simp only [smul_eq_mul] at key
      have hsimp : (1 - x) * 0 + x * 1 = x := by ring
      rw [hsimp] at key
      rw [hg0, hg1] at key
      linarith
    nlinarith [sq_nonneg (u x)]
  simp [hu_def, Pi.sub_apply] at hux_eq
  linarith


end SpectralTheory
