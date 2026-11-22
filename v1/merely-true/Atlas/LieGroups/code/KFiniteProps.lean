/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.KFinite
import Atlas.LieGroups.code.SchurLemma
import Atlas.LieGroups.code.Admissible
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G]

section KStability

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

theorem kFiniteSubspace_stable (π : ContinuousRep G V) (K : Subgroup G)
    (g : K) (v : V) (hv : v ∈ kFiniteSubspace π K) :
    (π.toMonoidHom g) v ∈ kFiniteSubspace π K := by
  rw [mem_kFiniteSubspace] at hv ⊢
  unfold IsKFinite at *
  have hsub : Submodule.span ℂ
      (Set.range (fun k : K => (π.toMonoidHom k) ((π.toMonoidHom g) v))) ≤
      Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
    apply Submodule.span_le.mpr
    intro x hx; obtain ⟨k, rfl⟩ := hx
    show (π.toMonoidHom k) ((π.toMonoidHom g) v) ∈
      (Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) : Set V)
    have heq : (π.toMonoidHom k) ((π.toMonoidHom g) v) =
        (π.toMonoidHom ((k : G) * (g : G))) v := by
      rw [← ContinuousLinearMap.mul_apply]; congr 1
      exact (π.toMonoidHom.map_mul (k : G) (g : G)).symm
    rw [heq]
    exact Submodule.subset_span ⟨⟨(k : G) * (g : G), K.mul_mem k.2 g.2⟩, rfl⟩
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

end KStability

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma unitary_adjoint_eq_inv (π : ContinuousRep G E) (hU : π.IsUnitary)
    (g : G) :
    ContinuousLinearMap.adjoint (π.toMonoidHom g) = π.toMonoidHom g⁻¹ := by
  have h1 := (hU g).1
  have hginv : π.toMonoidHom g * π.toMonoidHom g⁻¹ = 1 := by
    rw [← map_mul]; simp
  calc ContinuousLinearMap.adjoint (π.toMonoidHom g)
      = ContinuousLinearMap.adjoint (π.toMonoidHom g) * 1 := (mul_one _).symm
    _ = ContinuousLinearMap.adjoint (π.toMonoidHom g) *
        (π.toMonoidHom g * π.toMonoidHom g⁻¹) := by rw [hginv]
    _ = (ContinuousLinearMap.adjoint (π.toMonoidHom g) * π.toMonoidHom g) *
        π.toMonoidHom g⁻¹ := (mul_assoc _ _ _).symm
    _ = 1 * π.toMonoidHom g⁻¹ := by rw [h1]
    _ = π.toMonoidHom g⁻¹ := one_mul _

lemma unitary_inner_invariant (π : ContinuousRep G E) (hU : π.IsUnitary)
    (g : G) (v w : E) :
    @inner ℂ _ _ ((π.toMonoidHom g) v) ((π.toMonoidHom g) w) =
    @inner ℂ _ _ v w := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  congr 1
  have h := (hU g).1
  have : (ContinuousLinearMap.adjoint (π.toMonoidHom g) * π.toMonoidHom g) v = v := by
    rw [h]; simp
  rw [ContinuousLinearMap.mul_apply] at this
  exact this

lemma unitary_orthogonal_invariant (π : ContinuousRep G E)
    (hU : π.IsUnitary) (W : Submodule ℂ E)
    (hW : ∀ (g : G) (v : E), v ∈ W → (π.toMonoidHom g) v ∈ W)
    (g : G) (v : E) (hv : v ∈ Wᗮ) : (π.toMonoidHom g) v ∈ Wᗮ := by
  rw [Submodule.mem_orthogonal'] at hv ⊢
  intro w hw
  rw [← ContinuousLinearMap.adjoint_inner_right, unitary_adjoint_eq_inv π hU]
  exact hv _ (hW g⁻¹ w hw)

end Unitary

section Orthogonality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [IsTopologicalGroup G]

def orthogonalProjection_intertwines_subrep
    (π : ContinuousRep G E) (hU : π.IsUnitary) (K : Subgroup G)
    (W₁ W₂ : Submodule ℂ E)
    (hW₁ : (π.restrictSubgroup K).IsInvariantSubspace W₁)
    (hW₂ : (π.restrictSubgroup K).IsInvariantSubspace W₂) :
    RepHom ((π.restrictSubgroup K).subrepresentation W₁ hW₁)
           ((π.restrictSubgroup K).subrepresentation W₂ hW₂) where
  toContinuousLinearMap :=


    haveI : CompleteSpace ↥W₂ := hW₂.isClosed.completeSpace_coe
    haveI : W₂.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W₂
    W₂.orthogonalProjection.comp W₁.subtypeL
  intertwines := by
    haveI : CompleteSpace ↥W₂ := hW₂.isClosed.completeSpace_coe
    haveI : W₂.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W₂
    intro g
    ext ⟨v, hv⟩


    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]


    have hcomm_val : (W₂.orthogonalProjection ((π.toMonoidHom (g : G)) v) : E) =
        (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E) := by
      have h_mem : (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E) ∈ W₂ :=
        hW₂.invariant g _ (W₂.orthogonalProjection v).2
      have h_orth : ∀ w ∈ W₂,
          @inner ℂ _ _ ((π.toMonoidHom (g : G)) v -
            (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E)) w = 0 := by
        intro w hw
        have heq : (π.toMonoidHom (g : G)) v -
            (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E) =
            (π.toMonoidHom (g : G)) (v - (W₂.orthogonalProjection v : E)) := by
          rw [map_sub]
        rw [heq, ← ContinuousLinearMap.adjoint_inner_right,
            unitary_adjoint_eq_inv π hU (g : G)]
        exact Submodule.orthogonalProjectionFn_inner_eq_zero v _ (hW₂.invariant g⁻¹ w hw)
      rw [← Submodule.orthogonalProjectionFn_eq]
      exact Submodule.eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero h_mem h_orth


    show (W₂.orthogonalProjection
      ((((π.restrictSubgroup K).subrepresentation W₁ hW₁).toMonoidHom g) ⟨v, hv⟩ : E) : E) =
      ((((π.restrictSubgroup K).subrepresentation W₂ hW₂).toMonoidHom g)
        (W₂.orthogonalProjection (v : E)) : E)

    simp only [subrepresentation, restrictSubgroup, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact hcomm_val

theorem orthogonalProjection_intertwines_subrep_val
    (π : ContinuousRep G E) (hU : π.IsUnitary) (K : Subgroup G)
    (W₁ W₂ : Submodule ℂ E)
    (hW₁ : (π.restrictSubgroup K).IsInvariantSubspace W₁)
    (hW₂ : (π.restrictSubgroup K).IsInvariantSubspace W₂)
    [W₂.HasOrthogonalProjection]
    (v : ↥W₁) :
    (orthogonalProjection_intertwines_subrep π hU K W₁ W₂ hW₁ hW₂).toContinuousLinearMap v =
    W₂.orthogonalProjection (v : E) := by

  simp only [orthogonalProjection_intertwines_subrep, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

theorem continuous_inverse_of_bijective_clm
    {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [CompleteSpace V₁]
    {V₂ : Type*} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [CompleteSpace V₂]
    (f : V₁ →L[ℂ] V₂) (hbij : Function.Bijective f) :
    Continuous (LinearEquiv.ofBijective f.toLinearMap hbij).symm :=
  (LinearEquiv.ofBijective f.toLinearMap hbij).continuous_symm f.continuous

theorem repEquiv_of_bijective_repHom
    {G' : Type*} [Group G'] [TopologicalSpace G']
    {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [CompleteSpace V₁]
    {V₂ : Type*} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [CompleteSpace V₂]
    (π₁ : ContinuousRep G' V₁) (π₂ : ContinuousRep G' V₂)
    (T : RepHom π₁ π₂)
    (hbij : Function.Bijective T.toContinuousLinearMap) :
    Nonempty (RepEquiv π₁ π₂) := by

  let f := T.toContinuousLinearMap
  let linEquiv : V₁ ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective f.toLinearMap hbij
  let cle : V₁ ≃L[ℂ] V₂ :=
    { linEquiv with
      continuous_toFun := f.continuous
      continuous_invFun := continuous_inverse_of_bijective_clm f hbij }
  exact ⟨{
    toContinuousLinearEquiv := cle
    intertwines := by
      intro g
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      have hT := ContinuousLinearMap.ext_iff.mp (T.intertwines g) v
      simp only [ContinuousLinearMap.comp_apply] at hT
      exact hT
  }⟩

theorem repEquiv_trans
    {G' : Type*} [Group G'] [TopologicalSpace G']
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    {V₃ : Type*} [AddCommGroup V₃] [Module ℂ V₃] [TopologicalSpace V₃]
    {π₁ : ContinuousRep G' V₁} {π₂ : ContinuousRep G' V₂}
    {π₃ : ContinuousRep G' V₃}
    (h₁ : Nonempty (RepEquiv π₁ π₂))
    (h₂ : Nonempty (RepEquiv π₂ π₃)) :
    Nonempty (RepEquiv π₁ π₃) := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨{
    toContinuousLinearEquiv := e₁.toContinuousLinearEquiv.trans e₂.toContinuousLinearEquiv
    intertwines := by
      intro g
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
                  ContinuousLinearEquiv.trans_apply]
      have h1 := ContinuousLinearMap.ext_iff.mp (e₁.intertwines g) v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h1
      rw [h1]
      have h2 := ContinuousLinearMap.ext_iff.mp (e₂.intertwines g) (e₁.toContinuousLinearEquiv v)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at h2
      exact h2
  }⟩

theorem repEquiv_symm
    {G' : Type*} [Group G'] [TopologicalSpace G']
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    {π₁ : ContinuousRep G' V₁} {π₂ : ContinuousRep G' V₂}
    (h : Nonempty (RepEquiv π₁ π₂)) :
    Nonempty (RepEquiv π₂ π₁) := by
  obtain ⟨e⟩ := h
  exact ⟨{
    toContinuousLinearEquiv := e.toContinuousLinearEquiv.symm
    intertwines := by
      intro g
      ext w
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      have hg := ContinuousLinearMap.ext_iff.mp (e.intertwines g)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hg
      apply e.toContinuousLinearEquiv.injective
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      rw [hg (e.toContinuousLinearEquiv.symm w)]
      simp only [ContinuousLinearEquiv.apply_symm_apply]
  }⟩


lemma mem_orthogonal_sSup {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : Set (Submodule ℂ F)) (v : F)
    (h : ∀ W ∈ T, v ∈ Wᗮ) :
    v ∈ (sSup T)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  have key : sSup T ≤ (Submodule.span ℂ ({v} : Set F))ᗮ := by
    apply sSup_le
    intro W hW w' hw'
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [inner_smul_right]
    have hv : ∀ u ∈ W, @inner ℂ _ _ v u = 0 :=
      (Submodule.mem_orthogonal' W v).mp (h W hW)
    rw [inner_eq_zero_symm.mp (hv w' hw')]
    ring
  have hw2 := key hw
  have hw3 : ∀ u ∈ Submodule.span ℂ ({v} : Set F), @inner ℂ _ _ w u = 0 :=
    (Submodule.mem_orthogonal' _ w).mp hw2
  rw [inner_eq_zero_symm]
  exact hw3 v (Submodule.mem_span_singleton_self v)

lemma sSup_orthogonal_sSup {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (S T : Set (Submodule ℂ F))
    (h : ∀ U ∈ S, ∀ W ∈ T, U.IsOrtho W) :
    (sSup S).IsOrtho (sSup T) := by
  rw [Submodule.IsOrtho]
  apply sSup_le
  intro U hU v hv
  exact mem_orthogonal_sSup T v (fun W hW => h U hU W hW hv)


end Orthogonality

section MeasureRep

variable {V : Type uG} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [TopologicalSpace G] in
def discreteMeasureRep (π : G →* (V →L[ℂ] V)) :
    MonoidAlgebra ℂ G →ₐ[ℂ] (V →L[ℂ] V) :=
  MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π

omit [TopologicalSpace G] in
theorem discreteMeasureRep_extends (π : G →* (V →L[ℂ] V)) (g : G) :
    discreteMeasureRep π (MonoidAlgebra.single g 1) = π g := by
  simp [discreteMeasureRep, MonoidAlgebra.lift_single]

omit [TopologicalSpace G] in
theorem discreteMeasureRep_unique (π : G →* (V →L[ℂ] V))
    (φ : MonoidAlgebra ℂ G →ₐ[ℂ] (V →L[ℂ] V))
    (hφ : ∀ g : G, φ (MonoidAlgebra.single g 1) = π g) :
    φ = discreteMeasureRep π := by
  have key : (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G).symm φ = π := by
    ext g : 1
    rw [MonoidAlgebra.lift_symm_apply]
    exact hφ g
  have := (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G).apply_symm_apply φ
  rw [key] at this
  exact this.symm

class CompactlySupportedMeasureAlgebra
    (G : Type uG) [Group G] [TopologicalSpace G]
    (M : Type uM) [Ring M] [Algebra ℂ M] [TopologicalSpace M] where
  dirac : G →* M
  discrete_in_closure : ∀ (m : M),
    m ∈ closure (Set.range (MonoidAlgebra.lift ℂ M G dirac))
  total_variation_cont : ∀ (f : G → ℝ) (_hf : Continuous f) (_hf_nn : ∀ g, 0 ≤ f g),
    @Continuous (MonoidAlgebra ℂ G) ℝ
      (TopologicalSpace.induced
        (MonoidAlgebra.lift ℂ M G dirac)
        ‹TopologicalSpace M›)
      inferInstance
      (fun μ => μ.sum (fun g c => ‖c‖ * f g))

theorem total_variation_eval_cont
    {G : Type uG} [Group G] [TopologicalSpace G]
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [inst : CompactlySupportedMeasureAlgebra G M]
    (f : G → ℝ) (hf : Continuous f) (hf_nn : ∀ g, 0 ≤ f g) :
    @Continuous (MonoidAlgebra ℂ G) ℝ
      (TopologicalSpace.induced
        (MonoidAlgebra.lift ℂ M G inst.dirac)
        ‹TopologicalSpace M›)
      inferInstance
      (fun μ => μ.sum (fun g c => ‖c‖ * f g)) :=
  inst.total_variation_cont f hf hf_nn

lemma rep_lift_opNorm_le {G : Type*} [Group G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V)) (μ : MonoidAlgebra ℂ G) :
    ‖(MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π) μ‖ ≤
      μ.sum (fun g c => ‖c‖ * ‖π g‖) := by
  rw [MonoidAlgebra.lift_apply]
  calc ‖μ.sum (fun g c => c • π g)‖
      ≤ μ.support.sum (fun g => ‖μ g • π g‖) := norm_sum_le _ _
    _ = μ.support.sum (fun g => ‖μ g‖ * ‖π g‖) := by
        congr 1; ext g; exact norm_smul (μ g) (π g)
    _ = μ.sum (fun g c => ‖c‖ * ‖π g‖) := rfl

set_option checkBinderAnnotations false in
lemma total_variation_eval_continuous
    {G : Type uG} [Group G] [TopologicalSpace G]
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [CompactlySupportedMeasureAlgebra G M]
    (f : G → ℝ) (hf : Continuous f) (hf_nn : ∀ g, 0 ≤ f g) :
    @Continuous (MonoidAlgebra ℂ G) ℝ
      (TopologicalSpace.induced
        (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac)
        ‹TopologicalSpace M›)
      inferInstance
      (fun μ => μ.sum (fun g c => ‖c‖ * f g)) :=
  total_variation_eval_cont f hf hf_nn

theorem rep_continuous_theorem
    {G : Type uG} [Group G] [TopologicalSpace G]
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousMul M]
    [CompactlySupportedMeasureAlgebra G M]
    {V : Type uG} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V))
    (hcont_norm : Continuous (fun g : G => ‖(π g : V →L[ℂ] V)‖)) :
    @Continuous (MonoidAlgebra ℂ G) (V →L[ℂ] V)
      (TopologicalSpace.induced
        (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac)
        ‹TopologicalSpace M›)
      (by infer_instance)
      (MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π) := by

  let δ_lift := MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac
  letI t_ind : TopologicalSpace (MonoidAlgebra ℂ G) :=
    TopologicalSpace.induced δ_lift ‹TopologicalSpace M›

  haveI instCNM : ContinuousNeg M := by
    constructor
    have : (Neg.neg : M → M) = (fun a => (-1 : M) * a) := by
      ext a; exact (neg_one_mul a).symm
    rw [this]; exact continuous_const.mul continuous_id
  haveI : IsTopologicalAddGroup M :=
    { toContinuousAdd := ‹ContinuousAdd M›, toContinuousNeg := instCNM }

  haveI : IsTopologicalAddGroup (MonoidAlgebra ℂ G) :=
    topologicalAddGroup_induced δ_lift
  let π_lift := MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π
  change @Continuous _ _ t_ind _ π_lift

  have h_tendsto : Filter.Tendsto π_lift (@nhds _ t_ind 0) (nhds 0) := by
    apply squeeze_zero_norm (fun μ => rep_lift_opNorm_le π μ)

    rw [← show (0 : MonoidAlgebra ℂ G).sum (fun g c => ‖c‖ * ‖(π g : V →L[ℂ] V)‖) = 0 from
      Finsupp.sum_zero_index]

    exact (total_variation_eval_cont
      (fun g => ‖(π g : V →L[ℂ] V)‖) hcont_norm (fun g => norm_nonneg _)).continuousAt.tendsto


  have h_cont_hom : Continuous (π_lift.toAddMonoidHom : MonoidAlgebra ℂ G →+ (V →L[ℂ] V)) :=
    continuous_of_tendsto_nhds_zero π_lift.toAddMonoidHom h_tendsto

  convert h_cont_hom using 1

theorem discrete_measures_sequentially_dense
    {G : Type uG} [Group G] [TopologicalSpace G]
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [inst : CompactlySupportedMeasureAlgebra G M] [FrechetUrysohnSpace M] :
    ∀ (m : M), m ∈ seqClosure (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)) := by
  intro m

  have hm_clos := inst.discrete_in_closure m

  rw [mem_closure_iff_seq_limit] at hm_clos
  obtain ⟨x, hx_mem, hx_tendsto⟩ := hm_clos
  exact ⟨x, hx_mem, hx_tendsto⟩

theorem CompactlySupportedMeasureAlgebra.discrete_dense
    {G : Type uG} [Group G] [TopologicalSpace G]
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [inst : CompactlySupportedMeasureAlgebra G M] [FrechetUrysohnSpace M] :
    Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)) := by
  rw [dense_iff_closure_eq]
  ext x
  simp only [Set.mem_univ, iff_true]
  exact seqClosure_subset_closure (discrete_measures_sequentially_dense x)

theorem blt_alg_hom_extend
    {α : Type*} {β : Type*} {γ : Type*}
    [Semiring α] [Semiring β] [Semiring γ]
    [Algebra ℂ α] [Algebra ℂ β] [Algebra ℂ γ]
    [TopologicalSpace β] [ContinuousAdd β] [ContinuousMul β]
    [TopologicalSpace γ] [T2Space γ]
    [ContinuousAdd γ] [ContinuousMul γ]
    (ι : α →ₐ[ℂ] β) (f : α →ₐ[ℂ] γ)
    (h_dense : Dense (Set.range ι))
    (g_fun : β → γ) (hg_cont : Continuous g_fun)
    (hg_ext : ∀ x : α, g_fun (ι x) = f x) :
    ∃ (g : β →ₐ[ℂ] γ), Continuous g ∧ ∀ x : α, g (ι x) = f x := by
  refine ⟨{ toFun := g_fun,
             map_one' := ?_,
             map_mul' := ?_,
             map_zero' := ?_,
             map_add' := ?_,
             commutes' := ?_ }, hg_cont, hg_ext⟩

  · have h1 : (1 : β) = ι 1 := (map_one ι).symm
    rw [h1, hg_ext, map_one]


  · intro x y
    have key : (fun p : β × β => g_fun (p.1 * p.2)) =
               (fun p : β × β => g_fun p.1 * g_fun p.2) := by
      apply @Continuous.ext_on γ (β × β) _ _ _ (Set.range ι ×ˢ Set.range ι)
      · exact h_dense.prod h_dense
      · exact hg_cont.comp (continuous_fst.mul continuous_snd)
      · exact (hg_cont.comp continuous_fst).mul (hg_cont.comp continuous_snd)
      · rintro ⟨b₁, b₂⟩ ⟨⟨a₁, rfl⟩, ⟨a₂, rfl⟩⟩
        show g_fun (ι a₁ * ι a₂) = g_fun (ι a₁) * g_fun (ι a₂)
        rw [← map_mul ι, hg_ext, hg_ext, hg_ext, map_mul]
    exact congr_fun key (x, y)

  · have h0 : (0 : β) = ι 0 := (map_zero ι).symm
    rw [h0, hg_ext, map_zero]

  · intro x y
    have key : (fun p : β × β => g_fun (p.1 + p.2)) =
               (fun p : β × β => g_fun p.1 + g_fun p.2) := by
      apply @Continuous.ext_on γ (β × β) _ _ _ (Set.range ι ×ˢ Set.range ι)
      · exact h_dense.prod h_dense
      · exact hg_cont.comp (continuous_fst.add continuous_snd)
      · exact (hg_cont.comp continuous_fst).add (hg_cont.comp continuous_snd)
      · rintro ⟨b₁, b₂⟩ ⟨⟨a₁, rfl⟩, ⟨a₂, rfl⟩⟩
        show g_fun (ι a₁ + ι a₂) = g_fun (ι a₁) + g_fun (ι a₂)
        rw [← map_add ι, hg_ext, hg_ext, hg_ext, map_add]
    exact congr_fun key (x, y)


  · intro r
    have : algebraMap ℂ β r = ι (algebraMap ℂ α r) := (ι.commutes r).symm
    rw [this, hg_ext, f.commutes]

theorem CompactlySupportedMeasureAlgebra.alg_hom_extend
    {G : Type uG} [Group G] [TopologicalSpace G]
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousMul M]
    [inst : CompactlySupportedMeasureAlgebra G M]
    {A : Type*} [Ring A] [Algebra ℂ A] [inst_top_A : TopologicalSpace A]
    [inst_unif_A : UniformSpace A] [CompleteSpace A] [T2Space A]
    [ContinuousAdd A] [ContinuousMul A] [IsUniformAddGroup A]
    (f : MonoidAlgebra ℂ G →ₐ[ℂ] A)
    (h_dense : Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)))
    (h_cont : @Continuous (MonoidAlgebra ℂ G) A
      (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac)
        ‹TopologicalSpace M›)
      inst_top_A f)
    (h_top_eq : inst_top_A = inst_unif_A.toTopologicalSpace := by rfl) :
    ∃ (g : M →ₐ[ℂ] A), Continuous g ∧
      ∀ μ : MonoidAlgebra ℂ G,
        g ((MonoidAlgebra.lift ℂ M G inst.dirac) μ) = f μ := by

  subst h_top_eq

  letI : TopologicalSpace (MonoidAlgebra ℂ G) :=
    TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›
  have di : IsDenseInducing (MonoidAlgebra.lift ℂ M G inst.dirac : MonoidAlgebra ℂ G → M) := {
    eq_induced := rfl
    dense := h_dense
  }

  let g_fun := di.extend (f : MonoidAlgebra ℂ G → A)

  have hg_ext : ∀ x, g_fun ((MonoidAlgebra.lift ℂ M G inst.dirac) x) = f x :=
    IsDenseInducing.extend_eq di h_cont


  have h_filter : ∀ b : M, ∃ c : A,
      Filter.Tendsto (f : MonoidAlgebra ℂ G → A) (Filter.comap
        (MonoidAlgebra.lift ℂ M G inst.dirac : MonoidAlgebra ℂ G → M) (nhds b)) (nhds c) := by
    intro b
    set ι := (MonoidAlgebra.lift ℂ M G inst.dirac : MonoidAlgebra ℂ G → M)

    haveI : ContinuousNeg M := IsSemitopologicalSemiring.continuousNeg_of_mul
    haveI : IsTopologicalAddGroup M := ⟨⟩

    haveI : IsTopologicalAddGroup (MonoidAlgebra ℂ G) :=
      Topology.IsInducing.topologicalAddGroup
        (f := (MonoidAlgebra.lift ℂ M G inst.dirac).toAddMonoidHom') di.toIsInducing

    letI uM : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    haveI : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
    letI uS : UniformSpace (MonoidAlgebra ℂ G) :=
      IsTopologicalAddGroup.rightUniformSpace (MonoidAlgebra ℂ G)
    haveI : IsUniformAddGroup (MonoidAlgebra ℂ G) := isUniformAddGroup_of_addCommGroup

    have hι_ui : IsUniformInducing ι :=
      AddMonoidHom.isUniformInducing_of_isInducing
        (f := (MonoidAlgebra.lift ℂ M G inst.dirac).toAddMonoidHom') di.toIsInducing

    have hf_uc : UniformContinuous (f : MonoidAlgebra ℂ G → A) :=
      uniformContinuous_addMonoidHom_of_continuous (hom := MonoidAlgebra ℂ G →+ A)
        (f := f.toAddMonoidHom') h_cont

    exact uniformly_extend_exists hι_ui di.dense hf_uc b
  have hg_cont : Continuous g_fun := di.continuous_extend h_filter

  exact blt_alg_hom_extend (MonoidAlgebra.lift ℂ M G inst.dirac) f h_dense g_fun hg_cont hg_ext

variable {M : Type*} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
variable [ContinuousAdd M] [ContinuousMul M]
variable [CompactlySupportedMeasureAlgebra G M] [FrechetUrysohnSpace M]

@[reducible]
def weakTopologyOnDiscreteMeasures :
    TopologicalSpace (MonoidAlgebra ℂ G) :=
  TopologicalSpace.induced
    (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac)
    ‹TopologicalSpace M›

lemma continuous_opNorm_of_jointly_continuous [FiniteDimensional ℂ V] (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2)) :
    Continuous (fun g : G => ‖(π g : V →L[ℂ] V)‖) := by
  have hπ_cont : Continuous (fun g => (π g : V →L[ℂ] V)) := by
    rw [continuous_clm_apply]
    intro v
    exact hcont.comp (continuous_id.prodMk continuous_const)
  exact continuous_norm.comp hπ_cont


omit [FrechetUrysohnSpace M] in
lemma discreteMeasureRep_continuous_to_opnorm (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2))
    [FiniteDimensional ℂ V] :
    @Continuous (MonoidAlgebra ℂ G) (V →L[ℂ] V)
      (weakTopologyOnDiscreteMeasures (M := M))
      (by infer_instance)
      (discreteMeasureRep π) :=
  rep_continuous_theorem (M := M) π (continuous_opNorm_of_jointly_continuous π hcont)

omit [FrechetUrysohnSpace M] in
theorem discreteMeasureRep_weakly_continuous (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2))
    [FiniteDimensional ℂ V] :
    letI := weakTopologyOnDiscreteMeasures (G := G) (M := M)
    Continuous (fun p : MonoidAlgebra ℂ G × V => (discreteMeasureRep π p.1) p.2) := by

  letI : TopologicalSpace (MonoidAlgebra ℂ G) :=
    weakTopologyOnDiscreteMeasures (G := G) (M := M)

  have h_rep_cont := discreteMeasureRep_continuous_to_opnorm (M := M) π hcont


  exact (h_rep_cont.comp continuous_fst).clm_apply continuous_snd

omit [FrechetUrysohnSpace M] in
theorem discreteMeasureRep_BLT_extension (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2))

    [FiniteDimensional ℂ V]
    (h_dense : Dense (Set.range (MonoidAlgebra.lift ℂ M G
        CompactlySupportedMeasureAlgebra.dirac))) :
    ∃ (π_ext : M →ₐ[ℂ] (V →L[ℂ] V)), Continuous π_ext ∧
      ∀ μ : MonoidAlgebra ℂ G,
        π_ext ((MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) μ) =
        discreteMeasureRep π μ := by


  have h_weak_cont : @Continuous (MonoidAlgebra ℂ G) (V →L[ℂ] V)
      (weakTopologyOnDiscreteMeasures (M := M)) _ (discreteMeasureRep π) :=
    discreteMeasureRep_continuous_to_opnorm (M := M) π hcont


  exact CompactlySupportedMeasureAlgebra.alg_hom_extend
    (discreteMeasureRep π) h_dense h_weak_cont

theorem measureRep_exists_extension (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2))

    [FiniteDimensional ℂ V] :
    ∃ (π_ext : M →ₐ[ℂ] (V →L[ℂ] V)),

      Continuous π_ext ∧

      (∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g) ∧

      (∀ μ : MonoidAlgebra ℂ G,
        π_ext ((MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) μ) =
        discreteMeasureRep π μ) := by


  obtain ⟨π_ext, h_cont_ext, h_extends⟩ := discreteMeasureRep_BLT_extension (M := M) π hcont
    (CompactlySupportedMeasureAlgebra.discrete_dense (G := G) (M := M))

  exact ⟨π_ext, h_cont_ext, fun g => by


    have := h_extends (MonoidAlgebra.single g 1)
    simp only [discreteMeasureRep, MonoidAlgebra.lift_single, one_smul] at this
    exact this, h_extends⟩

omit [ContinuousAdd M] [ContinuousMul M] [FrechetUrysohnSpace M] in
theorem measureRep_continuous_bilinear (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2))
    [FiniteDimensional ℂ V]
    (π_ext : M →ₐ[ℂ] (V →L[ℂ] V))
    (h_extends : ∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g)
    (hcont_ext : Continuous π_ext) :
    Continuous (fun p : M × V => (π_ext p.1) p.2) := by


  exact (isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.comp (hcont_ext.prodMap continuous_id)

theorem measureRep_continuous_extension (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2))
    [FiniteDimensional ℂ V] :
    ∃ (π_ext : M →ₐ[ℂ] (V →L[ℂ] V)),
      (∀ g : G, π_ext (CompactlySupportedMeasureAlgebra.dirac g) = π g) ∧
      Continuous π_ext ∧
      Continuous (fun p : M × V => (π_ext p.1) p.2) := by
  obtain ⟨π_ext, hcont_ext, h_dirac, _h_extends⟩ := measureRep_exists_extension (M := M) π hcont
  exact ⟨π_ext, h_dirac, hcont_ext,
    measureRep_continuous_bilinear (M := M) π hcont π_ext h_dirac hcont_ext⟩


omit [ContinuousAdd M] [ContinuousMul M] in
theorem measureRep_unique_extension (π : G →* (V →L[ℂ] V))
    (hcont : Continuous (fun p : G × V => (π p.1) p.2))
    [CompleteSpace V]
    (φ₁ φ₂ : M →ₐ[ℂ] (V →L[ℂ] V))
    (h₁ : ∀ g : G, φ₁ (CompactlySupportedMeasureAlgebra.dirac g) = π g)
    (h₂ : ∀ g : G, φ₂ (CompactlySupportedMeasureAlgebra.dirac g) = π g)
    (hcont₁ : Continuous (fun p : M × V => (φ₁ p.1) p.2))
    (hcont₂ : Continuous (fun p : M × V => (φ₂ p.1) p.2)) :
    φ₁ = φ₂ := by


  ext m v


  have hcv₁ : Continuous (fun m : M => (φ₁ m) v) :=
    hcont₁.comp (Continuous.prodMk continuous_id continuous_const)
  have hcv₂ : Continuous (fun m : M => (φ₂ m) v) :=
    hcont₂.comp (Continuous.prodMk continuous_id continuous_const)

  have heq_on : Set.EqOn (fun m => (φ₁ m) v) (fun m => (φ₂ m) v)
      (Set.range (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac)) := by
    intro m ⟨μ, hμ⟩
    subst hμ
    simp only

    have eq₁ : φ₁.comp (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) =
        MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π := by
      ext g; simp [MonoidAlgebra.lift_single, h₁]
    have eq₂ : φ₂.comp (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac) =
        MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π := by
      ext g; simp [MonoidAlgebra.lift_single, h₂]
    have h1' := congr_fun (congr_arg DFunLike.coe eq₁) μ
    have h2' := congr_fun (congr_arg DFunLike.coe eq₂) μ
    simp [AlgHom.comp_apply] at h1' h2'
    rw [h1', h2']


  have := Continuous.ext_on (CompactlySupportedMeasureAlgebra.discrete_dense (G := G) (M := M)) hcv₁ hcv₂ heq_on

  exact congr_fun this m

end MeasureRep

section Density

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
variable [IsTopologicalGroup G] [CompactSpace G]

def IsKFiniteFunc (K : Subgroup G) (f : ↥K → ℂ) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun g : ↥K => fun k : ↥K => f (g⁻¹ * k))))

omit [IsTopologicalGroup G] [CompactSpace G] in

lemma finite_of_allKFiniteFunc (K : Subgroup G) [CompactSpace K]
    (hall : ∀ f : ↥K → ℂ, IsKFiniteFunc K f) : Finite ↥K := by
  classical
  have h_fd := hall (Pi.single 1 (1 : ℂ))
  rw [IsKFiniteFunc] at h_fd
  have h_orbit : (Set.range (fun (g : ↥K) (k : ↥K) =>
      (Pi.single (1 : ↥K) (1 : ℂ) : ↥K → ℂ) (g⁻¹ * k))) =
      Set.range (fun (g : ↥K) => (Pi.single g (1 : ℂ) : ↥K → ℂ)) := by
    ext f; simp only [Set.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, by ext k; simp [Pi.single_apply, inv_mul_eq_one, eq_comm]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, by ext k; simp [Pi.single_apply, inv_mul_eq_one, eq_comm]⟩
  rw [h_orbit] at h_fd
  exact (linearIndependent_span (Pi.linearIndependent_single_one (↥K) ℂ)).finite




end Density

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [IsTopologicalGroup G] [CompactSpace G]






end Projection

end ContinuousRep

end
