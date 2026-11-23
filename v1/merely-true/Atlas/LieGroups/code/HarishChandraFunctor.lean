/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.Admissible
import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.GKModuleDefs
import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.KFiniteProps

noncomputable section

set_option autoImplicit false

open scoped Manifold

@[reducible]
def kFiniteSubspace_lieRingModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_stable : ∀ (X : 𝔤) (v : F),
      v ∈ π.kFiniteSubspace K_sub → (ι X) v ∈ π.kFiniteSubspace K_sub) :
    LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub) :=
  letI : Bracket 𝔤 ↥(π.kFiniteSubspace K_sub) :=
    ⟨fun X v => ⟨(ι X) v.val, hι_stable X v.val v.prop⟩⟩
  { add_lie := fun x y m => by
      apply Subtype.ext
      show (ι (x + y)) m.val = (ι x) m.val + (ι y) m.val
      simp [map_add, LinearMap.add_apply]
    lie_add := fun x m n => by
      apply Subtype.ext
      show (ι x) (m.val + n.val) = (ι x) m.val + (ι x) n.val
      simp [map_add]
    leibniz_lie := fun x y m => by
      apply Subtype.ext
      show (ι x) ((ι y) m.val) = (ι ⁅x, y⁆) m.val + (ι y) ((ι x) m.val)
      rw [ι.map_lie x y, Ring.lie_def]; simp [LinearMap.sub_apply] }

@[reducible]
def kFiniteSubspace_lieModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_stable : ∀ (X : 𝔤) (v : F),
      v ∈ π.kFiniteSubspace K_sub → (ι X) v ∈ π.kFiniteSubspace K_sub) :
    @LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub) _ _ _ _ _
      (kFiniteSubspace_lieRingModule I π K_sub _hadm 𝔤 ι hι_stable) :=
  @LieModule.mk ℂ 𝔤 ↥(π.kFiniteSubspace K_sub) _ _ _ _ _
    (kFiniteSubspace_lieRingModule I π K_sub _hadm 𝔤 ι hι_stable)
    (fun t x m => by
      apply Subtype.ext
      show (ι (t • x)) m.val = t • ((ι x) m.val)
      simp [map_smul, LinearMap.smul_apply])
    (fun t x m => by
      apply Subtype.ext
      show (ι x) (t • m.val) = t • ((ι x) m.val)
      simp [map_smul])

def kFiniteSubspace_kAction
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) :
    Representation ℂ K_sub ↥(π.kFiniteSubspace K_sub) where
  toFun k :=
  { toFun := fun ⟨v, hv⟩ =>
      ⟨(π.toMonoidHom k) v,
       ContinuousRep.kFiniteSubspace_stable π K_sub k v hv⟩
    map_add' := fun ⟨v, _⟩ ⟨w, _⟩ => by
      ext; simp [map_add]
    map_smul' := fun c ⟨v, _⟩ => by
      ext; simp [map_smul] }
  map_one' := by
    ext ⟨v, _⟩; simp
  map_mul' := fun k₁ k₂ => by
    ext ⟨v, _⟩; simp

theorem kFiniteSubspace_kAction_locallyFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) :
    (kFiniteSubspace_kAction π K_sub).IsLocallyFinite := by
  intro ⟨v, hv⟩


  set σ := kFiniteSubspace_kAction π K_sub
  set S_VK := Submodule.span ℂ (Set.range (fun k : K_sub => σ k ⟨v, hv⟩))
  set S_F := Submodule.span ℂ (Set.range (fun k : K_sub => (π.toMonoidHom k) v))

  have hmap : S_VK.map (π.kFiniteSubspace K_sub).subtype ≤ S_F := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨⟨w, hw⟩, hk, rfl⟩ := hx
    obtain ⟨k, hk'⟩ := hk
    simp only [Submodule.subtype_apply]
    have : w = (π.toMonoidHom k) v := (congr_arg Subtype.val hk').symm
    rw [this]
    exact Submodule.subset_span ⟨k, rfl⟩

  haveI : FiniteDimensional ℂ S_F := hv

  haveI : FiniteDimensional ℂ (S_VK.map (π.kFiniteSubspace K_sub).subtype) :=
    Module.Finite.of_injective (Submodule.inclusion hmap) (Submodule.inclusion_injective hmap)

  exact Module.Finite.of_injective
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) S_VK).toLinearMap
    (LinearEquiv.injective _)

def harishChandraGKModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (_ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆) :
    GKModule 𝔤 K_sub 𝔨 Ad ↥(π.kFiniteSubspace K_sub) where
  σ := kFiniteSubspace_kAction π K_sub
  locallyFinite := kFiniteSubspace_kAction_locallyFinite π K_sub
  diffσ := (LieModule.toEnd ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)).toLinearMap.comp 𝔨.incl.toLinearMap
  diff_eq_lie := fun X v => by
    rfl
  equivariance := hequiv





def iterLieAction
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F)) (Xs : List 𝔤) (v : F) : F :=
  Xs.foldr (fun X w => (ι X) w) v

lemma iterLieAction_mem_kFiniteSubspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι X) w ∈ π.kFiniteSubspace K_sub)
    (Xs : List 𝔤) (v : F) (hv : v ∈ π.kFiniteSubspace K_sub) :
    iterLieAction ι Xs v ∈ π.kFiniteSubspace K_sub := by
  induction Xs with
  | nil => exact hv
  | cons X rest ih =>
    simp only [iterLieAction, List.foldr_cons]
    exact hι_stable X _ ih

lemma iterLieAction_agree_of_eq_on_kFinite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι₁ ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hlie_eq : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι₁ X) w = (ι₂ X) w)
    (hι₁_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι₁ X) w ∈ π.kFiniteSubspace K_sub)
    (hι₂_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι₂ X) w ∈ π.kFiniteSubspace K_sub)
    (Xs : List 𝔤) (v : F) (hv : v ∈ π.kFiniteSubspace K_sub) :
    iterLieAction ι₁ Xs v = iterLieAction ι₂ Xs v := by
  induction Xs with
  | nil => rfl
  | cons X rest ih =>
    show (ι₁ X) (iterLieAction ι₁ rest v) = (ι₂ X) (iterLieAction ι₂ rest v)
    rw [ih, hlie_eq X _ (iterLieAction_mem_kFiniteSubspace I π K_sub 𝔤 ι₂ hι₂_stable rest v hv)]





lemma separation_from_closed_submodule
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : Submodule ℂ F) (hS : IsClosed (S : Set F))
    (x : F) (hx : x ∉ S) :
    ∃ h : F →L[ℂ] ℂ, (∀ s ∈ S, h s = 0) ∧ h x ≠ 0 := by
  haveI : IsClosed (S : Set F) := hS
  have hx_bar : (Submodule.Quotient.mk (p := S) x : F ⧸ S) ≠ 0 := by
    rwa [ne_eq, Submodule.Quotient.mk_eq_zero]
  obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) (V := F ⧸ S) hx_bar
  have hcont : Continuous S.mkQ := continuous_quotient_mk'
  set h := g.comp (⟨S.mkQ, hcont⟩ : F →L[ℂ] F ⧸ S) with hh_def
  refine ⟨h, ?_, ?_⟩
  · intro s hs
    simp only [hh_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk']
    have : (Submodule.Quotient.mk (p := S) s : F ⧸ S) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hs
    simp [this]
  · simp only [hh_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk']
    exact hg

lemma iterLieAction_mem_image_submodule
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    {V : Submodule ℂ F}
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 V]
    [LieModule ℂ 𝔤 V]
    (hι_compat : ∀ (X : 𝔤) (w : V),
      V.subtype ⁅X, w⁆ = ι X (V.subtype w))
    (W : Submodule ℂ V)
    (hW_lie : ∀ (X : 𝔤) (w : V), w ∈ W → ⁅X, w⁆ ∈ W)
    (Xs : List 𝔤) (w : V) (hw : w ∈ W) :
    iterLieAction ι Xs (V.subtype w) ∈ Submodule.map V.subtype W := by
  induction Xs with
  | nil =>
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  | cons X Xs ih =>
    change ι X (iterLieAction ι Xs (V.subtype w)) ∈ Submodule.map V.subtype W
    obtain ⟨w', hw', heq⟩ := Submodule.mem_map.mp ih
    rw [← heq, ← hι_compat]
    exact Submodule.mem_map.mpr ⟨⁅X, w'⁆, hW_lie X w' hw', rfl⟩








theorem lie_action_preserves_invariant_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_compat : ∀ (X : 𝔤) (w : ↥(π.kFiniteSubspace K_sub)),
      (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ = ι X ((π.kFiniteSubspace K_sub).subtype w))
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U)
    (hι_inv : ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U)
    (X : 𝔤) (w : ↥(π.kFiniteSubspace K_sub))
    (hw : (π.kFiniteSubspace K_sub).subtype w ∈ U) :
    (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ ∈ U := by
  rw [hι_compat]
  exact hι_inv X _ hw













theorem repHom_maps_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    (T : RepHom π₁ π₂)
    (v : F₁) (hv : v ∈ π₁.kFiniteSubspace K_sub) :
    T.toContinuousLinearMap v ∈ π₂.kFiniteSubspace K_sub := by
  rw [ContinuousRep.mem_kFiniteSubspace] at hv ⊢
  unfold ContinuousRep.IsKFinite at *

  have hsub : Submodule.span ℂ
      (Set.range (fun k : K_sub => (π₂.toMonoidHom k) (T.toContinuousLinearMap v))) ≤
      (Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))).map
        T.toContinuousLinearMap.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx; obtain ⟨k, rfl⟩ := hx

    dsimp only
    have hintertwine := T.intertwines (k : G)
    have heq : (π₂.toMonoidHom ↑k) (T.toContinuousLinearMap v) =
        T.toContinuousLinearMap ((π₁.toMonoidHom ↑k) v) := by
      have := ContinuousLinearMap.ext_iff.mp hintertwine v
      simp [ContinuousLinearMap.comp_apply] at this
      exact this.symm
    rw [heq]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))) := hv
  haveI : FiniteDimensional ℂ
      ((Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))).map
        T.toContinuousLinearMap.toLinearMap) :=
    inferInstance
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

def repHom_restrict_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    (T : RepHom π₁ π₂) :
    ↥(π₁.kFiniteSubspace K_sub) →ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub) where
  toFun v := ⟨T.toContinuousLinearMap v.val,
    repHom_maps_kFinite π₁ π₂ K_sub T v.val v.prop⟩
  map_add' u v := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c v := by
    apply Subtype.ext
    simp [map_smul]


theorem kEquivariant_finiteRange_maps_to_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (P : F →L[ℂ] F)
    (hfin : FiniteDimensional ℂ (LinearMap.range P.toLinearMap))
    (hcomm : ∀ (k : K_sub), P.comp (π.toMonoidHom k) = (π.toMonoidHom k).comp P) :
    ∀ w, P w ∈ π.kFiniteSubspace K_sub := by
  intro w
  show ContinuousRep.IsKFinite π K_sub (P w)
  unfold ContinuousRep.IsKFinite


  have h_in_range : ∀ k : K_sub, (π.toMonoidHom ↑k) (P w) ∈
      LinearMap.range P.toLinearMap := by
    intro k
    have heq := congr_fun (congr_arg DFunLike.coe (hcomm k)) w
    simp only [ContinuousLinearMap.comp_apply] at heq
    rw [← heq]
    exact LinearMap.mem_range.mpr ⟨(π.toMonoidHom ↑k) w, rfl⟩
  have h_span_le : Submodule.span ℂ
      (Set.range (fun k : K_sub => (π.toMonoidHom ↑k) (P w))) ≤
      LinearMap.range P.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact h_in_range k
  exact Module.Finite.of_injective (Submodule.inclusion h_span_le)
    (Submodule.inclusion_injective h_span_le)

lemma finsupp_rep_intertwines
    {G : Type*} [Group G] [TopologicalSpace G]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
    (π₂ : ContinuousRep G F₂) (π₃ : ContinuousRep G F₃)
    (S : RepHom π₂ π₃)
    (K_sub : Subgroup G)
    (c : K_sub →₀ ℂ)
    (w : F₂) :
    S.toContinuousLinearMap
      ((c.sum (fun k a => a • π₂.toMonoidHom k)) w) =
    (c.sum (fun k a => a • π₃.toMonoidHom k))
      (S.toContinuousLinearMap w) := by
  simp only [Finsupp.sum]

  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  rw [map_sum]
  congr 1
  ext ⟨k, hk⟩
  rw [map_smul]
  congr 1
  have := S.intertwines (k : G)
  exact congr_fun (congr_arg DFunLike.coe this) w




structure UnitaryRepEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) extends RepEquiv π₁ π₂ where
  inner_preserving : ∀ (v w : V),
    @inner ℂ W _ (toContinuousLinearEquiv v) (toContinuousLinearEquiv w) =
    @inner ℂ V _ v w


end
