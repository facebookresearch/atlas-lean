/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HarishChandraFunctor
import Atlas.LieGroups.code.GKModuleDefs
import Atlas.LieGroups.code.AnalyticityRegularity
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Group.Quotient

universe uFw

noncomputable section

set_option autoImplicit false

open scoped Manifold

def ContinuousRep.IsWeaklyAnalytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (v : F) : Prop :=
  ∀ (h : F →L[ℂ] ℂ) (g₀ : G),
    AnalyticAt ℝ
      (fun (e : E) =>
        (h (π.toMonoidHom ((chartAt H g₀).symm (I.symm e)) v) : ℂ))
      (I (chartAt H g₀ g₀))

namespace EllipticOperator

def IsEllipticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (symbolAt : E → ℝ) : Prop :=
  ∀ (p : E), p ≠ 0 → symbolAt p ≠ 0

def IsElliptic
    {X : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : X → E → ℝ) : Prop :=
  ∀ (x : X), IsEllipticAt (σ x)

end EllipticOperator

open EllipticOperator in
theorem hahn_banach_separation_closed_subspace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : Set F) (x : F)
    (hS_subspace : ∃ (M : Submodule ℂ F), (M : Set F) = S)
    (hx : x ∉ closure S) :
    ∃ (h : F →L[ℂ] ℂ), (∀ v ∈ closure S, h v = 0) ∧ h x ≠ 0 := by
  obtain ⟨M, hMS⟩ := hS_subspace

  have hcl : closure S = (M.topologicalClosure : Set F) := by
    rw [← hMS, Submodule.topologicalClosure_coe]
  rw [hcl] at hx

  haveI hclosed : IsClosed (M.topologicalClosure : Set F) :=
    M.isClosed_topologicalClosure

  have hxQ : M.topologicalClosure.mkQ x ≠ 0 := by
    rwa [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]


  obtain ⟨g, hg⟩ : ∃ (g : (F ⧸ M.topologicalClosure) →L[ℂ] ℂ),
      g (M.topologicalClosure.mkQ x) ≠ 0 :=
    SeparatingDual.exists_ne_zero hxQ

  let mkQ_clm : F →L[ℂ] (F ⧸ M.topologicalClosure) :=
    { M.topologicalClosure.mkQ with cont := continuous_quot_mk }
  refine ⟨g.comp mkQ_clm, ?_, ?_⟩
  ·
    intro v hv
    rw [hcl] at hv
    show g (mkQ_clm v) = 0
    suffices hsuff : mkQ_clm v = 0 by rw [hsuff, map_zero]
    show M.topologicalClosure.mkQ v = 0
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  ·
    show g (mkQ_clm x) ≠ 0
    exact hg



lemma subrep_orbit_image
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U) (v : ↥U) :
    U.subtype '' (Set.range (fun k : K_sub =>
      ((π.subrepresentation U hU).toMonoidHom k) v)) =
    Set.range (fun k : K_sub => (π.toMonoidHom k) (v : F)) := by
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨k, hk⟩, hy⟩
    exact ⟨k, by simp only [Submodule.subtype_apply] at hy; rw [← hy, ← hk]; rfl⟩
  · rintro ⟨k, hk⟩
    refine ⟨((π.subrepresentation U hU).toMonoidHom k) v, ⟨k, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply]; rw [← hk]; rfl

lemma kFinite_subrep_to_full
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U)
    (v : ↥U) (hv : v ∈ ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub) :
    (v : F) ∈ ContinuousRep.kFiniteSubspace π K_sub := by
  rw [ContinuousRep.mem_kFiniteSubspace] at hv ⊢
  unfold ContinuousRep.IsKFinite at hv ⊢
  have hmap : Submodule.map U.subtype
    (Submodule.span ℂ (Set.range (fun k : K_sub =>
      ((π.subrepresentation U hU).toMonoidHom k) v))) =
    Submodule.span ℂ (Set.range (fun k : K_sub => (π.toMonoidHom k) (v : F))) := by
    rw [Submodule.map_span, subrep_orbit_image]
  rw [← hmap]
  exact Module.Finite.map
    (Submodule.span ℂ (Set.range (fun k : K_sub =>
      ((π.subrepresentation U hU).toMonoidHom k) v)))
    U.subtype

lemma subrep_kFinite_image_subset
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) [CompactSpace K_sub] [T2Space K_sub]

    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U) :
    U.subtype '' (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) ⊆
    ((π.kFiniteSubspace K_sub).subtype ''
      ((Submodule.comap (π.kFiniteSubspace K_sub).subtype U) :
        Set ↥(π.kFiniteSubspace K_sub))) := by
  intro x ⟨v, hv_kfin, hv_eq⟩
  have hx_kfin : x ∈ ContinuousRep.kFiniteSubspace π K_sub := by
    rw [← hv_eq]; exact kFinite_subrep_to_full π K_sub U hU v hv_kfin
  have hx_U : x ∈ (U : Set F) := by
    rw [← hv_eq]; exact v.2
  exact ⟨⟨x, hx_kfin⟩, hx_U, rfl⟩


theorem isotypic_projector_preserves_K_invariant_image
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (P : F →L[ℂ] F)
    (_hP_kfin : ∀ w, P w ∈ π.kFiniteSubspace K_sub)
    (_hP_comm : ∀ (k : K_sub), P.comp (π.toMonoidHom k) = (π.toMonoidHom k).comp P)
    (hP_preserves : ∀ (S : Submodule ℂ F),
      (∀ (k : K_sub) (s : F), s ∈ S → (π.toMonoidHom k) s ∈ S) →
      ∀ (s : F), s ∈ S → s ∈ π.kFiniteSubspace K_sub → P s ∈ S)

    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW_inv : ∀ (k : K_sub) (w : ↥(π.kFiniteSubspace K_sub)),
      w ∈ W → (kFiniteSubspace_kAction π K_sub) k w ∈ W) :
    ∀ w ∈ (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub)),
      P w ∈ (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub)) := by
  intro w ⟨w', hw'_mem, hw'_eq⟩
  subst hw'_eq


  set S := W.map (π.kFiniteSubspace K_sub).subtype with hS_def
  have hS_kstable : ∀ (k : K_sub) (s : F), s ∈ S → (π.toMonoidHom k) s ∈ S := by
    intro k s hs
    rw [hS_def, Submodule.mem_map] at hs ⊢
    obtain ⟨u, hu_mem, hu_eq⟩ := hs
    refine ⟨(kFiniteSubspace_kAction π K_sub) k u, hW_inv k u hu_mem, ?_⟩
    subst hu_eq

    rfl
  have hw'_S : (w' : F) ∈ S := by
    rw [hS_def, Submodule.mem_map]
    exact ⟨w', hw'_mem, rfl⟩
  have hw'_kfin : (w' : F) ∈ π.kFiniteSubspace K_sub := w'.property
  have hPw_S := hP_preserves S hS_kstable (w' : F) hw'_S hw'_kfin

  rw [hS_def, Submodule.mem_map] at hPw_S
  obtain ⟨v, hv_mem, hv_eq⟩ := hPw_S
  exact ⟨v, hv_mem, hv_eq⟩

theorem isotypic_projector_image_closed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (P : F →L[ℂ] F)
    (hP_fin : FiniteDimensional ℂ (LinearMap.range P.toLinearMap))
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub)) :
    IsClosed (P '' ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) : Set F) := by

  have h_eq : P '' ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) =
      (((W.map (π.kFiniteSubspace K_sub).subtype).map P.toLinearMap : Submodule ℂ F) : Set F) := by
    ext x; simp
  rw [h_eq]

  have h_le : (W.map (π.kFiniteSubspace K_sub).subtype).map P.toLinearMap ≤
      LinearMap.range P.toLinearMap := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
    exact LinearMap.mem_range.mpr ⟨y, rfl⟩
  haveI : FiniteDimensional ℂ ((W.map (π.kFiniteSubspace K_sub).subtype).map P.toLinearMap) :=
    Submodule.finiteDimensional_of_le h_le
  exact Submodule.closed_of_finiteDimensional _




def ContinuousRep.IsFiniteLength
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : ContinuousRep G V) : Prop :=
  ∃ (n : ℕ) (chain : Fin (n + 1) → Submodule ℂ V),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr (le_refl n)⟩ = ⊤ ∧
    (∀ (i : Fin n), chain i.castSucc < chain i.succ) ∧
    (∀ (i : Fin n), π.IsInvariantSubspace (chain i.castSucc)) ∧
    (∀ (i : Fin n), π.IsInvariantSubspace (chain i.succ)) ∧


    (∀ (i : Fin n) (W : Submodule ℂ V), π.IsInvariantSubspace W →
      chain i.castSucc ≤ W → W ≤ chain i.succ →
      W = chain i.castSucc ∨ W = chain i.succ)



theorem GKModule.finiteLength_finitelyGenerated
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hfl : M.IsFiniteLength) :
    ∃ (S : Finset V), ∀ v : V,
      v ∈ Submodule.span ℂ
        (⋃ (s : V) (_ : s ∈ S) (Xs : List 𝔤),
          ({GKModule.lieIterate Xs s} : Set V)) := by
  classical

  obtain ⟨n, chain, h0, hn, hlt, hsub_i, hsub_si, hirr⟩ := hfl

  have hexists_vi : ∀ (i : Fin n),
      ∃ v : V, v ∈ chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∧
              v ∉ chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
    intro i
    have hi := hlt i
    rw [SetLike.lt_iff_le_and_exists] at hi
    exact hi.2
  choose vi hvi_in hvi_nin using hexists_vi

  have hkorbit_fg : ∀ (i : Fin n),
      (Submodule.span ℂ (Set.range (fun k : K => M.σ k (vi i)))).FG := by
    intro i
    rw [Submodule.fg_iff_finiteDimensional]
    exact M.locallyFinite (vi i)

  choose Bi hBi using fun i => (hkorbit_fg i)

  use Finset.univ.biUnion Bi

  set TS := Submodule.span ℂ
      (⋃ (s : V) (_ : s ∈ Finset.univ.biUnion Bi) (Xs : List 𝔤),
        ({GKModule.lieIterate Xs s} : Set V)) with hTS_def

  have hmem_gen : ∀ (s : V) (Xs : List 𝔤), s ∈ Finset.univ.biUnion Bi →
      GKModule.lieIterate Xs s ∈ TS := by
    intro s Xs hs
    apply Submodule.subset_span
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨s, Finset.mem_coe.mpr hs, Xs, rfl⟩

  have hS_sub_TS : ∀ s, s ∈ Finset.univ.biUnion Bi → s ∈ TS := by
    intro s hs; exact hmem_gen s [] hs

  have hBi_sub_TS : ∀ (i : Fin n), (Submodule.span ℂ ↑(Bi i) : Submodule ℂ V) ≤ TS := by
    intro i
    apply Submodule.span_le.mpr
    intro w hw
    exact hS_sub_TS w (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hw⟩)

  have hvi_in_TS : ∀ (i : Fin n), vi i ∈ TS := by
    intro i
    have h1 : vi i ∈ Submodule.span ℂ (Set.range (fun k : K => M.σ k (vi i))) := by
      apply Submodule.subset_span
      exact ⟨1, by simp [map_one]⟩
    rw [← hBi i] at h1
    exact hBi_sub_TS i h1

  have hTS_lie : ∀ (X : 𝔤) (w : V), w ∈ TS → ⁅X, w⁆ ∈ TS := by
    intro X w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hu
      obtain ⟨s, hs, Xs, rfl⟩ := hu
      exact hmem_gen s (X :: Xs) hs
    | zero => simp [lie_zero]
    | add x y _ _ hx hy => rw [lie_add]; exact TS.add_mem hx hy
    | smul c x _ hx => rw [lie_smul]; exact TS.smul_mem c hx

  have hS_Kstable : ∀ (k : K) (s : V), s ∈ Finset.univ.biUnion Bi → M.σ k s ∈ TS := by
    intro k s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨i, _, hs_in_Bi⟩ := hs


    have hs_korbit : s ∈ Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i))) := by
      rw [← hBi i]; exact Submodule.subset_span (Finset.mem_coe.mpr hs_in_Bi)
    have hks_korbit : M.σ k s ∈ Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i))) := by

      have hle : Submodule.map (M.σ k) (Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i)))) ≤
          Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i))) := by
        rw [Submodule.map_span_le]
        intro u ⟨k', hk'⟩
        subst hk'
        exact Submodule.subset_span ⟨k * k', by simp [map_mul]⟩
      exact hle (Submodule.mem_map_of_mem hs_korbit)

    rw [← hBi i] at hks_korbit
    exact hBi_sub_TS i hks_korbit

  have hTS_K : ∀ (k : K) (w : V), w ∈ TS → M.σ k w ∈ TS := by
    intro k w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hu
      obtain ⟨s, hs, Xs, rfl⟩ := hu

      induction Xs with
      | nil =>
        simp only [GKModule.lieIterate, List.foldr_nil]
        exact hS_Kstable k s hs
      | cons X Xs' ihXs =>
        simp only [GKModule.lieIterate, List.foldr_cons]
        rw [M.equivariance k X (List.foldr (fun X acc => ⁅X, acc⁆) s Xs')]
        exact hTS_lie _ _ ihXs
    | zero => simp [map_zero]
    | add x y _ _ hx hy => rw [map_add]; exact TS.add_mem hx hy
    | smul c x _ hx => rw [LinearMap.map_smul]; exact TS.smul_mem c hx

  have hTS_sub : M.IsSubmodule TS := ⟨hTS_lie, hTS_K⟩

  suffices h_chain : ∀ (j : Fin (n + 1)), chain j ≤ TS by
    intro v
    have hv_top : v ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
    rw [← hn] at hv_top
    exact h_chain ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ hv_top
  intro ⟨j, hj⟩
  induction j with
  | zero =>
    show chain ⟨0, _⟩ ≤ TS
    rw [h0]; exact bot_le
  | succ j' ih =>
    have hj'_lt_n : j' < n := Nat.lt_of_succ_lt_succ hj
    have ih_j' : chain ⟨j', Nat.lt_succ_of_lt hj'_lt_n⟩ ≤ TS :=
      ih (Nat.lt_succ_of_lt hj'_lt_n)

    set W := TS ⊓ chain ⟨j' + 1, hj⟩
    have hW_sub : M.IsSubmodule W := by
      exact ⟨fun X w hw => Submodule.mem_inf.mpr
        ⟨hTS_lie X w (Submodule.mem_inf.mp hw).1,
         (hsub_si ⟨j', hj'_lt_n⟩).lie_invariant X w (Submodule.mem_inf.mp hw).2⟩,
       fun k w hw => Submodule.mem_inf.mpr
        ⟨hTS_K k w (Submodule.mem_inf.mp hw).1,
         (hsub_si ⟨j', hj'_lt_n⟩).group_invariant k w (Submodule.mem_inf.mp hw).2⟩⟩
    have hchain_le_W : chain ⟨j', Nat.lt_succ_of_lt hj'_lt_n⟩ ≤ W := by
      intro w hw
      exact Submodule.mem_inf.mpr ⟨ih_j' hw, (hlt ⟨j', hj'_lt_n⟩).le hw⟩
    have hW_le_chain : W ≤ chain ⟨j' + 1, hj⟩ := inf_le_right

    have hvi_in_W : vi ⟨j', hj'_lt_n⟩ ∈ W :=
      Submodule.mem_inf.mpr ⟨hvi_in_TS ⟨j', hj'_lt_n⟩, hvi_in ⟨j', hj'_lt_n⟩⟩

    have hW_ne : W ≠ chain ⟨j', Nat.lt_succ_of_lt hj'_lt_n⟩ := by
      intro heq; exact hvi_nin ⟨j', hj'_lt_n⟩ (heq ▸ hvi_in_W)

    rcases hirr ⟨j', hj'_lt_n⟩ W hW_sub hchain_le_W hW_le_chain with h_low | h_high
    · exact absurd h_low hW_ne
    ·
      show chain ⟨j' + 1, hj⟩ ≤ TS
      rw [← h_high]
      exact inf_le_left


end
