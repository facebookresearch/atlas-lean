/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.GKModuleDefs
import Atlas.LieGroups.code.DixmierLemma
import Atlas.LieGroups.code.InfinitesimalEquivalenceCore
import Atlas.LieGroups.code.InfinitesimalEquivalenceProposition71
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.Topology.DenseEmbedding
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative

noncomputable section

open scoped Cardinal

lemma gkmodule_has_countable_spanning_set
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    [FiniteDimensional ℂ 𝔤] :
    ∃ (s : Set V), Submodule.span ℂ s = ⊤ ∧ Cardinal.mk s ≤ Cardinal.aleph0 := by

  by_cases hV : (⊥ : Submodule ℂ V) = ⊤
  · refine ⟨∅, ?_, by simp⟩
    rw [Submodule.span_empty]
    exact hV

  · push Not at hV
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, v₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hV (Submodule.eq_top_iff'.mpr (fun v => by simp [h v]))

    let bg := Module.finBasis ℂ 𝔤

    let W₀ := Submodule.span ℂ (Set.range (fun k : K => (M.σ k) v₀))
    haveI : FiniteDimensional ℂ W₀ := M.locallyFinite v₀

    let bW₀ := Module.finBasis ℂ W₀

    let seeds : Fin (Module.finrank ℂ W₀) → V := fun j => (bW₀ j : V)

    let iterBracket : List (Fin (Module.finrank ℂ 𝔤)) → V → V :=
      fun l v => l.foldr (fun i w => ⁅bg i, w⁆) v

    let S := Set.range (fun p : List (Fin (Module.finrank ℂ 𝔤)) × Fin (Module.finrank ℂ W₀) =>
      iterBracket p.1 (seeds p.2))
    use S
    constructor
    ·

      have hW₀_eq : W₀ = Submodule.span ℂ (Set.range seeds) := by
        show W₀ = Submodule.span ℂ (Set.range (fun j => (bW₀ j : V)))
        rw [show (fun j => (bW₀ j : V)) = W₀.subtype ∘ bW₀ from rfl]
        rw [Set.range_comp, Submodule.span_image, bW₀.span_eq]
        simp [Submodule.map_top, Submodule.range_subtype]

      have hseeds_sub : Set.range seeds ⊆ S := by
        intro s hs
        obtain ⟨j', rfl⟩ := hs
        exact ⟨⟨[], j'⟩, show List.foldr (fun i w => ⁅bg i, w⁆) (seeds j') [] = seeds j' from rfl⟩

      have hW₀_le : W₀ ≤ Submodule.span ℂ S := by
        rw [hW₀_eq]; exact Submodule.span_mono hseeds_sub

      have hlie_inv : ∀ (X : 𝔤) (w : V), w ∈ Submodule.span ℂ S → ⁅X, w⁆ ∈ Submodule.span ℂ S := by
        intro X w' hw'
        have hbl : ∀ i' : Fin (Module.finrank ℂ 𝔤), ⁅(bg i' : 𝔤), w'⁆ ∈ Submodule.span ℂ S := by
          intro i'
          have : Submodule.map (LieModule.toEnd ℂ 𝔤 V (bg i'))
              (Submodule.span ℂ S) ≤ Submodule.span ℂ S := by
            rw [Submodule.map_span_le]
            intro s' hs'
            obtain ⟨⟨l'', j'⟩, rfl⟩ := hs'
            apply Submodule.subset_span
            exact ⟨⟨i' :: l'', j'⟩, rfl⟩
          exact this ⟨w', hw', rfl⟩
        rw [(bg.sum_repr X).symm, sum_lie]
        simp_rw [smul_lie]
        exact Submodule.sum_mem _ (fun i' _ => Submodule.smul_mem _ _ (hbl i'))

      have hSsub : M.IsSubmodule (Submodule.span ℂ S) := by
        constructor
        ·
          exact hlie_inv
        ·
          intro k w hw
          have : Submodule.map (M.σ k) (Submodule.span ℂ S) ≤ Submodule.span ℂ S := by
            rw [Submodule.map_span_le]
            intro s hs
            obtain ⟨⟨l, j⟩, rfl⟩ := hs

            induction l with
            | nil =>

              show (M.σ k) (List.foldr (fun i w => ⁅bg i, w⁆) (seeds j) []) ∈ Submodule.span ℂ S
              simp only [List.foldr_nil]

              have hW₀_Kinv : Submodule.map (M.σ k) W₀ ≤ W₀ := by
                rw [Submodule.map_span_le]
                intro s' hs'
                obtain ⟨k', rfl⟩ := hs'
                apply Submodule.subset_span
                refine ⟨k * k', ?_⟩
                show (M.σ (k * k')) v₀ = (M.σ k) ((M.σ k') v₀)
                rw [M.σ.map_mul]; rfl
              have hseed_in_W₀ : seeds j ∈ W₀ := (bW₀ j).property
              exact hW₀_le (hW₀_Kinv ⟨seeds j, hseed_in_W₀, rfl⟩)
            | cons i l' ih =>

              show (M.σ k) (List.foldr (fun i w => ⁅bg i, w⁆) (seeds j) (i :: l')) ∈ Submodule.span ℂ S
              simp only [List.foldr_cons]
              rw [M.equivariance]
              exact hlie_inv (Ad k (bg i)) _ ih
          exact this ⟨w, hw, rfl⟩

      rcases hirr _ hSsub with h | h
      ·
        exfalso
        have hv₀_in_W₀ : v₀ ∈ W₀ := Submodule.subset_span ⟨1, by simp⟩
        have : v₀ ∈ Submodule.span ℂ S := hW₀_le hv₀_in_W₀
        rw [h] at this
        exact hv₀ ((Submodule.mem_bot ℂ).mp this)
      · exact h
    ·
      exact (Set.countable_range _).le_aleph0

theorem dixmier_countable_dim_gkmodule
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    [FiniteDimensional ℂ 𝔤] :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by

  obtain ⟨s, hs_span, hs_count⟩ := gkmodule_has_countable_spanning_set M hirr

  rw [← rank_top (R := ℂ) (M := V), ← hs_span]
  exact (rank_span_le s).trans hs_count

theorem schur_gkmodule_zero_or_bijective
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (φ : GKModuleHom M M) :
    φ.toLinearMap = 0 ∨ Function.Bijective φ.toLinearMap := by

  have hker_sub : M.IsSubmodule (LinearMap.ker φ.toLinearMap) := by
    constructor
    ·
      intro X w hw
      simp only [LinearMap.mem_ker] at hw ⊢
      rw [φ.lie_comm]
      simp only [hw, lie_zero]
    ·
      intro k w hw
      simp only [LinearMap.mem_ker] at hw ⊢
      rw [φ.group_comm]
      simp only [hw, map_zero]

  have hker := hirr _ hker_sub
  cases hker with
  | inl hker_bot =>

    right
    constructor
    ·
      rwa [LinearMap.ker_eq_bot] at hker_bot
    ·
      have hrange_sub : M.IsSubmodule (LinearMap.range φ.toLinearMap) := by
        constructor
        · intro X w hw
          simp only [LinearMap.mem_range] at hw ⊢
          obtain ⟨u, rfl⟩ := hw
          exact ⟨⁅X, u⁆, φ.lie_comm X u⟩
        · intro k w hw
          simp only [LinearMap.mem_range] at hw ⊢
          obtain ⟨u, rfl⟩ := hw
          exact ⟨M.σ k u, φ.group_comm k u⟩
      have hrange := hirr _ hrange_sub
      cases hrange with
      | inl hrange_bot =>

        rw [LinearMap.range_eq_bot] at hrange_bot
        intro v
        have hv : v = 0 := by
          have hv_ker : v ∈ LinearMap.ker φ.toLinearMap := by
            rw [LinearMap.mem_ker, hrange_bot]
            simp
          rwa [hker_bot] at hv_ker
        exact ⟨0, by subst hv; simp [hrange_bot]⟩
      | inr htop =>
        rwa [LinearMap.range_eq_top] at htop
  | inr htop =>

    left
    ext v
    have : v ∈ LinearMap.ker φ.toLinearMap := htop ▸ trivial
    exact LinearMap.mem_ker.mp this

lemma adjoin_range_ι_uea
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] :
    Algebra.adjoin ℂ (Set.range (⇑(UniversalEnvelopingAlgebra.ι ℂ) : 𝔤 → _)) = ⊤ := by
  have surj := RingQuot.mkAlgHom_surjective ℂ (UniversalEnvelopingAlgebra.Rel ℂ 𝔤)
  have h1 := TensorAlgebra.adjoin_range_ι (R := ℂ) (M := 𝔤)
  have h2 := AlgHom.map_adjoin (UniversalEnvelopingAlgebra.mkAlgHom ℂ 𝔤)
    (Set.range (TensorAlgebra.ι ℂ (M := 𝔤)))
  rw [h1] at h2
  have h_map_top : Subalgebra.map (UniversalEnvelopingAlgebra.mkAlgHom ℂ 𝔤) ⊤ = ⊤ := by
    rw [eq_top_iff]; intro x _; obtain ⟨a, rfl⟩ := surj x; exact ⟨a, trivial, rfl⟩
  rw [h_map_top] at h2
  have h_range : (UniversalEnvelopingAlgebra.mkAlgHom ℂ 𝔤) '' Set.range (TensorAlgebra.ι ℂ) =
      Set.range (⇑(UniversalEnvelopingAlgebra.ι ℂ) : 𝔤 → _) := by
    ext x; simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩; exact ⟨g, by simp [UniversalEnvelopingAlgebra.ι_apply]⟩
    · rintro ⟨g, rfl⟩; exact ⟨_, ⟨g, rfl⟩, by simp [UniversalEnvelopingAlgebra.ι_apply]⟩
  rw [h_range] at h2; exact h2.symm

def gkmoduleSubScalar
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (φ : GKModuleHom M M) (c : ℂ) : GKModuleHom M M where
  toLinearMap := φ.toLinearMap - c • LinearMap.id
  lie_comm := by
    intro X v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [φ.lie_comm, lie_sub, lie_smul]
  group_comm := by
    intro k v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [φ.group_comm, map_sub, map_smul]

lemma no_inv_fd_subspace_of_all_bij
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : V →ₗ[ℂ] V)
    (hbij : ∀ c : ℂ, Function.Bijective (φ - (c • LinearMap.id : V →ₗ[ℂ] V)))
    (W : Submodule ℂ V) (hW : W ≠ ⊥) (hfin : FiniteDimensional ℂ W)
    (hinv : ∀ w ∈ W, φ w ∈ W) : False := by
  have hWnt : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let φ_W : Module.End ℂ W := φ.restrict hinv
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue φ_W
  obtain ⟨⟨w, hw⟩, hwev⟩ := hμ.exists_hasEigenvector
  have hw0 : w ≠ 0 := by intro h; exact hwev.2 (Subtype.ext h)
  have heq : φ w = μ • w := by
    have h1 := hwev.apply_eq_smul
    have h2 : (φ_W ⟨w, hw⟩ : V) = φ w := by simp [φ_W, LinearMap.restrict_apply]
    rw [h1] at h2; simpa using h2.symm
  have hker : (φ - (μ • LinearMap.id : V →ₗ[ℂ] V)) w = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, heq, sub_self]
  exact hw0 ((hbij μ).1 (hker.trans (map_zero _).symm))

theorem resolvent_vectors_linearIndependent
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (φ : V →ₗ[ℂ] V)
    (hbij : ∀ c : ℂ, Function.Bijective (φ - (c • LinearMap.id : V →ₗ[ℂ] V)))
    (v : V) (hv : v ≠ 0) :
    LinearIndependent ℂ (fun c : ℂ =>
      (LinearEquiv.ofBijective (φ - (c • LinearMap.id : V →ₗ[ℂ] V)) (hbij c)).symm v) := by
  set R : ℂ → V := fun c =>
    (LinearEquiv.ofBijective (φ - (c • LinearMap.id : V →ₗ[ℂ] V)) (hbij c)).symm v

  have hRI : ∀ i a₀ : ℂ,
      (φ - (a₀ • LinearMap.id : V →ₗ[ℂ] V)) (R i) = v + (i - a₀) • R i := by
    intro i a₀
    have h1 : (φ - (i • LinearMap.id : V →ₗ[ℂ] V)) (R i) = v :=
      LinearEquiv.apply_ofBijective_symm_apply _ _
    have h2 : (φ - (a₀ • LinearMap.id : V →ₗ[ℂ] V)) =
               (φ - (i • LinearMap.id : V →ₗ[ℂ] V)) +
                 ((i - a₀) • LinearMap.id : V →ₗ[ℂ] V) := by
      ext x; simp [LinearMap.sub_apply, LinearMap.smul_apply, sub_smul]
    rw [h2, LinearMap.add_apply, h1, LinearMap.smul_apply, LinearMap.id_apply]

  have hR_ne : ∀ i, R i ≠ 0 := by
    intro i hi; have h := hRI i i
    rw [hi, map_zero, sub_self, zero_smul, add_zero] at h; exact hv h.symm
  rw [linearIndependent_iff']
  intro s

  induction s using Finset.strongInduction with
  | H s ih =>
    intro g hsum i hi

    have h0 : (φ - (i • LinearMap.id : V →ₗ[ℂ] V)) (∑ j ∈ s, g j • R j) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h0
    simp_rw [LinearMap.map_smul, hRI] at h0

    have happ : (∑ j ∈ s, g j) • v +
        ∑ j ∈ s.erase i, (g j * (j - i)) • R j = 0 := by
      convert h0 using 1
      simp_rw [smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul]
      congr 1
      simp_rw [smul_comm (g _) ((_ : ℂ) - i), ← mul_smul]
      rw [← Finset.sum_erase_add _ _ hi]
      simp [sub_self]
      congr 1; ext j; ring

    by_cases hD : ∑ j ∈ s, g j = 0
    ·
      have h_er : ∑ j ∈ s.erase i, (g j * (j - i)) • R j = 0 := by
        rwa [hD, zero_smul, zero_add] at happ
      have h_coeff : ∀ j ∈ s.erase i, g j * (j - i) = 0 :=
        ih _ (Finset.erase_ssubset hi) _ h_er
      have h_gj : ∀ j ∈ s.erase i, g j = 0 := fun j hj =>
        (mul_eq_zero.mp (h_coeff j hj)).resolve_right
          (sub_ne_zero.mpr (Finset.ne_of_mem_erase hj))
      have : ∑ j ∈ s.erase i, g j = 0 :=
        Finset.sum_eq_zero (fun j hj => h_gj j hj)
      rwa [← Finset.sum_erase_add _ _ hi, this, zero_add] at hD
    ·
      exfalso
      set W : Submodule ℂ V := Submodule.span ℂ (R '' ↑s)

      have hv_in : v ∈ W := by
        have hv_eq : v = (∑ j ∈ s, g j)⁻¹ •
            (-(∑ j ∈ s.erase i, (g j * (j - i)) • R j)) := by
          have := eq_neg_of_add_eq_zero_left happ
          rw [← this, inv_smul_smul₀ hD]
        rw [hv_eq]; apply W.smul_mem; apply W.neg_mem
        exact Submodule.sum_mem _ fun j hj =>
          W.smul_mem _ (Submodule.subset_span
            ⟨j, Finset.mem_coe.mpr (Finset.erase_subset _ _ hj), rfl⟩)

      have hinv : ∀ w ∈ W, φ w ∈ W := by
        intro w hw
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨j, hj, rfl⟩
          have := hRI j 0; simp at this; rw [this]
          exact W.add_mem hv_in
            (W.smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩))
        · simp [map_zero, W.zero_mem]
        · intro x y _ _ hx hy; rw [map_add]; exact W.add_mem hx hy
        · intro c x _ hx; rw [LinearMap.map_smul]; exact W.smul_mem c hx

      have hW_ne : W ≠ ⊥ := by
        intro h
        have : R i ∈ (⊥ : Submodule ℂ V) :=
          h ▸ Submodule.subset_span ⟨i, hi, rfl⟩
        simp at this; exact hR_ne i this

      have hW_fd : FiniteDimensional ℂ W :=
        FiniteDimensional.span_of_finite ℂ (Set.Finite.image R s.finite_toSet)
      exact no_inv_fd_subspace_of_all_bij φ hbij W hW_ne hW_fd hinv

theorem gkmodule_endo_has_eigenvalue
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    [Nontrivial V] [FiniteDimensional ℂ 𝔤]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (φ : GKModuleHom M M) :
    ∃ c : ℂ, ¬ Function.Injective (gkmoduleSubScalar M φ c).toLinearMap := by

  by_contra h_all_inj
  push Not at h_all_inj

  have h_all_bij : ∀ c : ℂ,
      Function.Bijective (gkmoduleSubScalar M φ c).toLinearMap := by
    intro c
    have h_zb := schur_gkmodule_zero_or_bijective M hirr (gkmoduleSubScalar M φ c)
    rcases h_zb with h_zero | h_bij
    ·
      exfalso
      have h_not_inj : ¬ Function.Injective (0 : V →ₗ[ℂ] V) := by
        intro hinj
        obtain ⟨a, b, hab⟩ := exists_pair_ne V
        exact hab (hinj (by simp))
      exact h_not_inj (h_zero ▸ h_all_inj c)
    · exact h_bij

  obtain ⟨v, hv⟩ := exists_ne (0 : V)

  have h_bij_lm : ∀ c : ℂ,
      Function.Bijective (φ.toLinearMap - (c • LinearMap.id : V →ₗ[ℂ] V)) := by
    intro c
    exact h_all_bij c

  have hli := resolvent_vectors_linearIndependent φ.toLinearMap h_bij_lm v hv

  have h1 := hli.cardinal_lift_le_rank

  have hcount : Module.rank ℂ V ≤ Cardinal.aleph0 :=
    dixmier_countable_dim_gkmodule M hirr

  have h2 : Cardinal.lift.{0} (Module.rank ℂ V) ≤ Cardinal.aleph0 := by
    rwa [Cardinal.lift_le_aleph0]

  have h3 : Cardinal.lift.{_, 0} (Cardinal.mk ℂ) ≤ Cardinal.aleph0 := le_trans h1 h2

  rw [Cardinal.mk_complex, Cardinal.lift_continuum] at h3
  exact absurd h3 (not_le.mpr Cardinal.aleph0_lt_continuum)

theorem schur_gkmodule
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    [Nontrivial V] [FiniteDimensional ℂ 𝔤]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (φ : GKModuleHom M M) :
    ∃ c : ℂ, ∀ v : V, φ.toLinearMap v = c • v := by

  obtain ⟨c, hc⟩ := gkmodule_endo_has_eigenvalue M hirr φ

  set ψ := gkmoduleSubScalar M φ c with hψ_def

  have h_zb := schur_gkmodule_zero_or_bijective M hirr ψ

  have hψ_zero : ψ.toLinearMap = 0 := by
    rcases h_zb with h | h
    · exact h
    · exact absurd h.1 hc

  use c
  intro v

  have hv : ψ.toLinearMap v = 0 := by
    simp only [hψ_zero, LinearMap.zero_apply]

  have key : ψ.toLinearMap v = φ.toLinearMap v - c • v := rfl

  rw [key] at hv

  exact sub_eq_zero.mp hv

noncomputable def ueaAction (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V] :
    UniversalEnvelopingAlgebra ℂ 𝔤 →ₐ[ℂ] Module.End ℂ V :=
  UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ 𝔤 V)

lemma ueaAction_ι {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V] (X : 𝔤) :
    ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X) = LieModule.toEnd ℂ 𝔤 V X :=
  congr_fun (UniversalEnvelopingAlgebra.ι_comp_lift ℂ (LieModule.toEnd ℂ 𝔤 V)) X

lemma center_ueaAction_lie_comm {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤))
    (X : 𝔤) (v : V) :
    (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) (⁅X, v⁆) =
    ⁅X, (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) v⁆ := by
  rw [← LieModule.toEnd_apply_apply ℂ 𝔤 V X v]
  rw [← LieModule.toEnd_apply_apply ℂ 𝔤 V X]
  rw [← ueaAction_ι X]

  have key : (↑z : UniversalEnvelopingAlgebra ℂ 𝔤) * (UniversalEnvelopingAlgebra.ι ℂ X) =
    (UniversalEnvelopingAlgebra.ι ℂ X) * (↑z : UniversalEnvelopingAlgebra ℂ 𝔤) := by
    have hz := z.prop
    simp only [Subalgebra.mem_center_iff] at hz
    exact (hz _).symm
  show ((ueaAction 𝔤 V ↑z)) ((ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X)) v) =
    ((ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X))) ((ueaAction 𝔤 V ↑z) v)

  have lhs : (ueaAction 𝔤 V ↑z) ((ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X)) v) =
    (ueaAction 𝔤 V (↑z * UniversalEnvelopingAlgebra.ι ℂ X)) v := by
    change ((ueaAction 𝔤 V ↑z) * (ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X))) v =
      (ueaAction 𝔤 V (↑z * UniversalEnvelopingAlgebra.ι ℂ X)) v
    rw [← map_mul]
  have rhs : (ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X)) ((ueaAction 𝔤 V ↑z) v) =
    (ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X * ↑z)) v := by
    change ((ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X)) * (ueaAction 𝔤 V ↑z)) v =
      (ueaAction 𝔤 V (UniversalEnvelopingAlgebra.ι ℂ X * ↑z)) v
    rw [← map_mul]
  rw [lhs, rhs, key]

theorem infinitesimal_character_exists
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    [Nontrivial V] [FiniteDimensional ℂ 𝔤]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hK_center : ∀ (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤))
      (k : K) (v : V),
      (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) (M.σ k v) =
      M.σ k ((ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) v)) :
    ∃ χ : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤) →ₐ[ℂ] ℂ,
      ∀ (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) (v : V),
        (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) v = χ z • v := by

  classical

  have scalar_exists : ∀ z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤),
      ∃ c : ℂ, ∀ v : V, (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) v = c • v := by
    intro z

    have hlie : ∀ (X : 𝔤) (v : V),
        (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) ⁅X, v⁆ =
        ⁅X, (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) v⁆ :=
      center_ueaAction_lie_comm z
    have hgrp : ∀ (k : K) (v : V),
        (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) (M.σ k v) =
        M.σ k ((ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) v) :=
      hK_center z
    let φ : GKModuleHom M M := {
      toLinearMap := (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤)
      lie_comm := hlie
      group_comm := hgrp
    }
    exact schur_gkmodule M hirr φ

  let χ_fun : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤) → ℂ :=
    fun z => (scalar_exists z).choose
  have χ_spec : ∀ (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) (v : V),
      (ueaAction 𝔤 V) (z : UniversalEnvelopingAlgebra ℂ 𝔤) v = χ_fun z • v :=
    fun z => (scalar_exists z).choose_spec

  have hV_nontrivial : ∃ v₀ : V, v₀ ≠ 0 := exists_ne 0
  obtain ⟨v₀, hv₀⟩ := hV_nontrivial
  have scalar_unique : ∀ (c₁ c₂ : ℂ), (∀ v : V, c₁ • v = c₂ • v) → c₁ = c₂ := by
    intro c₁ c₂ h
    have := h v₀
    rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero, or_iff_left hv₀] at this
  have χ_mul : ∀ z₁ z₂ : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤),
      χ_fun (z₁ * z₂) = χ_fun z₁ * χ_fun z₂ := by
    intro z₁ z₂
    apply scalar_unique
    intro v
    rw [← χ_spec (z₁ * z₂) v]
    show (ueaAction 𝔤 V) ((↑(z₁ * z₂) : UniversalEnvelopingAlgebra ℂ 𝔤)) v = _
    rw [MulMemClass.coe_mul, map_mul]
    simp only [Module.End.mul_apply, χ_spec z₁, χ_spec z₂, smul_smul]
  have χ_add : ∀ z₁ z₂ : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤),
      χ_fun (z₁ + z₂) = χ_fun z₁ + χ_fun z₂ := by
    intro z₁ z₂
    apply scalar_unique
    intro v
    rw [← χ_spec (z₁ + z₂) v]
    show (ueaAction 𝔤 V) ((↑(z₁ + z₂) : UniversalEnvelopingAlgebra ℂ 𝔤)) v = _
    rw [AddMemClass.coe_add, map_add]
    simp only [LinearMap.add_apply, χ_spec z₁, χ_spec z₂, add_smul]
  have χ_one : χ_fun 1 = 1 := by
    apply scalar_unique
    intro v
    rw [← χ_spec 1 v]
    show (ueaAction 𝔤 V) ((↑(1 : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) :
      UniversalEnvelopingAlgebra ℂ 𝔤)) v = _
    simp [OneMemClass.coe_one, map_one, one_smul]

  have χ_zero : χ_fun 0 = 0 := by
    apply scalar_unique
    intro v
    rw [← χ_spec 0 v]
    show (ueaAction 𝔤 V) ((↑(0 : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) :
      UniversalEnvelopingAlgebra ℂ 𝔤)) v = _
    simp [ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply, zero_smul]
  have χ_smul : ∀ (c : ℂ) (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)),
      χ_fun (c • z) = c * χ_fun z := by
    intro c z
    apply scalar_unique
    intro v
    rw [← χ_spec (c • z) v]
    show (ueaAction 𝔤 V) ((↑(c • z) : UniversalEnvelopingAlgebra ℂ 𝔤)) v = _
    rw [Subalgebra.coe_smul, map_smul]
    simp only [LinearMap.smul_apply, χ_spec z, smul_smul]

  refine ⟨{
    toFun := χ_fun
    map_one' := χ_one
    map_mul' := χ_mul
    map_zero' := χ_zero
    map_add' := χ_add
    commutes' := ?_ }, χ_spec⟩
  intro c

  apply scalar_unique
  intro v
  rw [← χ_spec (algebraMap ℂ _ c) v]
  show (ueaAction 𝔤 V) ((↑(algebraMap ℂ (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) c) :
    UniversalEnvelopingAlgebra ℂ 𝔤)) v = _
  simp [Algebra.algebraMap_eq_smul_one, map_smul, map_one, LinearMap.smul_apply]

theorem intertwiner_additive_on_kfinite
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ)
    (_hT : ∀ (g : G) (w : G₁.Ŵ),
      T (@ContinuousRep.toMonoidHom G _ _ G₁.Ŵ
          G₁.instNACG.toAddCommGroup G₁.instIPS.toNormedSpace.toModule
          G₁.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₁.π g w) =
        @ContinuousRep.toMonoidHom G _ _ G₂.Ŵ
          G₂.instNACG.toAddCommGroup G₂.instIPS.toNormedSpace.toModule
          G₂.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₂.π g (T w))
    (hT_add : ∀ (x y : G₁.Ŵ),
      T (@HAdd.hAdd G₁.Ŵ G₁.Ŵ G₁.Ŵ
          (@instHAdd G₁.Ŵ G₁.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd) x y) =
        @HAdd.hAdd G₂.Ŵ G₂.Ŵ G₂.Ŵ
          (@instHAdd G₂.Ŵ G₂.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd) (T x) (T y))
    (v w : V₁) :
    T (@HAdd.hAdd G₁.Ŵ G₁.Ŵ G₁.Ŵ
        (@instHAdd G₁.Ŵ G₁.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd)
        (G₁.ι v) (G₁.ι w)) =
      @HAdd.hAdd G₂.Ŵ G₂.Ŵ G₂.Ŵ
        (@instHAdd G₂.Ŵ G₂.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd)
        (T (G₁.ι v)) (T (G₁.ι w)) := by
  exact hT_add (G₁.ι v) (G₁.ι w)

theorem intertwiner_smul_on_kfinite
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ)
    (_hT : ∀ (g : G) (w : G₁.Ŵ),
      T (@ContinuousRep.toMonoidHom G _ _ G₁.Ŵ
          G₁.instNACG.toAddCommGroup G₁.instIPS.toNormedSpace.toModule
          G₁.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₁.π g w) =
        @ContinuousRep.toMonoidHom G _ _ G₂.Ŵ
          G₂.instNACG.toAddCommGroup G₂.instIPS.toNormedSpace.toModule
          G₂.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₂.π g (T w))
    (hT_smul : ∀ (c : ℂ) (x : G₁.Ŵ),
      T (@HSMul.hSMul ℂ G₁.Ŵ G₁.Ŵ
          (@instHSMul ℂ G₁.Ŵ G₁.instIPS.toNormedSpace.toModule.toSMul) c x) =
        @HSMul.hSMul ℂ G₂.Ŵ G₂.Ŵ
          (@instHSMul ℂ G₂.Ŵ G₂.instIPS.toNormedSpace.toModule.toSMul) c (T x))
    (c : ℂ) (v : V₁) :
    T (@HSMul.hSMul ℂ G₁.Ŵ G₁.Ŵ
        (@instHSMul ℂ G₁.Ŵ G₁.instIPS.toNormedSpace.toModule.toSMul)
        c (G₁.ι v)) =
      @HSMul.hSMul ℂ G₂.Ŵ G₂.Ŵ
        (@instHSMul ℂ G₂.Ŵ G₂.instIPS.toNormedSpace.toModule.toSMul)
        c (T (G₁.ι v)) := by
  exact hT_smul c (G₁.ι v)

theorem intertwiner_preserves_kfinite
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ)
    (hT : ∀ (g : G) (w : G₁.Ŵ),
      T (@ContinuousRep.toMonoidHom G _ _ G₁.Ŵ
          G₁.instNACG.toAddCommGroup G₁.instIPS.toNormedSpace.toModule
          G₁.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₁.π g w) =
        @ContinuousRep.toMonoidHom G _ _ G₂.Ŵ
          G₂.instNACG.toAddCommGroup G₂.instIPS.toNormedSpace.toModule
          G₂.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₂.π g (T w))
    (hT_add : ∀ (x y : G₁.Ŵ),
      T (@HAdd.hAdd G₁.Ŵ G₁.Ŵ G₁.Ŵ
          (@instHAdd G₁.Ŵ G₁.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd) x y) =
        @HAdd.hAdd G₂.Ŵ G₂.Ŵ G₂.Ŵ
          (@instHAdd G₂.Ŵ G₂.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd) (T x) (T y))
    (hT_smul : ∀ (c : ℂ) (x : G₁.Ŵ),
      T (@HSMul.hSMul ℂ G₁.Ŵ G₁.Ŵ
          (@instHSMul ℂ G₁.Ŵ G₁.instIPS.toNormedSpace.toModule.toSMul) c x) =
        @HSMul.hSMul ℂ G₂.Ŵ G₂.Ŵ
          (@instHSMul ℂ G₂.Ŵ G₂.instIPS.toNormedSpace.toModule.toSMul) c (T x))
    (v : V₁) : T (G₁.ι v) ∈ Set.range G₂.ι := by

  letI : NormedAddCommGroup G₁.Ŵ := G₁.instNACG
  letI : NormedAddCommGroup G₂.Ŵ := G₂.instNACG
  letI : InnerProductSpace ℂ G₁.Ŵ := G₁.instIPS
  letI : InnerProductSpace ℂ G₂.Ŵ := G₂.instIPS

  rw [G₂.kfin_image]

  rw [SetLike.mem_coe, ContinuousRep.mem_kFiniteSubspace]
  unfold ContinuousRep.IsKFinite

  have hT_add' : ∀ (a b : V₁),
      T (G₁.ι a + G₁.ι b) = T (G₁.ι a) + T (G₁.ι b) := by
    intro a b; exact intertwiner_additive_on_kfinite M₁ M₂ G₁ G₂ T hT hT_add a b
  have hT_smul' : ∀ (c : ℂ) (a : V₁),
      T (c • G₁.ι a) = c • T (G₁.ι a) := by
    intro c a; exact intertwiner_smul_on_kfinite M₁ M₂ G₁ G₂ T hT hT_smul c a

  let S : V₁ →ₗ[ℂ] G₂.Ŵ := {
    toFun := fun w => T (G₁.ι w)
    map_add' := fun a b => by
      show T (G₁.ι (a + b)) = T (G₁.ι a) + T (G₁.ι b)
      rw [map_add]
      exact hT_add' a b
    map_smul' := fun c a => by
      show T (G₁.ι (c • a)) = c • T (G₁.ι a)
      rw [map_smul]
      exact hT_smul' c a
  }

  have hfd_V : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun k : K => (M₁.σ k) v))) :=
    M₁.locallyFinite v

  suffices h : Submodule.span ℂ
      (Set.range (fun k : ↥(MonoidHom.range K_sub) =>
        (G₂.π.toMonoidHom ↑k) (T (G₁.ι v)))) ≤
      Submodule.map S (Submodule.span ℂ (Set.range (fun k : K => (M₁.σ k) v))) by
    exact Module.Finite.of_injective
      (Submodule.inclusion h) (Submodule.inclusion_injective h)

  apply Submodule.span_le.mpr
  intro w hw
  obtain ⟨⟨g, hg⟩, rfl⟩ := hw

  obtain ⟨k', rfl⟩ := hg

  show (G₂.π.toMonoidHom (K_sub k')) (T (G₁.ι v)) ∈
    ↑(Submodule.map S (Submodule.span ℂ (Set.range (fun k : K => (M₁.σ k) v))))

  rw [← hT (K_sub k') (G₁.ι v)]

  rw [← G₁.K_compat k' v]

  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k', rfl⟩)

theorem intertwiner_restriction_linear
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ)
    (hT : ∀ (g : G) (w : G₁.Ŵ),
      T (@ContinuousRep.toMonoidHom G _ _ G₁.Ŵ
          G₁.instNACG.toAddCommGroup G₁.instIPS.toNormedSpace.toModule
          G₁.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₁.π g w) =
        @ContinuousRep.toMonoidHom G _ _ G₂.Ŵ
          G₂.instNACG.toAddCommGroup G₂.instIPS.toNormedSpace.toModule
          G₂.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₂.π g (T w))
    (hT_add : ∀ (x y : G₁.Ŵ),
      T (@HAdd.hAdd G₁.Ŵ G₁.Ŵ G₁.Ŵ
          (@instHAdd G₁.Ŵ G₁.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd) x y) =
        @HAdd.hAdd G₂.Ŵ G₂.Ŵ G₂.Ŵ
          (@instHAdd G₂.Ŵ G₂.instNACG.toAddCommGroup.toAddGroup.toAddMonoid.toAdd) (T x) (T y))
    (hT_smul : ∀ (c : ℂ) (x : G₁.Ŵ),
      T (@HSMul.hSMul ℂ G₁.Ŵ G₁.Ŵ
          (@instHSMul ℂ G₁.Ŵ G₁.instIPS.toNormedSpace.toModule.toSMul) c x) =
        @HSMul.hSMul ℂ G₂.Ŵ G₂.Ŵ
          (@instHSMul ℂ G₂.Ŵ G₂.instIPS.toNormedSpace.toModule.toSMul) c (T x))
    (φ_fun : V₁ → V₂)
    (hφ_fun : ∀ v, T (G₁.ι v) = G₂.ι (φ_fun v)) :
    ∃ (φ_lin : V₁ →ₗ[ℂ] V₂), ∀ v, φ_lin v = φ_fun v := by

  letI : AddCommGroup G₁.Ŵ := G₁.instNACG.toAddCommGroup
  letI : Module ℂ G₁.Ŵ := G₁.instIPS.toNormedSpace.toModule
  letI : AddCommGroup G₂.Ŵ := G₂.instNACG.toAddCommGroup
  letI : Module ℂ G₂.Ŵ := G₂.instIPS.toNormedSpace.toModule

  have h_add : ∀ v w : V₁, φ_fun (v + w) = φ_fun v + φ_fun w := by
    intro v w
    apply G₂.ι_injective
    rw [← hφ_fun (v + w), map_add, map_add]
    rw [← hφ_fun v, ← hφ_fun w]
    exact intertwiner_additive_on_kfinite M₁ M₂ G₁ G₂ T hT hT_add v w

  have h_smul : ∀ (c : ℂ) (v : V₁), φ_fun (c • v) = c • φ_fun v := by
    intro c v
    apply G₂.ι_injective
    rw [← hφ_fun (c • v), map_smul, map_smul]
    rw [← hφ_fun v]
    exact intertwiner_smul_on_kfinite M₁ M₂ G₁ G₂ T hT hT_smul c v
  exact ⟨⟨⟨φ_fun, h_add⟩, h_smul⟩, fun _ => rfl⟩

theorem intertwiner_restriction_lie_comm
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ)
    (_hT : ∀ (g : G) (w : G₁.Ŵ),
      T (@ContinuousRep.toMonoidHom G _ _ G₁.Ŵ
          G₁.instNACG.toAddCommGroup G₁.instIPS.toNormedSpace.toModule
          G₁.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₁.π g w) =
        @ContinuousRep.toMonoidHom G _ _ G₂.Ŵ
          G₂.instNACG.toAddCommGroup G₂.instIPS.toNormedSpace.toModule
          G₂.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          G₂.π g (T w))

    (hT_lie : ∀ (X : 𝔤) (w : G₁.Ŵ),
      T (G₁.lie_action_Ŵ X w) = G₂.lie_action_Ŵ X (T w))
    (φ_lin : V₁ →ₗ[ℂ] V₂)
    (hφ : ∀ v, T (G₁.ι v) = G₂.ι (φ_lin v)) :
    ∀ (X : 𝔤) (v : V₁), φ_lin ⁅X, v⁆ = ⁅X, φ_lin v⁆ := by
  intro X v
  apply G₂.ι_injective

  rw [← hφ ⁅X, v⁆]

  rw [G₁.lie_compat_ι X v]

  rw [hT_lie X (G₁.ι v)]

  rw [hφ v]

  rw [← G₂.lie_compat_ι X (φ_lin v)]

@[reducible] def Globalization.topologicalSpaceŴ
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (Gl : Globalization G K_sub M) : TopologicalSpace Gl.Ŵ :=
  Gl.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[reducible] def Globalization.addCommGroupŴ
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (Gl : Globalization G K_sub M) : AddCommGroup Gl.Ŵ :=
  Gl.instNACG.toAddCommGroup

@[reducible] def Globalization.moduleŴ
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (Gl : Globalization G K_sub M) :
    @Module ℂ Gl.Ŵ _ Gl.addCommGroupŴ.toAddCommMonoid :=
  Gl.instIPS.toNormedSpace.toModule

@[reducible] def Globalization.πApp
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (Gl : Globalization G K_sub M) (g : G) (w : Gl.Ŵ) : Gl.Ŵ :=
  @ContinuousRep.toMonoidHom G _ _ Gl.Ŵ
    Gl.instNACG.toAddCommGroup Gl.instIPS.toNormedSpace.toModule
    Gl.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Gl.π g w

def IsGIntertwiner
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    {M₁ : GKModule 𝔤 K 𝔨 Ad V₁} {M₂ : GKModule 𝔤 K 𝔨 Ad V₂}
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ) : Prop :=
  ∀ (g : G) (w : G₁.Ŵ), T (G₁.πApp g w) = G₂.πApp g (T w)

def IsGlobAdditive
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    {M₁ : GKModule 𝔤 K 𝔨 Ad V₁} {M₂ : GKModule 𝔤 K 𝔨 Ad V₂}
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ) : Prop :=
  ∀ (x y : G₁.Ŵ),
    T (@HAdd.hAdd G₁.Ŵ G₁.Ŵ G₁.Ŵ
        (@instHAdd G₁.Ŵ G₁.addCommGroupŴ.toAddGroup.toAddMonoid.toAdd) x y) =
      @HAdd.hAdd G₂.Ŵ G₂.Ŵ G₂.Ŵ
        (@instHAdd G₂.Ŵ G₂.addCommGroupŴ.toAddGroup.toAddMonoid.toAdd) (T x) (T y)

def IsGlobLinear
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    {M₁ : GKModule 𝔤 K 𝔨 Ad V₁} {M₂ : GKModule 𝔤 K 𝔨 Ad V₂}
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ) : Prop :=
  ∀ (c : ℂ) (x : G₁.Ŵ),
    T (@HSMul.hSMul ℂ G₁.Ŵ G₁.Ŵ (@instHSMul ℂ G₁.Ŵ G₁.moduleŴ.toSMul) c x) =
      @HSMul.hSMul ℂ G₂.Ŵ G₂.Ŵ (@instHSMul ℂ G₂.Ŵ G₂.moduleŴ.toSMul) c (T x)

end
