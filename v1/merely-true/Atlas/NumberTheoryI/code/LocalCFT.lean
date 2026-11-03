/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped RestrictedProduct
open Filter Set

section RestrictedProduct

variable {ι : Type*} (X : ι → Type*) (U : (i : ι) → Set (X i))

abbrev restrictedProduct : Type _ := Πʳ i, [X i, U i]

variable [∀ i, TopologicalSpace (X i)]

end RestrictedProduct

section DirectSystem

variable {I : Type*} [Preorder I]


abbrev IsDirectSystem (F : I → Type*) (f : ⦃i j : I⦄ → i ≤ j → F i → F j) : Prop :=
  DirectedSystem F f

end DirectSystem

noncomputable section

open scoped Pointwise

section MaximalExtensions

variable (K Ksep : Type*) [Field K] [Field Ksep] [Algebra K Ksep]

def IsFiniteAbelianExtension (L : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K L ∧ IsGalois K L ∧
    ∀ (σ τ : L ≃ₐ[K] L), σ * τ = τ * σ

def IsFiniteUnramifiedExtension (L : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K L ∧ Algebra.FormallyUnramified K L

def maximalAbelianExtension : IntermediateField K Ksep :=
  ⨆ (L : IntermediateField K Ksep) (_ : IsFiniteAbelianExtension K Ksep L), L

end MaximalExtensions

structure LocalArtinReciprocity where
  Kx : Type*
  [kx_comm_group : CommGroup Kx]
  [kx_topological_space : TopologicalSpace Kx]
  [kx_topological_group : IsTopologicalGroup Kx]
  I : Type*
  [ext_preorder : PartialOrder I]
  GalLK : I → Type*
  [gal_comm_group : ∀ i, CommGroup (GalLK i)]
  [gal_fintype : ∀ i, Fintype (GalLK i)]
  normGroup : I → Subgroup Kx
  artinMap : ∀ i, Kx →* GalLK i
  artinMap_surjective : ∀ i, Function.Surjective (artinMap i)
  artinMap_ker : ∀ i, (artinMap i).ker = normGroup i
  restrictMap : ∀ {i j : I}, i ≤ j → GalLK j →* GalLK i
  artinMap_compat : ∀ {i j : I} (h : i ≤ j) (x : Kx),
    restrictMap h (artinMap j x) = artinMap i x
  normGroup_antitone : ∀ {i j : I}, i ≤ j → normGroup j ≤ normGroup i
  normGroup_reflects_le : ∀ {i j : I}, normGroup j ≤ normGroup i → i ≤ j
  exists_sup : ∀ (i j : I), ∃ k : I, i ≤ k ∧ j ≤ k ∧
    normGroup k = normGroup i ⊓ normGroup j
  exists_inf : ∀ (i j : I), ∃ k : I, k ≤ i ∧ k ≤ j ∧
    normGroup k = normGroup i ⊔ normGroup j
  normGroup_isClosed : ∀ i, IsClosed (normGroup i : Set Kx)
  galois_subext : ∀ (i : I) (S : Subgroup (GalLK i)),
    ∃ j : I, j ≤ i ∧ normGroup j = S.comap (artinMap i)
  J : Type*
  unramifiedEmb : J → I
  frobElt : ∀ (j : J), GalLK (unramifiedEmb j)
  IsUniformizer : Kx → Prop
  artinMap_uniformizer_eq_frob : ∀ (j : J) (π : Kx),
    IsUniformizer π → artinMap (unramifiedEmb j) π = frobElt j

attribute [instance] LocalArtinReciprocity.kx_comm_group
  LocalArtinReciprocity.kx_topological_space
  LocalArtinReciprocity.kx_topological_group
  LocalArtinReciprocity.ext_preorder
  LocalArtinReciprocity.gal_comm_group
  LocalArtinReciprocity.gal_fintype

namespace LocalArtinReciprocity

variable (D : LocalArtinReciprocity)

def IsNormGroup (H : Subgroup D.Kx) : Prop :=
  ∃ i : D.I, D.normGroup i = H


def normSubgroup (i : D.I) : Subgroup D.Kx := D.normGroup i

def artinMap_quotient_equiv (i : D.I) :
    D.Kx ⧸ (D.normGroup i) ≃* D.GalLK i := by
  rw [← D.artinMap_ker i]
  exact QuotientGroup.quotientKerEquivOfSurjective _ (D.artinMap_surjective i)

theorem ext_eq_of_le_of_normGroup_eq {i j : D.I}
    (hij : i ≤ j) (hn : D.normGroup i = D.normGroup j) : i = j := by

  have hle : D.normGroup i ≤ D.normGroup j := le_of_eq hn

  have hji : j ≤ i := D.normGroup_reflects_le hle

  exact le_antisymm hij hji

theorem normGroup_injective {i j : D.I} (h : D.normGroup i = D.normGroup j) : i = j := by

  obtain ⟨k, hik, hjk, hk⟩ := D.exists_sup i j


  have hi_eq_k : D.normGroup i = D.normGroup k := by rw [hk, h, inf_idem]

  have hj_eq_k : D.normGroup j = D.normGroup k := by rw [hk, h, inf_idem]

  have hieqk : i = k := D.ext_eq_of_le_of_normGroup_eq hik hi_eq_k

  have hjeqk : j = k := D.ext_eq_of_le_of_normGroup_eq hjk hj_eq_k

  rw [hieqk, hjeqk]

theorem normGroup_map_injective : Function.Injective D.normGroup :=
  fun _ _ h => D.normGroup_injective h

theorem normGroup_finiteIndex (i : D.I) : (D.normGroup i).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  exact Finite.of_equiv _ (D.artinMap_quotient_equiv i).symm.toEquiv

theorem closed_finiteIndex_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] (H : Subgroup G) [H.FiniteIndex]
    (hclosed : IsClosed (H : Set G)) : IsOpen (H : Set G) :=
  H.isOpen_of_isClosed_of_finiteIndex hclosed

theorem normGroup_isOpen (i : D.I) : IsOpen (D.normGroup i : Set D.Kx) := by
  haveI := D.normGroup_finiteIndex i
  exact closed_finiteIndex_isOpen (D.normGroup i) (D.normGroup_isClosed i)

class LocalExistenceTheorem (D : LocalArtinReciprocity) : Prop where
  open_finiteIndex_isNormGroup :
    ∀ (H : Subgroup D.Kx), H.FiniteIndex → IsOpen (H : Set D.Kx) → D.IsNormGroup H

theorem restrictMap_jointly_injective
    {j k m : D.I} (hj : j ≤ m) (hk : k ≤ m)
    (hnorm : D.normGroup m = D.normGroup j ⊓ D.normGroup k)
    (g₁ g₂ : D.GalLK m)
    (hgj : D.restrictMap hj g₁ = D.restrictMap hj g₂)
    (hgk : D.restrictMap hk g₁ = D.restrictMap hk g₂) :
    g₁ = g₂ := by

  obtain ⟨x₁, rfl⟩ := D.artinMap_surjective m g₁
  obtain ⟨x₂, rfl⟩ := D.artinMap_surjective m g₂

  have hdiff_j : D.artinMap j (x₁ * x₂⁻¹) = 1 := by
    rw [map_mul, map_inv, ← D.artinMap_compat hj, ← D.artinMap_compat hj]
    rw [hgj, mul_inv_cancel]
  have hdiff_k : D.artinMap k (x₁ * x₂⁻¹) = 1 := by
    rw [map_mul, map_inv, ← D.artinMap_compat hk, ← D.artinMap_compat hk]
    rw [hgk, mul_inv_cancel]

  have hm_mem : x₁ * x₂⁻¹ ∈ D.normGroup m := by
    rw [hnorm]
    exact Subgroup.mem_inf.mpr
      ⟨(D.artinMap_ker j) ▸ MonoidHom.mem_ker.mpr hdiff_j,
       (D.artinMap_ker k) ▸ MonoidHom.mem_ker.mpr hdiff_k⟩

  have : D.artinMap m (x₁ * x₂⁻¹) = 1 := by
    rw [← D.artinMap_ker m] at hm_mem; exact MonoidHom.mem_ker.mp hm_mem
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

theorem artinMap_unique
    (θ₁ θ₂ : ∀ i, D.Kx →* D.GalLK i)
    (_h_surj₁ : ∀ i, Function.Surjective (θ₁ i))
    (_h_surj₂ : ∀ i, Function.Surjective (θ₂ i))
    (h_ker₁ : ∀ i, (θ₁ i).ker = D.normGroup i)
    (h_ker₂ : ∀ i, (θ₂ i).ker = D.normGroup i)
    (h_frob₁ : ∀ (j : D.J) (π : D.Kx),
      D.IsUniformizer π → θ₁ (D.unramifiedEmb j) π = D.frobElt j)
    (h_frob₂ : ∀ (j : D.J) (π : D.Kx),
      D.IsUniformizer π → θ₂ (D.unramifiedEmb j) π = D.frobElt j)
    (h_compat₁ : ∀ {i j : D.I} (h : i ≤ j) (x : D.Kx),
      D.restrictMap h (θ₁ j x) = θ₁ i x)
    (h_compat₂ : ∀ {i j : D.I} (h : i ≤ j) (x : D.Kx),
      D.restrictMap h (θ₂ j x) = θ₂ i x)
    (uniformizers_generate : Subgroup.closure {π : D.Kx | D.IsUniformizer π} = ⊤)
    (_h_LET : ∀ (U : Subgroup D.Kx), U.FiniteIndex → IsOpen (U : Set D.Kx) →
      ∃ i, D.normGroup i = U)
    (kab_eq_kpi_kunr : ∀ (π : D.Kx), D.IsUniformizer π → ∀ (i : D.I),
      ∃ (j : D.J) (k : D.I), π ∈ D.normGroup k ∧
        ∃ (m : D.I), D.unramifiedEmb j ≤ m ∧ k ≤ m ∧ i ≤ m ∧
          D.normGroup m = D.normGroup (D.unramifiedEmb j) ⊓ D.normGroup k) :
    ∀ i (x : D.Kx), θ₁ i x = θ₂ i x := by

  suffices h_unif : ∀ (π : D.Kx), D.IsUniformizer π → ∀ (i : D.I),
      θ₁ i π = θ₂ i π by


    intro i x
    have hx : x ∈ Subgroup.closure {π : D.Kx | D.IsUniformizer π} := by
      rw [uniformizers_generate]; exact Subgroup.mem_top x
    have key : ∀ y ∈ Subgroup.closure {π : D.Kx | D.IsUniformizer π},
        θ₁ i y = θ₂ i y := by
      apply Subgroup.closure_induction
      · intro y hy; exact h_unif y hy i
      · simp [map_one]
      · intro a b _ _ ha hb; simp only [map_mul]; rw [ha, hb]
      · intro a _ ha; simp only [map_inv]; rw [ha]
    exact key x hx

  intro π hπ i

  obtain ⟨j, k, hπk, m, hjm, hkm, him, hnorm_m⟩ := kab_eq_kpi_kunr π hπ i

  have h_agree_m : θ₁ m π = θ₂ m π := by

    have hj_eq : D.restrictMap hjm (θ₁ m π) = D.restrictMap hjm (θ₂ m π) := by
      rw [h_compat₁ hjm, h_compat₂ hjm, h_frob₁ j π hπ, h_frob₂ j π hπ]

    have hk_eq : D.restrictMap hkm (θ₁ m π) = D.restrictMap hkm (θ₂ m π) := by
      rw [h_compat₁ hkm, h_compat₂ hkm]
      have h1 : π ∈ (θ₁ k).ker := h_ker₁ k ▸ hπk
      have h2 : π ∈ (θ₂ k).ker := h_ker₂ k ▸ hπk
      rw [MonoidHom.mem_ker.mp h1, MonoidHom.mem_ker.mp h2]

    exact D.restrictMap_jointly_injective hjm hkm hnorm_m _ _ hj_eq hk_eq

  calc θ₁ i π = D.restrictMap him (θ₁ m π) := (h_compat₁ him π).symm
    _ = D.restrictMap him (θ₂ m π) := by rw [h_agree_m]
    _ = θ₂ i π := h_compat₂ him π

end LocalArtinReciprocity

structure LocalArtinMap extends LocalArtinReciprocity where
  GalAb : Type*
  [galAb_group : CommGroup GalAb]
  [galAb_topological_space : TopologicalSpace GalAb]
  [galAb_topological_group : IsTopologicalGroup GalAb]
  [galAb_compact : CompactSpace GalAb]
  [gal_topological_space : ∀ i, TopologicalSpace (GalLK i)]
  [gal_discrete_topology : ∀ i, DiscreteTopology (GalLK i)]
  artinHom : Kx →* GalAb
  artinHom_continuous : Continuous artinHom
  proj : ∀ i, GalAb →* GalLK i
  proj_continuous : ∀ i, Continuous (proj i)
  artinMap_eq_proj : ∀ i x, artinMap i x = proj i (artinHom x)
  proj_jointly_injective : ∀ g : GalAb, (∀ i, proj i g = 1) → g = 1
  proj_compat : ∀ {i j : I} (h : i ≤ j) (g : GalAb),
    restrictMap h (proj j g) = proj i g
  proj_nhd_basis : ∀ (g : GalAb) (U : Set GalAb), U ∈ nhds g →
    ∃ i, {h : GalAb | proj i h = proj i g} ⊆ U

attribute [instance] LocalArtinMap.galAb_group
  LocalArtinMap.galAb_topological_space
  LocalArtinMap.galAb_topological_group
  LocalArtinMap.galAb_compact
  LocalArtinMap.gal_topological_space
  LocalArtinMap.gal_discrete_topology

namespace LocalArtinMap

variable (M : LocalArtinMap)

def ProfiniteCompletionKx : Subgroup (∀ i, M.Kx ⧸ M.normGroup i) where
  carrier := {x | ∀ ⦃i j : M.I⦄ (h : i ≤ j),
    QuotientGroup.map (M.normGroup j) (M.normGroup i) (MonoidHom.id M.Kx)
      (M.toLocalArtinReciprocity.normGroup_antitone h) (x j) = x i}
  one_mem' := fun i j h => by simp [map_one]
  mul_mem' := fun ha hb i j h => by simp [map_mul, ha h, hb h]
  inv_mem' := fun ha i j h => by simp [map_inv, ha h]

def InvLimGalLK : Subgroup (∀ i, M.GalLK i) where
  carrier := {x | ∀ ⦃i j : M.I⦄ (h : i ≤ j), M.restrictMap h (x j) = x i}
  one_mem' := fun i j h => by simp [map_one]
  mul_mem' := fun ha hb i j h => by simp [map_mul, ha h, hb h]
  inv_mem' := fun ha i j h => by simp [map_inv, ha h]

def profiniteCompletionIso : M.ProfiniteCompletionKx ≃* M.InvLimGalLK := by

  let fwd_i (i : M.I) : M.Kx ⧸ M.normGroup i →* M.GalLK i :=
    QuotientGroup.lift (M.normGroup i) (M.artinMap i) (by rw [M.artinMap_ker i])

  have fwd_mk : ∀ (i : M.I) (x : M.Kx),
      fwd_i i (QuotientGroup.mk x) = M.artinMap i x :=
    fun i x => QuotientGroup.lift_mk _ _ _

  have naturality : ∀ ⦃i j : M.I⦄ (h : i ≤ j) (x : M.Kx),
      M.restrictMap h (fwd_i j (QuotientGroup.mk x)) =
        fwd_i i (QuotientGroup.map (M.normGroup j) (M.normGroup i) (MonoidHom.id M.Kx)
          (M.toLocalArtinReciprocity.normGroup_antitone h) (QuotientGroup.mk x)) := by
    intro i j h x
    rw [fwd_mk, QuotientGroup.map_mk, MonoidHom.id_apply, fwd_mk]
    exact M.artinMap_compat h x

  let piHom : (∀ i, M.Kx ⧸ M.normGroup i) →* (∀ i, M.GalLK i) :=
    Pi.monoidHom fun i => (fwd_i i).comp (Pi.evalMonoidHom _ i)

  have piHom_maps : ∀ q ∈ M.ProfiniteCompletionKx,
      piHom q ∈ M.InvLimGalLK := by
    intro q hq i j h
    show M.restrictMap h (fwd_i j (q j)) = fwd_i i (q i)
    rw [← hq h]
    exact QuotientGroup.induction_on (q j) (fun x => naturality h x)

  have fwd_bij : ∀ i, Function.Bijective (fwd_i i) := fun i => by
    constructor
    ·
      intro a b hab
      obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hab
      rw [QuotientGroup.eq, ← M.artinMap_ker i]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    · intro σ
      obtain ⟨x, hx⟩ := M.artinMap_surjective i σ
      exact ⟨QuotientGroup.mk x, by rw [fwd_mk]; exact hx⟩

  let fwdSubHom : M.ProfiniteCompletionKx →* M.InvLimGalLK :=
    (piHom.comp M.ProfiniteCompletionKx.subtype).codRestrict M.InvLimGalLK
      (fun ⟨q, hq⟩ => piHom_maps q hq)

  refine MulEquiv.ofBijective fwdSubHom ⟨?_, ?_⟩
  ·
    intro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ heq
    ext i
    have : fwd_i i (q₁ i) = fwd_i i (q₂ i) :=
      congr_arg (fun x => (x : ∀ i, M.GalLK i) i) (Subtype.ext_iff.mp heq)
    exact (fwd_bij i).1 this
  ·

    intro ⟨σ, hσ⟩
    choose q hq_eq using fun i => (fwd_bij i).2 (σ i)
    refine ⟨⟨q, fun i j h => ?_⟩, Subtype.ext (funext hq_eq)⟩


    apply (fwd_bij i).1


    have step1 : fwd_i i (QuotientGroup.map (M.normGroup j) (M.normGroup i) (MonoidHom.id M.Kx)
        (M.toLocalArtinReciprocity.normGroup_antitone h) (q j)) =
        M.restrictMap h (fwd_i j (q j)) :=
      QuotientGroup.induction_on (q j) fun x => by
        rw [fwd_mk, QuotientGroup.map_mk, MonoidHom.id_apply, fwd_mk]
        exact (M.artinMap_compat h x).symm
    rw [step1, hq_eq j, hq_eq i]
    exact hσ h

lemma proj_fiber_mem_nhds (i : M.I) (g : M.GalAb) :
    {h : M.GalAb | M.proj i h = M.proj i g} ∈ nhds g := by
  have : {h : M.GalAb | M.proj i h = M.proj i g} = (M.proj i) ⁻¹' {M.proj i g} := by
    ext; simp
  rw [this]
  exact (M.proj_continuous i).isOpen_preimage _ (isOpen_discrete _) |>.mem_nhds rfl

theorem proj_fiber_isOpen (i : M.I) (c : M.GalLK i) :
    IsOpen {g : M.GalAb | M.proj i g = c} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  rw [← hg]
  exact M.proj_fiber_mem_nhds i g

theorem proj_fiber_isClosed (i : M.I) (c : M.GalLK i) :
    IsClosed {g : M.GalAb | M.proj i g = c} := by
  rw [isOpen_compl_iff.symm]
  have : {g : M.GalAb | M.proj i g = c}ᶜ = ⋃ (d : M.GalLK i) (_ : d ≠ c),
      {g : M.GalAb | M.proj i g = d} := by
    ext g
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h; exact ⟨M.proj i g, h, rfl⟩
    · rintro ⟨d, hd, hg⟩; rw [hg]; exact hd
  rw [this]
  exact isOpen_iUnion fun d => isOpen_iUnion fun _ => M.proj_fiber_isOpen i d

def galAbIso : M.GalAb ≃* M.InvLimGalLK := by

  let fwd : M.GalAb →* (i : M.I) → M.GalLK i :=
    Pi.monoidHom fun i => M.proj i
  have fwd_mem : ∀ g, fwd g ∈ M.InvLimGalLK :=
    fun g i j h => M.proj_compat h g
  let fwdSub : M.GalAb →* M.InvLimGalLK :=
    fwd.codRestrict M.InvLimGalLK fwd_mem
  refine MulEquiv.ofBijective fwdSub ⟨?inj, ?surj⟩
  case inj =>
    intro a b hab
    have h := Subtype.ext_iff.mp hab
    have : ∀ i, M.proj i (a * b⁻¹) = 1 := fun i => by
      have hi : (fwd a) i = (fwd b) i := congr_fun h i
      simp [fwd, Pi.monoidHom, MonoidHom.coe_mk] at hi
      rw [map_mul, map_inv, hi, mul_inv_cancel]
    have := M.proj_jointly_injective (a * b⁻¹) this
    rw [mul_inv_eq_one] at this
    exact this
  case surj =>
    intro ⟨σ, hσ⟩

    by_cases hI : IsEmpty M.I
    ·
      exact ⟨1, Subtype.ext (funext (fun i => hI.elim i))⟩
    ·
      rw [not_isEmpty_iff] at hI
      haveI : Nonempty M.I := hI


      let F : M.I → Set M.GalAb := fun i => {g | M.proj i g = σ i}

      have hne : ∀ i, (F i).Nonempty := fun i => by
        obtain ⟨x, hx⟩ := M.artinMap_surjective i (σ i)
        exact ⟨M.artinHom x, by simp [F, ← M.artinMap_eq_proj, hx]⟩

      have hcl : ∀ i, IsClosed (F i) := fun i => M.proj_fiber_isClosed i (σ i)

      have hcpt : ∀ i, IsCompact (F i) := fun i =>
        (hcl i).isCompact

      have hdir : Directed (· ⊇ ·) F := by
        intro i j
        obtain ⟨k, hki, hkj, _⟩ := M.toLocalArtinReciprocity.exists_sup i j
        refine ⟨k, fun g hg => ?_, fun g hg => ?_⟩
        · simp only [F, Set.mem_setOf_eq] at hg ⊢
          rw [← M.proj_compat hki g, hg, hσ hki]
        · simp only [F, Set.mem_setOf_eq] at hg ⊢
          rw [← M.proj_compat hkj g, hg, hσ hkj]

      have hint := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        F hdir hne hcpt hcl
      obtain ⟨g, hg⟩ := hint
      simp only [Set.mem_iInter, Set.mem_setOf_eq, F] at hg
      exact ⟨g, Subtype.ext (funext hg)⟩

def profiniteCompletionMulEquiv : M.ProfiniteCompletionKx ≃* M.GalAb :=
  M.profiniteCompletionIso.trans M.galAbIso.symm

end LocalArtinMap

end
