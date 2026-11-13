/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Affine
import Atlas.Buildings.code.BNPair.ParabolicDefs

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace CompactSubgroups

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A bornology on a group $G$: a family of bounded sets closed under taking subsets, finite
unions, singletons, group products, and inversion. -/
structure GroupBornology (G : Type*) [Group G] where
  isBounded : Set G → Prop
  subset_bounded : ∀ {S T : Set G}, isBounded T → S ⊆ T → isBounded S
  singleton_bounded : ∀ (g : G), isBounded {g}
  union_bounded : ∀ {S T : Set G}, isBounded S → isBounded T → isBounded (S ∪ T)
  product_bounded : ∀ {S T : Set G}, isBounded S → isBounded T →
    isBounded (setMul S T)
  inv_bounded : ∀ {S : Set G}, isBounded S →
    isBounded ((fun x => x⁻¹) '' S)

/-- A subgroup $H$ is bounded in the bornology $\mathrm{born}$ if its underlying set is bounded. -/
def IsBoundedSubgroup (born : GroupBornology G) (H : Subgroup G) : Prop :=
  born.isBounded (H : Set G)

/-- A subgroup $K$ is *maximal bounded* if it is bounded and no strictly larger subgroup is bounded. -/
def IsMaximalBounded (born : GroupBornology G) (K : Subgroup G) : Prop :=
  IsBoundedSubgroup born K ∧ ∀ H : Subgroup G, K < H → ¬IsBoundedSubgroup born H

/-- $S$ is BN-pair bounded: covered by finitely many Bruhat cells of $\mathrm{bp}$. -/
def BNPairBoundedPredicate (bp : BNPair G M) (S : Set G) : Prop :=
  ∃ (ws : Finset M.Group), S ⊆ ⋃ w ∈ ws, bp.bruhatCell w

/-- Product of BN-pair bounded sets is BN-pair bounded (uses finiteness of Bruhat cell products). -/
theorem bnpair_product_bounded {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (S T : Set G) (hS : BNPairBoundedPredicate bp S) (hT : BNPairBoundedPredicate bp T) :
    BNPairBoundedPredicate bp (setMul S T) := by
  classical
  obtain ⟨ws₁, hS⟩ := hS
  obtain ⟨ws₂, hT⟩ := hT


  let allCells : Finset M.Group :=
    ws₁.biUnion (fun w => ws₂.biUnion (fun w' => (bd.cell_mul_finite w w').choose))
  refine ⟨allCells, ?_⟩
  intro g hg

  obtain ⟨x, hxS, y, hyT, rfl⟩ := hg

  have hx_union := hS hxS
  rw [Set.mem_iUnion₂] at hx_union
  obtain ⟨w, hw_mem, hx_cell⟩ := hx_union

  have hy_union := hT hyT
  rw [Set.mem_iUnion₂] at hy_union
  obtain ⟨w', hw'_mem, hy_cell⟩ := hy_union

  have hxy_in_prod : x * y ∈ setMul (bp.bruhatCell w) (bp.bruhatCell w') :=
    ⟨x, hx_cell, y, hy_cell, rfl⟩

  have h_finite := (bd.cell_mul_finite w w').choose_spec
  have hxy_in_cells := h_finite hxy_in_prod

  rw [Set.mem_iUnion₂] at hxy_in_cells ⊢
  obtain ⟨u, hu_mem, hxy_u⟩ := hxy_in_cells
  exact ⟨u, Finset.mem_biUnion.mpr ⟨w, hw_mem, Finset.mem_biUnion.mpr ⟨w', hw'_mem, hu_mem⟩⟩, hxy_u⟩

/-- The inverse of a BN-pair bounded set is BN-pair bounded. -/
theorem bnpair_inv_bounded {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (S : Set G) (hS : BNPairBoundedPredicate bp S) :
    BNPairBoundedPredicate bp ((fun x => x⁻¹) '' S) := by
  classical
  obtain ⟨ws, hS⟩ := hS

  refine ⟨ws.image (·⁻¹), ?_⟩
  intro g hg
  obtain ⟨x, hxS, rfl⟩ := hg
  have hx_union := hS hxS
  rw [Set.mem_iUnion₂] at hx_union ⊢
  obtain ⟨w, hw_mem, hx_cell⟩ := hx_union
  exact ⟨w⁻¹, Finset.mem_image.mpr ⟨w, hw_mem, rfl⟩, bd.cell_inv w x hx_cell⟩

/-- Every element of $G$ lies in some Bruhat cell of the BN-pair. -/
theorem bnpair_element_in_cell {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (bd : BNPair.BruhatProperties bp) (g : G) :
    ∃ w : M.Group, g ∈ bp.bruhatCell w :=
  bd.cell_cover g

/-- Union of two BN-pair bounded sets is BN-pair bounded. -/
theorem bnpair_union_bounded {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M)
    (S T : Set G) (hS : BNPairBoundedPredicate bp S) (hT : BNPairBoundedPredicate bp T) :
    BNPairBoundedPredicate bp (S ∪ T) := by
  classical
  obtain ⟨ws₁, hS⟩ := hS
  obtain ⟨ws₂, hT⟩ := hT
  exact ⟨ws₁ ∪ ws₂, Set.union_subset
    (hS.trans (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_left)))
    (hT.trans (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_right)))⟩



/-- For infinite Weyl group, the whole group $G = P_{\mathrm{Univ}}$ is not BN-pair bounded. -/
theorem whole_group_not_bounded
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp) :
    ¬ BNPairBoundedPredicate bp (bp.standardParabolic Set.univ) := by

  intro ⟨ws, h_cover⟩

  have h_parab_top : bp.parabolicSubgroupW Set.univ = ⊤ := by
    unfold BNPair.parabolicSubgroupW
    rw [Set.image_univ]
    exact M.toCoxeterSystem.subgroup_closure_range_simple


  have h_all_in_ws : ∀ w : M.Group, w ∈ ws := by
    intro w
    obtain ⟨g, hg⟩ := BNPair.exists_mem_bruhatCell bp w
    have hg_in_parab : g ∈ bp.standardParabolic Set.univ :=
      Set.mem_iUnion₂.mpr ⟨w, h_parab_top ▸ Subgroup.mem_top w, hg⟩
    have hg_in_union := h_cover hg_in_parab
    obtain ⟨w', hw'_mem, hg_cell'⟩ := Set.mem_iUnion₂.mp hg_in_union
    have : w = w' := bd.cell_disjoint w w' ⟨g, hg, hg_cell'⟩
    rwa [this]

  haveI : Fintype M.Group := ⟨ws, h_all_in_ws⟩
  exact not_finite M.Group

/-- Standard parabolic subgroups are monotone in the simple-root subset. -/
lemma standardParabolic_mono
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (S₁ S₂ : Set B_idx) (h : S₁ ⊆ S₂) :
    bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
  intro g hg
  obtain ⟨w, hw, hg_cell⟩ := Set.mem_iUnion₂.mp hg
  refine Set.mem_iUnion₂.mpr ⟨w, ?_, hg_cell⟩
  exact Subgroup.closure_mono (Set.image_mono h) hw



/-- Carrier of a conjugated subgroup $gKg^{-1}$ lies inside the set product $\{g\} \cdot K \cdot \{g^{-1}\}$. -/
lemma subgroup_map_conj_carrier_subset_setMul
    {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    (K.map (MulAut.conj g).toMonoidHom : Set G) ⊆
      setMul (setMul {g} (K : Set G)) {g⁻¹} := by
  intro x hx
  simp only [SetLike.mem_coe, Subgroup.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  show g * k * g⁻¹ ∈ _
  exact ⟨g * k, ⟨g, Set.mem_singleton g, k, hk, rfl⟩, g⁻¹, Set.mem_singleton g⁻¹, rfl⟩

/-- Conjugation preserves boundedness of subgroups. -/
lemma isBoundedSubgroup_map_conj
    {G : Type*} [Group G]
    (born : GroupBornology G)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) (g : G) :
    IsBoundedSubgroup born (K.map (MulAut.conj g).toMonoidHom) := by
  apply born.subset_bounded
    (born.product_bounded (born.product_bounded (born.singleton_bounded g) hK)
      (born.singleton_bounded g⁻¹))
  exact subgroup_map_conj_carrier_subset_setMul g K

/-- Conjugation preserves maximal-boundedness of subgroups. -/
lemma isMaximalBounded_map_conj
    {G : Type*} [Group G]
    (born : GroupBornology G)
    (K : Subgroup G) (hK : IsMaximalBounded born K) (g : G) :
    IsMaximalBounded born (K.map (MulAut.conj g).toMonoidHom) := by
  constructor
  ·
    exact isBoundedSubgroup_map_conj born K hK.1 g
  ·
    intro H hH_lt hH_bounded

    set H' := H.map (MulAut.conj g⁻¹).toMonoidHom with hH'_def

    have hH'_bounded : IsBoundedSubgroup born H' :=
      isBoundedSubgroup_map_conj born H hH_bounded g⁻¹

    have hK_lt_H' : K < H' := by
      have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom :=
        (MulAut.conj g⁻¹).injective


      have h_recover : (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
        rw [Subgroup.map_map]
        convert Subgroup.map_id K using 2
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [← h_recover]
      constructor
      · exact Subgroup.map_mono (le_of_lt hH_lt)
      · intro heq
        have h2 := (Subgroup.map_le_map_iff_of_injective hinj).mp heq.ge
        exact absurd (le_antisymm h2 (le_of_lt hH_lt)) (ne_of_lt hH_lt).symm

    exact hK.2 H' hK_lt_H' hH'_bounded


/-- Carrier set of $gKg^{-1}$ equals the conjugate image $\{gkg^{-1} : k \in K\}$. -/
lemma subgroup_map_conj_coe {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    (K.map (MulAut.conj g).toMonoidHom : Set G) =
    (fun x => g * x * g⁻¹) '' (K : Set G) := by
  ext x; simp [MulAut.conj_apply]












/-- Each coatom standard parabolic $P_{\mathrm{Univ} \setminus \{s_0\}}$ is a maximal bounded
subgroup containing $B$. -/
theorem standardParabolic_maximal_bounded
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (s₀ : B_idx)

    (h_fin_parabolic : ∃ ws : Finset M.Group,
      ∀ w, w ∈ bp.parabolicSubgroupW (Set.univ \ {s₀}) → w ∈ ws)

    (h_not_bounded_top : ¬ BNPairBoundedPredicate bp (bp.standardParabolic Set.univ))


    (h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
      bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂) :
    ∃ K : Subgroup G, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) ∧
      IsMaximalBounded born K ∧ bp.B ≤ K := by

  have h_sg := BNPair.parabolicsAreSubgroups bp bd (Set.univ \ {s₀})
  let K : Subgroup G := {
    carrier := bp.standardParabolic (Set.univ \ {s₀})
    mul_mem' := fun ha hb => h_sg.2.1 _ _ ha hb
    one_mem' := h_sg.1
    inv_mem' := fun ha => h_sg.2.2 _ ha
  }
  refine ⟨K, rfl, ⟨?_, ?_⟩, ?_⟩
  ·
    rw [IsBoundedSubgroup, hborn]
    obtain ⟨ws, hws⟩ := h_fin_parabolic
    exact ⟨ws, fun g hg => by
      obtain ⟨w, hw, hg_cell⟩ := Set.mem_iUnion₂.mp hg
      exact Set.mem_biUnion (hws w hw) hg_cell⟩
  ·
    intro H hKH
    rw [IsBoundedSubgroup, hborn]
    intro ⟨ws, hH_cover⟩

    have hB_le_K : bp.B ≤ K := by
      intro b hb
      show b ∈ bp.standardParabolic (Set.univ \ {s₀})
      exact Set.mem_biUnion
        (bp.parabolicSubgroupW (Set.univ \ {s₀})).one_mem
        ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩, bp.π.map_one,
          by simp [mul_one]⟩
    have hB_le_H : bp.B ≤ H := le_trans hB_le_K (le_of_lt hKH)

    obtain ⟨S'', hH_eq⟩ := bd.subgroup_over_B_eq_parabolic H hB_le_H

    suffices h_eq : S'' = Set.univ by
      rw [h_eq] at hH_eq
      exact h_not_bounded_top ⟨ws, hH_eq ▸ hH_cover⟩

    have h_sub : bp.standardParabolic (Set.univ \ {s₀}) ⊆ bp.standardParabolic S'' := by
      intro g hg
      have : g ∈ (H : Set G) := (le_of_lt hKH) hg
      rwa [hH_eq] at this

    have h_S_sub : Set.univ \ {s₀} ⊆ S'' := h_parabolic_reflects_order _ _ h_sub

    have h_S_ne : Set.univ \ {s₀} ≠ S'' := by
      intro heq
      have : (K : Set G) = (H : Set G) := by
        show bp.standardParabolic _ = _
        rw [heq, ← hH_eq]
      exact ne_of_lt hKH (SetLike.ext' this)

    ext x
    constructor
    · intro _; exact Set.mem_univ x
    · intro _
      by_cases hx : x = s₀
      ·
        subst hx
        by_contra hc
        apply h_S_ne
        ext y
        constructor
        · intro hy; exact h_S_sub hy
        · intro hy
          exact ⟨Set.mem_univ y, fun hy' => hc (Set.mem_singleton_iff.mp hy' ▸ hy)⟩
      · exact h_S_sub ⟨Set.mem_univ x, fun h => hx (Set.mem_singleton_iff.mp h)⟩
  ·
    intro b hb
    show b ∈ bp.standardParabolic (Set.univ \ {s₀})
    exact Set.mem_biUnion
      (bp.parabolicSubgroupW (Set.univ \ {s₀})).one_mem
      ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩, bp.π.map_one,
        by simp [mul_one]⟩




/-- $s_0$ is a *special vertex* (with respect to a linear-part homomorphism) if every element in
the image of the linear part has a preimage in the standard parabolic $W_{\mathrm{Univ} \setminus \{s_0\}}$. -/
structure IsSpecialVertex (M : CoxeterMatrix B_idx)
    (linearPart : M.Group →* M.Group) (s₀ : B_idx) : Prop where
  surjective : ∀ wbar : M.Group, wbar ∈ Set.range linearPart →
    ∃ w : M.Group,
      w ∈ (Subgroup.closure
        (M.toCoxeterSystem.simple '' (Set.univ \ {s₀})) : Set M.Group) ∧
      linearPart w = wbar

/-- A *good maximal bounded subgroup*: a maximal bounded subgroup $K$ containing $B$ that equals
a coatom standard parabolic $P_{\mathrm{Univ} \setminus \{\mathrm{vertex}\}}$ where the vertex is special. -/
structure GoodMaximalBounded (bp : BNPair G M) (born : GroupBornology G)
    (linearPart : M.Group →* M.Group) where
  K : Subgroup G
  maximal_bounded : IsMaximalBounded born K
  contains_B : bp.B ≤ K
  vertex : B_idx
  eq_parabolic : (K : Set G) = bp.standardParabolic (Set.univ \ {vertex})
  is_special : IsSpecialVertex M linearPart vertex

/-- For an indecomposable affine Coxeter matrix admitting a special vertex, there exists a good
maximal bounded subgroup. -/
theorem good_maximal_bounded_exists
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (linearPart : M.Group →* M.Group)
    (hM_indec : M.IsIndecomposable) (hM_aff : M.IsAffine)

    (h_special : ∃ s₀ : B_idx, IsSpecialVertex M linearPart s₀)


    (h_fin_parabolic : ∀ s₀ : B_idx, ∃ ws : Finset M.Group,
      ∀ w, w ∈ bp.parabolicSubgroupW (Set.univ \ {s₀}) → w ∈ ws)
    (h_not_bounded_top : ¬ BNPairBoundedPredicate bp (bp.standardParabolic Set.univ))
    (h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
      bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂) :
    ∃ (s₀ : B_idx) (K : Subgroup G),

      (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) ∧

      IsMaximalBounded born K ∧

      bp.B ≤ K ∧

      IsSpecialVertex M linearPart s₀ := by

  obtain ⟨s₀, hs₀⟩ := h_special

  obtain ⟨K, hK_eq, hK_max, hK_B⟩ :=
    standardParabolic_maximal_bounded bp bd born hborn s₀
      (h_fin_parabolic s₀) h_not_bounded_top h_parabolic_reflects_order

  exact ⟨s₀, K, hK_eq, hK_max, hK_B, hs₀⟩



end CompactSubgroups
