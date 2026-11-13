/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.ApplicationsToGroups
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Topology Filter

section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation by $g$ as a self-homeomorphism of a topological group $G$. -/
def conjHomeomorph (g : G) : G ≃ₜ G where
  toEquiv := MulAut.conj g
  continuous_toFun := by
    show Continuous (fun x => g * x * g⁻¹)
    exact (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := by
    show Continuous (fun x => g⁻¹ * x * g)
    exact (continuous_const.mul continuous_id).mul continuous_const

/-- The conjugate $gSg^{-1}$ of a subset $S \subseteq G$. -/
def conjSet (g : G) (S : Set G) : Set G :=
  (conjHomeomorph g) '' S

/-- $gSg^{-1}$ as the image of $S$ under the conjugation map. -/
lemma conjSet_eq (g : G) (S : Set G) :
    conjSet g S = (fun x => g * x * g⁻¹) '' S := rfl

/-- Conjugation preserves compactness. -/
lemma isCompact_conjSet (g : G) (S : Set G) (hS : IsCompact S) :
    IsCompact (conjSet g S) :=
  (conjHomeomorph g).isCompact_image.mpr hS

/-- Conjugation preserves openness. -/
lemma isOpen_conjSet (g : G) (S : Set G) (hS : IsOpen S) :
    IsOpen (conjSet g S) :=
  (conjHomeomorph g).isOpenMap _ hS

/-- Conjugation preserves closedness. -/
lemma isClosed_conjSet (g : G) (S : Set G) (hS : IsClosed S) :
    IsClosed (conjSet g S) :=
  (conjHomeomorph g).isClosedMap _ hS

end Conjugation

section OpenImpliesClosed

end OpenImpliesClosed

section BuildingFixer

/-- The pointwise fixer of a subset $Y \subseteq X$ under a group action:
the set of group elements that fix every point of $Y$. -/
def pointwiseFixer {G : Type*} {X : Type*} (act : G → X → X) (Y : Set X) : Set G :=
  {g : G | ∀ y ∈ Y, act g y = y}

/-- The identity belongs to every pointwise fixer. -/
lemma one_mem_pointwiseFixer {G : Type*} [Group G] {X : Type*}
    (act : G → X → X) (hact_one : ∀ x : X, act 1 x = x) (Y : Set X) :
    (1 : G) ∈ pointwiseFixer act Y :=
  fun y _ => hact_one y

/-- The pointwise fixer is closed under inversion. -/
lemma inv_mem_pointwiseFixer {G : Type*} [Group G] {X : Type*}
    (act : G → X → X)
    (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
    (hact_one : ∀ x : X, act 1 x = x)
    {Y : Set X} {g : G} (hg : g ∈ pointwiseFixer act Y) :
    g⁻¹ ∈ pointwiseFixer act Y := by
  intro y hy
  calc act g⁻¹ y = act g⁻¹ (act g y) := by rw [hg y hy]
    _ = act (g⁻¹ * g) y := by rw [← hact_mul]
    _ = act 1 y := by rw [inv_mul_cancel]
    _ = y := hact_one y

/-- The fixer of a union is the intersection of fixers:
$\mathrm{Fix}(\bigcup_i C_i) = \bigcap_i \mathrm{Fix}(C_i)$. -/
lemma pointwiseFixer_iUnion {G : Type*} {X : Type*} {ι : Type*}
    (act : G → X → X) (C : ι → Set X) :
    pointwiseFixer act (⋃ i, C i) = ⋂ i, pointwiseFixer act (C i) := by
  ext g
  simp only [pointwiseFixer, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro h i y hy; exact h y ⟨i, hy⟩
  · intro h y ⟨i, hy⟩; exact h i y hy

/-- The fixer of a translated set equals the conjugate of the fixer:
$\mathrm{Fix}(h \cdot C_0) = h \,\mathrm{Fix}(C_0)\, h^{-1}$. -/
lemma pointwiseFixer_image_eq_conj {G : Type*} [Group G] {X : Type*}
    (act : G → X → X)
    (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
    (hact_one : ∀ x : X, act 1 x = x)
    (h : G) (C₀ : Set X) :
    pointwiseFixer act (act h '' C₀) =
    (fun b => h * b * h⁻¹) '' (pointwiseFixer act C₀) := by
  ext g
  simp only [pointwiseFixer, Set.mem_setOf_eq, Set.mem_image]
  constructor
  ·
    intro hg
    refine ⟨h⁻¹ * g * h, fun y hy => ?_, by group⟩
    have := hg (act h y) ⟨y, hy, rfl⟩
    rw [show h⁻¹ * g * h = h⁻¹ * (g * h) from by group, hact_mul, hact_mul, this]
    rw [← hact_mul, inv_mul_cancel, hact_one]
  ·
    intro ⟨b, hb, hg_eq⟩
    subst hg_eq
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst hxy
    rw [show h * b * h⁻¹ = h * (b * h⁻¹) from by group, hact_mul, hact_mul]
    rw [← hact_mul h⁻¹ h, inv_mul_cancel, hact_one, hb x hx]

end BuildingFixer

section PointwiseFixer

/-- The pointwise fixer of a finite union of $G$-translates of the base
chamber $C_0$ is both open and compact, given that the Borel subgroup $B$
fixes $C_0$ and is itself compact open. -/
theorem pointwise_fixer_compact_open
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B : Subgroup G)
    (hB_compact : IsCompact (B : Set G))
    (hB_open : IsOpen (B : Set G))

    {X : Type*} (act : G → X → X)
    (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
    (hact_one : ∀ x : X, act 1 x = x)

    (C₀ : Set X)
    (hB_fixer : (B : Set G) = pointwiseFixer act C₀)

    (Y : Set X)


    (IsChamber : Set X → Prop)
    (hY_contains_chamber : ∃ C, IsChamber C ∧ C ⊆ Y)


    {n : ℕ} (hn : 0 < n)
    (chambers : Fin n → Set X)


    (chambers_cover_Y : Y ⊆ ⋃ i, chambers i)


    (fixer_covers_chambers : ∀ g ∈ pointwiseFixer act Y,
        ∀ (i : Fin n) (x : X), x ∈ chambers i → act g x = x)


    (chamber_transit : ∀ i, ∃ h : G, chambers i = act h '' C₀) :
    IsOpen (pointwiseFixer act Y) ∧ IsCompact (pointwiseFixer act Y) := by


  have hY_fixer_eq : pointwiseFixer act Y =
      pointwiseFixer act (⋃ i, chambers i) := by
    ext g; constructor
    · intro hg x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact fixer_covers_chambers g hg i x hi
    · intro hg y hy
      exact hg y (chambers_cover_Y hy)


  choose h_conj h_transit using chamber_transit


  have key : pointwiseFixer act Y =
      ⋂ (i : Fin n), conjSet (h_conj i) (B : Set G) := by
    rw [hY_fixer_eq, pointwiseFixer_iUnion]
    congr 1; ext i
    rw [h_transit i, pointwiseFixer_image_eq_conj act hact_mul hact_one,
        hB_fixer, conjSet_eq]


  rw [key]
  constructor
  ·
    exact isOpen_iInter_of_finite (fun i => isOpen_conjSet (h_conj i) _ hB_open)
  ·
    have hB_closed : IsClosed (B : Set G) := Subgroup.isClosed_of_isOpen B hB_open
    apply IsCompact.of_isClosed_subset
      (isCompact_conjSet (h_conj (⟨0, hn⟩ : Fin n)) _ hB_compact)
    · exact isClosed_iInter (fun i => isClosed_conjSet (h_conj i) _ hB_closed)
    · exact Set.iInter_subset _ (⟨0, hn⟩ : Fin n)

end PointwiseFixer

section ClusterPoint

/-- Any sequence valued in a compact subgroup $B$ has a cluster point in $B$. -/
theorem compact_subgroup_cluster_point
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B : Subgroup G) (hB_compact : IsCompact (B : Set G))
    (u : ℕ → G) (hu : ∀ i, u i ∈ B) :
    ∃ β ∈ (B : Set G), MapClusterPt β atTop u := by
  apply hB_compact.exists_mapClusterPt
  rw [le_principal_iff, mem_map]
  exact univ_mem' hu

/-- A cluster point of $u_n$ has neighbourhoods $V$ which contain $u_i$ for
arbitrarily large $i$. -/
lemma mapClusterPt_frequently_in_nhds
    {G : Type*} [TopologicalSpace G]
    {β : G} {u : ℕ → G} (hβ : MapClusterPt β atTop u)
    {V : Set G} (hV : V ∈ nhds β) (N : ℕ) :
    ∃ i ≥ N, u i ∈ V := by
  have h1 : ∃ᶠ y in map u atTop, y ∈ V := hβ.frequently hV
  rw [frequently_map] at h1
  exact h1.forall_exists_of_atTop N

end ClusterPoint

section FixerCoset

/-- Right-multiplying by an element of the fixer of $Y$ does not change the
action on points of $Y$. -/
lemma act_eq_of_mul_fixer {G : Type*} [Group G] {X : Type*}
    (act : G → X → X)
    (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
    (bⱼ f : G) {Y : Set X} (hf : f ∈ pointwiseFixer act Y)
    {x : X} (hx : x ∈ Y) :
    act (bⱼ * f) x = act bⱼ x := by
  rw [hact_mul, hf x hx]

/-- A coset-of-fixer argument: if $g$ can be written as $b_j f$ with $f$ in
the fixer of each $Y_i$, and the $b_j$ send $Y_i$ into $A_0$, then $g$ sends
the union $\bigcup_i Y_i$ into $A_0$. -/
lemma image_sub_from_fixer_chain {G : Type*} [Group G] {X : Type*}
    (act : G → X → X)
    (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
    {Y : ℕ → Set X} {A₀ : Set X} {b : ℕ → G}
    (hb_maps : ∀ i j, i ≤ j → ∀ x ∈ Y i, act (b j) x ∈ A₀)
    {g : G}
    (hg_coset : ∀ i, ∃ j ≥ i, ∃ f ∈ pointwiseFixer act (Y i), g = b j * f) :
    ∀ x ∈ ⋃ i, Y i, act g x ∈ A₀ := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj, f, hf, hg_eq⟩ := hg_coset i
  rw [hg_eq, act_eq_of_mul_fixer act hact_mul (b j) f hf hi]
  exact hb_maps i j hj x hi

end FixerCoset

section StrongTransitivityTheorem

/-- Core technical lemma for strong transitivity: given a compact-open Borel
$B$ acting on a topological building, an apartment $A'$ exhausted by an
ascending chain $Y_i$ each mapped into the base apartment $A_0$ by elements
$b_i \in B$, one finds a single $g \in B$ with $g \cdot A' = A_0$. -/
theorem maximally_strong_transitivity_core
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

    (B : Subgroup G) (hB_compact : IsCompact (B : Set G)) (hB_open : IsOpen (B : Set G))

    {X : Type*} (act : G → X → X)
    (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
    (hact_one : ∀ x : X, act 1 x = x)

    (A₀ : Set X)
    (C₀ : Set X) (hC₀_sub : C₀ ⊆ A₀)

    (hB_fixer : (B : Set G) = pointwiseFixer act C₀)


    (A' : Set X) (hC₀_in_A' : C₀ ⊆ A')


    (Y : ℕ → Set X)
    (hY_mono : ∀ i, Y i ⊆ Y (i + 1))
    (hC₀_in_Y : C₀ ⊆ Y 0)
    (hY_union : A' = ⋃ i, Y i)


    (A_chain : ℕ → Set X)
    (hY_in_A : ∀ i, Y i ⊆ A_chain i)


    (b : ℕ → G) (hb : ∀ i, b i ∈ B)
    (hb_maps_apt : ∀ i, ∀ x ∈ A_chain i, act (b i) x ∈ A₀)

    (hY_in_Aj : ∀ i j, i ≤ j → Y i ⊆ A_chain j)


    (hF_open : ∀ i, IsOpen (pointwiseFixer act (Y i)))


    (hapt_surj : ∀ g : G, (∀ x ∈ A', act g x ∈ A₀) →
        (fun x => act g x) '' A' = A₀) :
    ∃ g : G, g ∈ (B : Set G) ∧ (fun x => act g x) '' A' = A₀ := by


  have hF_one : ∀ i, (1 : G) ∈ pointwiseFixer act (Y i) :=
    fun i => one_mem_pointwiseFixer act hact_one (Y i)
  have hF_inv : ∀ i x, x ∈ pointwiseFixer act (Y i) → x⁻¹ ∈ pointwiseFixer act (Y i) :=
    fun i x hx => inv_mem_pointwiseFixer act hact_mul hact_one hx

  have hb_maps : ∀ i j, i ≤ j → ∀ x ∈ Y i, act (b j) x ∈ A₀ :=
    fun i j hij x hx => hb_maps_apt j x (hY_in_Aj i j hij hx)


  have hseq : ∀ i, (b 0)⁻¹ * b i ∈ B := fun i => B.mul_mem (B.inv_mem (hb 0)) (hb i)
  obtain ⟨β, hβ_mem, hβ_cluster⟩ := compact_subgroup_cluster_point B hB_compact
    (fun i => (b 0)⁻¹ * b i) hseq


  set g := b 0 * β with hg_def
  have hg_mem : g ∈ (B : Set G) := B.mul_mem (hb 0) hβ_mem


  have hg_coset : ∀ i, ∃ j ≥ i, ∃ f ∈ pointwiseFixer act (Y i), g = b j * f := by
    intro i

    have hU_open : IsOpen ((fun x => β * x) '' (pointwiseFixer act (Y i))) :=
      (Homeomorph.mulLeft β).isOpenMap _ (hF_open i)
    have hU_nhds : (fun x => β * x) '' (pointwiseFixer act (Y i)) ∈ nhds β :=
      hU_open.mem_nhds ⟨1, hF_one i, by simp⟩

    obtain ⟨j, hj, u, hu_mem, hu_eq⟩ :=
      mapClusterPt_frequently_in_nhds hβ_cluster hU_nhds i

    refine ⟨j, hj, u⁻¹, hF_inv i u hu_mem, ?_⟩
    show b 0 * β = b j * u⁻¹
    have h1 : β * u = (b 0)⁻¹ * b j := by exact_mod_cast hu_eq
    have h2 : b 0 * (β * u) = b j := by rw [h1]; group
    calc b 0 * β = b 0 * (β * u) * u⁻¹ := by group
      _ = b j * u⁻¹ := by rw [h2]


  have hg_maps : ∀ x ∈ A', act g x ∈ A₀ := by
    rw [hY_union]
    exact image_sub_from_fixer_chain act hact_mul hb_maps hg_coset


  exact ⟨g, hg_mem, hapt_surj g hg_maps⟩

/-- A bundle of data abstracting a thick building $X$ with a strongly
transitive topological group action: the action and base chamber $C_0
\subseteq A_0$, a compact-open Borel $B$ that fixes $C_0$ pointwise, the
notion of chamber, the maximal apartment system, chamber transitivity, and
exhaustion data for each apartment. -/
structure ThickBuildingData (G : Type*) (X : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] where
  act : G → X → X
  act_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x)
  act_one : ∀ x : X, act 1 x = x
  C₀ : Set X
  A₀ : Set X
  chamber_sub_apt : C₀ ⊆ A₀
  B : Subgroup G
  B_eq_fixer : (B : Set G) = pointwiseFixer act C₀
  B_compact : IsCompact (B : Set G)
  B_open : IsOpen (B : Set G)
  IsChamber : Set X → Prop
  C₀_is_chamber : IsChamber C₀
  maxAptSystem : Set (Set X)
  A₀_in_max : A₀ ∈ maxAptSystem
  maxAptSystem_invariant : ∀ (g : G) (A' : Set X),
    A' ∈ maxAptSystem → (fun x => act g x) '' A' ∈ maxAptSystem
  apt_contains_chamber : ∀ A' ∈ maxAptSystem, ∃ C', IsChamber C' ∧ C' ⊆ A'
  chamber_transitive : ∀ C', IsChamber C' → ∃ h : G,
    (fun x => act h x) '' C₀ = C'
  exhaustion_data : ∀ A' ∈ maxAptSystem, C₀ ⊆ A' →
    ∃ (Y : ℕ → Set X)
      (_ : ∀ i, Y i ⊆ Y (i + 1))
      (_ : C₀ ⊆ Y 0)
      (_ : A' = ⋃ i, Y i)
      (A_chain : ℕ → Set X)
      (_ : ∀ i, Y i ⊆ A_chain i)
      (b : ℕ → G)
      (_ : ∀ i, b i ∈ B)
      (_ : ∀ i, ∀ x ∈ A_chain i, act (b i) x ∈ A₀)
      (_ : ∀ i j, i ≤ j → Y i ⊆ A_chain j)
      (_ : ∀ i, IsOpen (pointwiseFixer act (Y i)))
      (_ : ∀ g : G, (∀ x ∈ A', act g x ∈ A₀) →
          (fun x => act g x) '' A' = A₀),
      True

/-- Maximally strong transitivity (Bourbaki/Tits): the group $G$ acts
transitively on pairs $(C', A')$ where $C'$ is a chamber contained in an
apartment $A'$ of the maximal system — there is $g \in G$ sending the pair
$(C', A')$ to the base pair $(C_0, A_0)$. -/
theorem maximally_strong_transitivity_theorem
    {G : Type*} {X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (Δ : ThickBuildingData G X) :
    ∀ A' ∈ Δ.maxAptSystem, ∀ C', Δ.IsChamber C' → C' ⊆ A' →
      ∃ g : G, (fun x => Δ.act g x) '' C' = Δ.C₀ ∧
              (fun x => Δ.act g x) '' A' = Δ.A₀ := by
  intro A' hA' C' hC'_chamber hC'_sub


  obtain ⟨h, hh_eq⟩ := Δ.chamber_transitive C' hC'_chamber


  set A'' := (fun x => Δ.act h⁻¹ x) '' A' with hA''_def

  have hA''_max : A'' ∈ Δ.maxAptSystem :=
    Δ.maxAptSystem_invariant h⁻¹ A' hA'


  have hC₀_sub_A'' : Δ.C₀ ⊆ A'' := by
    intro c hc
    have hc_in_C' : Δ.act h c ∈ C' := by rw [← hh_eq]; exact ⟨c, hc, rfl⟩
    exact ⟨Δ.act h c, hC'_sub hc_in_C', by show Δ.act h⁻¹ (Δ.act h c) = c; rw [← Δ.act_mul, inv_mul_cancel, Δ.act_one]⟩


  obtain ⟨Y, hY_mono, hC₀_in_Y, hY_union, A_chain, hY_in_A, b, hb, hb_maps,
          hY_in_Aj, hF_open, hapt_surj, _⟩ :=
    Δ.exhaustion_data A'' hA''_max hC₀_sub_A''
  obtain ⟨g₀, hg₀_mem, hg₀_img⟩ := maximally_strong_transitivity_core
    Δ.B Δ.B_compact Δ.B_open Δ.act Δ.act_mul Δ.act_one Δ.A₀ Δ.C₀
    Δ.chamber_sub_apt Δ.B_eq_fixer A'' hC₀_sub_A''
    Y hY_mono hC₀_in_Y hY_union A_chain hY_in_A b hb hb_maps hY_in_Aj
    hF_open hapt_surj


  refine ⟨g₀ * h⁻¹, ?_, ?_⟩
  ·


    ext x; simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩

      simp only [Δ.act_mul]

      have hy_in_C' := hy

      obtain ⟨c, hc, rfl⟩ : ∃ c ∈ Δ.C₀, Δ.act h c = y := by
        rw [← hh_eq] at hy_in_C'; exact hy_in_C'

      have hinv : Δ.act h⁻¹ (Δ.act h c) = c := by
        rw [← Δ.act_mul, inv_mul_cancel, Δ.act_one]
      rw [hinv]

      have hg₀_fixes : g₀ ∈ pointwiseFixer Δ.act Δ.C₀ := by
        rw [← Δ.B_eq_fixer]; exact hg₀_mem
      rw [hg₀_fixes c hc]; exact hc
    · intro hx


      have hg₀_fixes : g₀ ∈ pointwiseFixer Δ.act Δ.C₀ := by
        rw [← Δ.B_eq_fixer]; exact hg₀_mem

      refine ⟨Δ.act h x, ?_, ?_⟩
      · rw [← hh_eq]; exact ⟨x, hx, rfl⟩
      · simp only [Δ.act_mul]
        have hinv : Δ.act h⁻¹ (Δ.act h x) = x := by
          rw [← Δ.act_mul, inv_mul_cancel, Δ.act_one]
        rw [hinv, hg₀_fixes x hx]
  ·

    rw [show (fun x => Δ.act (g₀ * h⁻¹) x) '' A' =
        (fun x => Δ.act g₀ x) '' ((fun x => Δ.act h⁻¹ x) '' A') from by
      ext x; simp only [Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Δ.act h⁻¹ y, ⟨y, hy, rfl⟩, by simp only [Δ.act_mul]⟩
      · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by simp only [Δ.act_mul]⟩]
    exact hg₀_img

end StrongTransitivityTheorem

section AscendingChain

/-- For an ascending chain of apartments $A_i$ each sent to $A_0$ by $b_i$,
the composite $(b_i)^{-1} b_j$ sends $A_j$ back to $A_i$. -/
theorem ascending_chain_fixer_property
    {G : Type*} [Group G]
    {Apt : Type*} (act : G → Apt → Apt)
    (hact_mul : ∀ g₁ g₂ a, act (g₁ * g₂) a = act g₁ (act g₂ a))
    (hact_one : ∀ a, act 1 a = a)
    (A₀ : Apt) (A : ℕ → Apt) (b : ℕ → G)
    (hb_map : ∀ i, act (b i) (A i) = A₀)
    (i j : ℕ) (hij : i ≤ j) :
    act ((b i)⁻¹ * b j) (A j) = A i := by
  rw [hact_mul, hb_map j]
  rw [show A₀ = act (b i) (A i) from (hb_map i).symm]
  rw [← hact_mul]
  simp [inv_mul_cancel, hact_one]

end AscendingChain

section MaximalCorollary

/-- If $g \cdot A = A_0$, then $A = g^{-1} \cdot A_0$. -/
lemma preimage_of_image_eq {G X : Type*} [Group G]
    (act : G → X → X)
    (hact_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x))
    (hact_one : ∀ x : X, act 1 x = x)
    (g : G) (A A₀ : Set X) (hg : (fun x => act g x) '' A = A₀) :
    A = (fun x => act g⁻¹ x) '' A₀ := by
  rw [← hg]; ext x; simp only [Set.mem_image]
  constructor
  · intro hx
    exact ⟨act g x, ⟨x, hx, rfl⟩, by
      show act g⁻¹ (act g x) = x
      rw [← hact_mul, inv_mul_cancel, hact_one]⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, hyx⟩
    have : x = z := by
      have h : act g⁻¹ (act g z) = x := hyx
      rw [← hact_mul, inv_mul_cancel, hact_one] at h; exact h.symm
    rwa [this]



end MaximalCorollary
