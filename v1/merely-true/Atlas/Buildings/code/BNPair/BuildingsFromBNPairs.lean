/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.BNPair.Basic
import Atlas.Buildings.code.BNPair.ParabolicDefs
import Atlas.Buildings.code.BNPair.ConjugatorProof
import Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false

variable {B_idx : Type*} [DecidableEq B_idx]

namespace BNPair

variable {G : Type*} [Group G] {M : CoxeterMatrix B_idx}

/-- *Special subsets* of $G$: left cosets $g \cdot P_{S'}$ of a *proper* standard parabolic
$P_{S'}$ ($S' \subsetneq S$). These index the chambers and facets of the building. -/
def specialSubsets (bp : BNPair G M) : Set (Set G) :=
  { X | ∃ (g : G) (S' : Set B_idx), S' ≠ Set.univ ∧
    X = (fun x => g * x) '' bp.standardParabolic S' }

/-- The left coset $g \cdot P_{S'}$ of the standard parabolic indexed by $S'$. -/
def leftCoset (bp : BNPair G M) (g : G) (S' : Set B_idx) : Set G :=
  (fun x => g * x) '' bp.standardParabolic S'

/-- The *fundamental coset* at the identity: the standard parabolic $P_{S'}$ itself. -/
def fundamentalCoset (bp : BNPair G M) (S' : Set B_idx) : Set G :=
  bp.standardParabolic S'

/-- The *conjugate parabolic* $g P_{S'} g^{-1}$ — the image of $P_{S'}$ under conjugation by $g$. -/
def conjugateParabolic (bp : BNPair G M) (g : G) (S' : Set B_idx) : Set G :=
  (fun x => g * x * g⁻¹) '' bp.standardParabolic S'

/-- If $g P_{S_1} \subseteq h P_{S_2}$ then $g \in h P_{S_2}$, witnessed by some $q \in P_{S_2}$. -/
lemma coset_element_in_target (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
    ∃ q : G, q ∈ bp.standardParabolic S₂ ∧ g = h * q := by
  have h1 : (1 : G) ∈ bp.standardParabolic S₁ := (parabolicsAreSubgroups bp bd S₁).1
  have hg_mem : g * 1 ∈ bp.leftCoset g S₁ := by
    show g * 1 ∈ (fun x => g * x) '' bp.standardParabolic S₁
    exact Set.mem_image_of_mem _ h1
  have hg_in := hcontain (by rwa [mul_one] at hg_mem)
  obtain ⟨q, hq, hgq⟩ := hg_in
  exact ⟨q, hq, by simpa using hgq.symm⟩

/-- Coset inclusion forces inclusion of the underlying parabolics: $g P_{S_1} \subseteq h P_{S_2}$
implies $P_{S_1} \subseteq P_{S_2}$. -/
lemma coset_inclusion_implies_subgroup_inclusion (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
    bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
  obtain ⟨q, hq, hg_eq⟩ := coset_element_in_target bp bd g h S₁ S₂ hcontain
  intro x hx

  have : g * x ∈ bp.leftCoset g S₁ := Set.mem_image_of_mem _ hx
  have hgx_in := hcontain this
  obtain ⟨z, hz, hgxz⟩ := hgx_in


  have hgxz' : h * z = g * x := by simpa using hgxz
  have hqx : q * x = z := by
    have : h * q * x = h * z := by rw [← hg_eq, hgxz']
    have : h * (q * x) = h * z := by rwa [mul_assoc] at this
    exact mul_left_cancel this
  have : x = q⁻¹ * z := by rw [← hqx]; group
  rw [this]
  exact (parabolicsAreSubgroups bp bd S₂).2.1 _ _
    ((parabolicsAreSubgroups bp bd S₂).2.2 _ hq) hz

/-- The conjugation map descends to cosets: if $g P_{S'} = h P_{S'}$ then $g P_{S'} g^{-1} = h P_{S'} h^{-1}$. -/
lemma conjugation_well_defined (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S' : Set B_idx)
    (heq : bp.leftCoset g S' = bp.leftCoset h S') :
    bp.conjugateParabolic g S' = bp.conjugateParabolic h S' := by

  have h1_mem := (parabolicsAreSubgroups bp bd S').1
  have hg_mem : g ∈ bp.leftCoset h S' := by
    rw [← heq]
    show g ∈ (fun x => g * x) '' bp.standardParabolic S'
    exact ⟨1, h1_mem, mul_one g⟩
  obtain ⟨p₀, hp₀, hg_eq'⟩ := hg_mem
  have hg_eq : g = h * p₀ := by simpa using hg_eq'.symm
  unfold conjugateParabolic; ext y; simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨p₀ * x * p₀⁻¹, (parabolicsAreSubgroups bp bd S').2.1 _ _
      ((parabolicsAreSubgroups bp bd S').2.1 _ _ hp₀ hx)
      ((parabolicsAreSubgroups bp bd S').2.2 _ hp₀), ?_⟩
    show h * (p₀ * x * p₀⁻¹) * h⁻¹ = g * x * g⁻¹
    rw [hg_eq]; group
  · rintro ⟨x, hx, rfl⟩
    refine ⟨p₀⁻¹ * x * p₀, (parabolicsAreSubgroups bp bd S').2.1 _ _
      ((parabolicsAreSubgroups bp bd S').2.1 _ _
        ((parabolicsAreSubgroups bp bd S').2.2 _ hp₀) hx) hp₀, ?_⟩
    show g * (p₀⁻¹ * x * p₀) * g⁻¹ = h * x * h⁻¹
    rw [hg_eq]; group

/-- Conjugation respects the inclusion order on coset facets: $g P_{S_1} \subseteq h P_{S_2}$
implies $g P_{S_1} g^{-1} \subseteq h P_{S_2} h^{-1}$. -/
lemma conjugation_mono (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂) :
    bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂ := by
  obtain ⟨q, hq, hg_eq⟩ := coset_element_in_target bp bd g h S₁ S₂ hcontain
  have hsub := coset_inclusion_implies_subgroup_inclusion bp bd g h S₁ S₂ hcontain
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨q * x * q⁻¹, (parabolicsAreSubgroups bp bd S₂).2.1 _ _
    ((parabolicsAreSubgroups bp bd S₂).2.1 _ _ hq (hsub hx))
    ((parabolicsAreSubgroups bp bd S₂).2.2 _ hq), ?_⟩
  show h * (q * x * q⁻¹) * h⁻¹ = g * x * g⁻¹
  rw [hg_eq]; group

/-- The *type* (parabolic-index $S'$) of a coset facet is well-defined: if $g P_{S_1} = h P_{S_2}$
as subsets of $G$, then $S_1 = S_2$. This makes the building's labelling unambiguous. -/
theorem labelling_well_defined (bp : BNPair G M)
    (bd : BruhatProperties bp) (g h : G) (S₁ S₂ : Set B_idx)
    (heq : bp.leftCoset g S₁ = bp.leftCoset h S₂) :
    S₁ = S₂ := by
  have h12 := coset_inclusion_implies_subgroup_inclusion bp bd g h S₁ S₂ heq.le
  have h21 := coset_inclusion_implies_subgroup_inclusion bp bd h g S₂ S₁ heq.ge
  exact standardParabolicInjective bp bd S₁ S₂ (Set.Subset.antisymm h12 h21)

/-- The *fundamental apartment* expressed as a set of $B$-cosets: $\{nB : n \in N\}$. -/
def fundamentalApartmentCosets (bp : BNPair G M) : Set (Set G) :=
  { X | ∃ (n : bp.N), X = bp.leftCoset (n : G) ∅ }

/-- The $g$-translate $g \cdot \mathcal{A}$ of the fundamental apartment: $\{(gn)B : n \in N\}$. -/
def translatedApartmentCosets (bp : BNPair G M) (g : G) : Set (Set G) :=
  { X | ∃ (n : bp.N), X = bp.leftCoset (g * (n : G)) ∅ }

/-- Equivariance: $(gh) P_{S'} (gh)^{-1} = g \cdot (h P_{S'} h^{-1}) \cdot g^{-1}$. -/
lemma conjugation_equivariant (bp : BNPair G M) (g h : G) (S' : Set B_idx) :
    bp.conjugateParabolic (g * h) S' =
    (fun x => g * x * g⁻¹) '' bp.conjugateParabolic h S' := by
  unfold conjugateParabolic
  ext y; simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h * x * h⁻¹, ⟨x, hx, rfl⟩, by group⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩

/-- Left multiplication by $g$ on a coset $h P_{S'}$ gives the coset $(gh) P_{S'}$. -/
lemma leftCoset_left_action (bp : BNPair G M) (g h : G) (S' : Set B_idx) :
    (fun x => g * x) '' bp.leftCoset h S' = bp.leftCoset (g * h) S' := by
  unfold leftCoset
  ext y; simp only [Set.mem_image]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by group⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h * x, ⟨x, hx, rfl⟩, by group⟩

/-- $B$ is contained in every standard parabolic $P_{S'}$. -/
lemma B_mem_standardParabolic (bp : BNPair G M) (S' : Set B_idx)
    (b : G) (hb : b ∈ bp.B) :
    b ∈ bp.standardParabolic S' := by
  rw [standardParabolic, Set.mem_iUnion₂]
  exact ⟨1, (bp.parabolicSubgroupW S').one_mem,
    ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩,
      bp.π.map_one, by simp⟩⟩

/-- Right multiplication by $p \in P_{S'}$ does not change the coset: $gP_{S'} = (gp) P_{S'}$. -/
lemma leftCoset_right_mul_eq (bp : BNPair G M) (bd : BruhatProperties bp)
    (g : G) (S' : Set B_idx) (p : G) (hp : p ∈ bp.standardParabolic S') :
    bp.leftCoset g S' = bp.leftCoset (g * p) S' := by
  unfold leftCoset
  ext x; simp only [Set.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨p⁻¹ * q, (parabolicsAreSubgroups bp bd S').2.1 _ _
      ((parabolicsAreSubgroups bp bd S').2.2 _ hp) hq, ?_⟩
    group
  · rintro ⟨q, hq, rfl⟩
    refine ⟨p * q, (parabolicsAreSubgroups bp bd S').2.1 _ _ hp hq, ?_⟩
    group

/-- *Building axiom (B1)*: any two chambers $g_1 B, g_2 B$ lie in a common apartment.
Concretely, there exists $g \in G$ such that both $g_1 B$ and $g_2 B$ belong to $g \cdot \mathcal{A}$. -/
theorem bruhat_common_apartment (bp : BNPair G M) (bd : BruhatProperties bp)
    (g₁ g₂ : G) :
    ∃ (g : G), bp.leftCoset g₁ ∅ ∈ bp.translatedApartmentCosets g ∧
               bp.leftCoset g₂ ∅ ∈ bp.translatedApartmentCosets g := by

  obtain ⟨w, b₁, n, b₂, hπ, hg⟩ := bd.cell_cover (g₁⁻¹ * g₂)

  refine ⟨g₁ * b₁, ?_, ?_⟩
  ·
    refine ⟨⟨1, bp.N.one_mem⟩, ?_⟩
    rw [leftCoset_right_mul_eq bp bd g₁ (∅ : Set B_idx) b₁
      (B_mem_standardParabolic bp ∅ b₁ b₁.prop)]
    simp [leftCoset]
  ·
    refine ⟨n, ?_⟩
    have hg₂ : g₂ = g₁ * ((b₁ : G) * (n : G) * (b₂ : G)) := by
      rwa [inv_mul_eq_iff_eq_mul] at hg

    conv_lhs => rw [show g₂ = g₁ * (↑b₁ * ↑n) * ↑b₂ from by rw [hg₂]; group]
    rw [← leftCoset_right_mul_eq bp bd (g₁ * (↑b₁ * ↑n)) (∅ : Set B_idx) b₂
      (B_mem_standardParabolic bp ∅ b₂ b₂.prop)]
    congr 1; group

/-- If conjugation by $g$ sends $P_{S_1}$ into $P_{S_2}$, then $g$ itself lies in $P_{S_2}$.
A self-normalization property of standard parabolics. -/
theorem conjugator_in_target_of_subset {B_idx : Type*} [DecidableEq B_idx]
    {G : Type*} [Group G] {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BruhatProperties bp)
    (ax : BNPairAxioms bp)
    (S₁ S₂ : Set B_idx) (g : G)
    (hsub : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ ⊆
      bp.standardParabolic S₂) :
    g ∈ bp.standardParabolic S₂ := by

  let PS₂ := bp.standardParabolic S₂
  let pAS₂ := parabolicsAreSubgroups bp bd S₂

  let Q : Subgroup G :=
  { carrier := PS₂
    mul_mem' := fun hx hy => pAS₂.2.1 _ _ hx hy
    one_mem' := pAS₂.1
    inv_mem' := fun hx => pAS₂.2.2 _ hx }
  have hBQ : bp.B ≤ Q := B_mem_standardParabolic bp S₂


  have hgBg_sub : ∀ b ∈ bp.B, g * b * g⁻¹ ∈ PS₂ := by
    intro b hb
    have hb_PS1 : b ∈ bp.standardParabolic S₁ :=
      B_mem_standardParabolic bp S₁ b hb
    exact hsub ⟨b, hb_PS1, rfl⟩

  obtain ⟨w, hwg⟩ := bd.cell_cover g

  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hwg

  have hn_conj : ∀ b' ∈ bp.B, (n : G) * b' * (n : G)⁻¹ ∈ (Q : Set G) := by
    intro b' hb'
    have hb'' : (b₂ : G)⁻¹ * b' * b₂ ∈ bp.B :=
      bp.B.mul_mem (bp.B.mul_mem (bp.B.inv_mem hb₂) hb') hb₂
    have hgconj : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ ∈ PS₂ := hgBg_sub _ hb''
    have heq : g * ((b₂ : G)⁻¹ * b' * b₂) * g⁻¹ =
        (b₁ : G) * ((n : G) * b' * (n : G)⁻¹) * (b₁ : G)⁻¹ := by
      rw [hg_eq]; group
    rw [heq] at hgconj
    have hb₁_Q : b₁ ∈ (Q : Set G) := hBQ hb₁
    have hb₁_inv_Q : b₁⁻¹ ∈ (Q : Set G) := Q.inv_mem hb₁_Q
    have key : (n : G) * b' * (n : G)⁻¹ =
        b₁⁻¹ * (b₁ * ((n : G) * b' * (n : G)⁻¹) * b₁⁻¹) * b₁ := by group
    rw [key]
    exact Q.mul_mem (Q.mul_mem hb₁_inv_Q hgconj) hb₁_Q

  have hBwB_sub : bp.bruhatCell w ⊆ PS₂ :=
    NormalizerParabolic.bruhatCell_sub_of_conj bp ax Q hBQ w n hπ hn_conj

  exact hBwB_sub ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩

/-- From $g P_{S_1} g^{-1} \subseteq P_{S_2}$ deduce the direct inclusion $P_{S_1} \subseteq P_{S_2}$. -/
lemma subgroup_inclusion_of_conj_inclusion (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (S₁ S₂ : Set B_idx) (g : G)
    (hsub : (fun x => g * x * g⁻¹) '' bp.standardParabolic S₁ ⊆
      bp.standardParabolic S₂) :
    bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
  have hg_mem := conjugator_in_target_of_subset bp bd ax S₁ S₂ g hsub
  intro x hx

  have hgxg : g * x * g⁻¹ ∈ bp.standardParabolic S₂ :=
    hsub ⟨x, hx, rfl⟩

  have hx_eq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [hx_eq]
  exact (parabolicsAreSubgroups bp bd S₂).2.1 _ _
    ((parabolicsAreSubgroups bp bd S₂).2.1 _ _
      ((parabolicsAreSubgroups bp bd S₂).2.2 _ hg_mem) hgxg)
    hg_mem

/-- Reverse direction of `conjugation_mono`: inclusion of conjugate parabolics
$g P_{S_1} g^{-1} \subseteq h P_{S_2} h^{-1}$ implies inclusion of cosets $g P_{S_1} \subseteq h P_{S_2}$. -/
lemma conjugation_reflects_order (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (g h : G) (S₁ S₂ : Set B_idx)
    (hcontain : bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂) :
    bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ := by

  have hsub : (fun x => (h⁻¹ * g) * x * (h⁻¹ * g)⁻¹) '' bp.standardParabolic S₁ ⊆
      bp.standardParabolic S₂ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy

    show h⁻¹ * g * x * (h⁻¹ * g)⁻¹ ∈ bp.standardParabolic S₂

    have hgxg : g * x * g⁻¹ ∈ bp.conjugateParabolic g S₁ :=
      ⟨x, hx, rfl⟩
    have hgxg_in := hcontain hgxg

    obtain ⟨z, hz, hzq⟩ := hgxg_in


    have heq : h⁻¹ * g * x * (h⁻¹ * g)⁻¹ = z := by
      have hzq' : h * z * h⁻¹ = g * x * g⁻¹ := hzq
      calc h⁻¹ * g * x * (h⁻¹ * g)⁻¹
          = h⁻¹ * (g * x * g⁻¹) * h := by group
        _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [hzq']
        _ = z := by group
    rw [heq]; exact hz

  set a := h⁻¹ * g with ha_def
  have ha_mem := conjugator_in_target_of_subset bp bd ax S₁ S₂ a hsub
  have hP_sub := subgroup_inclusion_of_conj_inclusion bp bd ax S₁ S₂ a hsub

  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy

  show g * x ∈ bp.leftCoset h S₂
  refine ⟨a * x, ?_, ?_⟩
  ·
    exact (parabolicsAreSubgroups bp bd S₂).2.1 _ _ ha_mem (hP_sub hx)
  ·
    show h * (a * x) = g * x
    simp [ha_def]; group

/-- Equivalence: coset inclusion $\Leftrightarrow$ conjugate-parabolic inclusion.
This is the order-preservation half of the poset isomorphism between cosets and conjugate parabolics. -/
theorem conjugation_preserves_order (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (g h : G) (S₁ S₂ : Set B_idx) :
    bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ ↔
    bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂ :=
  ⟨conjugation_mono bp bd g h S₁ S₂,
   conjugation_reflects_order bp bd ax g h S₁ S₂⟩

/-- Synonym wrapper around `conjugation_preserves_order`. -/
theorem conjugation_order_iff (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (g h : G) (S₁ S₂ : Set B_idx) :
    bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ ↔
    bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂ :=
  conjugation_preserves_order bp bd ax g h S₁ S₂

/-- *Proper parabolics*: conjugates $g P_{S'} g^{-1}$ of proper standard parabolics ($S' \subsetneq S$). -/
def properParabolics (bp : BNPair G M) : Set (Set G) :=
  { Q | ∃ (g : G) (S' : Set B_idx), S' ≠ Set.univ ∧
    Q = bp.conjugateParabolic g S' }

/-- Concrete representative of the conjugation map sending a coset $gP_{S'}$ to its conjugate parabolic. -/
def conjugationMapRepr (bp : BNPair G M) (g : G) (S' : Set B_idx) : Set G :=
  bp.conjugateParabolic g S'

/-- Injectivity at the coset level: equal conjugate parabolics force equal cosets. -/
lemma conjugation_injective_on_cosets (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp)
    (g h : G) (S₁ S₂ : Set B_idx)
    (heq : bp.conjugateParabolic g S₁ = bp.conjugateParabolic h S₂) :
    bp.leftCoset g S₁ = bp.leftCoset h S₂ := by
  apply Set.Subset.antisymm
  · exact conjugation_reflects_order bp bd ax g h S₁ S₂ heq.le
  · exact conjugation_reflects_order bp bd ax h g S₂ S₁ heq.ge

/-- Bundle theorem: the conjugation map gives a poset isomorphism between the special
subsets (left cosets $gP_{S'}$) and proper parabolic subgroups ($gP_{S'}g^{-1}$). Encodes
inclusion-iff, well-definedness, injectivity, surjectivity, and equivariance simultaneously. -/
theorem poset_isomorphism_specialSubsets_properParabolics (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp) :

    (∀ (g h : G) (S₁ S₂ : Set B_idx),
      bp.leftCoset g S₁ ⊆ bp.leftCoset h S₂ ↔
      bp.conjugateParabolic g S₁ ⊆ bp.conjugateParabolic h S₂) ∧

    (∀ (g h : G) (S' : Set B_idx),
      bp.leftCoset g S' = bp.leftCoset h S' →
      bp.conjugateParabolic g S' = bp.conjugateParabolic h S') ∧

    (∀ (g h : G) (S₁ S₂ : Set B_idx),
      bp.conjugateParabolic g S₁ = bp.conjugateParabolic h S₂ →
      bp.leftCoset g S₁ = bp.leftCoset h S₂) ∧

    (∀ Q ∈ bp.properParabolics,
      ∃ (g : G) (S' : Set B_idx), S' ≠ Set.univ ∧
        Q = bp.conjugateParabolic g S') ∧

    (∀ (g h : G) (S' : Set B_idx),
      bp.conjugateParabolic (g * h) S' =
      (fun x => g * x * g⁻¹) '' bp.conjugateParabolic h S') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g h S₁ S₂
    exact conjugation_order_iff bp bd ax g h S₁ S₂
  ·
    intro g h S'
    exact conjugation_well_defined bp bd g h S'
  ·
    intro g h S₁ S₂
    exact conjugation_injective_on_cosets bp bd ax g h S₁ S₂
  ·
    intro Q hQ
    exact hQ
  ·
    intro g h S'
    exact conjugation_equivariant bp g h S'

/-- Choose a group-element representative $g$ such that $X = g P_{S'}$ for a special subset $X$. -/
noncomputable def specialSubsetReprG (bp : BNPair G M)
    (X : bp.specialSubsets) : G :=
  Classical.choose X.prop

/-- Choose a parabolic-type representative $S'$ such that $X = g P_{S'}$ for a special subset $X$. -/
noncomputable def specialSubsetReprS (bp : BNPair G M)
    (X : bp.specialSubsets) : Set B_idx :=
  Classical.choose (Classical.choose_spec X.prop)

/-- Defining property of the chosen representatives: $S' \neq S$ and $X$ equals $g P_{S'}$. -/
lemma specialSubsetRepr_prop (bp : BNPair G M) (X : bp.specialSubsets) :
    bp.specialSubsetReprS X ≠ Set.univ ∧
    (X : Set G) = bp.leftCoset (bp.specialSubsetReprG X) (bp.specialSubsetReprS X) :=
  (Classical.choose_spec (Classical.choose_spec X.prop)).imp_right id

/-- First conjunct of `specialSubsetRepr_prop`: the chosen $S'$ is a proper subset. -/
lemma specialSubsetRepr_ne_univ (bp : BNPair G M) (X : bp.specialSubsets) :
    bp.specialSubsetReprS X ≠ Set.univ :=
  (specialSubsetRepr_prop bp X).1

/-- Second conjunct: $X$ equals the coset $g P_{S'}$ formed from the chosen representatives. -/
lemma specialSubsetRepr_eq (bp : BNPair G M) (X : bp.specialSubsets) :
    (X : Set G) = bp.leftCoset (bp.specialSubsetReprG X) (bp.specialSubsetReprS X) :=
  (specialSubsetRepr_prop bp X).2

/-- Choose a conjugator $g$ such that $Q = g P_{S'} g^{-1}$ for a proper parabolic $Q$. -/
noncomputable def properParabolicReprG (bp : BNPair G M)
    (Q : bp.properParabolics) : G :=
  Classical.choose Q.prop

/-- Choose the parabolic type $S'$ such that $Q = g P_{S'} g^{-1}$ for a proper parabolic $Q$. -/
noncomputable def properParabolicReprS (bp : BNPair G M)
    (Q : bp.properParabolics) : Set B_idx :=
  Classical.choose (Classical.choose_spec Q.prop)

/-- Defining property of the chosen representatives: $S' \neq S$ and $Q$ equals the conjugate parabolic. -/
lemma properParabolicRepr_prop (bp : BNPair G M) (Q : bp.properParabolics) :
    bp.properParabolicReprS Q ≠ Set.univ ∧
    (Q : Set G) = bp.conjugateParabolic (bp.properParabolicReprG Q) (bp.properParabolicReprS Q) :=
  (Classical.choose_spec (Classical.choose_spec Q.prop)).imp_right id

/-- The chosen $S'$ is a proper subset. -/
lemma properParabolicRepr_ne_univ (bp : BNPair G M) (Q : bp.properParabolics) :
    bp.properParabolicReprS Q ≠ Set.univ :=
  (properParabolicRepr_prop bp Q).1

/-- $Q$ equals the conjugate parabolic $g P_{S'} g^{-1}$ formed from the chosen representatives. -/
lemma properParabolicRepr_eq (bp : BNPair G M) (Q : bp.properParabolics) :
    (Q : Set G) = bp.conjugateParabolic (bp.properParabolicReprG Q) (bp.properParabolicReprS Q) :=
  (properParabolicRepr_prop bp Q).2

/-- Forward map of the poset isomorphism: a special subset $X = g P_{S'}$ is sent to the
proper parabolic $g P_{S'} g^{-1}$. -/
noncomputable def conjugationForward (bp : BNPair G M)
    (X : bp.specialSubsets) : bp.properParabolics :=
  ⟨bp.conjugateParabolic (bp.specialSubsetReprG X) (bp.specialSubsetReprS X),
   ⟨bp.specialSubsetReprG X, bp.specialSubsetReprS X, bp.specialSubsetRepr_ne_univ X, rfl⟩⟩

/-- Inverse map of the poset isomorphism: a proper parabolic $Q = g P_{S'} g^{-1}$ is sent
back to the coset $g P_{S'}$. -/
noncomputable def conjugationBackward (bp : BNPair G M)
    (Q : bp.properParabolics) : bp.specialSubsets :=
  ⟨bp.leftCoset (bp.properParabolicReprG Q) (bp.properParabolicReprS Q),
   ⟨bp.properParabolicReprG Q, bp.properParabolicReprS Q, bp.properParabolicRepr_ne_univ Q, rfl⟩⟩

/-- Order isomorphism $\text{specialSubsets} \;\simeq_o\; \text{properParabolics}$
realized by conjugation. The two maps are mutual inverses, and inclusion of cosets
corresponds to inclusion of conjugate parabolics. -/
noncomputable def poset_orderIso_specialSubsets_properParabolics (bp : BNPair G M)
    (bd : BruhatProperties bp) (ax : BNPairAxioms bp) :
    bp.specialSubsets ≃o bp.properParabolics where
  toFun := conjugationForward bp
  invFun := conjugationBackward bp
  left_inv := by
    intro X
    ext : 1


    show (conjugationBackward bp (conjugationForward bp X) : Set G) = (X : Set G)
    simp only [conjugationForward, conjugationBackward]

    set g₁ := bp.specialSubsetReprG X
    set S₁ := bp.specialSubsetReprS X
    set Q_val := bp.conjugateParabolic g₁ S₁
    set Q_mem : Q_val ∈ bp.properParabolics :=
      ⟨g₁, S₁, bp.specialSubsetRepr_ne_univ X, rfl⟩
    set Q : bp.properParabolics := ⟨Q_val, Q_mem⟩
    set g₂ := bp.properParabolicReprG Q
    set S₂ := bp.properParabolicReprS Q
    have heq_Q : Q_val = bp.conjugateParabolic g₂ S₂ := properParabolicRepr_eq bp Q


    have h_inj := conjugation_injective_on_cosets bp bd ax g₂ g₁ S₂ S₁ heq_Q.symm
    rw [h_inj]
    exact (specialSubsetRepr_eq bp X).symm
  right_inv := by
    intro Q
    ext : 1
    show (conjugationForward bp (conjugationBackward bp Q) : Set G) = (Q : Set G)
    simp only [conjugationBackward, conjugationForward]
    set g₁ := bp.properParabolicReprG Q
    set S₁ := bp.properParabolicReprS Q
    set X_val := bp.leftCoset g₁ S₁
    set X_mem : X_val ∈ bp.specialSubsets :=
      ⟨g₁, S₁, bp.properParabolicRepr_ne_univ Q, rfl⟩
    set X : bp.specialSubsets := ⟨X_val, X_mem⟩
    set g₂ := bp.specialSubsetReprG X
    set S₂ := bp.specialSubsetReprS X
    have heq_X : X_val = bp.leftCoset g₂ S₂ := specialSubsetRepr_eq bp X


    have hS_eq := labelling_well_defined bp bd g₂ g₁ S₂ S₁ heq_X.symm
    rw [hS_eq] at heq_X ⊢
    have h_wd := conjugation_well_defined bp bd g₂ g₁ S₁ heq_X.symm
    rw [h_wd]
    exact (properParabolicRepr_eq bp Q).symm

  map_rel_iff' := by
    intro X Y
    show (conjugationForward bp X : Set G) ⊆ (conjugationForward bp Y : Set G) ↔
         (X : Set G) ⊆ (Y : Set G)
    simp only [conjugationForward]
    set g₁ := bp.specialSubsetReprG X
    set S₁ := bp.specialSubsetReprS X
    set g₂ := bp.specialSubsetReprG Y
    set S₂ := bp.specialSubsetReprS Y
    have heq₁ := specialSubsetRepr_eq bp X
    have heq₂ := specialSubsetRepr_eq bp Y
    constructor
    · intro h
      rw [heq₁, heq₂]
      exact conjugation_reflects_order bp bd ax g₁ g₂ S₁ S₂ h
    · intro h
      have h' : bp.leftCoset g₁ S₁ ⊆ bp.leftCoset g₂ S₂ := by rw [← heq₁, ← heq₂]; exact h
      exact conjugation_mono bp bd g₁ g₂ S₁ S₂ h'

end BNPair
