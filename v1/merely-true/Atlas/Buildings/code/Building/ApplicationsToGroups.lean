/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Affine
import Atlas.Buildings.code.BNPair.ParabolicDefs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Algebra.OpenSubgroup

set_option linter.unusedSectionVars false

open ChamberComplex

section Parahorics

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A parahoric subgroup of $G$ from a BN-pair of indecomposable affine Coxeter
type, bundled with a chosen subset $J \subseteq B$ of simple generators. The
underlying subgroup is the standard parabolic $P_J$. -/
structure ParahoricSubgroup (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  bnpair : BNPair G M
  generatorSubset : Set B_idx
  indecomposable : M.IsIndecomposable
  affine : M.IsAffine

/-- The underlying set of a parahoric subgroup, namely the standard parabolic
$P_J$. -/
def ParahoricSubgroup.toSet {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (P : ParahoricSubgroup G M) : Set G :=
  P.bnpair.standardParabolic P.generatorSubset

/-- A "parabolic subgroup at infinity" of $G$: a subgroup that is parabolic with
respect to the BN-pair, conceptually corresponding to a parabolic associated to
the spherical building at infinity of an affine building. -/
structure ParabolicSubgroupAtInfinity (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  bnpair : BNPair G M
  subgroup : Subgroup G
  isParabolic : bnpair.IsParabolic subgroup

/-- The parahoric/parabolic correspondence asserts that for every subset
$J \subseteq B$ there is a (typically smaller) subset $J_0 \subseteq J$ with
$P_J \subseteq P_{J_0}$. -/
def ParahoricParabolicCorrespondence {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) : Prop :=
  ∀ (J : Set B_idx),
    ∃ (J₀ : Set B_idx), J₀ ⊆ J ∧

      bp.standardParabolic J ⊆ bp.standardParabolic J₀

end Parahorics

section Decompositions

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- The Bruhat decomposition predicate on a BN-pair: $G$ is the disjoint union
of the Bruhat cells $BwB$ indexed by $w \in W$. -/
def BruhatDecomposition {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) : Prop :=

  (∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w) ∧

  (∀ w₁ w₂ : M.Group, w₁ ≠ w₂ →
    Disjoint (bp.bruhatCell w₁) (bp.bruhatCell w₂))

/-- The Cartan decomposition $G = KAK$: every $g \in G$ factors as $g = k_1 a k_2$
with $k_1, k_2 \in K$ and $a \in A$, where $K$ is a maximal compact subgroup
and $A$ is a chosen torus or split component. -/
def CartanDecomposition {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (_bp : BNPair G M) (K : Subgroup G) (A : Set G) : Prop :=

  ∀ g : G, ∃ (k₁ : K) (a : G) (k₂ : K),
    a ∈ A ∧ g = k₁ * a * k₂

/-- The Iwasawa decomposition $G = KAN$: every $g \in G$ factors as $g = kan$ with
$k \in K$, $a \in A$ and $n \in N$ unipotent. -/
def IwasawaDecomposition {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (_bp : BNPair G M) (K : Subgroup G)
    (A : Set G) (N_unip : Set G) : Prop :=

  ∀ g : G, ∃ (k : K) (a : G) (n : G),
    a ∈ A ∧ n ∈ N_unip ∧ g = k * a * n

end Decompositions

section TopologicalGroupDefinition

/-- Bundled definition of a topological group: continuous multiplication and
inversion. -/
structure TopologicalGroupDef (G : Type*) [TopologicalSpace G] [Group G] : Prop where
  mul_continuous : Continuous (fun p : G × G => p.1 * p.2)
  inv_continuous : Continuous (Inv.inv : G → G)

/-- Extract the bundled TopologicalGroupDef from Mathlib's IsTopologicalGroup. -/
theorem TopologicalGroupDef.of_isTopologicalGroup
    (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    TopologicalGroupDef G :=
  ⟨continuous_mul, continuous_inv⟩

/-- Convert the bundled TopologicalGroupDef to Mathlib's IsTopologicalGroup. -/
theorem TopologicalGroupDef.toIsTopologicalGroup
    {G : Type*} [TopologicalSpace G] [Group G] (h : TopologicalGroupDef G) :
    IsTopologicalGroup G :=
  { continuous_mul := h.mul_continuous
    continuous_inv := h.inv_continuous }

end TopologicalGroupDefinition

section PointwiseFixerProposition

/-- A finite intersection of conjugates $\bigcap_i g_i B g_i^{-1}$ of a compact-open
subgroup $B$ in a topological group $G$ is again open and compact. This is the
topological backbone for showing that pointwise fixers of finite sets of chambers
in a building are compact-open, as needed for strong transitivity arguments. -/
theorem pointwiseFixer_compact_open_prop
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B : Subgroup G)
    (hB_compact : IsCompact (B : Set G))
    (hB_open : IsOpen (B : Set G))


    (G_Y : Set G)
    {n : ℕ} (hn : 0 < n)
    (h_conj : Fin n → G)
    (hG_Y_eq : G_Y = ⋂ i, (fun x => h_conj i * x * (h_conj i)⁻¹) '' (B : Set G)) :
    IsOpen G_Y ∧ IsCompact G_Y := by

  have conj_eq : ∀ (g : G),
      (fun x => g * x * g⁻¹) = (fun x => g * x) ∘ (fun x => x * g⁻¹) := by
    intro g; ext x; simp [Function.comp, mul_assoc]

  have isOpen_conj : ∀ g : G, IsOpen ((fun x => g * x * g⁻¹) '' (B : Set G)) := by
    intro g; rw [conj_eq, Set.image_comp]
    exact (isOpenMap_mul_left g) _ ((isOpenMap_mul_right g⁻¹) _ hB_open)

  have isClosed_conj : ∀ g : G, IsClosed ((fun x => g * x * g⁻¹) '' (B : Set G)) := by
    intro g; rw [conj_eq, Set.image_comp]
    exact (isClosedMap_mul_left g) _ ((isClosedMap_mul_right g⁻¹) _
      (Subgroup.isClosed_of_isOpen B hB_open))

  have isCompact_conj : ∀ g : G, IsCompact ((fun x => g * x * g⁻¹) '' (B : Set G)) := by
    intro g; rw [conj_eq, Set.image_comp]
    exact (hB_compact.image (continuous_mul_const g⁻¹)).image (continuous_const_mul g)
  rw [hG_Y_eq]


  refine ⟨isOpen_iInter_of_finite (fun i => isOpen_conj (h_conj i)),
    IsCompact.of_isClosed_subset
      (isCompact_conj (h_conj (⟨0, hn⟩ : Fin n)))
      (isClosed_iInter (fun i => isClosed_conj (h_conj i)))
      (Set.iInter_subset _ (⟨0, hn⟩ : Fin n))⟩

end PointwiseFixerProposition

section StrongTransitivity

/-- A group action is maximally strongly transitive if, for every apartment $A'$ in
the system and every chamber $C' \subseteq A'$, some $g \in G$ simultaneously
sends $C'$ to the fixed reference chamber $C_0$ and $A'$ to the fixed reference
apartment $A_0$. This is the relevant transitivity hypothesis for maximal
apartment systems in non-spherical buildings. -/
def IsMaximallyStronglyTransitive
    {G : Type*} {X : Type*}
    (act : G → X → X)
    (IsChamber : Set X → Prop)
    (aptSystem : Set (Set X))
    (C₀ : Set X) (A₀ : Set X) : Prop :=
  ∀ A' ∈ aptSystem, ∀ C', IsChamber C' → C' ⊆ A' →
    ∃ g : G, (fun x => act g x) '' C' = C₀ ∧
            (fun x => act g x) '' A' = A₀

/-- Bundle of data witnessing a maximally strongly transitive action of a
topological group $G$ on a building-like set $X$. It records the action, a
reference chamber $C_0 \subseteq A_0$ inside a reference apartment, the
compact-open stabiliser $B$ of $C_0$, the system of maximal apartments and its
$G$-invariance, chamber-transitivity of $G$, and an exhaustion of each apartment
by $B$-conjugable pieces that together force a translating element back into
$A_0$. This is the precise hypothesis package used to prove strong transitivity
on maximal apartment systems. -/
structure MaxStrongTransData (G : Type*) (X : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] where
  act : G → X → X
  act_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x)
  act_one : ∀ x : X, act 1 x = x
  C₀ : Set X
  A₀ : Set X
  chamber_sub_apt : C₀ ⊆ A₀
  B : Subgroup G
  B_eq_fixer : (B : Set G) = {g | ∀ x ∈ C₀, act g x = x}
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
      (_ : ∀ i, IsOpen {g : G | ∀ y ∈ Y i, act g y = y})
      (_ : ∀ g : G, (∀ x ∈ A', act g x ∈ A₀) →
          (fun x => act g x) '' A' = A₀),
      True

end StrongTransitivity

section CanonicalTranslations

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A canonical translation in an affine Coxeter system: an element of the Coxeter
group that conjugates the set of simple reflections to itself and has infinite
order. Such elements act as translations on the geometric realisation of the
affine apartment. -/
structure CanonicalTranslation (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) (bp : BNPair G M) where
  element : M.Group
  permutes_simples : ∀ s : B_idx,
    ∃ s' : B_idx,
      element * M.toCoxeterSystem.simple s * element⁻¹ =
        M.toCoxeterSystem.simple s'
  infinite_order : ∀ n : ℕ, n ≠ 0 → element ^ n ≠ 1

end CanonicalTranslations

section LeviFiltration

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A descending filtration $P_J = F_0 \supseteq F_1 \supseteq \cdots$ on a standard
parabolic subgroup $P_J$ of a BN-pair, abstracting the Moy-Prasad / Levi
filtrations used in the structure theory of $p$-adic groups. -/
structure LeviFiltration (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  bnpair : BNPair G M
  generatorSubset : Set B_idx
  filtration : ℕ → Set G
  level_zero : filtration 0 = bnpair.standardParabolic generatorSubset
  descending : ∀ n : ℕ, filtration (n + 1) ⊆ filtration n

end LeviFiltration
