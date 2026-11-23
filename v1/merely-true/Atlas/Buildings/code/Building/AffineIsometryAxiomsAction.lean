/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineIsometry.Contexts
import Atlas.Buildings.code.Building.AffineIsometry.LatticeChains
import Atlas.Buildings.code.Building.AffineIsometry.Theorems
import Atlas.Buildings.code.Building.GroupApplicationsCh17

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AffineIsometryBuilding DVRContext

/-- An $n \times n$ matrix over $\mathfrak{o}$ is upper-triangular modulo
$\mathfrak{m}$ if every strictly-below-diagonal entry is divisible by the
uniformizer $\pi$. -/
def IsUpperTriangularModM_Isometry (C : DVRContext)
    (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, i.val > j.val →
    ∃ h : C.𝔬, g i j = C.uniformizer * h

/-- A matrix is congruent to the identity modulo $\mathfrak{m}$ if each entry
differs from the corresponding entry of the identity matrix by a multiple of
the uniformizer $\pi$. -/
def IsCongruentToIdentity_Isometry (C : DVRContext)
    (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, ∃ h : C.𝔬,
    g i j - (if i = j then 1 else 0) = C.uniformizer * h

/-- A matrix congruent to the identity mod $\mathfrak{m}$ is in particular
upper-triangular mod $\mathfrak{m}$: the off-diagonal entries reduce to
zero $\bmod\ \mathfrak{m}$, hence are multiples of $\pi$. -/
theorem isometry_congruent_to_identity_is_upper_tri
    (C : DVRContext)
    (g : Fin C.n → Fin C.n → C.𝔬)
    (hg : IsCongruentToIdentity_Isometry C g) :
    IsUpperTriangularModM_Isometry C g := by
  intro i j hij
  obtain ⟨h, hh⟩ := hg i j
  have hne : i ≠ j := Fin.ne_of_gt hij
  simp only [if_neg hne] at hh
  rw [sub_zero] at hh
  exact ⟨h, hh⟩

/-- The Iwahori subgroup of the isometry group in the alternating-form setting:
matrices that are upper-triangular modulo $\mathfrak{m}$. -/
def IwahoriSubgroup_Alternating (C : DVRContext) :
    Set (Fin C.n → Fin C.n → C.𝔬) :=
  {g | IsUpperTriangularModM_Isometry C g}

namespace Isometry

/-- The parahoric subgroup associated to a lattice chain and an index set
$J$: matrices preserving each $\mathfrak{o}$-lattice $\Lambda_j$ for
$j \in J$. -/
def ParahoricSubgroup (C : DVRContext)
    (chain : ℤ → OLattice C) (J : Set ℤ) :
    Set (Fin C.n → Fin C.n → C.𝔬) :=
  {g | ∀ j ∈ J, ∀ v ∈ (chain j).carrier,
    (fun k => ∑ l, C.embed (g k l) * v l) ∈ (chain j).carrier}

end Isometry

/-- Abstract topology lemma: a set $B$ that is open and equals one cell of an
open-cell partition is closed, because its complement is the open union of
the other cells. -/
theorem open_plus_decomp_closed_isometry
    {α : Type*} [TopologicalSpace α]
    (B : Set α) (_hopen : IsOpen B)
    (hdecomp : ∃ (I : Type*) (cells : I → Set α),
      (∀ i, IsOpen (cells i)) ∧
      Set.univ = ⋃ i, cells i ∧
      (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧
      ∃ i₀, cells i₀ = B) :
    IsClosed B := by
  obtain ⟨I, cells, hcells_open, hcover, hdisj, i₀, hi₀⟩ := hdecomp
  rw [← isOpen_compl_iff]
  have hBc : Bᶜ = ⋃ (i : {i // i ≠ i₀}), cells i.1 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · intro hxB
      have hx_univ : x ∈ Set.univ := Set.mem_univ x
      rw [hcover] at hx_univ
      simp only [Set.mem_iUnion] at hx_univ
      obtain ⟨i, hi⟩ := hx_univ
      have hne : i ≠ i₀ := fun heq => hxB (hi₀ ▸ heq ▸ hi)
      exact ⟨⟨i, hne⟩, hi⟩
    · intro ⟨⟨i, hne⟩, hxi⟩ hxB
      rw [← hi₀] at hxB
      exact Set.disjoint_left.mp (hdisj i i₀ hne) hxi hxB
  rw [hBc]
  exact isOpen_iUnion (fun ⟨i, _⟩ => hcells_open i)

/-- Abstract topology lemma: a closed subset of a compact set is compact. -/
theorem closed_in_compact_isometry
    {α : Type*} [TopologicalSpace α]
    (B K : Set α)
    (hB_closed : IsClosed B) (hBK : B ⊆ K) (hK_compact : IsCompact K) :
    IsCompact B :=
  hK_compact.of_isClosed_subset hB_closed hBK

