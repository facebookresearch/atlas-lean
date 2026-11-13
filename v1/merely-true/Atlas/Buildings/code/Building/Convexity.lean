/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.RetractionDef

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- $S$ is *gallery-convex* in $K$ if every minimal gallery between two chambers of $S$ has all of
its chambers in $S$. -/
def IsGalleryConvex (K : SimplicialComplex V) (S : Set (Finset V)) : Prop :=
  ∀ C D, C ∈ S → D ∈ S →
    ∀ g : Gallery K, g.Connects C D →
    g.length = galleryDist K C D →
    ∀ E ∈ g.chambers, E ∈ S

/-- $D$ is a *gate* for chamber $C$ inside $S$ if $D \in S$ and $D$ minimizes the gallery distance
from $C$ over chambers in $S$. -/
def IsGate (K : SimplicialComplex V) (S : Set (Finset V))
    (C D : Finset V) : Prop :=
  D ∈ S ∧ ∀ E ∈ S, galleryDist K C D ≤ galleryDist K C E

/-- A subcomplex $A$ of $K$ is *convex* if its set of maximal chambers is gallery-convex in $K$. -/
def IsConvexSubcomplex (K : SimplicialComplex V) (A : SimplicialComplex V)
    (_h : IsSubcomplex A K) : Prop :=
  IsGalleryConvex K { C | C ∈ A.faces ∧ A.IsMaximal C }

/-- In a chain $a :: b :: l$ where $a$ satisfies $P$ but some element $E$ does not, there is an adjacent pair witnessing the $P$-to-$\lnot P$ transition. -/
lemma chain_exists_transition {α : Type*} {R : α → α → Prop} {a b : α} {l : List α}
    (hchain : List.IsChain R (a :: b :: l)) (P : α → Prop)
    (hPa : P a) (E : α) (hE_mem : E ∈ a :: b :: l) (hE_not : ¬ P E) :
    ∃ x y, x ∈ a :: b :: l ∧ y ∈ a :: b :: l ∧ R x y ∧ P x ∧ ¬ P y := by
  by_cases hPb : P b
  · have hchain_tail : List.IsChain R (b :: l) := hchain.tail
    have hE_tail : E ∈ b :: l := by
      cases hE_mem with
      | head => exact absurd hPa hE_not
      | tail _ h => exact h
    cases l with
    | nil =>
      simp at hE_tail
      subst hE_tail
      exact absurd hPb hE_not
    | cons c l' =>
      obtain ⟨x, y, hx, hy, hR, hPx, hnPy⟩ :=
        chain_exists_transition hchain_tail P hPb E hE_tail hE_not
      exact ⟨x, y, List.mem_cons_of_mem a hx, List.mem_cons_of_mem a hy,
             hR, hPx, hnPy⟩
  · exact ⟨a, b, .head _, .tail _ (.head _), hchain.rel_head, hPa, hPb⟩

/-- A face of $A$ that is maximal in $K$ is also maximal in $A$, when $A \subseteq K$. -/
lemma maximal_in_building_and_subcomplex
    (K A : SimplicialComplex V) (hAK : IsSubcomplex A K)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_K_max : K.IsMaximal C) :
    A.IsMaximal C :=
  ⟨hC_A, fun y hy hsub => hC_K_max.2 y (hAK hy) hsub⟩

/-- If $f$ fixes every element of a finset $s$, then $s.\mathrm{image}\, f = s$. -/
lemma finset_image_eq_self_of_fixes {f : V → V} {s : Finset V}
    (hfix : ∀ v ∈ s, f v = v) : s.image f = s := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; rwa [hfix w hw]
  · intro hv; exact ⟨v, hv, hfix v hv⟩

/-- Apartments in a building are gallery-convex: minimal galleries between chambers of an
apartment $A$ stay inside $A$. -/
theorem Building.ApartmentsAreConvex (b : Building V) :
    ∀ A ∈ b.apartmentSystem.apartments,
      ∀ C D : Finset V,
        C ∈ A.faces → A.IsMaximal C →
        D ∈ A.faces → A.IsMaximal D →
        ∀ g : Gallery b.toSimplicialComplex,
          g.Connects C D →
          g.length = galleryDist b.toSimplicialComplex C D →
          ∀ E ∈ g.chambers, E ∈ A.faces := by
  intro A hA C D hC hCmax hD hDmax g hconn hmin E hEmem
  exact b.apartmentSystem.gallery_convex A hA C D hC
    (b.apartmentSystem.maximal_in_apt_is_maximal A hA C hCmax)
    hD (b.apartmentSystem.maximal_in_apt_is_maximal A hA D hDmax)
    g hconn hmin E hEmem

/-- Convex hull of two chambers $C, D$: the union of chambers occurring on some minimal gallery
from $C$ to $D$. -/
def ConvexHull (K : SimplicialComplex V) (C D : Finset V) : Set (Finset V) :=
  { E : Finset V | ∃ g : Gallery K, g.Connects C D ∧
    g.length = galleryDist K C D ∧ E ∈ g.chambers }
