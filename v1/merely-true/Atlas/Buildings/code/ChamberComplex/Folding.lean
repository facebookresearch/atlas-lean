/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Basic
import Atlas.Buildings.code.ChamberComplex.Uniqueness

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- Propagate a head-property along an `IsChain`: if $P$ holds at the head and is preserved by
$R$-steps, then $P$ holds at every element of the list. -/
lemma List.chain_forall_of_head {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (l : List α) (hne : l ≠ [])
    (hchain : l.IsChain R)
    (hhead : P (l.head hne))
    (hprop : ∀ a b, R a b → P a → P b) :
    ∀ x ∈ l, P x := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro x hx
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hhead
    · cases tl with
      | nil => simp at hx
      | cons b rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        exact ih (List.cons_ne_nil b rest) hchain_tl
          (hprop a b (hrel b rfl) hhead) x hx

namespace ChamberComplex

/-- A *folding* of a chamber complex $X$: an idempotent simplicial endomorphism that maps
chambers to chambers and facets to facets, is not the identity, is two-to-one on its fixed
half-apartment, has a boundary edge (a fixed chamber adjacent to a moved one), and along any
gallery between two fixed chambers any "moved" chamber forces an exit edge from the fixed
half. Also requires `stutter_at_boundary`: a moved chamber adjacent to a fixed one is mapped to
that fixed chamber. The final clause excludes stutters in minimal galleries between fixed
chambers. -/
structure Folding (X : ChamberComplex V) where
  morph : SimplicialComplex.Morphism X.toSimplicialComplex X.toSimplicialComplex
  chamberMap : morph.IsChamberMap
  preservesFacets : morph.PreservesFacets
  idempotent : ∀ v, morph.toFun (morph.toFun v) = morph.toFun v
  not_id : ∃ C, X.toSimplicialComplex.IsMaximal C ∧ C.image morph.toFun ≠ C
  twoToOne : ∀ C, X.toSimplicialComplex.IsMaximal C →
    C.image morph.toFun = C →
    ∃! D, X.toSimplicialComplex.IsMaximal D ∧ D ≠ C ∧ D.image morph.toFun = C
  exists_boundary : ∃ C D, X.toSimplicialComplex.Adjacent C D ∧
    C.image morph.toFun = C ∧ D.image morph.toFun ≠ D
  gallery_exits :
    ∀ (C D : Finset V),
      X.toSimplicialComplex.IsMaximal C → C.image morph.toFun = C →
      X.toSimplicialComplex.IsMaximal D → D.image morph.toFun = D →
      ∀ (g : Gallery X.toSimplicialComplex), g.Connects C D →
      ∀ (E : Finset V), E ∈ g.chambers → E.image morph.toFun ≠ E →
      ∃ Ci Ci1, Ci ∈ g.chambers ∧ Ci1 ∈ g.chambers ∧
        X.toSimplicialComplex.Adjacent Ci Ci1 ∧
        (X.toSimplicialComplex.IsMaximal Ci ∧ Ci.image morph.toFun = Ci) ∧
        ¬(X.toSimplicialComplex.IsMaximal Ci1 ∧ Ci1.image morph.toFun = Ci1)
  stutter_at_boundary :
    ∀ (Ci Ci1 : Finset V),
      X.toSimplicialComplex.Adjacent Ci Ci1 →
      (X.toSimplicialComplex.IsMaximal Ci ∧ Ci.image morph.toFun = Ci) →
      Ci1.image morph.toFun ≠ Ci1 →
      Ci1.image morph.toFun = Ci
  stutter_contradicts_minimality :
    ∀ (C D : Finset V),
      X.toSimplicialComplex.IsMaximal C → C.image morph.toFun = C →
      X.toSimplicialComplex.IsMaximal D → D.image morph.toFun = D →
      ∀ (g : Gallery X.toSimplicialComplex), g.Connects C D →
      g.length = galleryDist X.toSimplicialComplex C D →
      ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers →
        X.toSimplicialComplex.Adjacent Ci Ci1 →
        Ci1.image morph.toFun = Ci.image morph.toFun → False

variable {X : ChamberComplex V}

namespace Folding

/-- The set of chambers fixed (as sets) by the folding $f$, i.e. $f(C) = C$. -/
def fixedChambers (f : Folding X) : Set (Finset V) :=
  {C | X.toSimplicialComplex.IsMaximal C ∧ C.image f.morph.toFun = C}

/-- The set of chambers moved by the folding $f$, i.e. $f(C) \neq C$. -/
def movedChambers (f : Folding X) : Set (Finset V) :=
  {C | X.toSimplicialComplex.IsMaximal C ∧ C.image f.morph.toFun ≠ C}

/-- Every chamber is either fixed or moved by $f$. -/
lemma fixed_or_moved (f : Folding X) {C : Finset V}
    (hC : X.toSimplicialComplex.IsMaximal C) :
    C ∈ f.fixedChambers ∨ C ∈ f.movedChambers := by
  by_cases h : C.image f.morph.toFun = C
  · exact Or.inl ⟨hC, h⟩
  · exact Or.inr ⟨hC, h⟩

/-- The image $f(C)$ of any chamber is a fixed chamber (by idempotence). -/
lemma image_is_fixed (f : Folding X) {C : Finset V}
    (hC : X.toSimplicialComplex.IsMaximal C) :
    C.image f.morph.toFun ∈ f.fixedChambers := by
  refine ⟨f.chamberMap C hC, ?_⟩
  ext v; simp only [Finset.mem_image]; constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, (f.idempotent u).symm⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨f.morph.toFun w, ⟨w, hw, rfl⟩, f.idempotent w⟩

/-- If $f(C) = C$ as a set, then $f$ fixes every vertex of $C$ pointwise. -/
theorem fixes_pointwise (f : Folding X) {C : Finset V}
    (hfC : C.image f.morph.toFun = C) :
    ∀ v ∈ C, f.morph.toFun v = v := by
  intro v hv; rw [← hfC] at hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
  exact f.idempotent u

/-- In a thin chamber complex, a folding sends a moved chamber adjacent to a fixed chamber $C$
back onto $C$: $f(D) = C$. -/
theorem fold_adj_to_self (f : Folding X) (hThin : X.IsThin)
    {C D : Finset V} (hadj : X.toSimplicialComplex.Adjacent C D)
    (hfC : C.image f.morph.toFun = C) (hfD : D.image f.morph.toFun ≠ D) :
    D.image f.morph.toFun = C := by
  obtain ⟨hCmax, hDmax, hne, F, hFC, hFD⟩ := hadj
  have hfix := f.fixes_pointwise hfC

  have hfF : F.image f.morph.toFun = F := by
    ext v; simp only [Finset.mem_image]; constructor
    · rintro ⟨w, hw, rfl⟩; rwa [hfix w (hFC.1.2.2 hw)]
    · intro hv; exact ⟨v, hv, hfix v (hFC.1.2.2 hv)⟩

  have hfFfD := f.preservesFacets F D hFD
  rw [hfF] at hfFfD

  have hfDmax := f.chamberMap D hDmax

  obtain ⟨D', ⟨_, _, _⟩, hD'uniq⟩ := hThin F C hFC hCmax
  have hD'D : D = D' := hD'uniq D ⟨hne.symm, hFD, hDmax⟩


  by_contra hfD_ne_C
  have : D.image f.morph.toFun = D' :=
    hD'uniq (D.image f.morph.toFun) ⟨hfD_ne_C, hfFfD, hfDmax⟩
  rw [← hD'D] at this; exact hfD this

end Folding

/-- A *reversible folding* is a pair $(f, g)$ of foldings such that $f$'s fixed chambers equal
$g$'s moved chambers (and vice versa), and the two foldings exchange the two boundary chambers
of any wall: $g(C) = C'$ where $C, C'$ are an adjacent fixed/moved pair under $f$. -/
structure ReversibleFolding (X : ChamberComplex V) where
  f : Folding X
  g : Folding X
  complementary_fixed : f.fixedChambers = g.movedChambers
  complementary_moved : f.movedChambers = g.fixedChambers
  opposite_action : ∀ C C',
    X.toSimplicialComplex.IsMaximal C →
    X.toSimplicialComplex.IsMaximal C' →
    C ≠ C' → C.image f.morph.toFun = C → C'.image f.morph.toFun = C →
    C.image g.morph.toFun = C'
  opposite_action' : ∀ C C',
    X.toSimplicialComplex.IsMaximal C →
    X.toSimplicialComplex.IsMaximal C' →
    C ≠ C' → C.image g.morph.toFun = C → C'.image g.morph.toFun = C →
    C.image f.morph.toFun = C'

namespace ReversibleFolding

variable (rf : ReversibleFolding X)

/-- The two half-apartments of a reversible folding are disjoint: no chamber is fixed by both
$f$ and $g$. -/
theorem halves_disjoint (C : Finset V) :
    ¬(C ∈ rf.f.fixedChambers ∧ C ∈ rf.g.fixedChambers) := by
  intro ⟨hf, hg⟩
  have : C ∈ rf.g.movedChambers := rf.complementary_fixed ▸ hf
  exact this.2 hg.2

end ReversibleFolding

/-- The *wall* of a folding $f$: faces fixed pointwise by $f$ that lie in some moved chamber. -/
def Wall (X : ChamberComplex V) (f : Folding X) : Set (Finset V) :=
  {x | x ∈ X.toSimplicialComplex.faces ∧
       (∀ v ∈ x, f.morph.toFun v = v) ∧
       (∃ C, X.toSimplicialComplex.IsMaximal C ∧
              C.image f.morph.toFun ≠ C ∧ x ⊆ C)}

/-- The vertex-level reflection associated with a reversible folding: at each vertex, apply $g$
where $f$ fixes, and $f$ elsewhere. -/
def reflectionFun (rf : ReversibleFolding X) : V → V :=
  fun v => if rf.f.morph.toFun v = v then rf.g.morph.toFun v
           else rf.f.morph.toFun v

/-- Two chambers lie on *opposite* sides of the wall of $f$: one is fixed and the other moved. -/
def OppositeSides (f : Folding X) (C D : Finset V) : Prop :=
  (C.image f.morph.toFun = C ∧ D.image f.morph.toFun ≠ D) ∨
  (D.image f.morph.toFun = D ∧ C.image f.morph.toFun ≠ C)

/-- Two chambers lie on the *same* side of the wall of $f$: both fixed or both moved. -/
def SameSide (f : Folding X) (C D : Finset V) : Prop :=
  (C.image f.morph.toFun = C ∧ D.image f.morph.toFun = D) ∨
  (C.image f.morph.toFun ≠ C ∧ D.image f.morph.toFun ≠ D)

/-- Under the cover / cross-fixed-point hypotheses, the reflection map associated with a
reversible folding is an involution: $\rho \circ \rho = \mathrm{id}$. -/
theorem reflection_involutive (rf : ReversibleFolding X)
    (hfg : ∀ v, rf.f.morph.toFun v = v →
           rf.f.morph.toFun (rf.g.morph.toFun v) = v)
    (hgf : ∀ v, rf.g.morph.toFun v = v →
           rf.g.morph.toFun (rf.f.morph.toFun v) = v)
    (hcover : ∀ v, rf.f.morph.toFun v = v ∨ rf.g.morph.toFun v = v) :
    ∀ v, reflectionFun rf (reflectionFun rf v) = v := by
  intro v; simp only [reflectionFun]
  rcases hcover v with hfv | hgv
  ·
    simp [hfv]
    by_cases hgv' : rf.f.morph.toFun (rf.g.morph.toFun v) = rf.g.morph.toFun v
    ·
      have : rf.g.morph.toFun v = v := by
        have h1 := hfg v hfv; rw [hgv'] at h1; exact h1
      simp [this, hfv]
    ·
      simp [hgv']; exact hfg v hfv
  ·
    by_cases hfv : rf.f.morph.toFun v = v
    ·
      simp [hfv, hgv]
    ·
      simp [hfv, show rf.f.morph.toFun (rf.f.morph.toFun v) = rf.f.morph.toFun v from
        rf.f.idempotent v]
      exact hgf v hgv

/-- A *wall reflection*: a reversible folding equipped with the cross-fixing and cover axioms
needed to make its associated reflection a well-defined involution. -/
structure WallReflection (X : ChamberComplex V) where
  rf : ReversibleFolding X
  fg_id : ∀ v, rf.f.morph.toFun v = v → rf.f.morph.toFun (rf.g.morph.toFun v) = v
  gf_id : ∀ v, rf.g.morph.toFun v = v → rf.g.morph.toFun (rf.f.morph.toFun v) = v
  cover : ∀ v, rf.f.morph.toFun v = v ∨ rf.g.morph.toFun v = v

namespace WallReflection

variable (s : WallReflection X)

/-- The reflection map of a wall reflection. -/
def refl : V → V := reflectionFun s.rf

/-- The wall (fixed set) of a wall reflection, viewed as a set of faces. -/
def wall : Set (Finset V) := Wall X s.rf.f

/-- The wall reflection $\rho$ is an involution: $\rho \circ \rho = \mathrm{id}$. -/
theorem refl_involutive : ∀ v, s.refl (s.refl v) = v :=
  reflection_involutive s.rf s.fg_id s.gf_id s.cover

/-- The wall reflection is injective. -/
theorem refl_injective : Function.Injective s.refl := by
  intro a b hab
  have := congr_arg s.refl hab
  rwa [s.refl_involutive a, s.refl_involutive b] at this

/-- The wall reflection is surjective. -/
theorem refl_surjective : Function.Surjective s.refl :=
  fun b => ⟨s.refl b, s.refl_involutive b⟩

/-- The wall reflection is bijective. -/
theorem refl_bijective : Function.Bijective s.refl :=
  ⟨s.refl_injective, s.refl_surjective⟩

end WallReflection

/-- Thinness implies the "at most two chambers per facet" property used by the uniqueness
lemma. -/
lemma thin_implies_atMostTwo (hThin : X.IsThin) :
    SimplicialComplex.AtMostTwoChambers X.toSimplicialComplex := by
  intro F C D E hFC hCmax hFD hDmax hDne hFE hEmax hEne
  obtain ⟨D', ⟨_, _, _⟩, hD'uniq⟩ := hThin F C hFC hCmax
  have hD_eq : D = D' := hD'uniq D ⟨hDne, hFD, hDmax⟩
  have hE_eq : E = D' := hD'uniq E ⟨hEne, hFE, hEmax⟩
  rw [hD_eq, hE_eq]

end ChamberComplex
