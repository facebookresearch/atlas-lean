/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section1
import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Exact
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Prod

open Set Topology

universe u

namespace EilenbergSteenrod

/-- A pair of topological spaces `(X, A)`: a space `X` (the carrier `space` with topology
`instTop`) together with a subset `A ⊆ X` (called `sub`). Pairs of spaces are the objects of
the category `Top₂` on which a homology theory is defined. -/
structure TopPair where
  space : Type u
  instTop : TopologicalSpace space
  sub : Set space

attribute [instance] TopPair.instTop

/-- The pair `(X, ∅)` associated with a topological space `X`, viewing an absolute space
as a relative one with empty subspace. -/
def TopPair.ofSpace (X : Type u) [TopologicalSpace X] : TopPair := ⟨X, ‹_›, ∅⟩

/-- The pair `(A, ∅)` obtained by regarding the subspace `A` of a pair `P = (X, A)` as
a standalone space. This is used to express the boundary map `Hₙ(X, A) → Hₙ₋₁(A)`. -/
def TopPair.subPair (P : TopPair) : TopPair := TopPair.ofSpace P.sub

/-- The one-point pair `(*, ∅)`, used as the test object for the dimension axiom of a
homology theory. -/
def TopPair.point : TopPair.{u} := TopPair.ofSpace PUnit.{u + 1}

/-- Given a pair `P = (X, A)` and a subset `U ⊆ X`, the excised pair `(X − U, A − U)`. This
is the source of the excision inclusion `(X − U, A − U) ↪ (X, A)`. -/
def TopPair.excisePair (P : TopPair) (U : Set P.space) : TopPair where
  space := (Uᶜ : Set P.space)
  instTop := instTopologicalSpaceSubtype
  sub := Subtype.val ⁻¹' P.sub

/-- The pair `(∐ᵢ Xᵢ, ∅)` formed by the disjoint union of a family of spaces, used to state
the Milnor (coproduct) axiom of a homology theory. -/
def TopPair.coproduct (ι : Type u) (X : ι → Type u) [∀ i, TopologicalSpace (X i)] :
    TopPair := TopPair.ofSpace (Σ i, X i)

/-- A morphism of pairs `(X, A) → (Y, B)`: a continuous map `f : X → Y` such that
`f(A) ⊆ B`. These are the morphisms in the category of pairs. -/
structure MapOfPairs (P Q : TopPair) where
  toFun : P.space → Q.space
  continuous_toFun : Continuous toFun
  mapsTo : MapsTo toFun P.sub Q.sub

/-- The identity morphism on a pair `(X, A)`. -/
def MapOfPairs.id (P : TopPair) : MapOfPairs P P where
  toFun := _root_.id
  continuous_toFun := continuous_id
  mapsTo := fun _ h => h

/-- Composition of morphisms of pairs. -/
def MapOfPairs.comp {P Q R : TopPair} (g : MapOfPairs Q R) (f : MapOfPairs P Q) :
    MapOfPairs P R where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  mapsTo := g.mapsTo.comp f.mapsTo

/-- The restriction of a map of pairs `f : (X, A) → (Y, B)` to the subspaces, producing
`f|_A : (A, ∅) → (B, ∅)`. Used to express naturality of the boundary map. -/
def MapOfPairs.restrictToSub {P Q : TopPair} (f : MapOfPairs P Q) :
    MapOfPairs P.subPair Q.subPair where
  toFun := fun a => ⟨f.toFun a.val, f.mapsTo a.property⟩
  continuous_toFun := Continuous.subtype_mk (f.continuous_toFun.comp continuous_subtype_val) _
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(A, ∅) ↪ (X, ∅)` arising from the subspace inclusion `A ⊆ X`.
This is the map `i` in the relative homology long exact sequence. -/
def inclusionSubToSpace (P : TopPair) : MapOfPairs P.subPair (TopPair.ofSpace P.space) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ h => h.elim

/-- The map of pairs `(X, ∅) → (X, A)` given by the identity on `X`. This is the
quotient-type map `j` in the relative long exact sequence. -/
def inclusionSpaceToPair (P : TopPair) : MapOfPairs (TopPair.ofSpace P.space) P where
  toFun := _root_.id
  continuous_toFun := continuous_id
  mapsTo := fun _ h => h.elim

/-- The excision inclusion of pairs `(X − U, A − U) ↪ (X, A)`. The excision axiom asserts
this map induces an isomorphism in homology whenever the triple `(X, A, U)` is excisive. -/
def excisionInclusion (P : TopPair) (U : Set P.space) :
    MapOfPairs (P.excisePair U) P where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun ⟨_, _⟩ hx => hx

/-- The inclusion of the `i`-th summand `Xᵢ ↪ ∐ⱼ Xⱼ` of a coproduct of spaces, as a map of
pairs. These maps assemble into the Milnor (coproduct) axiom isomorphism. -/
def coproductInclusion (ι : Type u) (X : ι → Type u) [∀ j, TopologicalSpace (X j)] (i : ι) :
    MapOfPairs (TopPair.ofSpace (X i)) (TopPair.coproduct ι X) where
  toFun := Sigma.mk i
  continuous_toFun := continuous_sigmaMk
  mapsTo := fun _ h => h.elim

/-- A homotopy of pair maps `f₀, f₁ : (X, A) → (Y, B)`: a continuous map
`h : X × I → Y` interpolating from `f₀` to `f₁` such that `h(A × I) ⊆ B` at every time. -/
structure HomotopyOfPairMaps {P Q : TopPair} (f₀ f₁ : MapOfPairs P Q) where
  toFun : P.space × unitInterval → Q.space
  continuous_toFun : Continuous toFun
  map_zero : ∀ x, toFun (x, ⟨0, unitInterval.zero_mem⟩) = f₀.toFun x
  map_one : ∀ x, toFun (x, ⟨1, unitInterval.one_mem⟩) = f₁.toFun x
  mapsTo : ∀ (a : P.space), a ∈ P.sub → ∀ (t : unitInterval), toFun (a, t) ∈ Q.sub

/-- Two maps of pairs are homotopic if there exists a homotopy of pair maps between them. -/
def AreHomotopic {P Q : TopPair} (f₀ f₁ : MapOfPairs P Q) : Prop :=
  Nonempty (HomotopyOfPairMaps f₀ f₁)

/-- A triple `(X, A, U)` with `U ⊆ A ⊆ X` is *excisive* if the closure of `U` lies inside
the interior of `A` (Definition 10.1). For such a triple, the excision inclusion
`(X − U, A − U) ↪ (X, A)` is required to be a homology isomorphism. -/
structure IsExcisiveTriple (P : TopPair) (U : Set P.space) : Prop where
  sub_mem : U ⊆ P.sub
  closure_sub_interior : closure U ⊆ interior P.sub

/-- **Definition 11.1 (Eilenberg–Steenrod axioms).** A homology theory on `Top` consists of
a sequence of functors `Hₙ : Top₂ → Ab` (`n ∈ ℤ`) together with natural boundary maps
`∂ : Hₙ(X, A) → Hₙ₋₁(A, ∅)` satisfying:

1. **Homotopy invariance** — homotopic maps of pairs induce equal maps on `Hₙ`.
2. **Excision** — excisive inclusions induce isomorphisms in homology.
3. **Long exact sequence** — for every pair `(X, A)` the sequence
   `⋯ → Hₙ(A) → Hₙ(X) → Hₙ(X, A) → Hₙ₋₁(A) → ⋯` is exact.
4. **Dimension axiom** — `Hₙ(pt)` vanishes for `n ≠ 0`.
5. **Milnor (additivity) axiom** — for any disjoint union `∐ᵢ Xᵢ`, the canonical map
   `⨁ᵢ Hₙ(Xᵢ) → Hₙ(∐ᵢ Xᵢ)` is an isomorphism. -/
structure HomologyTheory where
  H : ℤ → TopPair → Type u
  instAddCommGroup : ∀ (n : ℤ) (P : TopPair), AddCommGroup (H n P)
  map : ∀ (n : ℤ) {P Q : TopPair}, MapOfPairs P Q → (H n P →+ H n Q)
  map_id : ∀ (n : ℤ) (P : TopPair), map n (MapOfPairs.id P) = AddMonoidHom.id (H n P)
  map_comp : ∀ (n : ℤ) {P Q R : TopPair} (f : MapOfPairs P Q) (g : MapOfPairs Q R),
    map n (g.comp f) = (map n g).comp (map n f)
  boundary : ∀ (n : ℤ) (P : TopPair), H (n + 1) P →+ H n P.subPair
  boundary_natural : ∀ (n : ℤ) {P Q : TopPair} (f : MapOfPairs P Q),
    (map n f.restrictToSub).comp (boundary n P) = (boundary n Q).comp (map (n + 1) f)
  homotopy_invariance : ∀ (n : ℤ) {P Q : TopPair} (f₀ f₁ : MapOfPairs P Q),
    AreHomotopic f₀ f₁ → map n f₀ = map n f₁
  excision : ∀ (n : ℤ) (P : TopPair) (U : Set P.space),
    IsExcisiveTriple P U → Function.Bijective (map n (excisionInclusion P U))
  exact_at_sub : ∀ (n : ℤ) (P : TopPair),
    Function.Exact (boundary n P) (map n (inclusionSubToSpace P))
  exact_at_space : ∀ (n : ℤ) (P : TopPair),
    Function.Exact (map n (inclusionSubToSpace P)) (map n (inclusionSpaceToPair P))
  exact_at_pair : ∀ (n : ℤ) (P : TopPair),
    Function.Exact (map (n + 1) (inclusionSpaceToPair P)) (boundary n P)
  dimension : ∀ (n : ℤ), n ≠ 0 → Subsingleton (H n TopPair.point)
  coproduct : ∀ (n : ℤ) {ι : Type u} [DecidableEq ι] (X : ι → Type u)
    [∀ i, TopologicalSpace (X i)],
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => H n (TopPair.ofSpace (X i)))
        (fun i => map n (coproductInclusion ι X i)))

attribute [instance] HomologyTheory.instAddCommGroup

end EilenbergSteenrod

variable {X : Type*} [TopologicalSpace X]

/-- **Definition 11.2 (Cover).** A family `𝒜` of subsets of a topological space `X` is a
*cover* if the union of the interiors of its members equals all of `X`. -/
def IsCover (𝒜 : Set (Set X)) : Prop :=
  ⋃₀ (interior '' 𝒜) = Set.univ

/-- Pointwise reformulation of `IsCover`: a family `𝒜` covers `X` iff every point of `X`
lies in the interior of some member of `𝒜`. -/
lemma isCover_iff (𝒜 : Set (Set X)) :
    IsCover 𝒜 ↔ ∀ x : X, ∃ A ∈ 𝒜, x ∈ interior A := by
  simp [IsCover, Set.eq_univ_iff_forall]

namespace AlgebraicTopologyI

/-- **Definition 11.3 (𝒜-small simplex).** Given a cover `𝒜` of `X`, a singular `n`-simplex
`σ : Δⁿ → X` is *𝒜-small* if its image lies entirely in some `A ∈ 𝒜`. -/
def IsSmall {n : ℕ} (𝒜 : Set (Set X)) (σ : SingularSimplex n X) : Prop :=
  ∃ A ∈ 𝒜, Set.range (show C(↥(stdSimplex ℝ (Fin (n + 1))), X) from σ) ⊆ A

end AlgebraicTopologyI

namespace MayerVietoris

open Function

/-- Exactness at the middle term `C × A'` in the Mayer–Vietoris–style sequence of
Lemma 11.6. Given two horizontal exact sequences related by a ladder of vertical maps with
the indicated commutation properties, the composite
`c' ↦ (h c', −k' c')` followed by `(c, a') ↦ k c + f a'` is exact at `C × A'`. -/
theorem exact_at_prod
    {A B C A' B' C' Bprev Bprev' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [AddCommGroup Bprev] [AddCommGroup Bprev']
    (k : C →+ A) (j : A →+ B)
    (k' : C' →+ A') (j' : A' →+ B')
    (h : C' →+ C) (f : A' →+ A) (g : B' ≃+ B)
    (dprev : Bprev →+ C) (d'prev : Bprev' →+ C')
    (gprev : Bprev' ≃+ Bprev)
    (exact_A_top : Exact k j)
    (exact_A'_bot : Exact k' j')
    (exact_C_top : Exact dprev k)
    (exact_C'_bot : Exact d'prev k')
    (comm1 : ∀ x, k (h x) = f (k' x))
    (comm2 : ∀ x, j (f x) = g (j' x))
    (comm_prev : ∀ x, dprev (gprev x) = h (d'prev x)) :
    Exact
      (fun x : C' => (h x, -k' x) : C' → C × A')
      (fun p : C × A' => k p.1 + f p.2 : C × A' → A) := by
  intro ⟨c, a'⟩
  simp only
  constructor
  · intro heq
    have hjkc : j (k c) = 0 := by rw [exact_A_top]; exact ⟨c, rfl⟩
    have hjfa : j (f a') = 0 := by
      have := congr_arg j heq
      rw [map_add, hjkc, zero_add, map_zero] at this
      exact this
    have hj'a : j' a' = 0 := by
      have hgj' := (comm2 a').symm
      rw [hjfa] at hgj'
      exact g.injective (hgj'.trans (map_zero g).symm)
    rw [exact_A'_bot] at hj'a
    obtain ⟨y, hy⟩ := hj'a
    have hkc_eq : k (c + h y) = 0 := by rw [map_add, comm1, hy, heq]
    rw [exact_C_top] at hkc_eq
    obtain ⟨b, hb⟩ := hkc_eq
    have hb' : h (d'prev (gprev.symm b)) = c + h y := by
      rw [← comm_prev, AddEquiv.apply_symm_apply]; exact hb
    have hk'z : k' (d'prev (gprev.symm b)) = 0 := by
      rw [exact_C'_bot]; exact ⟨gprev.symm b, rfl⟩
    refine ⟨d'prev (gprev.symm b) - y, ?_⟩
    refine Prod.ext ?_ ?_
    · show h (d'prev (gprev.symm b) - y) = c
      rw [map_sub, hb']
      exact add_sub_cancel_right c (h y)
    · show -(k' (d'prev (gprev.symm b) - y)) = a'
      rw [map_sub, hk'z, zero_sub, neg_neg]
      exact hy
  · rintro ⟨x, hx⟩
    have h1 : h x = c := congr_arg Prod.fst hx
    have h2 : -k' x = a' := congr_arg Prod.snd hx
    rw [← h1, ← h2, map_neg, comm1, add_neg_cancel]

/-- Exactness at the term `A` of the Mayer–Vietoris–style sequence: the composite
`(c, a') ↦ k c + f a'` followed by the connecting map `a ↦ d'(g⁻¹(j a))` is exact at `A`. -/
theorem exact_at_A
    {A B C A' B' C₂' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C₂']
    (k : C →+ A) (j : A →+ B)
    (j' : A' →+ B') (d' : B' →+ C₂')
    (f : A' →+ A) (g : B' ≃+ B)
    (exact_A_top : Exact k j)
    (exact_B'_bot : Exact j' d')
    (comm2 : ∀ x, j (f x) = g (j' x)) :
    Exact
      (fun p : C × A' => k p.1 + f p.2)
      (fun a : A => d' (g.symm (j a))) := by
  intro a
  constructor
  · intro ha
    rw [exact_B'_bot (g.symm (j a))] at ha
    obtain ⟨a', ha'⟩ := ha
    have hja : j a = g (j' a') := by rw [ha']; exact (g.apply_symm_apply _).symm
    rw [← comm2 a'] at hja
    have hsub : j (a - f a') = 0 := by rw [map_sub, hja, sub_self]
    rw [exact_A_top] at hsub
    obtain ⟨c, hc⟩ := hsub
    refine ⟨(c, a'), ?_⟩
    show k c + f a' = a
    rw [hc]
    exact sub_add_cancel a (f a')
  · rintro ⟨⟨c, a'⟩, rfl⟩
    show d' (g.symm (j (k c + f a'))) = 0
    have hkc : j (k c) = 0 := by rw [exact_A_top]; exact ⟨c, rfl⟩
    have hd'j' : d' (j' a') = 0 := by rw [exact_B'_bot]; exact ⟨a', rfl⟩
    calc d' (g.symm (j (k c + f a')))
        = d' (g.symm (j (k c) + j (f a'))) := by rw [map_add]
      _ = d' (g.symm (0 + j (f a'))) := by rw [hkc]
      _ = d' (g.symm (j (f a'))) := by rw [zero_add]
      _ = d' (g.symm (g (j' a'))) := by rw [comm2]
      _ = d' (j' a') := by rw [g.symm_apply_apply]
      _ = 0 := hd'j'

/-- Exactness at the term `C'` of the Mayer–Vietoris–style sequence: the connecting map
`a ↦ d'(g⁻¹(j a))` followed by `c' ↦ (h c', −k' c')` is exact at `C'`. -/
theorem exact_at_C'
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (j : A →+ B) (dtop : B →+ C)
    (k' : C' →+ A') (d' : B' →+ C')
    (h : C' →+ C) (g : B' ≃+ B)
    (exact_B_top : Exact j dtop)
    (exact_C'_bot : Exact d' k')
    (comm3 : ∀ x, dtop (g x) = h (d' x)) :
    Exact
      (fun a : A => d' (g.symm (j a)))
      (fun x : C' => (h x, -k' x) : C' → C × A') := by
  intro x
  simp only [Prod.mk_eq_zero, neg_eq_zero]
  constructor
  · intro ⟨hx1, hx2⟩
    rw [exact_C'_bot] at hx2
    obtain ⟨b', hb'⟩ := hx2
    have hdtop : dtop (g b') = 0 := by rw [comm3, hb', hx1]
    rw [exact_B_top] at hdtop
    obtain ⟨a, ha⟩ := hdtop
    have hgsym : g.symm (j a) = b' := by rw [ha]; exact g.symm_apply_apply b'
    exact ⟨a, by show d' (g.symm (j a)) = x; rw [hgsym, hb']⟩
  · rintro ⟨a, ha⟩
    have ha' : d' (g.symm (j a)) = x := ha
    constructor
    · rw [← ha', ← comm3, g.apply_symm_apply]
      rw [exact_B_top]; exact ⟨a, rfl⟩
    · rw [← ha', exact_C'_bot]; exact ⟨g.symm (j a), rfl⟩

/-- **Lemma 11.6 (Mayer–Vietoris assembly).** Given two horizontal exact sequences linked by
a ladder of vertical maps satisfying the stated commutativity, the sequence
`⋯ → C'ₙ₊₁ → Cₙ₊₁ ⊕ A'ₙ → Aₙ → C'ₙ → ⋯`,
with morphisms `c' ↦ (h c', −k' c')`, `(c, a') ↦ k c + f a'`, and the connecting map
`a ↦ d'(g⁻¹(j a))`, is exact at each of `C × A'`, `A`, and `C'`. This is the
algebraic core of the Mayer–Vietoris theorem (Theorem 11.5). -/
theorem exact_sequence
    {Aprev Bprev Bprev' C C' A A' B B' Cnext' : Type*}
    [AddCommGroup Aprev] [AddCommGroup Bprev] [AddCommGroup Bprev']
    [AddCommGroup C] [AddCommGroup C']
    [AddCommGroup A] [AddCommGroup A']
    [AddCommGroup B] [AddCommGroup B']
    [AddCommGroup Cnext']
    (jprev : Aprev →+ Bprev) (dprev : Bprev →+ C) (k : C →+ A) (j : A →+ B)
    (d'prev : Bprev' →+ C') (k' : C' →+ A') (j' : A' →+ B') (d'next : B' →+ Cnext')
    (gprev : Bprev' ≃+ Bprev) (h : C' →+ C) (f : A' →+ A) (g : B' ≃+ B)
    (exact_jprev_dprev : Exact jprev dprev)
    (exact_dprev_k : Exact dprev k)
    (exact_k_j : Exact k j)
    (exact_d'prev_k' : Exact d'prev k')
    (exact_k'_j' : Exact k' j')
    (exact_j'_d'next : Exact j' d'next)
    (comm_kh : ∀ x, k (h x) = f (k' x))
    (comm_jf : ∀ x, j (f x) = g (j' x))
    (comm_dg : ∀ x, dprev (gprev x) = h (d'prev x)) :
    Exact (fun x : C' => (h x, -k' x) : C' → C × A')
          (fun p : C × A' => k p.1 + f p.2 : C × A' → A) ∧
    Exact (fun p : C × A' => k p.1 + f p.2)
          (fun a : A => d'next (g.symm (j a))) ∧
    Exact (fun a : Aprev => d'prev (gprev.symm (jprev a)))
          (fun x : C' => (h x, -k' x) : C' → C × A') :=
  ⟨exact_at_prod k j k' j' h f g dprev d'prev gprev
      exact_k_j exact_k'_j' exact_dprev_k exact_d'prev_k'
      comm_kh comm_jf comm_dg,
   exact_at_A k j j' d'next f g exact_k_j exact_j'_d'next comm_jf,
   exact_at_C' jprev dprev k' d'prev h gprev
      exact_jprev_dprev exact_d'prev_k' comm_dg⟩

end MayerVietoris
