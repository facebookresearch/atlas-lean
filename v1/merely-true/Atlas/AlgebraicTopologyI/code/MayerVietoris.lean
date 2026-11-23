/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section11

open Set Topology EilenbergSteenrod Function

universe u

namespace MayerVietoris

/-- A Mayer-Vietoris cover of a space: a two-element family `{A, B}` of subsets of `X`
whose interiors cover `X`. This is the input data for Theorem 11.5. -/
structure MayerVietorisCover where
  X : Type u
  instTop : TopologicalSpace X
  A : Set X
  B : Set X
  cover : interior A ∪ interior B = univ

attribute [instance] MayerVietorisCover.instTop

/-- The trivial pair `(X, ∅)` associated to the ambient space of a Mayer-Vietoris cover. -/
def MayerVietorisCover.pairX (c : MayerVietorisCover) : TopPair := TopPair.ofSpace c.X
/-- The trivial pair `(A, ∅)` associated to the first cover element. -/
def MayerVietorisCover.pairA (c : MayerVietorisCover) : TopPair := TopPair.ofSpace c.A
/-- The trivial pair `(B, ∅)` associated to the second cover element. -/
def MayerVietorisCover.pairB (c : MayerVietorisCover) : TopPair := TopPair.ofSpace c.B
/-- The trivial pair `(A ∩ B, ∅)` associated to the intersection of the cover elements. -/
def MayerVietorisCover.pairAB (c : MayerVietorisCover) : TopPair :=
  TopPair.ofSpace (c.A ∩ c.B : Set c.X)

/-- The inclusion of pairs `(A ∩ B, ∅) ↪ (A, ∅)`, which underlies the map
`j_1 : H_n(A ∩ B) → H_n(A)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclAB_A (c : MayerVietorisCover) : MapOfPairs c.pairAB c.pairA where
  toFun := fun x => ⟨x.1, x.2.1⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(A ∩ B, ∅) ↪ (B, ∅)`, which underlies the map
`j_2 : H_n(A ∩ B) → H_n(B)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclAB_B (c : MayerVietorisCover) : MapOfPairs c.pairAB c.pairB where
  toFun := fun x => ⟨x.1, x.2.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(A, ∅) ↪ (X, ∅)`, which underlies the map
`i_1 : H_n(A) → H_n(X)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclA_X (c : MayerVietorisCover) : MapOfPairs c.pairA c.pairX where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(B, ∅) ↪ (X, ∅)`, which underlies the map
`i_2 : H_n(B) → H_n(X)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclB_X (c : MayerVietorisCover) : MapOfPairs c.pairB c.pairX where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ h => h.elim

/-- The Mayer-Vietoris long exact sequence for a homology theory `h` and a cover `c`
(Theorem 11.5): connecting homomorphisms `∂ : H_{n+1}(X) →+ H_n(A ∩ B)` together with
exactness of the long sequence
`⋯ → H_n(A ∩ B) → H_n(A) ⊕ H_n(B) → H_n(X) → H_{n-1}(A ∩ B) → ⋯`,
where the first map is `[j_{1*}, -j_{2*}]` and the second is `i_{1*} + i_{2*}`. -/
structure MayerVietorisSequence (h : HomologyTheory) (c : MayerVietorisCover) where
  connecting : ∀ (n : ℤ), h.H (n + 1) c.pairX →+ h.H n c.pairAB
  exact_at_prod : ∀ (n : ℤ),
    Exact
      (fun x => (h.map n c.inclAB_A x, -(h.map n c.inclAB_B x)))
      (fun p : h.H n c.pairA × h.H n c.pairB =>
        h.map n c.inclA_X p.1 + h.map n c.inclB_X p.2)
  exact_at_X : ∀ (n : ℤ),
    Exact
      (fun p : h.H (n + 1) c.pairA × h.H (n + 1) c.pairB =>
        h.map (n + 1) c.inclA_X p.1 + h.map (n + 1) c.inclB_X p.2)
      (connecting n)
  exact_at_AB : ∀ (n : ℤ),
    Exact
      (connecting n)
      (fun x => (h.map n c.inclAB_A x, -(h.map n c.inclAB_B x)))

/-- The pair `(X, A)` extracted from a Mayer-Vietoris cover, used as the input to the
excision axiom that drives the construction of the connecting homomorphism. -/
def MayerVietorisCover.pairXA (c : MayerVietorisCover) : TopPair where
  space := c.X
  instTop := c.instTop
  sub := c.A

/-- The complement of `B` is an excisive subset of the pair `(X, A)`: its closure lies
in the interior of `A`. This is the geometric input that lets us apply excision when
building the Mayer-Vietoris connecting homomorphism. -/
lemma MayerVietorisCover.excisive (c : MayerVietorisCover) :
    IsExcisiveTriple c.pairXA (c.Bᶜ) where
  sub_mem := by
    intro x hx
    have hmem := Set.eq_univ_iff_forall.mp c.cover x
    exact hmem.elim (fun h => interior_subset h) (fun hB => absurd (interior_subset hB) hx)
  closure_sub_interior := by
    rw [closure_compl]
    intro x hx
    simp only [Set.mem_compl_iff] at hx
    exact (Set.eq_univ_iff_forall.mp c.cover x).resolve_right hx

/-- The excised pair `(X \ Bᶜ, A \ Bᶜ)`, abbreviated `EP`, used as the intermediate
pair through which the connecting homomorphism is factored. -/
abbrev MayerVietorisCover.EP (c : MayerVietorisCover) : TopPair :=
  c.pairXA.excisePair c.Bᶜ

/-- The homeomorphism of pairs from the sub-pair of `EP` to `(A ∩ B, ∅)`: each point of
the excised subspace lies in `A` (by sub-pair membership) and in `B` (since it is not
in `Bᶜ`). -/
def MayerVietorisCover.trSub (c : MayerVietorisCover) : MapOfPairs c.EP.subPair c.pairAB where
  toFun := fun p => ⟨p.1.1, ⟨p.2, not_not.mp p.1.2⟩⟩
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  mapsTo := fun _ h => h.elim

/-- Inverse to `trSub`: each point of `A ∩ B` lies outside `Bᶜ`, hence in the sub-pair
of the excised pair `EP`. -/
def MayerVietorisCover.trSubInv (c : MayerVietorisCover) : MapOfPairs c.pairAB c.EP.subPair where
  toFun := fun p => ⟨⟨p.1, not_not.mpr p.2.2⟩, p.2.1⟩
  continuous_toFun := (Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _)
  mapsTo := fun _ h => h.elim

/-- The homeomorphism of pairs from the total-space pair of `EP` to `(B, ∅)`: a point
of `X` that lies outside `Bᶜ` is the same data as a point of `B`. -/
def MayerVietorisCover.trSp (c : MayerVietorisCover) :
    MapOfPairs (TopPair.ofSpace c.EP.space) c.pairB where
  toFun := fun p => ⟨p.1, not_not.mp p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- Inverse to `trSp`: a point of `B` corresponds to the point of `X` lying outside
`Bᶜ` in the total space of the excised pair. -/
def MayerVietorisCover.trSpInv (c : MayerVietorisCover) :
    MapOfPairs c.pairB (TopPair.ofSpace c.EP.space) where
  toFun := fun p => ⟨p.1, not_not.mpr p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- The constant homotopy from a self-map of a pair `f : P → P` that acts as the
identity on points (`f x = x`) to the identity map of `P`. -/
def constHomotopy {P : TopPair} (f : MapOfPairs P P) (hf : ∀ x, f.toFun x = x) :
    HomotopyOfPairMaps f (MapOfPairs.id P) where
  toFun := fun ⟨x, _⟩ => x
  continuous_toFun := continuous_fst
  map_zero := fun x => (hf x).symm
  map_one := fun _ => rfl
  mapsTo := fun _ ha _ => ha

/-- `trSub` and `trSubInv` compose (one way) to the identity of `(A ∩ B, ∅)`, up to
homotopy of pair maps. -/
lemma MayerVietorisCover.trSub_comp_inv_htpy (c : MayerVietorisCover) :
    AreHomotopic (c.trSub.comp c.trSubInv) (MapOfPairs.id c.pairAB) :=
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSub, trSubInv])⟩

/-- `trSub` and `trSubInv` compose (the other way) to the identity of `EP.subPair`,
up to homotopy of pair maps. -/
lemma MayerVietorisCover.trSubInv_comp_htpy (c : MayerVietorisCover) :
    AreHomotopic (c.trSubInv.comp c.trSub) (MapOfPairs.id c.EP.subPair) :=
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSub, trSubInv])⟩

/-- `trSp` and `trSpInv` compose (one way) to the identity of `(B, ∅)`, up to homotopy
of pair maps. -/
lemma MayerVietorisCover.trSp_comp_inv_htpy (c : MayerVietorisCover) :
    AreHomotopic (c.trSp.comp c.trSpInv) (MapOfPairs.id c.pairB) :=
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSp, trSpInv])⟩

/-- `trSp` and `trSpInv` compose (the other way) to the identity of the total-space
pair of `EP`, up to homotopy. -/
lemma MayerVietorisCover.trSpInv_comp_htpy (c : MayerVietorisCover) :
    AreHomotopic (c.trSpInv.comp c.trSp) (MapOfPairs.id (TopPair.ofSpace c.EP.space)) :=
  ⟨constHomotopy _ (fun x => by simp [MapOfPairs.comp, trSp, trSpInv])⟩

/-- If `g ∘ f` is homotopic to the identity, then on a homology theory `ht.map n g`
is a left inverse of `ht.map n f`, by homotopy invariance and functoriality. -/
lemma hom_inv_id (ht : HomologyTheory) (n : ℤ)
    {P Q : TopPair} (f : MapOfPairs P Q) (g : MapOfPairs Q P)
    (hgf : AreHomotopic (g.comp f) (MapOfPairs.id P)) :
    ∀ x, (ht.map n g) ((ht.map n f) x) = x := by
  have h2 : (ht.map n g).comp (ht.map n f) = AddMonoidHom.id _ := by
    rw [← ht.map_comp, ht.homotopy_invariance n _ _ hgf, ht.map_id]
  intro x; exact congr_fun (congr_arg DFunLike.coe h2) x |>.symm ▸ rfl

/-- If `f` and `g` are pair maps whose compositions are both homotopic to the identity,
then `ht.map n f` is a bijection. This packages the homotopy equivalence into a
bijection on homology, used to transfer information across the excised pair. -/
lemma transfer_bijective (ht : HomologyTheory) (n : ℤ)
    {P Q : TopPair} (f : MapOfPairs P Q) (g : MapOfPairs Q P)
    (hfg : AreHomotopic (f.comp g) (MapOfPairs.id Q))
    (hgf : AreHomotopic (g.comp f) (MapOfPairs.id P)) :
    Bijective (ht.map n f) := by
  constructor
  · intro x y hxy
    have hx := hom_inv_id ht n f g hgf x
    have hy := hom_inv_id ht n f g hgf y
    rw [← hx, ← hy, hxy]
  · intro y
    exact ⟨ht.map n g y, by
      have := hom_inv_id ht n g f hfg y; simpa using this⟩

/-- The two ways of including `A ∩ B` into `X` (via `A` and via `B`) agree as pair maps. -/
lemma MayerVietorisCover.inclA_X_comp_inclAB_A_eq (c : MayerVietorisCover) :
    c.inclA_X.comp c.inclAB_A = c.inclB_X.comp c.inclAB_B := rfl

/-- The inclusion `(A ∩ B, ∅) ↪ (B, ∅)` factors as the round-trip
`(A ∩ B, ∅) → EP.subPair ↪ EP.space → (B, ∅)` through the excised pair. -/
lemma MayerVietorisCover.inclAB_B_comp_eq (c : MayerVietorisCover) :
    c.trSp.comp ((inclusionSubToSpace c.EP).comp c.trSubInv) = c.inclAB_B := rfl

/-- The restriction of the excision inclusion to subspaces factors as
`trSub` followed by `inclAB_A`. -/
lemma MayerVietorisCover.exc_restrictToSub_eq (c : MayerVietorisCover) :
    (excisionInclusion c.pairXA c.Bᶜ).restrictToSub = c.inclAB_A.comp c.trSub := rfl

/-- The composite `(B, ∅) ↪ (X, ∅) ↪ (X, A)` agrees with the composite that goes
through the excised pair `EP` via `trSpInv` and the excision inclusion. -/
lemma MayerVietorisCover.comm2_eq (c : MayerVietorisCover) :
    (inclusionSpaceToPair c.pairXA).comp c.inclB_X =
    (excisionInclusion c.pairXA c.Bᶜ).comp ((inclusionSpaceToPair c.EP).comp c.trSpInv) := rfl

/-- Exactness transfer along bijective homomorphisms: if `f, g` form an exact sequence at
`B`, `ψ : B ≃+ B'` is a two-sided inverse pair, and `χ : C →+ C'` is injective, then
`(ψ ∘ f, χ ∘ g ∘ ψ⁻¹)` is exact at `B'`. Used to push exactness across the
homotopy equivalences `trSub`, `trSp` in the Mayer-Vietoris construction. -/
lemma exact_transfer_bij {A B C B' C' : Type*}
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup B'] [AddCommGroup C']
    {f : A → B} {g : B → C}
    (he : Exact f g)
    (ψ : B →+ B') (ψ' : B' →+ B) (hψψ' : ∀ y, ψ (ψ' y) = y) (hψ'ψ : ∀ x, ψ' (ψ x) = x)
    (χ : C →+ C') (hχ_inj : Injective χ) :
    Exact (ψ ∘ f) (fun y' => χ (g (ψ' y'))) := by
  intro y'
  constructor
  · intro hy'
    have h1 : g (ψ' y') = 0 := hχ_inj (by rwa [map_zero])
    obtain ⟨x, hx⟩ := (he _).mp h1
    exact ⟨x, show ψ (f x) = y' by rw [hx, hψψ']⟩
  · rintro ⟨x, rfl⟩
    show χ (g (ψ' (ψ (f x)))) = 0
    rw [hψ'ψ, (he (f x)).mpr ⟨x, rfl⟩, map_zero]

/-- The Mayer-Vietoris long exact sequence (Theorem 11.5): from any Eilenberg-Steenrod
homology theory `h` and a cover `c = {A, B}` of `X` by sets whose interiors cover, we
construct the connecting homomorphism `∂` and the three exactness statements assembling
into the long exact sequence
`⋯ → H_n(A ∩ B) → H_n(A) ⊕ H_n(B) → H_n(X) → H_{n-1}(A ∩ B) → ⋯`. The proof factors
the boundary `H_{n+1}(X) → H_n(A ∩ B)` through the long exact sequence of the pair
`(X, A)` and the excised pair, using the homotopy equivalences `trSub`, `trSp`. -/
noncomputable def mayer_vietoris_sequence
    (h : HomologyTheory) (c : MayerVietorisCover) :
    MayerVietorisSequence h c := by
  let EP := c.EP
  have exc_bij : ∀ n, Bijective (h.map n (excisionInclusion c.pairXA c.Bᶜ)) :=
    fun n => h.excision n c.pairXA c.Bᶜ c.excisive
  let excEquiv (n : ℤ) : h.H n EP ≃+ h.H n c.pairXA :=
    AddEquiv.ofBijective (h.map n (excisionInclusion c.pairXA c.Bᶜ)) (exc_bij n)
  have trSub_bij (n : ℤ) : Bijective (h.map n c.trSub) :=
    transfer_bijective h n c.trSub c.trSubInv c.trSub_comp_inv_htpy c.trSubInv_comp_htpy
  have trSp_bij (n : ℤ) : Bijective (h.map n c.trSp) :=
    transfer_bijective h n c.trSp c.trSpInv c.trSp_comp_inv_htpy c.trSpInv_comp_htpy

  have trSub_inv : ∀ n x, (h.map n c.trSub) ((h.map n c.trSubInv) x) = x :=
    fun n => hom_inv_id h n c.trSubInv c.trSub c.trSub_comp_inv_htpy
  have trSubInv_inv : ∀ n x, (h.map n c.trSubInv) ((h.map n c.trSub) x) = x :=
    fun n => hom_inv_id h n c.trSub c.trSubInv c.trSubInv_comp_htpy
  have trSp_inv : ∀ n x, (h.map n c.trSp) ((h.map n c.trSpInv) x) = x :=
    fun n => hom_inv_id h n c.trSpInv c.trSp c.trSp_comp_inv_htpy
  have trSpInv_inv : ∀ n x, (h.map n c.trSpInv) ((h.map n c.trSp) x) = x :=
    fun n => hom_inv_id h n c.trSp c.trSpInv c.trSpInv_comp_htpy

  let conn (n : ℤ) : h.H (n + 1) c.pairX →+ h.H n c.pairAB :=
    (h.map n c.trSub).comp ((h.boundary n EP).comp ((excEquiv (n + 1)).symm.toAddMonoidHom.comp
      (h.map (n + 1) (inclusionSpaceToPair c.pairXA))))

  let j' (n : ℤ) : h.H n c.pairB →+ h.H n EP :=
    (h.map n (inclusionSpaceToPair EP)).comp (h.map n c.trSpInv)
  let d'prev (n : ℤ) : h.H (n + 1) EP →+ h.H n c.pairAB :=
    (h.map n c.trSub).comp (h.boundary n EP)

  have comm_kh : ∀ n x, h.map n c.inclA_X (h.map n c.inclAB_A x) =
      h.map n c.inclB_X (h.map n c.inclAB_B x) := by
    intro n x
    have := congr_arg (fun f => (h.map n f) x) c.inclA_X_comp_inclAB_A_eq
    simp only [h.map_comp] at this; exact this
  have comm_jf : ∀ n x, h.map n (inclusionSpaceToPair c.pairXA) (h.map n c.inclB_X x) =
      (excEquiv n) (j' n x) := by
    intro n x
    have := congr_arg (fun f => (h.map n f) x) c.comm2_eq
    simp only [h.map_comp] at this
    simp only [AddMonoidHom.comp_apply] at this; exact this
  have comm_dg : ∀ n x, h.boundary n c.pairXA ((excEquiv (n + 1)) x) =
      h.map n c.inclAB_A (d'prev n x) := by
    intro n x
    show h.boundary n c.pairXA (h.map (n + 1) (excisionInclusion c.pairXA c.Bᶜ) x) =
      h.map n c.inclAB_A ((h.map n c.trSub) (h.boundary n EP x))
    have nat := h.boundary_natural n (excisionInclusion c.pairXA c.Bᶜ)
    have := congr_fun (congr_arg DFunLike.coe nat) x
    simp only [AddMonoidHom.comp_apply] at this
    rw [← this, c.exc_restrictToSub_eq]
    have mc := h.map_comp n c.trSub c.inclAB_A
    exact congr_fun (congr_arg DFunLike.coe mc) ((h.boundary n EP) x)


  have inclAB_B_decomp : ∀ n y,
      (h.map n c.inclAB_B) y =
      (h.map n c.trSp) ((h.map n (inclusionSubToSpace EP)) ((h.map n c.trSubInv) y)) := by
    intro n y
    have := congr_arg (fun f => (h.map n f) y) c.inclAB_B_comp_eq.symm
    simp only [h.map_comp, AddMonoidHom.comp_apply] at this; exact this
  have bot_exact_sub : ∀ n, Exact (d'prev n) (h.map n c.inclAB_B) := by
    intro n y
    rw [inclAB_B_decomp]
    have he := exact_transfer_bij (h.exact_at_sub n EP)
      (h.map n c.trSub) (h.map n c.trSubInv) (trSub_inv n) (trSubInv_inv n)
      (h.map n c.trSp) (trSp_bij n).1
    exact he y
  have bot_exact_sp : ∀ n, Exact (h.map n c.inclAB_B) (j' n) := by
    intro n y
    constructor
    ·
      intro hy


      have hsp : (h.map n (inclusionSpaceToPair EP)) ((h.map n c.trSpInv) y) = 0 := hy
      obtain ⟨z, hz⟩ := (h.exact_at_space n EP ((h.map n c.trSpInv) y)).mp hsp


      refine ⟨(h.map n c.trSub) z, ?_⟩
      rw [inclAB_B_decomp, trSubInv_inv, hz, trSp_inv]
    ·
      rintro ⟨x, rfl⟩
      show (h.map n (inclusionSpaceToPair EP)) ((h.map n c.trSpInv) ((h.map n c.inclAB_B) x)) = 0
      rw [inclAB_B_decomp, trSpInv_inv n ((h.map n (inclusionSubToSpace EP)) _)]
      exact (h.exact_at_space n EP _).mpr ⟨(h.map n c.trSubInv) x, rfl⟩
  have bot_exact_pair : ∀ n, Exact (j' (n + 1)) (d'prev n) := by
    intro n y
    constructor
    ·
      intro hy

      have hbd : (h.boundary n EP) y = 0 := (trSub_bij n).1 (by rw [map_zero]; exact hy)

      obtain ⟨z, hz⟩ := (h.exact_at_pair n EP y).mp hbd


      exact ⟨(h.map (n + 1) c.trSp) z, by show (h.map (n+1) (inclusionSpaceToPair EP)) ((h.map (n+1) c.trSpInv) ((h.map (n+1) c.trSp) z)) = y; rw [trSpInv_inv, hz]⟩
    ·
      rintro ⟨x, rfl⟩
      show (h.map n c.trSub) ((h.boundary n EP) ((h.map (n + 1) (inclusionSpaceToPair EP)) ((h.map (n + 1) c.trSpInv) x))) = 0
      rw [(h.exact_at_pair n EP _).mpr ⟨(h.map (n + 1) c.trSpInv) x, rfl⟩, map_zero]
  refine ⟨conn, ?_, ?_, ?_⟩
  · intro n
    exact exact_at_prod (h.map n c.inclA_X) (h.map n (inclusionSpaceToPair c.pairXA))
      (h.map n c.inclAB_B) (j' n) (h.map n c.inclAB_A) (h.map n c.inclB_X) (excEquiv n)
      (h.boundary n c.pairXA) (d'prev n) (excEquiv (n + 1))
      (h.exact_at_space n c.pairXA) (bot_exact_sp n) (h.exact_at_sub n c.pairXA) (bot_exact_sub n)
      (comm_kh n) (fun x => comm_jf n x) (fun x => comm_dg n x)
  · intro n
    exact exact_at_A (h.map (n + 1) c.inclA_X) (h.map (n + 1) (inclusionSpaceToPair c.pairXA))
      (j' (n + 1)) (d'prev n) (h.map (n + 1) c.inclB_X) (excEquiv (n + 1))
      (h.exact_at_space (n + 1) c.pairXA) (bot_exact_pair n) (fun x => comm_jf (n + 1) x)
  · intro n
    exact exact_at_C' (h.map (n + 1) (inclusionSpaceToPair c.pairXA)) (h.boundary n c.pairXA)
      (h.map n c.inclAB_B) (d'prev n) (h.map n c.inclAB_A) (excEquiv (n + 1))
      (h.exact_at_pair n c.pairXA) (bot_exact_sub n) (fun x => comm_dg n x)

end MayerVietoris
