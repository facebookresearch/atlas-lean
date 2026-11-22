/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
import Atlas.Buildings.code.AffineCoxeter.TitsCone
import Atlas.Buildings.code.ChamberComplex.Uniqueness
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Set.Card

set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

noncomputable section

namespace AffineCoxeter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A map $f : E \to E'$ is a similitude with respect to distances $d_1, d_2$ if there
exists a uniform scale factor $\mu$ with $d_2(f(x), f(y)) = \mu \cdot d_1(x, y)$. -/
def IsSimilitude {E' : Type*} [NormedAddCommGroup E'] (f : E → E')
    (d₁ : E → E → ℝ) (d₂ : E' → E' → ℝ) : Prop :=
  ∃ (μ : ℝ), ∀ x y : E, d₂ (f x) (f y) = μ * d₁ x y

/-- The Euclidean distance on an inner-product space: $d(x, y) = \|x - y\|$. -/
def euclideanDist (x y : E) : ℝ := ‖x - y‖

/-- A distance function is $W$-invariant if every element of the affine reflection
group acts as an isometry. -/
def IsWInvariant (W : AffineReflectionGroup E) (d : E → E → ℝ) : Prop :=
  ∀ w ∈ W.group, ∀ x y : E, d (w x) (w y) = d x y

/-- The Euclidean distance is invariant under any affine reflection group, since each
element is an affine isometry. -/
theorem euclideanDist_isWInvariant (W : AffineReflectionGroup E) :
    IsWInvariant W euclideanDist := by
  intro w hw x y
  simp only [euclideanDist]
  have : dist (w x) (w y) = dist x y := AffineIsometryEquiv.dist_map w x y
  simp only [dist_eq_norm] at this
  exact this

/-- An isomorphism of simplicial complexes: a pair of mutually inverse morphisms
between $K$ and $L$. -/
structure SimplicialComplexIso {V W : Type*} [DecidableEq V] [DecidableEq W]
    (K : SimplicialComplex V) (L : SimplicialComplex W) where
  toMorphism : SimplicialComplex.Morphism K L
  invMorphism : SimplicialComplex.Morphism L K
  left_inv : ∀ v, invMorphism.toFun (toMorphism.toFun v) = v
  right_inv : ∀ w, toMorphism.toFun (invMorphism.toFun w) = w

/-- The structure of an abstract affine Coxeter complex in $E$: an abstract simplicial
complex on vertices $V$ with a labelling, an affine vertex map onto a spanning subset,
a chosen chamber diameter, a Coxeter matrix and normal basis with Gram matrix encoding
the local Coxeter data, and the bijection between chamber adjacencies and Coxeter exponents. -/
structure AffineCoxeterComplex (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  V : Type*
  [decEq : DecidableEq V]
  W : AffineReflectionGroup E
  complex : SimplicialComplex V
  vertexMap : V → E
  affineSpan_vertexMap_eq_top : affineSpan ℝ (Set.range vertexMap) = ⊤
  chamberDiameter : ℝ
  chamberDiameter_pos : chamberDiameter > 0
  n : ℕ
  normalBasis : Module.Basis (Fin n) ℝ E
  coxeterMatrix : Fin n → Fin n → ℕ
  coxeterGram : Fin n → Fin n → ℝ
  coxeterGram_of_coxeterMatrix : ∀ i j : Fin n,
    coxeterGram i j = -Real.cos (Real.pi / (coxeterMatrix i j : ℝ))
  normalBasis_inner : ∀ i j : Fin n, @inner ℝ E _ (normalBasis i) (normalBasis j) = coxeterGram i j
  chamber_card : ∀ C, complex.IsMaximal C → C.card = n + 1
  exists_chamber : ∃ C, complex.IsMaximal C
  vertexType : V → Fin (n + 1)
  vertexType_chamber_bijective :
    ∀ (C : Finset V), complex.IsMaximal C →
      ∀ (t : Fin (n + 1)), ∃! v, v ∈ C ∧ vertexType v = t
  coxeterMatrix_eq_chamberCount :
    ∀ (C : Finset V), complex.IsMaximal C →
    ∀ i j : Fin n,
      Set.ncard {D | complex.IsMaximal D ∧
        C.filter (fun v => vertexType v ≠ i.castSucc ∧ vertexType v ≠ j.castSucc) ⊆ D} =
      2 * coxeterMatrix i j
  chamberCount_finite :
    ∀ (C : Finset V), complex.IsMaximal C →
    ∀ i j : Fin n,
      Set.Finite {D | complex.IsMaximal D ∧
        C.filter (fun v => vertexType v ≠ i.castSucc ∧ vertexType v ≠ j.castSucc) ⊆ D}
  vertex_in_chamber : ∀ v : V, ∃ C : Finset V, complex.IsMaximal C ∧ v ∈ C

attribute [instance] AffineCoxeterComplex.decEq

/-- The canonical normalised distance on an affine Coxeter complex: the Euclidean
distance scaled so that every closed chamber has diameter $1$. -/
def normalizedDist (A : AffineCoxeterComplex E) (x y : E) : ℝ :=
  euclideanDist x y / A.chamberDiameter

/-- The vertex type $V$ of an affine Coxeter complex is nonempty, since otherwise the
affine span condition forces $\mathbb{R}^0 = \top$, a contradiction. -/
theorem AffineCoxeterComplex.nonempty_V (A : AffineCoxeterComplex E) :
    Nonempty A.V := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  have hrng : (Set.range A.vertexMap) = ∅ := by
    ext x; constructor
    · rintro ⟨v, _⟩; exact (hemp.false v).elim
    · intro h; exact h.elim
  have hspan := A.affineSpan_vertexMap_eq_top
  rw [hrng, AffineSubspace.span_empty] at hspan
  exact bot_ne_top hspan

/-- A linear map that sends one basis to another with matching Gram matrices
preserves the inner product on all of $E$. -/
theorem inner_preservation_from_gram_matching
    {n : ℕ}
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (b : Module.Basis (Fin n) ℝ E) (b' : Module.Basis (Fin n) ℝ E')
    (hgram : ∀ i j : Fin n, @inner ℝ E' _ (b' i) (b' j) = @inner ℝ E _ (b i) (b j))
    (Ψ : E →ₗ[ℝ] E')
    (hΨ : ∀ i : Fin n, Ψ (b i) = b' i) :
    ∀ x y : E, @inner ℝ E' _ (Ψ x) (Ψ y) = @inner ℝ E _ x y := by
  intro x y
  conv_lhs => rw [show x = ∑ i : Fin n, b.equivFun x i • b i from (b.sum_equivFun x).symm]
  conv_lhs => rw [show y = ∑ i : Fin n, b.equivFun y i • b i from (b.sum_equivFun y).symm]
  simp only [map_sum, map_smul, hΨ]
  simp_rw [sum_inner (𝕜 := ℝ), inner_sum (𝕜 := ℝ), inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  conv_rhs => rw [show x = ∑ i : Fin n, b.equivFun x i • b i from (b.sum_equivFun x).symm]
  conv_rhs => rw [show y = ∑ i : Fin n, b.equivFun y i • b i from (b.sum_equivFun y).symm]
  simp_rw [sum_inner (𝕜 := ℝ), inner_sum (𝕜 := ℝ), inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  congr 1; ext i; congr 1; ext j; rw [hgram]

/-- A linear map that preserves the inner product also preserves the norm. -/
theorem norm_of_inner_preserving_map
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (Ψ : E →ₗ[ℝ] E')
    (h : ∀ x y : E, @inner ℝ E' _ (Ψ x) (Ψ y) = @inner ℝ E _ x y) :
    ∀ v : E, ‖Ψ v‖ = ‖v‖ := by
  intro v
  have h1 : ‖Ψ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (F := E') (Ψ v)]
    rw [← real_inner_self_eq_norm_sq (F := E) v]
    exact h v v
  nlinarith [norm_nonneg (Ψ v), norm_nonneg v, sq_nonneg (‖Ψ v‖ - ‖v‖)]

/-- The forward morphism of a simplicial complex isomorphism is injective. -/
theorem SimplicialComplexIso.injective {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) : Function.Injective φ.toMorphism.toFun :=
  Function.HasLeftInverse.injective ⟨φ.invMorphism.toFun, φ.left_inv⟩

/-- The inverse of a simplicial complex isomorphism, obtained by swapping forward and
backward morphisms. -/
def SimplicialComplexIso.symm {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) : SimplicialComplexIso L K where
  toMorphism := φ.invMorphism
  invMorphism := φ.toMorphism
  left_inv := φ.right_inv
  right_inv := φ.left_inv

/-- Simplicial isomorphisms preserve maximal faces (chambers). -/
theorem SimplicialComplexIso.maps_maximal {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) (C : Finset V') (hC : K.IsMaximal C) :
    L.IsMaximal (C.image φ.toMorphism.toFun) := by
  refine ⟨φ.toMorphism.map_face C hC.1, ?_⟩
  intro D hD hCD
  have hD_inv := φ.invMorphism.map_face D hD
  have hC_sub : C ⊆ D.image φ.invMorphism.toFun := by
    intro v hv
    have := hCD (Finset.mem_image_of_mem _ hv)
    exact Finset.mem_image.mpr ⟨φ.toMorphism.toFun v, this, φ.left_inv v⟩
  have := hC.2 _ hD_inv hC_sub
  rw [this]; ext w; simp only [Finset.mem_image]
  exact ⟨fun ⟨v, ⟨u, hu, huv⟩, hvw⟩ => by rw [← huv, φ.right_inv] at hvw; rwa [← hvw],
         fun hw => ⟨φ.invMorphism.toFun w, ⟨w, hw, rfl⟩, φ.right_inv w⟩⟩

/-- An isomorphism of affine Coxeter complexes implies their ranks (dimensions) are equal. -/
theorem coxeter_iso_dim_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex) :
    A.n = A'.n := by
  obtain ⟨C, hC⟩ := A.exists_chamber
  have h1 := A.chamber_card C hC
  have h2 := A'.chamber_card _ (φ.maps_maximal C hC)
  have h3 := Finset.card_image_of_injective C φ.injective
  omega





/-- An isomorphism preserves the number of chambers containing a given face. -/
theorem iso_chamber_count_preserved
    {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) (F : Finset V') :
    Set.ncard {D | L.IsMaximal D ∧ F.image φ.toMorphism.toFun ⊆ D} =
    Set.ncard {C | K.IsMaximal C ∧ F ⊆ C} := by


  suffices h : (fun C => C.image φ.toMorphism.toFun) '' {C | K.IsMaximal C ∧ F ⊆ C} =
      {D | L.IsMaximal D ∧ F.image φ.toMorphism.toFun ⊆ D} by
    rw [← h]
    exact Set.ncard_image_of_injective _ (fun _ _ h => Finset.image_injective φ.injective h)
  ext D
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, ⟨hCmax, hFC⟩, rfl⟩
    exact ⟨φ.maps_maximal C hCmax, Finset.image_subset_image hFC⟩
  · rintro ⟨hDmax, hFD⟩

    refine ⟨D.image φ.invMorphism.toFun, ⟨φ.symm.maps_maximal D hDmax, ?_⟩, ?_⟩
    ·
      intro v hv
      have hφv : φ.toMorphism.toFun v ∈ D := hFD (Finset.mem_image_of_mem _ hv)
      exact Finset.mem_image.mpr ⟨φ.toMorphism.toFun v, hφv, φ.left_inv v⟩
    ·
      rw [Finset.image_image]
      have : φ.toMorphism.toFun ∘ φ.invMorphism.toFun = id := funext φ.right_inv
      rw [this, Finset.image_id]












/-- Uniqueness of the affine extension: two affine maps that agree with $\varphi$ on
the vertex set $\mathrm{range}(A.\mathrm{vertexMap})$ agree everywhere, because the
vertex set affinely spans $E$. -/
theorem vertex_compatible_map_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (f g : E →ᵃ[ℝ] E')
    (hf : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v))
    (hg : ∀ v, g (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
    f = g := by


  ext x
  have h_eqon : Set.EqOn f g (Set.range A.vertexMap) := by
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    rw [hf v, hg v]
  have h_span := AffineMap.eqOn_affineSpan h_eqon
  have hx : x ∈ (affineSpan ℝ (Set.range A.vertexMap) : Set E) := by
    rw [A.affineSpan_vertexMap_eq_top]; trivial
  exact h_span hx



/-- The canonical distance: Euclidean distance divided by the chamber diameter, so
that each chamber has diameter exactly $1$. -/
def canonicalDist (chamberDiam : ℝ) (_hD : chamberDiam > 0) (x y : E) : ℝ :=
  euclideanDist x y / chamberDiam

/-- The Weyl-group-invariance of the Euclidean distance descends to its rescaling
$d/\mathrm{chamberDiameter}$. -/
theorem normalizedDist_isWInvariant (A : AffineCoxeterComplex E) :
    IsWInvariant A.W (normalizedDist A) := by
  intro w hw x y
  simp only [normalizedDist]
  rw [euclideanDist_isWInvariant A.W w hw x y]


end AffineCoxeter

end
