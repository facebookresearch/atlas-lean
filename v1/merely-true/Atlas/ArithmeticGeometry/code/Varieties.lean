/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AffineVarieties
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

variable (k : Type*) [Field k]

/-- An affine variety is an irreducible algebraic subset of affine $n$-space (Definition 12.7). -/
def IsAffineVariety (n : ℕ) (V : Set (AffineSpace_k k n)) : Prop :=
  IsAlgebraicSubset k n V ∧ IsIrreducibleAlgebraicSet k n V

/-- An affine variety is in particular an algebraic subset. -/
theorem IsAffineVariety.isAlgebraicSubset {n : ℕ} {V : Set (AffineSpace_k k n)}
    (h : IsAffineVariety k n V) : IsAlgebraicSubset k n V :=
  h.1


/-- An affine variety is nonempty (since irreducible algebraic sets are required to be nonempty). -/
theorem IsAffineVariety.nonempty {n : ℕ} {V : Set (AffineSpace_k k n)}
    (h : IsAffineVariety k n V) : V.Nonempty :=
  h.2.1


/-- The coordinate ring $\bar{k}[V]$ of an affine variety $V$ is an integral domain. -/
theorem coordinateRingBar_isDomain {n : ℕ} {V : Set (AffineSpace_k k n)}
    (hV : IsAffineVariety k n V) :
    IsDomain (AffineCoordinateRingBar V) := by
  have hprime := (isIrreducibleAlgebraicSet_iff_isPrime k hV.1).mp hV.2
  exact Ideal.Quotient.isDomain (idealOfAlgebraicSet V)

/-- The function field $\bar{k}(V)$ of an affine variety, defined as the fraction field of the coordinate ring $\bar{k}[V]$. -/
noncomputable def functionFieldBar {n : ℕ}
    (V : Set (AffineSpace_k k n)) (hV : IsAffineVariety k n V) : Type _ :=
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain k hV
  FractionRing (AffineCoordinateRingBar V)

/-- The function field $\bar{k}(V)$ is a field. -/
@[reducible] noncomputable def functionFieldBar.instField {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAffineVariety k n V) :
    Field (functionFieldBar k V hV) := by
  unfold functionFieldBar
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain k hV
  exact FractionRing.field (AffineCoordinateRingBar V)

noncomputable instance {n : ℕ} {V : Set (AffineSpace_k k n)}
    (hV : IsAffineVariety k n V) : Field (functionFieldBar k V hV) :=
  functionFieldBar.instField k hV

/-- The function field $\bar{k}(V)$ is an algebra over the algebraic closure $\bar{k}$. -/
@[reducible] noncomputable def functionFieldBar.instAlgebra {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAffineVariety k n V) :
    Algebra (AlgebraicClosure k) (functionFieldBar k V hV) := by
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain k hV
  show Algebra (AlgebraicClosure k)
    (FractionRing (MvPolynomial (Fin n) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V))
  infer_instance

noncomputable instance {n : ℕ} {V : Set (AffineSpace_k k n)}
    (hV : IsAffineVariety k n V) :
    Algebra (AlgebraicClosure k) (functionFieldBar k V hV) :=
  functionFieldBar.instAlgebra k hV

/-- The $k$-rational function field $k(V)$ of an affine variety, defined as the fraction field of the $k$-coordinate ring $k[V]$ when it is a domain. -/
noncomputable def functionField_k {n : ℕ}
    (V : Set (AffineSpace_k k n)) (_hV : IsAffineVariety k n V)
    (_hdom : IsDomain (AffineCoordinateRing V)) : Type _ :=
  FractionRing (AffineCoordinateRing V)

noncomputable instance {n : ℕ} {V : Set (AffineSpace_k k n)}
    (_hV : IsAffineVariety k n V) (hdom : IsDomain (AffineCoordinateRing V)) :
    Field (functionField_k k V _hV hdom) :=
  FractionRing.field _

/-- The dimension of an affine variety $V$ is the transcendence degree of its function field $\bar{k}(V)$ over $\bar{k}$ (Definition 12.21). -/
noncomputable def varietyDim {n : ℕ}
    (V : Set (AffineSpace_k k n)) (hV : IsAffineVariety k n V) : Cardinal :=
  Algebra.trdeg (AlgebraicClosure k) (functionFieldBar k V hV)

/-- A subset $V \subseteq \mathbb{A}^n$ is an algebraic set if it is the zero locus $\mathcal{V}(S)$ of some set $S$ of polynomials. -/
def IsAlgebraicSetAffine (n : ℕ) (V : Set (AffineSpace_k k n)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)), V = AlgebraicSet k n S

/-- The collection of all algebraic subsets of $\mathbb{A}^n$, used as the closed sets of the Zariski topology. -/
def algebraicSetsCollection (n : ℕ) : Set (Set (AffineSpace_k k n)) :=
  {V | IsAlgebraicSetAffine k n V}

/-- The empty set is an algebraic set, namely $\mathcal{V}(\{1\})$. -/
lemma algebraicSetsCollection_empty_mem (n : ℕ) : ∅ ∈ algebraicSetsCollection k n :=
  ⟨{1}, by ext P; simp [AlgebraicSet]⟩

/-- An arbitrary intersection of algebraic sets is again algebraic. -/
lemma algebraicSetsCollection_sInter_mem (n : ℕ) (A : Set (Set (AffineSpace_k k n)))
    (hA : A ⊆ algebraicSetsCollection k n) :
    ⋂₀ A ∈ algebraicSetsCollection k n := by
  choose S hS using fun V (hV : V ∈ A) => hA hV
  refine ⟨⋃ V ∈ A, S V ‹_›, ?_⟩
  ext P
  simp only [Set.mem_sInter, AlgebraicSet, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h f ⟨V, hV, hfS⟩
    have := h V hV; rw [hS V hV] at this; exact this f hfS
  · intro h V hV
    rw [hS V hV]; intro f hfS; exact h f ⟨V, hV, hfS⟩

/-- The union of two algebraic sets is algebraic: $\mathcal{V}(S) \cup \mathcal{V}(T) = \mathcal{V}(ST)$. -/
lemma algebraicSetsCollection_union_mem (n : ℕ)
    (A : Set (AffineSpace_k k n)) (hA : A ∈ algebraicSetsCollection k n)
    (B : Set (AffineSpace_k k n)) (hB : B ∈ algebraicSetsCollection k n) :
    A ∪ B ∈ algebraicSetsCollection k n := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  refine ⟨{f * g | (f ∈ S) (g ∈ T)}, ?_⟩
  ext P
  simp only [Set.mem_union, AlgebraicSet, Set.mem_setOf_eq]
  constructor
  · rintro (hS | hT)
    · rintro _ ⟨f, hf, g, hg, rfl⟩; simp [hS f hf]
    · rintro _ ⟨f, hf, g, hg, rfl⟩; simp [hT g hg]
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨⟨f, hf, hfP⟩, ⟨g, hg, hgP⟩⟩ := hc
    have := h (f * g) ⟨f, hf, g, hg, rfl⟩
    rw [map_mul] at this
    exact (mul_eq_zero.mp this).elim hfP hgP

/-- The Zariski topology on $\mathbb{A}^n_k$, whose closed sets are the algebraic sets. -/
@[reducible]
def zariskiTopology (n : ℕ) : TopologicalSpace (AffineSpace_k k n) :=
  TopologicalSpace.ofClosed (algebraicSetsCollection k n)
    (algebraicSetsCollection_empty_mem k n)
    (algebraicSetsCollection_sInter_mem k n)
    (algebraicSetsCollection_union_mem k n)

/-- A subset of $\mathbb{A}^n_k$ is closed in the Zariski topology iff it is an algebraic set. -/
theorem isClosed_zariskiTopology_iff_isAlgebraicSet (n : ℕ) (V : Set (AffineSpace_k k n)) :
    @IsClosed _ (zariskiTopology k n) V ↔ IsAlgebraicSetAffine k n V := by
  constructor
  · intro hV
    have : Vᶜᶜ ∈ algebraicSetsCollection k n := hV.isOpen_compl
    rwa [compl_compl] at this
  · intro hV
    exact @IsClosed.mk _ (zariskiTopology k n) _
      (by show Vᶜᶜ ∈ algebraicSetsCollection k n; rwa [compl_compl])

noncomputable section

/-- Evaluate a tuple of polynomials at a point, giving a map $\mathbb{A}^m \to \mathbb{A}^n$. -/
def polyMapEval (m n : ℕ)
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  fun j => MvPolynomial.eval P (polys j)

/-- Evaluating $g \circ f$ at $P$ equals evaluating $g$ at $f(P)$, where $f$ is given by a tuple of polynomials. -/
lemma eval_bind₁_eq_eval_polyMapEval {m n : ℕ} (P : AffineSpace_k k m)
    (f : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (g : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    MvPolynomial.eval P (MvPolynomial.bind₁ f g) =
    MvPolynomial.eval (polyMapEval k m n f P) g := by
  change MvPolynomial.eval₂Hom _ P (MvPolynomial.bind₁ f g) =
         MvPolynomial.eval₂Hom _ (polyMapEval k m n f P) g
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 1

/-- Polynomial maps compose: $(g \circ f)(P) = g(f(P))$. -/
lemma polyMapEval_bind₁ {m n r : ℕ} (P : AffineSpace_k k m)
    (f : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (g : Fin r → MvPolynomial (Fin n) (AlgebraicClosure k)) :
    polyMapEval k m r (fun j => MvPolynomial.bind₁ f (g j)) P =
    polyMapEval k n r g (polyMapEval k m n f P) := by
  ext j
  exact eval_bind₁_eq_eval_polyMapEval k P f (g j)

/-- A morphism of affine varieties $X \to Y$ is given by an $n$-tuple of polynomials whose induced map sends $X$ into $Y$. -/
structure AffineMorphism (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)
  maps_to : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y

/-- The underlying set-theoretic map of an affine morphism. -/
def AffineMorphism.toFun {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : AffineMorphism k m n X Y)
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  polyMapEval k m n φ.polys P


/-- The image of any point of $X$ under an affine morphism lies in $Y$. -/
theorem AffineMorphism.image_mem {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : AffineMorphism k m n X Y)
    {P : AffineSpace_k k m} (hP : P ∈ X) : φ.toFun k P ∈ Y :=
  φ.maps_to P hP

/-- The identity affine morphism on $X$, given by the coordinate polynomials $X_1, \ldots, X_n$. -/
def AffineMorphism.id {n : ℕ} (X : Set (AffineSpace_k k n)) :
    AffineMorphism k n n X X where
  polys := fun i => MvPolynomial.X i
  maps_to := by
    intro P hP
    have : polyMapEval k n n (fun i => MvPolynomial.X i) P = P := by
      ext j; simp [polyMapEval, MvPolynomial.eval_X]
    rw [this]; exact hP

/-- Composition of affine morphisms $g \circ f : X \to Z$. -/
def AffineMorphism.comp {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (g : AffineMorphism k n r Y Z) (f : AffineMorphism k m n X Y) :
    AffineMorphism k m r X Z where
  polys := fun j => MvPolynomial.bind₁ f.polys (g.polys j)
  maps_to := by
    intro P hP
    rw [polyMapEval_bind₁]
    exact g.maps_to _ (f.maps_to P hP)

/-- The identity morphism evaluates to the identity function. -/
theorem AffineMorphism.toFun_id {n : ℕ} {X : Set (AffineSpace_k k n)}
    (P : AffineSpace_k k n) :
    (AffineMorphism.id k X).toFun k P = P := by
  ext j; simp [toFun, AffineMorphism.id, polyMapEval, MvPolynomial.eval_X]

/-- The underlying function of the composite of two affine morphisms is the composite of their underlying functions. -/
theorem AffineMorphism.toFun_comp {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (g : AffineMorphism k n r Y Z) (f : AffineMorphism k m n X Y)
    (P : AffineSpace_k k m) :
    (g.comp k f).toFun k P = g.toFun k (f.toFun k P) := by
  simp only [toFun, comp]
  exact polyMapEval_bind₁ k P f.polys g.polys

/-- A subset $U$ of a variety $X$ is open in $X$ iff $U = X \cap W$ for some Zariski-open $W$. -/
def IsOpenInVariety (m : ℕ) (X U : Set (AffineSpace_k k m)) : Prop :=
  U ⊆ X ∧ ∃ W : Set (AffineSpace_k k m), @IsOpen _ (zariskiTopology k m) W ∧ U = X ∩ W

/-- A subset $U$ is dense in the variety $X$ iff $X$ is contained in the Zariski closure of $U$. -/
def IsDenseInVariety (m : ℕ) (X U : Set (AffineSpace_k k m)) : Prop :=
  X ⊆ @closure _ (zariskiTopology k m) U

/-- Evaluate a rational function $\mathrm{num}/\mathrm{denom}$ at a point $P$. -/
def ratFunEval (m : ℕ)
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : AlgebraicClosure k :=
  MvPolynomial.eval P num / MvPolynomial.eval P denom

/-- Evaluate a rational map $\mathbb{A}^m \dashrightarrow \mathbb{A}^n$ given by tuples of numerators and denominators. -/
def ratMapEval (m n : ℕ)
    (nums denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  fun j => ratFunEval k m (nums j) (denoms j) P

/-- The domain of definition of a rational map: points of $X$ where every denominator is nonzero. -/
def ratMapDom (m n : ℕ)
    (X : Set (AffineSpace_k k m))
    (denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)) : Set (AffineSpace_k k m) :=
  {P ∈ X | ∀ j, MvPolynomial.eval P (denoms j) ≠ 0}

/-- The domain of a rational map is a subset of $X$. -/
lemma ratMapDom_subset {m n : ℕ} (X : Set (AffineSpace_k k m))
    (denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)) :
    ratMapDom k m n X denoms ⊆ X :=
  fun _ h => h.1

/-- A rational map with all denominators equal to $1$ reduces to a polynomial map. -/
lemma ratMapEval_eq_polyMapEval_of_denom_one {m n : ℕ}
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) :
    ratMapEval k m n polys (fun _ => 1) P = polyMapEval k m n polys P := by
  ext j
  simp [ratMapEval, ratFunEval, polyMapEval, map_one, div_one]

/-- If all denominators are $1$, the domain of the rational map is all of $X$. -/
lemma ratMapDom_of_denom_one {m n : ℕ} (X : Set (AffineSpace_k k m)) :
    ratMapDom k m n X (fun _ => (1 : MvPolynomial (Fin m) (AlgebraicClosure k))) = X := by
  ext P
  simp [ratMapDom, map_one]

/-- A rational map $X \dashrightarrow Y$ between affine varieties: a tuple of numerators/denominators, defined on an open dense subset of $X$, sending its domain into $Y$. -/
structure RationalMap (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  nums : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)
  denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)
  denoms_ne_zero : ∀ j, denoms j ≠ 0
  dom_open : IsOpenInVariety k m X (ratMapDom k m n X denoms)
  dom_dense : IsDenseInVariety k m X (ratMapDom k m n X denoms)
  maps_to : ∀ P ∈ ratMapDom k m n X denoms, ratMapEval k m n nums denoms P ∈ Y

/-- The domain of definition of a rational map. -/
def RationalMap.dom {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y) : Set (AffineSpace_k k m) :=
  ratMapDom k m n X φ.denoms

/-- The underlying partial function of a rational map. -/
def RationalMap.toFun {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y)
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  ratMapEval k m n φ.nums φ.denoms P


/-- The image of a point in the domain of a rational map lies in $Y$. -/
theorem RationalMap.image_mem {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y)
    {P : AffineSpace_k k m} (hP : P ∈ φ.dom k) : φ.toFun k P ∈ Y :=
  φ.maps_to P hP


/-- Every affine morphism is a rational map (with all denominators equal to $1$). -/
def AffineMorphism.toRationalMap {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y) :
    RationalMap k m n X Y where
  nums := φ.polys
  denoms := fun _ => 1
  denoms_ne_zero := fun _ => one_ne_zero
  dom_open := by
    rw [ratMapDom_of_denom_one]
    exact ⟨Set.Subset.refl X, Set.univ, @isOpen_univ _ (zariskiTopology k m),
      (Set.inter_univ X).symm⟩
  dom_dense := by
    rw [ratMapDom_of_denom_one]
    intro x hx
    rw [@mem_closure_iff _ (zariskiTopology k m)]
    intro U hU hxU
    exact ⟨x, hxU, hx⟩
  maps_to := by
    intro P hP
    rw [ratMapEval_eq_polyMapEval_of_denom_one]
    exact φ.maps_to P hP.1

/-- The domain of the rational map associated to an affine morphism is all of $X$. -/
@[simp]
theorem AffineMorphism.toRationalMap_dom {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y) :
    (φ.toRationalMap k).dom k = X := by
  simp [RationalMap.dom, AffineMorphism.toRationalMap, ratMapDom_of_denom_one]

/-- A rational map is regular if its domain of definition is the entire source variety. -/
def RationalMap.IsRegular {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y) : Prop :=
  φ.dom k = X

/-- Convert a regular rational map to an affine morphism, given an explicit choice of polynomials agreeing with $\varphi$ on $X$. -/
def RationalMap.toAffineMorphism {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : RationalMap k m n X Y) (hreg : φ.IsRegular)
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (hpolys : ∀ P ∈ X, polyMapEval k m n polys P = ratMapEval k m n φ.nums φ.denoms P) :
    AffineMorphism k m n X Y where
  polys := polys
  maps_to := by
    intro P hP
    rw [hpolys P hP]
    have hdom : P ∈ ratMapDom k m n X φ.denoms := by rw [show ratMapDom k m n X φ.denoms = X from hreg]; exact hP
    exact φ.maps_to P hdom

/-- The rational map associated to an affine morphism is regular. -/
theorem AffineMorphism.toRationalMap_isRegular {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y) :
    (φ.toRationalMap k).IsRegular := by
  simp [RationalMap.IsRegular, AffineMorphism.toRationalMap_dom]

/-- The underlying function of the rational map associated to an affine morphism agrees with that of the morphism. -/
theorem AffineMorphism.toRationalMap_toFun_eq {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (f : AffineMorphism k m n X Y) (P : AffineSpace_k k m) :
    (f.toRationalMap k).toFun k P = f.toFun k P := by
  ext j
  simp [RationalMap.toFun, ratMapEval, ratFunEval, AffineMorphism.toRationalMap,
    AffineMorphism.toFun, polyMapEval, map_one, div_one]

/-- A rational function $\mathrm{num}/\mathrm{denom}$ is regular at $P \in X$ if some equivalent representation $g/h$ has $g(P) \neq 0$, modulo the vanishing ideal of $X$. -/
def IsRegularAtPoint {m : ℕ} (X : Set (AffineSpace_k k m))
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : Prop :=
  P ∈ X ∧ ∃ (g h : MvPolynomial (Fin m) (AlgebraicClosure k)),
    MvPolynomial.eval P g ≠ 0 ∧
    g * num - h * denom ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k) X

/-- The domain of definition of a rational function $\mathrm{num}/\mathrm{denom}$ on $X$. -/
def RationalFunctionDom {m : ℕ} (X : Set (AffineSpace_k k m))
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k)) : Set (AffineSpace_k k m) :=
  {P ∈ X | ∃ (g h : MvPolynomial (Fin m) (AlgebraicClosure k)),
    MvPolynomial.eval P g ≠ 0 ∧
    g * num - h * denom ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k) X}

/-- A rational function $\mathrm{num}/\mathrm{denom}$ lies in the coordinate ring of $X$ if it is congruent to a polynomial modulo the vanishing ideal. -/
def RationalFunctionLiesInCoordinateRing {m : ℕ} (X : Set (AffineSpace_k k m))
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k)) : Prop :=
  ∃ poly : MvPolynomial (Fin m) (AlgebraicClosure k),
    num - poly * denom ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k) X


/-- On an affine variety $X$, a rational function whose denominator vanishes nowhere on $X$ agrees pointwise with a polynomial: there is $p \in \bar{k}[X_1, \ldots, X_m]$ with $p(P) = \mathrm{num}(P)/\mathrm{denom}(P)$ for all $P \in X$. -/
theorem regular_rational_function_is_polynomial
    (k : Type*) [Field k] {m : ℕ}
    {X : Set (AffineSpace_k k m)}
    (hX : IsAffineVariety k m X)
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k))
    (_hdenom_ne_zero : denom ≠ 0)
    (hdenom_nonvanishing : ∀ P ∈ X, MvPolynomial.eval P denom ≠ 0) :
    ∃ poly : MvPolynomial (Fin m) (AlgebraicClosure k),
      ∀ P ∈ X, MvPolynomial.eval P poly =
        MvPolynomial.eval P num / MvPolynomial.eval P denom := by

  set k' := AlgebraicClosure k
  set I := MvPolynomial.vanishingIdeal k' X with hI_def

  have htop : I ⊔ Ideal.span {denom} = ⊤ := by
    by_contra hne_top
    have hrad : (I ⊔ Ideal.span {denom}).radical ≠ ⊤ := by rwa [Ne, Ideal.radical_eq_top]
    rw [← @MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (AlgebraicClosure k) (AlgebraicClosure k) _ _ _ (Fin m) _ _] at hrad
    have hzl_ne : (MvPolynomial.zeroLocus k' (I ⊔ Ideal.span {denom})).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      exact hrad (by rw [hempty, MvPolynomial.vanishingIdeal_empty])
    obtain ⟨P, hP⟩ := hzl_ne
    have hPI : P ∈ MvPolynomial.zeroLocus k' I :=
      MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection.monotone_l le_sup_left hP
    have hPd : P ∈ MvPolynomial.zeroLocus k' (Ideal.span {denom}) :=
      MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection.monotone_l le_sup_right hP
    have hPX : P ∈ X := by
      obtain ⟨S, hS⟩ := hX.1
      rw [hS]
      rw [MvPolynomial.mem_zeroLocus_iff] at hPI
      intro f hf
      have : f ∈ I := by
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro Q hQ
        rw [hS] at hQ
        exact hQ f hf
      exact hPI f this
    have hdenom_zero : MvPolynomial.eval P denom = 0 := by
      rw [MvPolynomial.mem_zeroLocus_iff] at hPd
      rw [eval_eq_aeval_algebraicClosure]
      exact hPd denom (Ideal.subset_span rfl)
    exact hdenom_nonvanishing P hPX hdenom_zero

  have h1 : (1 : MvPolynomial (Fin m) k') ∈ I ⊔ Ideal.span {denom} :=
    htop ▸ Submodule.mem_top
  obtain ⟨h_ix, hh_ix, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb


  refine ⟨c * num, fun P hP => ?_⟩
  have h_ix_vanish : MvPolynomial.eval P h_ix = 0 := by
    rw [eval_eq_aeval_algebraicClosure]
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hh_ix) P hP
  have hdenom_ne : MvPolynomial.eval P denom ≠ 0 := hdenom_nonvanishing P hP
  have heval : MvPolynomial.eval P denom * MvPolynomial.eval P c = 1 := by
    have hab' := congr_arg (MvPolynomial.eval P) hab
    simp only [map_add, map_mul, map_one] at hab'
    rw [h_ix_vanish, zero_add] at hab'
    exact hab'

  simp only [map_mul]
  rw [eq_div_iff hdenom_ne]

  have heval' : MvPolynomial.eval P c * MvPolynomial.eval P denom = 1 := by
    rw [mul_comm]; exact heval
  rw [mul_assoc, mul_comm (MvPolynomial.eval P num) (MvPolynomial.eval P denom),
      ← mul_assoc, heval', one_mul]

/-- A regular rational map between affine varieties extends to an affine morphism that agrees with it pointwise on $X$. -/
theorem regular_rational_map_is_morphism {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (hX : IsAffineVariety k m X)
    (φ : RationalMap k m n X Y) (hreg : φ.IsRegular) :
    ∃ (f : AffineMorphism k m n X Y), ∀ P ∈ X, f.toFun k P = φ.toFun k P := by

  have hdenom_nonvanishing : ∀ j, ∀ P ∈ X, MvPolynomial.eval P (φ.denoms j) ≠ 0 := by
    intro j P hP
    have hdom : P ∈ φ.dom k := by rw [show φ.dom k = X from hreg]; exact hP
    exact hdom.2 j

  have hpoly : ∀ j, ∃ poly : MvPolynomial (Fin m) (AlgebraicClosure k),
      ∀ P ∈ X, MvPolynomial.eval P poly =
        MvPolynomial.eval P (φ.nums j) / MvPolynomial.eval P (φ.denoms j) := by
    intro j
    exact regular_rational_function_is_polynomial k hX (φ.nums j) (φ.denoms j)
      (φ.denoms_ne_zero j) (hdenom_nonvanishing j)

  choose polys hpolys using hpoly

  have hpolys_eq : ∀ P ∈ X, polyMapEval k m n polys P = ratMapEval k m n φ.nums φ.denoms P := by
    intro P hP
    ext j
    exact hpolys j P hP

  refine ⟨φ.toAffineMorphism k hreg polys hpolys_eq, fun P hP => ?_⟩
  show polyMapEval k m n polys P = ratMapEval k m n φ.nums φ.denoms P
  exact hpolys_eq P hP


/-- A rational map $\varphi : X \dashrightarrow Y$ is dominant if its image is Zariski-dense in $Y$. -/
def RationalMap.IsDominant {m n : ℕ} {X : Set (AffineSpace_k k m)}
    {Y : Set (AffineSpace_k k n)} (φ : RationalMap k m n X Y) : Prop :=
  Y ⊆ @closure _ (zariskiTopology k n) (φ.toFun k '' φ.dom)

/-- The domain on which the composition $\varphi \circ \psi$ of rational maps is defined. -/
def RationalMap.compDom {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (φ : RationalMap k n r Y Z) (ψ : RationalMap k m n X Y) :
    Set (AffineSpace_k k m) :=
  {P ∈ ψ.dom | ψ.toFun k P ∈ φ.dom}

/-- Two affine varieties $X, Y$ are birationally equivalent if there exist dominant rational maps $\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ that are mutually inverse where both compositions are defined. -/
def IsBirationallyEquivalent {m n : ℕ}
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) : Prop :=
  ∃ (φ : RationalMap k m n X Y) (ψ : RationalMap k n m Y X),
    φ.IsDominant k ∧ ψ.IsDominant k ∧
    (∀ P ∈ RationalMap.compDom k ψ φ,
      ψ.toFun k (φ.toFun k P) = P) ∧
    (∀ P ∈ RationalMap.compDom k φ ψ,
      φ.toFun k (ψ.toFun k P) = P)

/-- A strict chain $V_0 \subsetneq V_1 \subsetneq \cdots \subsetneq V_d = V$ of affine subvarieties of $V$. -/
def IsStrictVarietyChain {n : ℕ} (V : Set (AffineSpace_k k n)) (d : ℕ)
    (chain : Fin (d + 1) → Set (AffineSpace_k k n)) : Prop :=
  (∀ i, IsAffineVariety k n (chain i)) ∧
  (∀ i j, i < j → chain i ⊂ chain j) ∧
  chain ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = V

/-- The geometric dimension of an affine variety $V$ is the supremum of $d$ for which there exists a strict chain of affine subvarieties of length $d$ ending at $V$. -/
def geometricDim {n : ℕ} (V : Set (AffineSpace_k k n)) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : ∃ chain, IsStrictVarietyChain k V d chain), (d : ℕ∞)

end
