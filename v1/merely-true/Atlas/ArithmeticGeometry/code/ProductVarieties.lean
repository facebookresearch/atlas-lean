/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Varieties
import Atlas.ArithmeticGeometry.code.Morphisms
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic

variable (k : Type*) [Field k]

/-- Embedding $\overline{k}[x_1, \ldots, x_m] \hookrightarrow \overline{k}[x_1, \ldots, x_{m+n}]$
in the first $m$ variables, by renaming via `Fin.castAdd`. -/
noncomputable def embedPolyLeft (m n : ℕ) :
    MvPolynomial (Fin m) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.castAdd n)

/-- Embedding $\overline{k}[y_1, \ldots, y_n] \hookrightarrow \overline{k}[x_1, \ldots, x_{m+n}]$
in the last $n$ variables, by renaming via `Fin.natAdd`. -/
noncomputable def embedPolyRight (m n : ℕ) :
    MvPolynomial (Fin n) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.natAdd m)

/-- Image of a set of polynomials under `embedPolyLeft`. -/
def embedSetLeft (m n : ℕ) (S : Set (MvPolynomial (Fin m) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)) :=
  (embedPolyLeft k m n) '' S

/-- Image of a set of polynomials under `embedPolyRight`. -/
def embedSetRight (m n : ℕ) (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)) :=
  (embedPolyRight k m n) '' S

/-- Definition 16.2: the product algebraic set $V(S_X) \times V(S_Y) \subseteq \overline{k}^{m+n}$,
defined as the algebraic set in $\overline{k}^{m+n}$ cut out by the embedded polynomials. -/
def ProductAlgebraicSet (m n : ℕ)
    (S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k)))
    (S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (AffineSpace_k k (m + n)) :=
  AlgebraicSet k (m + n) (embedSetLeft k m n S_X ∪ embedSetRight k m n S_Y)

/-- Projection $\overline{k}^{m+n} \to \overline{k}^m$ onto the first $m$ coordinates. -/
def projLeft (m n : ℕ) (P : AffineSpace_k k (m + n)) : AffineSpace_k k m :=
  P ∘ Fin.castAdd n

/-- Projection $\overline{k}^{m+n} \to \overline{k}^n$ onto the last $n$ coordinates. -/
def projRight (m n : ℕ) (P : AffineSpace_k k (m + n)) : AffineSpace_k k n :=
  P ∘ Fin.natAdd m

/-- The Cartesian product $X \times Y \subseteq \overline{k}^{m+n}$ as a set, defined by the
projection criteria. -/
def CartesianProduct (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) :
    Set (AffineSpace_k k (m + n)) :=
  {P | projLeft k m n P ∈ X ∧ projRight k m n P ∈ Y}

/-- Projecting `Fin.append a b` to the left gives `a`. -/
@[simp]
theorem projLeft_append (m n : ℕ) (a : AffineSpace_k k m) (b : AffineSpace_k k n) :
    projLeft k m n (Fin.append a b) = a := by
  ext i
  simp [projLeft, Function.comp, Fin.append_left]

/-- Projecting `Fin.append a b` to the right gives `b`. -/
@[simp]
theorem projRight_append (m n : ℕ) (a : AffineSpace_k k m) (b : AffineSpace_k k n) :
    projRight k m n (Fin.append a b) = b := by
  ext i
  simp [projRight, Function.comp, Fin.append_right]

/-- Reconstruction: appending the left and right projections of $P$ recovers $P$. -/
theorem append_proj (m n : ℕ) (P : AffineSpace_k k (m + n)) :
    Fin.append (projLeft k m n P) (projRight k m n P) = P := by
  simp only [projLeft, projRight]
  exact Fin.append_castAdd_natAdd

/-- A point $P \in \overline{k}^{m+n}$ lies in $V(S_X) \times V(S_Y)$ iff its left projection
lies in $V(S_X)$ and its right projection lies in $V(S_Y)$. -/
theorem mem_productAlgebraicSet (m n : ℕ)
    (S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k)))
    (S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (P : AffineSpace_k k (m + n)) :
    P ∈ ProductAlgebraicSet k m n S_X S_Y ↔
    projLeft k m n P ∈ AlgebraicSet k m S_X ∧
    projRight k m n P ∈ AlgebraicSet k n S_Y := by
  simp only [ProductAlgebraicSet, AlgebraicSet, Set.mem_setOf_eq,
    Set.mem_union, embedSetLeft, embedSetRight, projLeft, projRight]
  constructor
  · intro h
    constructor
    · intro f hf
      have := h (embedPolyLeft k m n f) (Or.inl ⟨f, hf, rfl⟩)
      simp only [embedPolyLeft, MvPolynomial.eval_rename] at this
      exact this
    · intro g hg
      have := h (embedPolyRight k m n g) (Or.inr ⟨g, hg, rfl⟩)
      simp only [embedPolyRight, MvPolynomial.eval_rename] at this
      exact this
  · intro ⟨hX, hY⟩ f hf
    rcases hf with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · simp only [embedPolyLeft, MvPolynomial.eval_rename]
      exact hX g hg
    · simp only [embedPolyRight, MvPolynomial.eval_rename]
      exact hY g hg


/-- The product of two nonempty algebraic sets is nonempty. -/
theorem productAlgebraicSet_nonempty (m n : ℕ)
    (S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k)))
    (S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (hX : (AlgebraicSet k m S_X).Nonempty)
    (hY : (AlgebraicSet k n S_Y).Nonempty) :
    (ProductAlgebraicSet k m n S_X S_Y).Nonempty := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  exact ⟨Fin.append a b, (mem_productAlgebraicSet k m n S_X S_Y _).mpr
    ⟨by rwa [projLeft_append], by rwa [projRight_append]⟩⟩

/-- Partial evaluation of a polynomial in $m+n$ variables by fixing the last $n$ variables to
the values $b \in \overline{k}^n$, returning a polynomial in the first $m$ variables. -/
noncomputable def partialEvalRight (m n : ℕ) (b : AffineSpace_k k n) :
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) →+*
    MvPolynomial (Fin m) (AlgebraicClosure k) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (m + n) =>
      if h : i.val < m
      then MvPolynomial.X ⟨i.val, h⟩
      else MvPolynomial.C (b ⟨i.val - m, by omega⟩))

/-- Compatibility: evaluating `partialEvalRight b f` at `a` equals evaluating `f` at the
appended point `Fin.append a b`. -/
theorem eval_partialEvalRight (m n : ℕ) (b : AffineSpace_k k n)
    (f : MvPolynomial (Fin (m + n)) (AlgebraicClosure k))
    (a : AffineSpace_k k m) :
    MvPolynomial.eval a (partialEvalRight k m n b f) =
    MvPolynomial.eval (Fin.append a b) f := by
  suffices h : (MvPolynomial.eval a).comp (partialEvalRight k m n b) =
      MvPolynomial.eval (Fin.append a b) from RingHom.congr_fun h f
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [partialEvalRight, MvPolynomial.eval_C]
  · intro i
    simp only [RingHom.comp_apply, partialEvalRight, MvPolynomial.eval₂Hom_X',
               MvPolynomial.eval_X]
    split_ifs with h
    · simp only [MvPolynomial.eval_X, Fin.append, Fin.addCases, h, dite_true]
      rfl
    · simp only [MvPolynomial.eval_C, Fin.append, Fin.addCases, h, dite_false]
      simp [Fin.subNat, Fin.cast]

/-- For an algebraic set $V(T) \subseteq \overline{k}^{m+n}$, the fiber
$\{a \mid (a, b) \in V(T)\}$ over a fixed $b \in \overline{k}^n$ is an algebraic subset
of $\overline{k}^m$. -/
theorem algebraicSubset_fiber_left (m n : ℕ)
    (T : Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)))
    (b : AffineSpace_k k n) :
    IsAlgebraicSubset k m
      {a : AffineSpace_k k m | Fin.append a b ∈ AlgebraicSet k (m + n) T} := by
  refine ⟨(partialEvalRight k m n b) '' T, ?_⟩
  ext a
  simp only [AlgebraicSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro ha g hg
    obtain ⟨f, hf, rfl⟩ := hg
    rw [eval_partialEvalRight]
    exact ha f hf
  · intro ha f hf
    rw [← eval_partialEvalRight k m n b]
    exact ha _ ⟨f, hf, rfl⟩

/-- Partial evaluation of a polynomial in $m+n$ variables by fixing the first $m$ variables
to the values $a \in \overline{k}^m$, returning a polynomial in the last $n$ variables. -/
noncomputable def partialEvalLeft (m n : ℕ) (a : AffineSpace_k k m) :
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) →+*
    MvPolynomial (Fin n) (AlgebraicClosure k) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (m + n) =>
      if h : i.val < m
      then MvPolynomial.C (a ⟨i.val, h⟩)
      else MvPolynomial.X ⟨i.val - m, by omega⟩)

/-- Compatibility: evaluating `partialEvalLeft a f` at `b` equals evaluating `f` at
`Fin.append a b`. -/
theorem eval_partialEvalLeft (m n : ℕ) (a : AffineSpace_k k m)
    (f : MvPolynomial (Fin (m + n)) (AlgebraicClosure k))
    (b : AffineSpace_k k n) :
    MvPolynomial.eval b (partialEvalLeft k m n a f) =
    MvPolynomial.eval (Fin.append a b) f := by
  suffices h : (MvPolynomial.eval b).comp (partialEvalLeft k m n a) =
      MvPolynomial.eval (Fin.append a b) from RingHom.congr_fun h f
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [partialEvalLeft, MvPolynomial.eval_C]
  · intro i
    simp only [RingHom.comp_apply, partialEvalLeft, MvPolynomial.eval₂Hom_X',
               MvPolynomial.eval_X]
    split_ifs with h
    · simp only [MvPolynomial.eval_C, Fin.append, Fin.addCases, h, dite_true]
      rfl
    · simp only [MvPolynomial.eval_X, Fin.append, Fin.addCases, h, dite_false]
      simp [Fin.subNat, Fin.cast]

/-- For an algebraic set $V(T) \subseteq \overline{k}^{m+n}$, the fiber
$\{b \mid (a, b) \in V(T)\}$ over a fixed $a \in \overline{k}^m$ is an algebraic subset
of $\overline{k}^n$. -/
theorem algebraicSubset_fiber_right (m n : ℕ)
    (T : Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)))
    (a : AffineSpace_k k m) :
    IsAlgebraicSubset k n
      {b : AffineSpace_k k n | Fin.append a b ∈ AlgebraicSet k (m + n) T} := by
  refine ⟨(partialEvalLeft k m n a) '' T, ?_⟩
  ext b
  simp only [AlgebraicSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hb g hg
    obtain ⟨f, hf, rfl⟩ := hg
    rw [eval_partialEvalLeft]
    exact hb f hf
  · intro hb f hf
    rw [← eval_partialEvalLeft k m n a]
    exact hb _ ⟨f, hf, rfl⟩

/-- An arbitrary intersection of algebraic subsets is an algebraic subset (cut out by the
union of the defining polynomial sets). -/
theorem isAlgebraicSubset_iInter {ι : Type*} (n : ℕ)
    (V : ι → Set (AffineSpace_k k n))
    (hV : ∀ i, IsAlgebraicSubset k n (V i)) :
    IsAlgebraicSubset k n (⋂ i, V i) := by
  choose S hS using hV
  refine ⟨⋃ i, S i, ?_⟩
  ext P
  simp only [Set.mem_iInter, AlgebraicSet, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hP f ⟨i, hfi⟩
    have := hP i
    rw [hS i] at this
    exact this f hfi
  · intro hP i
    rw [hS i]
    intro f hf
    exact hP f ⟨i, hf⟩

/-- Lemma 16.4/16.5: the product of two irreducible affine algebraic sets is irreducible
(the product of two affine varieties is again an affine variety). -/
theorem productVariety (m n : ℕ)
    (S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k)))
    (S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (hX : IsIrreducibleAlgebraicSet k m (AlgebraicSet k m S_X))
    (hY : IsIrreducibleAlgebraicSet k n (AlgebraicSet k n S_Y)) :
    IsIrreducibleAlgebraicSet k (m + n) (ProductAlgebraicSet k m n S_X S_Y) := by
  constructor
  · exact productAlgebraicSet_nonempty k m n S_X S_Y hX.nonempty hY.nonempty
  · intro V₁ V₂ hV₁_alg hV₂_alg hcover

    obtain ⟨T₁, hT₁⟩ := hV₁_alg
    obtain ⟨T₂, hT₂⟩ := hV₂_alg

    set X := AlgebraicSet k m S_X with hX_def
    set Y := AlgebraicSet k n S_Y with hY_def
    set XY := ProductAlgebraicSet k m n S_X S_Y with hXY_def

    have hV₁_sub_XY : V₁ ⊆ XY := by rw [hcover]; exact Set.subset_union_left
    have hV₂_sub_XY : V₂ ⊆ XY := by rw [hcover]; exact Set.subset_union_right

    have fiber_covers : ∀ b ∈ Y, ∀ a ∈ X,
        Fin.append a b ∈ V₁ ∨ Fin.append a b ∈ V₂ := by
      intro b hb a ha
      have hmem : Fin.append a b ∈ XY := by
        rw [mem_productAlgebraicSet]
        exact ⟨by rwa [projLeft_append], by rwa [projRight_append]⟩
      rw [hcover] at hmem
      exact hmem

    have fiber₁_alg : ∀ b, IsAlgebraicSubset k m
        {a : AffineSpace_k k m | Fin.append a b ∈ V₁} := by
      intro b; rw [hT₁]; exact algebraicSubset_fiber_left k m n T₁ b
    have fiber₂_alg : ∀ b, IsAlgebraicSubset k m
        {a : AffineSpace_k k m | Fin.append a b ∈ V₂} := by
      intro b; rw [hT₂]; exact algebraicSubset_fiber_left k m n T₂ b

    have hfib₁_sub : ∀ b, {a | Fin.append a b ∈ V₁} ⊆ X := by
      intro b a ha
      have hmem := hV₁_sub_XY ha
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨h1, _⟩ := hmem
      rwa [projLeft_append] at h1
    have hfib₂_sub : ∀ b, {a | Fin.append a b ∈ V₂} ⊆ X := by
      intro b a ha
      have hmem := hV₂_sub_XY ha
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨h1, _⟩ := hmem
      rwa [projLeft_append] at h1

    have fiber_irred : ∀ b ∈ Y,
        {a | Fin.append a b ∈ V₁} = X ∨ {a | Fin.append a b ∈ V₂} = X := by
      intro b hb
      have hcov : X ⊆ {a | Fin.append a b ∈ V₁} ∪ {a | Fin.append a b ∈ V₂} :=
        fun a ha => fiber_covers b hb a ha
      have hX_eq : X = {a | Fin.append a b ∈ V₁} ∪ {a | Fin.append a b ∈ V₂} :=
        Set.Subset.antisymm hcov (Set.union_subset (hfib₁_sub b) (hfib₂_sub b))
      exact hX.2 _ _ (fiber₁_alg b) (fiber₂_alg b) hX_eq


    set Y₁ := ⋂ (a : X), {b : AffineSpace_k k n | Fin.append a.1 b ∈ V₁} with hY₁_def
    set Y₂ := ⋂ (a : X), {b : AffineSpace_k k n | Fin.append a.1 b ∈ V₂} with hY₂_def

    have hY₁_alg : IsAlgebraicSubset k n Y₁ := by
      apply isAlgebraicSubset_iInter
      intro ⟨a, _⟩
      rw [hT₁]
      exact algebraicSubset_fiber_right k m n T₁ a
    have hY₂_alg : IsAlgebraicSubset k n Y₂ := by
      apply isAlgebraicSubset_iInter
      intro ⟨a, _⟩
      rw [hT₂]
      exact algebraicSubset_fiber_right k m n T₂ a

    have hY₁_sub : Y₁ ⊆ Y := by
      intro b hb
      obtain ⟨a, ha⟩ := hX.nonempty
      have := Set.mem_iInter.mp hb ⟨a, ha⟩
      simp only [Set.mem_setOf_eq] at this
      have hmem := hV₁_sub_XY this
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨_, h2⟩ := hmem
      rwa [projRight_append] at h2
    have hY₂_sub : Y₂ ⊆ Y := by
      intro b hb
      obtain ⟨a, ha⟩ := hX.nonempty
      have := Set.mem_iInter.mp hb ⟨a, ha⟩
      simp only [Set.mem_setOf_eq] at this
      have hmem := hV₂_sub_XY this
      rw [mem_productAlgebraicSet] at hmem
      obtain ⟨_, h2⟩ := hmem
      rwa [projRight_append] at h2

    have hY_cover : Y = Y₁ ∪ Y₂ := by
      ext b
      constructor
      · intro hb
        rcases fiber_irred b hb with h | h
        · left
          rw [hY₁_def]
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
          intro ⟨a, ha⟩
          have := h.symm ▸ ha
          exact this
        · right
          rw [hY₂_def]
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
          intro ⟨a, ha⟩
          have := h.symm ▸ ha
          exact this
      · intro hb
        rcases hb with hb | hb
        · exact hY₁_sub hb
        · exact hY₂_sub hb

    rcases hY.2 Y₁ Y₂ hY₁_alg hY₂_alg hY_cover with h | h
    ·
      left
      apply Set.Subset.antisymm hV₁_sub_XY
      intro P hP

      rw [mem_productAlgebraicSet] at hP
      obtain ⟨hPX, hPY⟩ := hP

      have hb_in_Y₁ : projRight k m n P ∈ Y₁ := h ▸ hPY

      have := Set.mem_iInter.mp hb_in_Y₁ ⟨projLeft k m n P, hPX⟩
      simp only [Set.mem_setOf_eq] at this
      rwa [append_proj] at this
    ·
      right
      apply Set.Subset.antisymm hV₂_sub_XY
      intro P hP
      rw [mem_productAlgebraicSet] at hP
      obtain ⟨hPX, hPY⟩ := hP
      have hb_in_Y₂ : projRight k m n P ∈ Y₂ := h ▸ hPY
      have := Set.mem_iInter.mp hb_in_Y₂ ⟨projLeft k m n P, hPX⟩
      simp only [Set.mem_setOf_eq] at this
      rwa [append_proj] at this

/-- The $\overline{k}$-vanishing ideal of a subset $V \subseteq \overline{k}^n$: polynomials
in $\overline{k}[x_1, \ldots, x_n]$ that vanish on $V$. -/
def vanishingIdeal_kbar (n : ℕ) (V : Set (AffineSpace_k k n)) :
    Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)) where
  carrier := {f | ∀ P ∈ V, MvPolynomial.eval P f = 0}
  add_mem' := by
    intro a b ha hb P hP
    simp [ha P hP, hb P hP]
  zero_mem' := by intro P _; simp
  smul_mem' := by intro c f hf P hP; simp [hf P hP]

/-- $S \subseteq I(V(S))$: every polynomial in $S$ vanishes on its own zero set. -/
lemma subset_vanishingIdeal_algebraicSet (n : ℕ)
    (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    S ⊆ ↑(vanishingIdeal_kbar k n (AlgebraicSet k n S)) := by
  intro f hf P hP
  exact hP f hf

/-- The algebraic set operator is antitone: $S \subseteq T$ implies $V(T) \subseteq V(S)$. -/
lemma algebraicSet_anti (n : ℕ)
    {S T : Set (MvPolynomial (Fin n) (AlgebraicClosure k))} (h : S ⊆ T) :
    AlgebraicSet k n T ⊆ AlgebraicSet k n S := by
  intro P hP f hf
  exact hP f (h hf)

/-- $V \subseteq V(I(V))$: every point of $V$ lies in the zero set of its vanishing ideal. -/
lemma subset_algebraicSet_vanishingIdeal (n : ℕ) (V : Set (AffineSpace_k k n)) :
    V ⊆ AlgebraicSet k n ↑(vanishingIdeal_kbar k n V) := by
  intro P hP f hf
  exact hf P hP

/-- Closure-like idempotence: $V(I(V(S))) = V(S)$. -/
lemma algebraicSet_vanishingIdeal_eq (n : ℕ)
    (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    AlgebraicSet k n ↑(vanishingIdeal_kbar k n (AlgebraicSet k n S)) = AlgebraicSet k n S :=
  Set.Subset.antisymm
    (algebraicSet_anti k n (subset_vanishingIdeal_algebraicSet k n S))
    (subset_algebraicSet_vanishingIdeal k n (AlgebraicSet k n S))

/-- The vanishing ideal operator is antitone in the subset argument. -/
lemma vanishingIdeal_kbar_anti (n : ℕ) {V W : Set (AffineSpace_k k n)} (h : V ⊆ W) :
    vanishingIdeal_kbar k n W ≤ vanishingIdeal_kbar k n V := by
  intro f hf P hP
  exact hf P (h hP)

/-- The vanishing ideal operator is injective on algebraic sets: equal ideals implies
equal algebraic sets. -/
lemma vanishingIdeal_kbar_injective_on_algebraicSets (n : ℕ)
    {S₁ S₂ : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
    (heq : vanishingIdeal_kbar k n (AlgebraicSet k n S₁) =
           vanishingIdeal_kbar k n (AlgebraicSet k n S₂)) :
    AlgebraicSet k n S₁ = AlgebraicSet k n S₂ := by
  rw [← algebraicSet_vanishingIdeal_eq k n S₁, ← algebraicSet_vanishingIdeal_eq k n S₂, heq]

/-- Strict antitone: a proper inclusion of algebraic sets gives a strict inclusion of
vanishing ideals (in the reverse direction). -/
lemma vanishingIdeal_kbar_strictAnti_algebraicSets (n : ℕ)
    {S₁ S₂ : Set (MvPolynomial (Fin n) (AlgebraicClosure k))}
    (h : AlgebraicSet k n S₁ ⊂ AlgebraicSet k n S₂) :
    vanishingIdeal_kbar k n (AlgebraicSet k n S₂) <
    vanishingIdeal_kbar k n (AlgebraicSet k n S₁) := by
  refine lt_of_le_of_ne (vanishingIdeal_kbar_anti k n h.le) ?_
  intro heq
  exact h.ne (vanishingIdeal_kbar_injective_on_algebraicSets k n heq.symm)


/-- The vanishing ideal is injective on Zariski-closed subsets of $\overline{k}^n$. -/
lemma vanishingIdeal_kbar_injective_closeds (n : ℕ)
    {V₁ V₂ : Set (AffineSpace_k k n)}
    (hV₁ : IsAlgebraicSetAffine k n V₁) (hV₂ : IsAlgebraicSetAffine k n V₂)
    (heq : vanishingIdeal_kbar k n V₁ = vanishingIdeal_kbar k n V₂) :
    V₁ = V₂ := by
  obtain ⟨S₁, rfl⟩ := hV₁
  obtain ⟨S₂, rfl⟩ := hV₂
  exact vanishingIdeal_kbar_injective_on_algebraicSets k n heq


/-- Affine space $\overline{k}^n$ equipped with the Zariski topology is a Noetherian
topological space (consequence of the Hilbert basis theorem). -/
theorem affineSpace_noetherianSpace (n : ℕ) :
    @TopologicalSpace.NoetherianSpace _ (zariskiTopology k n) := by
  letI inst : TopologicalSpace (AffineSpace_k k n) := zariskiTopology k n

  exact ((TopologicalSpace.noetherianSpace_TFAE (AffineSpace_k k n)).out 0 1).mpr <| by
    constructor


    apply Subrelation.wf (r := InvImage (· > ·) (fun C : TopologicalSpace.Closeds (AffineSpace_k k n) =>
      vanishingIdeal_kbar k n C.carrier))
    ·
      intro ⟨a, ha⟩ ⟨b, hb⟩ (hab : (⟨a, ha⟩ : TopologicalSpace.Closeds _) < ⟨b, hb⟩)
      show vanishingIdeal_kbar k n a > vanishingIdeal_kbar k n b
      have ha' := (isClosed_zariskiTopology_iff_isAlgebraicSet k n a).mp ha
      have hb' := (isClosed_zariskiTopology_iff_isAlgebraicSet k n b).mp hb


      have hab_sub : a ⊆ b := hab.le
      have h_le : vanishingIdeal_kbar k n b ≤ vanishingIdeal_kbar k n a :=
        vanishingIdeal_kbar_anti k n hab_sub

      have h_ne : vanishingIdeal_kbar k n a ≠ vanishingIdeal_kbar k n b := by
        intro heq
        have := vanishingIdeal_kbar_injective_closeds k n ha' hb' heq
        exact hab.ne (SetLike.ext' this)
      exact lt_of_le_of_ne h_le h_ne.symm
    ·
      exact InvImage.wf _ (IsNoetherian.wf inferInstance)

/-- Every subset of $\overline{k}^n$ (with the Zariski topology) is quasi-compact, a
consequence of $\overline{k}^n$ being Noetherian. -/
theorem affineSpace_quasiCompact (n : ℕ) (S : Set (AffineSpace_k k n)) :
    @IsCompact _ (zariskiTopology k n) S := by
  letI : TopologicalSpace (AffineSpace_k k n) := zariskiTopology k n
  haveI := affineSpace_noetherianSpace k n
  exact TopologicalSpace.NoetherianSpace.isCompact S

section Lemma163

open MvPolynomial

variable {k} {n : ℕ}

/-- If $P \in V$, then every polynomial vanishing on $V$ vanishes at $P$, i.e.
$I(V) \subseteq \ker(\mathrm{eval}_P)$. -/
lemma idealOfAlgebraicSet_le_ker_eval
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    idealOfAlgebraicSet V ≤ RingHom.ker (MvPolynomial.eval P) := by
  intro f hf
  rw [RingHom.mem_ker]
  exact hf P hP

/-- Evaluation at a point $P \in V$ descends to a ring homomorphism
$\overline{k}[V] \to \overline{k}$ from the coordinate ring. -/
noncomputable def evalOnCoordinateRingBar
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    AffineCoordinateRingBar V →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet V) (MvPolynomial.eval P)
    (idealOfAlgebraicSet_le_ker_eval V P hP)

/-- The descended evaluation commutes with the quotient map: it agrees with `eval P` on
polynomials. -/
lemma evalOnCoordinateRingBar_mk
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V)
    (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    evalOnCoordinateRingBar V P hP (Ideal.Quotient.mk _ f) = MvPolynomial.eval P f :=
  Ideal.Quotient.lift_mk _ _ _

/-- The evaluation map $\overline{k}[V] \to \overline{k}$ at a point of $V$ is surjective. -/
lemma evalOnCoordinateRingBar_surjective
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    Function.Surjective (evalOnCoordinateRingBar V P hP) := by
  intro c
  exact ⟨Ideal.Quotient.mk _ (MvPolynomial.C c), by
    rw [evalOnCoordinateRingBar_mk, MvPolynomial.eval_C]⟩

/-- The maximal ideal $\mathfrak{m}_P \subseteq \overline{k}[V]$ associated to a point
$P \in V$, defined as the kernel of evaluation at $P$. -/
noncomputable def maximalIdealOfPoint
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    Ideal (AffineCoordinateRingBar V) :=
  RingHom.ker (evalOnCoordinateRingBar V P hP)

/-- The ideal $\mathfrak{m}_P$ is maximal, since it is the kernel of a surjection onto a field. -/
theorem maximalIdealOfPoint_isMaximal
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    (maximalIdealOfPoint V P hP).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (evalOnCoordinateRingBar_surjective V P hP)

/-- Pulling back $\mathfrak{m}_P$ along the quotient map recovers the kernel of `eval P`. -/
lemma comap_maximalIdealOfPoint_eq_ker_eval
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V))
      (maximalIdealOfPoint V P hP) = RingHom.ker (MvPolynomial.eval P) := by
  ext f
  simp only [maximalIdealOfPoint, Ideal.mem_comap, RingHom.mem_ker]
  change evalOnCoordinateRingBar V P hP (Ideal.Quotient.mk _ f) = 0 ↔ _
  rw [evalOnCoordinateRingBar_mk]

/-- The map $P \mapsto \mathfrak{m}_P$ from points of $V$ to maximal ideals of $\overline{k}[V]$
is injective. -/
theorem maximalIdealOfPoint_injective
    (V : Set (AffineSpace_k k n))
    (P₁ P₂ : AffineSpace_k k n) (hP₁ : P₁ ∈ V) (hP₂ : P₂ ∈ V)
    (heq : maximalIdealOfPoint V P₁ hP₁ = maximalIdealOfPoint V P₂ hP₂) :
    P₁ = P₂ := by

  have hker : RingHom.ker (MvPolynomial.eval P₁) =
      RingHom.ker (MvPolynomial.eval (R := AlgebraicClosure k) P₂) := by
    rw [← comap_maximalIdealOfPoint_eq_ker_eval V P₁ hP₁,
        ← comap_maximalIdealOfPoint_eq_ker_eval V P₂ hP₂, heq]


  ext i
  have hmem : MvPolynomial.X i - MvPolynomial.C (P₁ i) ∈
      RingHom.ker (MvPolynomial.eval (R := AlgebraicClosure k) P₁) := by
    simp [RingHom.mem_ker]
  rw [hker] at hmem
  simp [RingHom.mem_ker] at hmem
  exact (sub_eq_zero.mp hmem).symm

/-- For an algebraic subset $V$, $I(V) \subseteq I(\{P\})$ iff $P \in V$. -/
lemma idealOfAlgebraicSet_le_vanishingIdeal_singleton_iff
    (V : Set (AffineSpace_k k n))
    (hV : IsAlgebraicSubset k n V)
    (P : AffineSpace_k k n) :
    idealOfAlgebraicSet V ≤
      MvPolynomial.vanishingIdeal (AlgebraicClosure k)
        ({P} : Set (AffineSpace_k k n)) ↔ P ∈ V := by
  rw [idealOfAlgebraicSet_eq_vanishingIdeal]
  constructor
  · intro h
    obtain ⟨S, rfl⟩ := hV

    intro f hf

    have hfV : f ∈ MvPolynomial.vanishingIdeal (AlgebraicClosure k)
        (AlgebraicSet k n S) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro Q hQ
      rw [MvPolynomial.aeval_eq_eval]
      exact hQ f hf

    have hfP := h hfV
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hfP
    have := hfP P (Set.mem_singleton P)
    rwa [MvPolynomial.aeval_eq_eval] at this
  · intro hP f hf
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
    intro Q hQ
    rw [Set.mem_singleton_iff] at hQ
    subst hQ
    exact hf Q hP

/-- Lemma 16.3: for an affine algebraic subset $V$, the map $P \mapsto \mathfrak{m}_P$ is a
bijection from points of $V$ to maximal ideals of $\overline{k}[V]$. -/
theorem lemma_16_3
    (V : Set (AffineSpace_k k n))
    (hV : IsAlgebraicSubset k n V) :
    Function.Bijective
      (fun (Pt : V) => ⟨maximalIdealOfPoint V Pt.1 Pt.2,
        maximalIdealOfPoint_isMaximal V Pt.1 Pt.2⟩ :
        V → {m : Ideal (AffineCoordinateRingBar V) // m.IsMaximal}) := by
  constructor
  ·
    intro ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩ heq
    simp only [Subtype.mk.injEq] at heq
    exact Subtype.ext (maximalIdealOfPoint_injective V P₁ P₂ hP₁ hP₂ heq)
  ·
    intro ⟨mbar, hmbar⟩

    set m := Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V)) mbar

    have hm_max : m.IsMaximal := by
      unfold AffineCoordinateRingBar at mbar hmbar
      haveI : mbar.IsMaximal := hmbar
      exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

    obtain ⟨P, hP_eq⟩ := maximal_ideal_eq_vanishingIdeal_singleton k m hm_max

    have hIV_le_m : idealOfAlgebraicSet V ≤ m := by
      intro f hf
      show Ideal.Quotient.mk (idealOfAlgebraicSet V) f ∈ mbar
      have : Ideal.Quotient.mk (idealOfAlgebraicSet V) f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hf
      rw [this]
      exact mbar.zero_mem

    rw [hP_eq] at hIV_le_m

    have hPV : P ∈ V :=
      (idealOfAlgebraicSet_le_vanishingIdeal_singleton_iff V hV P).mp hIV_le_m

    use ⟨P, hPV⟩
    simp only [Subtype.mk.injEq]


    have hinj : Function.Injective
        (Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V)) :
          Ideal (AffineCoordinateRingBar V) →
          Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))) := by
      intro I₁ I₂ h
      have hsurj : ∀ (I : Ideal (AffineCoordinateRingBar V)),
          Ideal.map (Ideal.Quotient.mk (idealOfAlgebraicSet V))
            (Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet V)) I) = I :=
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← hsurj I₁, ← hsurj I₂, h]
    apply hinj

    rw [comap_maximalIdealOfPoint_eq_ker_eval]


    show RingHom.ker (MvPolynomial.eval P) = m


    rw [hP_eq, ker_eval_eq_vanishingIdeal_singleton k P]

end Lemma163

open MvPolynomial

/-- The product projective space $\mathbb{P}^m \times \mathbb{P}^n$ over $k$ as a Cartesian
product of projective spaces. -/
def ProductProjectiveSpace (k : Type*) [Field k] (m n : ℕ) : Type _ :=
  ProjectiveSpace_k k m × ProjectiveSpace_k k n

/-- A *bihomogeneous polynomial* of bi-degree $(d_X, d_Y)$: a polynomial in
$m + 1 + (n + 1)$ variables which is homogeneous of degree $d_X$ in the first $m + 1$
variables and homogeneous of degree $d_Y$ in the last $n + 1$ variables. -/
structure BihomogPoly (k : Type*) [Field k] (m n : ℕ) where
  poly : MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)
  degX : ℕ
  degY : ℕ
  homogX : ∀ (c : AlgebraicClosure k) (v : Fin (m + 1 + (n + 1)) → AlgebraicClosure k),
    eval (fun i => if i.val < m + 1 then c * v i else v i) poly =
    c ^ degX * eval v poly
  homogY : ∀ (c : AlgebraicClosure k) (v : Fin (m + 1 + (n + 1)) → AlgebraicClosure k),
    eval (fun i => if i.val < m + 1 then v i else c * v i) poly =
    c ^ degY * eval v poly

/-- Embedding $\overline{k}[x_0, \ldots, x_m] \hookrightarrow$ the bigger polynomial ring in
$m + 1 + (n + 1)$ variables, on the first $m + 1$ variables. -/
noncomputable def embedHomogPolyLeft {k : Type*} [Field k] (m n : ℕ) :
    MvPolynomial (Fin (m + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.castAdd (n + 1))

/-- Embedding $\overline{k}[y_0, \ldots, y_n] \hookrightarrow$ the bigger polynomial ring in
$m + 1 + (n + 1)$ variables, on the last $n + 1$ variables. -/
noncomputable def embedHomogPolyRight {k : Type*} [Field k] (m n : ℕ) :
    MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.natAdd (m + 1))

/-- Image of a set of homogeneous polynomials under `embedHomogPolyLeft`. -/
def embedHomogSetLeft {k : Type*} [Field k] (m n : ℕ)
    (S : Set (MvPolynomial (Fin (m + 1)) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  (embedHomogPolyLeft m n) '' S

/-- Image of a set of homogeneous polynomials under `embedHomogPolyRight`. -/
def embedHomogSetRight {k : Type*} [Field k] (m n : ℕ)
    (S : Set (MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  (embedHomogPolyRight m n) '' S

/-- Evaluating $\mathrm{embedHomogPolyLeft}(p)$ at `Fin.append a b` equals evaluating $p$
at $a$. -/
theorem eval_embedHomogPolyLeft {k : Type*} [Field k] (m n : ℕ)
    (p : MvPolynomial (Fin (m + 1)) (AlgebraicClosure k))
    (a : Fin (m + 1) → AlgebraicClosure k) (b : Fin (n + 1) → AlgebraicClosure k) :
    eval (Fin.append a b) (embedHomogPolyLeft m n p) = eval a p := by
  simp only [embedHomogPolyLeft, eval_rename]
  have : Fin.append a b ∘ Fin.castAdd (n + 1) = a := by
    funext i; exact Fin.append_left a b i
  rw [this]

/-- Evaluating $\mathrm{embedHomogPolyRight}(p)$ at `Fin.append a b` equals evaluating $p$
at $b$. -/
theorem eval_embedHomogPolyRight {k : Type*} [Field k] (m n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))
    (a : Fin (m + 1) → AlgebraicClosure k) (b : Fin (n + 1) → AlgebraicClosure k) :
    eval (Fin.append a b) (embedHomogPolyRight m n p) = eval b p := by
  simp only [embedHomogPolyRight, eval_rename]
  have : Fin.append a b ∘ Fin.natAdd (m + 1) = b := by
    funext i; exact Fin.append_right a b i
  rw [this]

/-- The combined polynomial set: union of the embeddings of homogeneous polynomial sets from
$\mathbb{P}^m$ and $\mathbb{P}^n$ into the bigger polynomial ring. -/
def combinedHomogPolySet {k : Type*} [Field k] (m n : ℕ)
    (S_X : Set (HomogPoly k m))
    (S_Y : Set (HomogPoly k n)) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  embedHomogSetLeft m n (HomogPoly.poly '' S_X) ∪
  embedHomogSetRight m n (HomogPoly.poly '' S_Y)

/-- Vanishing of the combined homogeneous polynomial set is invariant under rescaling each
of the two homogeneous coordinate vectors by a nonzero scalar (well-definedness on
projective coordinates). -/
lemma combinedHomogPolySet_vanish_of_rescale {k : Type*} [Field k] {m n : ℕ}
    {S_X : Set (HomogPoly k m)} {S_Y : Set (HomogPoly k n)}
    {a₁ : Fin (m + 1) → AlgebraicClosure k} {b₁ : Fin (n + 1) → AlgebraicClosure k}
    {a₂ : Fin (m + 1) → AlgebraicClosure k} {b₂ : Fin (n + 1) → AlgebraicClosure k}
    {c d : AlgebraicClosure k} (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : a₁ = fun i => c * a₂ i) (hb : b₁ = fun i => d * b₂ i)
    (h : ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₁ b₁) f = 0) :
    ∀ f ∈ combinedHomogPolySet m n S_X S_Y, eval (Fin.append a₂ b₂) f = 0 := by
  intro f hf
  simp only [combinedHomogPolySet, Set.mem_union, embedHomogSetLeft, embedHomogSetRight,
    Set.mem_image] at hf
  rcases hf with ⟨p, ⟨g, hgS, rfl⟩, rfl⟩ | ⟨q, ⟨g, hgS, rfl⟩, rfl⟩
  · have hmem : (embedHomogPolyLeft m n) g.poly ∈ combinedHomogPolySet m n S_X S_Y :=
      Set.mem_union_left _ ⟨g.poly, ⟨g, hgS, rfl⟩, rfl⟩
    have heval := h _ hmem
    rw [eval_embedHomogPolyLeft] at heval ⊢
    rw [ha, homog_eval_rescale] at heval
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hc)
  · have hmem : (embedHomogPolyRight m n) g.poly ∈ combinedHomogPolySet m n S_X S_Y :=
      Set.mem_union_right _ ⟨g.poly, ⟨g, hgS, rfl⟩, rfl⟩
    have heval := h _ hmem
    rw [eval_embedHomogPolyRight] at heval ⊢
    rw [hb, homog_eval_rescale] at heval
    exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hd)

/-- The product projective algebraic set in $\mathbb{P}^m \times \mathbb{P}^n$ cut out by
two sets of homogeneous polynomials, defined as the common zero locus of the combined set
on the quotient $\mathbb{P}^m \times \mathbb{P}^n$. -/
def ProductProjectiveAlgebraicSet {k : Type*} [Field k] (m n : ℕ)
    (S_X : Set (HomogPoly k m))
    (S_Y : Set (HomogPoly k n)) :
    Set (ProductProjectiveSpace k m n) :=
  {PQ | Quotient.liftOn₂ PQ.1 PQ.2
    (fun v w => ∀ f ∈ combinedHomogPolySet m n S_X S_Y,
      eval (Fin.append v.1 w.1) f = 0)
    (by
      intro a₁ b₁ a₂ b₂ ⟨c, hc, hab1⟩ ⟨d, hd, hab2⟩
      simp only [eq_iff_iff]
      constructor
      · exact combinedHomogPolySet_vanish_of_rescale hc hd
          (funext (hab1 ·)) (funext (hab2 ·))
      · exact combinedHomogPolySet_vanish_of_rescale
          (inv_ne_zero hc) (inv_ne_zero hd)
          (funext fun i => by rw [hab1 i, inv_mul_cancel_left₀ hc])
          (funext fun i => by rw [hab2 i, inv_mul_cancel_left₀ hd]))}

/-- A subset $V \subseteq \mathbb{P}^m \times \mathbb{P}^n$ is a product projective algebraic
set if it equals `ProductProjectiveAlgebraicSet S_X S_Y` for some homogeneous polynomial sets. -/
def IsProductProjectiveAlgSet {k : Type*} [Field k] (m n : ℕ)
    (V : Set (ProductProjectiveSpace k m n)) : Prop :=
  ∃ (S_X : Set (HomogPoly k m)) (S_Y : Set (HomogPoly k n)),
    V = ProductProjectiveAlgebraicSet m n S_X S_Y

/-- A point $(P, Q) \in \mathbb{P}^m \times \mathbb{P}^n$ lies in the product projective
algebraic set iff $P$ lies in the projective vanishing set of $S_X$ and $Q$ lies in the
projective vanishing set of $S_Y$. -/
theorem mem_productProjectiveAlgebraicSet {k : Type*} [Field k] (m n : ℕ)
    (S_X : Set (HomogPoly k m))
    (S_Y : Set (HomogPoly k n))
    (PQ : ProductProjectiveSpace k m n) :
    PQ ∈ ProductProjectiveAlgebraicSet m n S_X S_Y ↔
    PQ.1 ∈ ProjVanishingSet k m S_X ∧
    PQ.2 ∈ ProjVanishingSet k n S_Y := by
  obtain ⟨P, Q⟩ := PQ
  obtain ⟨v, rfl⟩ := P.exists_rep
  obtain ⟨w, rfl⟩ := Q.exists_rep
  simp only [ProductProjectiveAlgebraicSet, Set.mem_setOf_eq,
    ProjVanishingSet, Quotient.liftOn_mk]
  constructor
  · intro h
    exact ⟨fun f hf => by
      have := h _ (Set.mem_union_left _ ⟨f.poly, ⟨f, hf, rfl⟩, rfl⟩)
      rwa [eval_embedHomogPolyLeft] at this,
    fun f hf => by
      have := h _ (Set.mem_union_right _ ⟨f.poly, ⟨f, hf, rfl⟩, rfl⟩)
      rwa [eval_embedHomogPolyRight] at this⟩
  · intro ⟨hP, hQ⟩ f hf
    simp only [combinedHomogPolySet, Set.mem_union, embedHomogSetLeft, embedHomogSetRight,
      Set.mem_image] at hf
    rcases hf with ⟨p, ⟨g, hgS, rfl⟩, rfl⟩ | ⟨q, ⟨g, hgS, rfl⟩, rfl⟩
    · rw [eval_embedHomogPolyLeft]; exact hP g hgS
    · rw [eval_embedHomogPolyRight]; exact hQ g hgS


/-- Concatenation of two vectors of homogeneous coordinates from $\mathbb{A}^{m+1}$ and
$\mathbb{A}^{n+1}$ into a single vector in $\mathbb{A}^{m+1+(n+1)}$. -/
def concatVec {k : Type*} [Field k] (m n : ℕ) (a : Fin (m + 1) → AlgebraicClosure k)
    (b : Fin (n + 1) → AlgebraicClosure k) :
    Fin (m + 1 + (n + 1)) → AlgebraicClosure k :=
  Fin.append a b

/-- The Segre map on coordinates: $((a_i), (b_j)) \mapsto (a_i b_j)_{i,j}$, sending
$\mathbb{A}^{m+1} \times \mathbb{A}^{n+1} \to \mathbb{A}^{(m+1)(n+1)}$, indexed by
the pair $(i, j)$ encoded as $i \cdot (n+1) + j$. -/
noncomputable def segreMap {k : Type*} [Field k] (m n : ℕ)
    (a : Fin (m + 1) → AlgebraicClosure k)
    (b : Fin (n + 1) → AlgebraicClosure k) :
    Fin ((m + 1) * (n + 1)) → AlgebraicClosure k :=
  fun ij => a (Fin.mk (ij.val / (n + 1))
              (Nat.div_lt_of_lt_mul (Nat.mul_comm (m+1) (n+1) ▸ ij.isLt))) *
            b (Fin.mk (ij.val % (n + 1)) (Nat.mod_lt _ (by omega)))
