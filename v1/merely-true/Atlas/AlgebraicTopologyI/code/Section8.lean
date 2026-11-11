/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Atlas.AlgebraicTopologyI.code.Section6

namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- A pair of consecutive group homomorphisms `f`, `g` forms a complex when `g ∘ f = 0`,
i.e. the image of `f` is contained in the kernel of `g`. This is the "complex" half of
Definition 8.1's notion of an exact sequence: a sequence whose composites all vanish. -/
def isComplex (f : A →+ B) (g : B →+ C) : Prop := ∀ a, g (f a) = 0

/-- Exactness at the middle term of `A →+ B →+ C`: the image of `f` equals the kernel of `g`.
This formalizes the equality `im f = ker g` from Definition 8.1 by reusing Mathlib's
`Function.Exact`. -/
abbrev exactAt (f : A →+ B) (g : B →+ C) : Prop := Function.Exact f g

/-- A short exact sequence `0 → A → B → C → 0` of abelian groups, packaged as the
injectivity of `i`, the surjectivity of `p`, and exactness at the middle term `B`.
This realizes Definition 8.3. -/
structure IsShortExact (i : A →+ B) (p : B →+ C) : Prop where
  injective : Function.Injective i
  surjective : Function.Surjective p
  exact : Function.Exact i p

/-- A chain complex indexed by the integers: a sequence of abelian groups `X n` together
with differentials `d : X n →+ X (n - 1)` satisfying `d ∘ d = 0`. This is the structure
underlying Definition 1.6, used here as the ambient setting for relative chain complexes. -/
structure IntChainComplex where
  X : ℤ → Type*
  instAddCommGroup : ∀ n, AddCommGroup (X n)
  d : ∀ n, X n →+ X (n - 1)
  d_comp_d : ∀ n, (d (n - 1)).comp (d n) = 0

attribute [instance] IntChainComplex.instAddCommGroup

/-- A subcomplex of an integer-indexed chain complex `B`: a choice of subgroup in each
degree that is closed under the differential `d`. This is the input data for
forming the quotient chain complex in Lemma 8.4. -/
structure IntChainComplex.Subcomplex (B : IntChainComplex) where
  toSubgroup : ∀ n, AddSubgroup (B.X n)
  d_maps : ∀ n (x : B.X n), x ∈ toSubgroup n → B.d n x ∈ toSubgroup (n - 1)

/-- A chain map between integer-indexed chain complexes: a family of group homomorphisms
commuting with the differentials in each degree. -/
structure IntChainMap (B C : IntChainComplex) where
  f : ∀ n, B.X n →+ C.X n
  comm : ∀ n, (C.d n).comp (f n) = (f (n - 1)).comp (B.d n)

/-- The induced differential on the quotient `B.X n / A.toSubgroup n`, obtained by
descending `d : B.X n →+ B.X (n - 1)` through the projection. This realizes the
existence half of Lemma 8.4 in the integer-indexed setting. -/
noncomputable def IntChainComplex.Subcomplex.quotientD
    (B : IntChainComplex) (A : B.Subcomplex) (n : ℤ) :
    B.X n ⧸ A.toSubgroup n →+ B.X (n - 1) ⧸ A.toSubgroup (n - 1) :=
  QuotientAddGroup.lift (A.toSubgroup n)
    ((QuotientAddGroup.mk' (A.toSubgroup (n - 1))).comp (B.d n))
    (fun x hx => by
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff]
      exact A.d_maps n x hx)

/-- The induced differential on the quotient squares to zero, so the quotient really
forms a chain complex (the `d ∘ d = 0` half of Lemma 8.4). -/
theorem IntChainComplex.Subcomplex.quotientD_comp_quotientD
    (B : IntChainComplex) (A : B.Subcomplex) (n : ℤ) :
    (A.quotientD B (n - 1)).comp (A.quotientD B n) = 0 := by
  apply QuotientAddGroup.addMonoidHom_ext
  ext x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, quotientD,
    QuotientAddGroup.lift_mk', QuotientAddGroup.mk'_apply]
  have h := DFunLike.congr_fun (B.d_comp_d n) x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at h
  simp [h]

/-- The quotient chain complex `B / A` of an integer-indexed chain complex by a
subcomplex: in degree `n` the group is `B.X n / A.toSubgroup n`, with the induced
differential. This packages the conclusion of Lemma 8.4. -/
noncomputable def IntChainComplex.Subcomplex.quotientComplex
    (B : IntChainComplex) (A : B.Subcomplex) : IntChainComplex where
  X n := B.X n ⧸ A.toSubgroup n
  instAddCommGroup _ := inferInstance
  d n := A.quotientD B n
  d_comp_d n := A.quotientD_comp_quotientD B n

/-- Uniqueness of the quotient differential: any family `d'` on the quotient groups
that makes the projection `B → B / A` into a chain map agrees with `quotientD`.
This is the uniqueness assertion of Lemma 8.4. -/
theorem IntChainComplex.Subcomplex.quotientComplex_unique
    (B : IntChainComplex) (A : B.Subcomplex)
    (d' : ∀ n, B.X n ⧸ A.toSubgroup n →+ B.X (n - 1) ⧸ A.toSubgroup (n - 1))
    (hcomm : ∀ n, (d' n).comp (QuotientAddGroup.mk' (A.toSubgroup n)) =
      (QuotientAddGroup.mk' (A.toSubgroup (n - 1))).comp (B.d n)) :
    ∀ n, d' n = A.quotientD B n := by
  intro n
  have h_quot : (A.quotientD B n).comp (QuotientAddGroup.mk' (A.toSubgroup n)) =
      (QuotientAddGroup.mk' (A.toSubgroup (n - 1))).comp (B.d n) :=
    QuotientAddGroup.lift_comp_mk' _ _ _
  rw [← sub_eq_zero]
  apply QuotientAddGroup.addMonoidHom_ext
  ext x
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    QuotientAddGroup.mk'_apply, sub_eq_zero]
  have h1 := DFunLike.congr_fun (hcomm n) x
  have h2 := DFunLike.congr_fun h_quot x
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply] at h1 h2
  rw [h1, h2]

/-- Transport a chain group along an equality of indices, packaged as a group
homomorphism `C.X m →+ C.X n` when `m = n`. Used to bridge mismatched indices
when defining the homology groups. -/
def IntChainComplex.castHom (C : IntChainComplex) {m n : ℤ} (h : m = n) :
    C.X m →+ C.X n where
  toFun x := h ▸ x
  map_zero' := by subst h; rfl
  map_add' _ _ := by subst h; rfl

/-- Compatibility of the differential with the cast homomorphism: applying `d` after
casting is the same as casting after applying `d`. -/
theorem IntChainComplex.d_castHom (C : IntChainComplex) {m n : ℤ} (h : m = n) (z : C.X m) :
    C.d n (C.castHom h z) = C.castHom (show m - 1 = n - 1 by omega) (C.d m z) := by
  subst h; rfl

/-- A reindexed differential `d' : C.X (n + 1) →+ C.X n` obtained from `d` by casting
the target along `n + 1 - 1 = n`. Convenient for stating cycles/boundaries
without subtraction in the index. -/
def IntChainComplex.d' (C : IntChainComplex) (n : ℤ) : C.X (n + 1) →+ C.X n :=
  (C.castHom (show n + 1 - 1 = n by omega)).comp (C.d (n + 1))

/-- The group of `n`-cycles `Z_n(C) = ker(d : C.X n →+ C.X (n - 1))`. Generalizes
Definition 1.4 to an abstract integer-indexed chain complex. -/
def IntChainComplex.cycles (C : IntChainComplex) (n : ℤ) : AddSubgroup (C.X n) :=
  AddMonoidHom.ker (C.d n)

/-- The group of `n`-boundaries `B_n(C) = im(d : C.X (n + 1) →+ C.X n)`. Generalizes
the boundary subgroup from Definition 1.7 to an abstract integer-indexed chain complex. -/
def IntChainComplex.boundaries (C : IntChainComplex) (n : ℤ) : AddSubgroup (C.X n) :=
  AddMonoidHom.range (C.d' n)

/-- The `n`th homology group `H_n(C) = Z_n(C) / B_n(C)` of an integer-indexed chain
complex, as in Definition 1.7. -/
noncomputable def IntChainComplex.homologyGroup (C : IntChainComplex) (n : ℤ) :=
  (C.cycles n) ⧸ (C.boundaries n).addSubgroupOf (C.cycles n)

/-- The homology group inherits an abelian group structure from the quotient construction. -/
noncomputable instance IntChainComplex.instAddCommGroupHomology
    (C : IntChainComplex) (n : ℤ) : AddCommGroup (C.homologyGroup n) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The `n`th relative homology of a chain complex `B` modulo a subcomplex `A`, defined
as the homology of the quotient complex `B / A`. This is the abstract algebraic
version of the relative homology of Definition 8.6. -/
noncomputable def RelativeHomology (n : ℤ) (B : IntChainComplex) (A : B.Subcomplex) :=
  (A.quotientComplex B).homologyGroup n

end ExactSequence

namespace AlgebraicTopologyI

open AlgebraicTopologyI

/-- Push a singular `n`-simplex of the subspace `A ⊆ X` forward along the inclusion
`A ↪ X` to obtain a singular `n`-simplex of `X`. -/
def singularSimplexInclusion (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    SingularSimplex n ↥A → SingularSimplex n X :=
  fun σ => ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ σ

/-- The inclusion of singular chain groups `S_n(A) →+ S_n(X)` induced by the inclusion
`A ↪ X`, obtained by freely extending `singularSimplexInclusion`. -/
def singularChainsInclusion (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    SingularChains n ↥A →+ SingularChains n X :=
  FreeAbelianGroup.map (singularSimplexInclusion n X A)

/-- The relative singular `n`-chains `S_n(X, A) = S_n(X) / S_n(A)`, defined by quotienting
the singular chains of `X` by the image of the inclusion from the singular chains
of `A`. This is the underlying group of Definition 8.5 in a single degree. -/
def RelativeSingularChains (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :=
  SingularChains n X ⧸ (singularChainsInclusion n X A).range

/-- The relative chain group `S_n(X, A)` inherits an abelian group structure from the
quotient. -/
instance RelativeSingularChains.instAddCommGroup
    (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    AddCommGroup (RelativeSingularChains n X A) :=
  inferInstanceAs (AddCommGroup (SingularChains n X ⧸ (singularChainsInclusion n X A).range))

/-- Taking the `i`th face commutes with pushforward along a continuous map: the
`i`th face of `f ∘ σ` equals `f` composed with the `i`th face of `σ`. -/
theorem SingularSimplex.map_face {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i : Fin (n + 2)) (σ : SingularSimplex (n + 1) X) :
    SingularSimplex.face i (SingularSimplex.map f σ) =
    SingularSimplex.map f (SingularSimplex.face i σ) := by
  simp [SingularSimplex.face, SingularSimplex.map, ContinuousMap.comp_assoc]

/-- Naturality of the singular boundary map: pushforward along a continuous map
commutes with the boundary, i.e. `f_* ∘ d = d ∘ f_*`. -/
theorem SingularChains.map_comp_boundaryMap {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (boundaryMap n Y).comp (SingularChains.map f) =
    (SingularChains.map f).comp (boundaryMap n X) := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  show boundaryMap n Y (SingularChains.map f (FreeAbelianGroup.of σ)) =
    SingularChains.map f (boundaryMap n X (FreeAbelianGroup.of σ))
  simp only [SingularChains.map, boundaryMap]
  erw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
  rw [map_sum]
  congr 1
  ext i
  dsimp
  erw [map_zsmul (FreeAbelianGroup.map (SingularSimplex.map f)),
    FreeAbelianGroup.map_of_apply, SingularSimplex.map_face]



/-- The inclusion `S_*(A) →+ S_*(X)` commutes with the boundary maps, exhibiting
`S_*(A)` as a subcomplex of `S_*(X)`. This is the input needed to form `S_*(X, A)`. -/
theorem singularChainsInclusion_comm_boundary (n : ℕ) (X : Type*) [TopologicalSpace X]
    (A : Set X) :
    (boundaryMap n X).comp (singularChainsInclusion (n + 1) X A) =
    (singularChainsInclusion n X A).comp (boundaryMap n ↥A) :=
  SingularChains.map_comp_boundaryMap
    (n := n) (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X))

/-- A non-negatively graded chain complex: a sequence of abelian groups `X n` for `n : ℕ`
together with differentials `d : X (n + 1) →+ X n` satisfying `d ∘ d = 0`. This is the
form most naturally suited to the singular chain complex. -/
structure NatChainComplex where
  X : ℕ → Type*
  instAddCommGroup : ∀ n, AddCommGroup (X n)
  d : ∀ n, X (n + 1) →+ X n
  d_comp_d : ∀ n, (d n).comp (d (n + 1)) = 0

attribute [instance] NatChainComplex.instAddCommGroup


/-- A subcomplex of a naturally indexed chain complex `B`: a subgroup in each degree
that is preserved by the differential. This will be used to package `S_*(A) ⊆ S_*(X)`. -/
structure NatChainComplex.Subcomplex (B : NatChainComplex) where
  toSubgroup : ∀ n, AddSubgroup (B.X n)
  d_maps : ∀ n (x : B.X (n + 1)), x ∈ toSubgroup (n + 1) → B.d n x ∈ toSubgroup n

/-- The induced differential on `B.X (n + 1) / A.toSubgroup (n + 1) →+ B.X n / A.toSubgroup n`,
defined by descending `B.d n` through the projection. This is the naturally indexed
analogue of `IntChainComplex.Subcomplex.quotientD` and the heart of Lemma 8.4. -/
noncomputable def NatChainComplex.Subcomplex.quotientD
    (B : NatChainComplex) (A : B.Subcomplex) (n : ℕ) :
    B.X (n + 1) ⧸ A.toSubgroup (n + 1) →+ B.X n ⧸ A.toSubgroup n :=
  QuotientAddGroup.lift (A.toSubgroup (n + 1))
    ((QuotientAddGroup.mk' (A.toSubgroup n)).comp (B.d n))
    (fun x hx => by
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff]
      exact A.d_maps n x hx)

/-- The induced differential on the quotient squares to zero (`d ∘ d = 0`), so the
quotient really forms a chain complex. -/
theorem NatChainComplex.Subcomplex.quotientD_comp_quotientD
    (B : NatChainComplex) (A : B.Subcomplex) (n : ℕ) :
    (A.quotientD B n).comp (A.quotientD B (n + 1)) = 0 := by
  apply QuotientAddGroup.addMonoidHom_ext
  ext x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply,
    QuotientAddGroup.mk'_apply]
  show (A.quotientD B n) ((A.quotientD B (n + 1)) (QuotientAddGroup.mk x)) = 0
  simp only [quotientD, QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply,
    QuotientAddGroup.mk'_apply]
  have h := DFunLike.congr_fun (B.d_comp_d n) x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] at h
  simp [h]

/-- The quotient chain complex `B / A` of a naturally indexed chain complex by a
subcomplex: degree `n` is `B.X n / A.toSubgroup n`, with the induced differential.
This realizes Lemma 8.4 in the `ℕ`-graded setting. -/
noncomputable def NatChainComplex.Subcomplex.quotientComplex
    (B : NatChainComplex) (A : B.Subcomplex) : NatChainComplex where
  X n := B.X n ⧸ A.toSubgroup n
  instAddCommGroup _ := inferInstance
  d n := A.quotientD B n
  d_comp_d n := A.quotientD_comp_quotientD B n



/-- The relative boundary map `S_{n+1}(X, A) →+ S_n(X, A)`, defined directly by
descending the singular boundary through the quotient by `S_*(A)`. -/
noncomputable def relativeBoundaryMap (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    RelativeSingularChains (n + 1) X A →+ RelativeSingularChains n X A :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' (singularChainsInclusion n X A).range).comp (boundaryMap n X))
    (fun x hx => by
      simp only [AddMonoidHom.mem_ker]
      obtain ⟨a, ha⟩ := hx
      rw [← ha]
      have h := DFunLike.congr_fun (singularChainsInclusion_comm_boundary n X A) a
      simp only [AddMonoidHom.comp_apply] at h
      show (QuotientAddGroup.mk' _) ((boundaryMap n X) ((singularChainsInclusion (n + 1) X A) a)) = 0
      rw [h, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨boundaryMap n ↥A a, rfl⟩)

/-- The relative boundary of the class `[c] ∈ S_{n+1}(X, A)` is the class of the
ordinary singular boundary `dc ∈ S_n(X)`. -/
@[simp]
theorem relativeBoundaryMap_mk (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X)
    (c : SingularChains (n + 1) X) :
    relativeBoundaryMap n X A (QuotientAddGroup.mk c) =
    QuotientAddGroup.mk (boundaryMap n X c) := by
  show QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk c) = _
  rw [QuotientAddGroup.lift_mk]
  rfl

/-- The group of `n`-cycles `Z_n(C)` of a naturally indexed chain complex. In degree
`0` everything is a cycle (since `S_{-1}` is zero); in positive degrees it is the
kernel of the differential. Compare Definition 1.4. -/
def NatChainComplex.cycles (C : NatChainComplex) (n : ℕ) : AddSubgroup (C.X n) :=
  match n with
  | 0 => ⊤
  | n + 1 => AddMonoidHom.ker (C.d n)

/-- The group of `n`-boundaries `B_n(C) = im(d : C.X (n + 1) →+ C.X n)` of a
naturally indexed chain complex. -/
def NatChainComplex.boundaries (C : NatChainComplex) (n : ℕ) : AddSubgroup (C.X n) :=
  AddMonoidHom.range (C.d n)

/-- The `n`th homology group `H_n(C) = Z_n(C) / B_n(C)` of a naturally indexed chain
complex, as in Definition 1.7. -/
noncomputable def NatChainComplex.homologyGroup (C : NatChainComplex) (n : ℕ) :=
  (C.cycles n) ⧸ (C.boundaries n).addSubgroupOf (C.cycles n)

/-- The homology group of a naturally indexed chain complex inherits its abelian
group structure from the quotient construction. -/
noncomputable instance NatChainComplex.instAddCommGroupHomology
    (C : NatChainComplex) (n : ℕ) : AddCommGroup (C.homologyGroup n) :=
  QuotientAddGroup.Quotient.addCommGroup _


end AlgebraicTopologyI
