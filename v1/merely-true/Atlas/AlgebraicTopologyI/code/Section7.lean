/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section6
import Atlas.AlgebraicTopologyI.code.CrossProductExistence
import Atlas.AlgebraicTopologyI.code.Section8

open ExactSequence

namespace HomologyCrossProduct

/-- A graded bilinear pairing of integer-indexed chain complexes
`A_* × B_* → C_*`: in every bidegree `(p, q)` a bilinear map
`A_p × B_q → C_{p+q}` satisfying the Leibniz rule
`d(a × b) = (da) × b + (-1)^p a × db` together with the boundary conditions
that cross-multiplying a boundary with a cycle (in either argument) lands in
the boundaries. These are exactly the data needed by Lemma 7.1 to induce a
bilinear pairing on homology. -/
structure GradedBilinearMap (A B C : IntChainComplex) where
  cross : ∀ (p q : ℤ), A.X p →+ (B.X q →+ C.X (p + q))
  leibniz_d : ∀ (p q : ℤ) (a : A.X p) (b : B.X q),
    C.d (p + q) ((cross p q) a b) =
      C.castHom (show (p - 1) + q = p + q - 1 by omega)
        ((cross (p - 1) q) (A.d p a) b) +
      (-1 : ℤ) ^ p.toNat •
        C.castHom (show p + (q - 1) = p + q - 1 by omega)
          ((cross p (q - 1)) a (B.d q b))
  cross_boundary_left : ∀ (p q : ℤ) (a_bar : A.X (p + 1)) (b : B.X q),
    b ∈ B.cycles q →
    (cross p q) (A.d' p a_bar) b ∈ C.boundaries (p + q)
  cross_boundary_right : ∀ (p q : ℤ) (a : A.X p) (b_bar : B.X (q + 1)),
    a ∈ A.cycles p →
    (cross p q) a (B.d' q b_bar) ∈ C.boundaries (p + q)

/-- The cross product of two cycles is a cycle: if `da = 0` and `db = 0`, the
Leibniz rule forces `d(a × b) = 0`. -/
theorem GradedBilinearMap.cross_mem_cycles
    {A B C : IntChainComplex} (μ : GradedBilinearMap A B C)
    {p q : ℤ} {a : A.X p} {b : B.X q}
    (ha : a ∈ A.cycles p) (hb : b ∈ B.cycles q) :
    (μ.cross p q) a b ∈ C.cycles (p + q) := by
  simp only [IntChainComplex.cycles, AddMonoidHom.mem_ker] at ha hb ⊢
  rw [μ.leibniz_d p q a b, ha, hb]
  simp only [AddMonoidHom.zero_apply, map_zero, smul_zero, add_zero]

/-- Restriction of the bidegree-`(p, q)` cross product to cycles, packaged so
that its codomain is the subgroup of cycles in `C_{p+q}`. -/
def GradedBilinearMap.cross_on_cycles
    {A B C : IntChainComplex} (μ : GradedBilinearMap A B C)
    (p q : ℤ) (a : A.cycles p) (b : B.cycles q) : C.cycles (p + q) :=
  ⟨(μ.cross p q) a.1 b.1, μ.cross_mem_cycles a.2 b.2⟩

/-- **Lemma 7.1.** Given chain complexes `A_*, B_*, C_*` and a bilinear
pairing `A_p × B_q → C_{p+q}` satisfying the Leibniz formula, the induced map
on homology is a bilinear pairing
`H_p(A) × H_q(B) → H_{p+q}(C)`. This is the descent of `cross_on_cycles` to
homology groups, using that cycles cross-multiply to cycles and that boundaries
cross-multiply (against cycles) to boundaries. -/
noncomputable def GradedBilinearMap.homology_cross_product
    {A B C : IntChainComplex} (μ : GradedBilinearMap A B C)
    (p q : ℤ) :
    A.homologyGroup p →+ (B.homologyGroup q →+ C.homologyGroup (p + q)) := by

  let BA := (A.boundaries p).addSubgroupOf (A.cycles p)
  let BB := (B.boundaries q).addSubgroupOf (B.cycles q)
  let BC := (C.boundaries (p + q)).addSubgroupOf (C.cycles (p + q))
  let mkC := QuotientAddGroup.mk' BC


  let crossFixedA : A.cycles p → B.cycles q →+ C.cycles (p + q) :=
    fun a => {
      toFun := fun b => μ.cross_on_cycles p q a b
      map_zero' := Subtype.ext (by simp [cross_on_cycles, map_zero])
      map_add' := fun b₁ b₂ => Subtype.ext (by simp [cross_on_cycles, map_add])
    }

  let phiA : A.cycles p → B.cycles q →+ C.homologyGroup (p + q) :=
    fun a => mkC.comp (crossFixedA a)

  have phiA_kills_BB : ∀ (a : A.cycles p), BB ≤ (phiA a).ker := by
    intro a b hb
    simp only [AddMonoidHom.mem_ker, phiA]
    change mkC (crossFixedA a b) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [AddSubgroup.mem_addSubgroupOf] at hb ⊢
    obtain ⟨b_bar, hb_bar⟩ := hb
    show (μ.cross_on_cycles p q a b).1 ∈ C.boundaries (p + q)
    simp only [cross_on_cycles]
    rw [show b.1 = B.d' q b_bar from hb_bar.symm]
    exact μ.cross_boundary_right p q a.1 b_bar a.2

  let psiA : A.cycles p → B.homologyGroup q →+ C.homologyGroup (p + q) :=
    fun a => QuotientAddGroup.lift BB (phiA a) (phiA_kills_BB a)

  have psiA_add : ∀ (a₁ a₂ : A.cycles p),
      psiA (a₁ + a₂) = psiA a₁ + psiA a₂ := by
    intro a₁ a₂
    ext ⟨b⟩
    simp only [psiA, phiA, AddMonoidHom.add_apply]
    show mkC (crossFixedA (a₁ + a₂) b) = mkC (crossFixedA a₁ b) + mkC (crossFixedA a₂ b)
    rw [← map_add]
    congr 1
    exact Subtype.ext (by simp [crossFixedA, cross_on_cycles, map_add, AddMonoidHom.add_apply])

  have psiA_zero : psiA 0 = 0 := by
    ext ⟨b⟩
    simp only [psiA, phiA, AddMonoidHom.zero_apply]
    show mkC (crossFixedA 0 b) = 0
    have : crossFixedA 0 b = 0 :=
      Subtype.ext (by simp [crossFixedA, cross_on_cycles, map_zero, AddMonoidHom.zero_apply])
    rw [this, map_zero]

  have psiA_kills_BA : ∀ (a : A.cycles p),
      a ∈ BA → psiA a = 0 := by
    intro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨a_bar, ha_bar⟩ := ha
    ext ⟨b⟩
    simp only [psiA, phiA, AddMonoidHom.zero_apply]
    show mkC (crossFixedA a b) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [AddSubgroup.mem_addSubgroupOf]
    show (μ.cross p q) a.1 b.1 ∈ C.boundaries (p + q)
    rw [show a.1 = A.d' p a_bar from ha_bar.symm]
    exact μ.cross_boundary_left p q a_bar b.1 b.2

  let outerHom : A.cycles p →+ (B.homologyGroup q →+ C.homologyGroup (p + q)) :=
    { toFun := psiA
      map_zero' := psiA_zero
      map_add' := psiA_add }
  exact QuotientAddGroup.lift BA outerHom (fun a ha => by
    rw [AddMonoidHom.mem_ker]
    exact psiA_kills_BA a ha)

/-- **Theorem 7.2 (Homology cross product).** Bundle packaging the existence
of a natural, bilinear, and normalized homology cross product
`× : H_p(X) × H_q(Y) → H_{p+q}(X × Y)` for singular homology. It supplies a
chain-level cross product `chainCross`, an integer-indexed chain complex
`singularIntComplex X` for each space, a `GradedBilinearMap` packaging the
Leibniz formula and boundary conditions for the chain cross product, and the
induced homology pairing `homologyCross` shown equal to the descent provided
by Lemma 7.1 (`homologyCross_eq_lemma71`), together with the naturality and
normalization properties inherited from the chain-level cross product. -/
structure HomologyCrossProductSingular where
  chainCross : AlgebraicTopologyI.CrossProduct
  singularIntComplex : ∀ (X : Type) [TopologicalSpace X], ExactSequence.IntChainComplex
  gradedBilinear : ∀ (X : Type) (Y : Type) [TopologicalSpace X] [TopologicalSpace Y],
    GradedBilinearMap
      (singularIntComplex X)
      (singularIntComplex Y)
      (singularIntComplex (X × Y))
  homologyCross : ∀ (p q : ℤ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y],
    (singularIntComplex X).homologyGroup p →+
      ((singularIntComplex Y).homologyGroup q →+
        (singularIntComplex (X × Y)).homologyGroup (p + q))
  homologyCross_eq_lemma71 : ∀ (p q : ℤ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y],
    homologyCross p q X Y =
      (gradedBilinear X Y).homology_cross_product p q
  naturality : ∀ (p q : ℕ) (X X' Y Y' : Type)
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y'))
    (a : AlgebraicTopologyI.SingularChains p X)
    (b : AlgebraicTopologyI.SingularChains q Y),
    (chainCross.crossMap p q X' Y')
      (AlgebraicTopologyI.SingularChains.map f a)
      (AlgebraicTopologyI.SingularChains.map g b) =
    AlgebraicTopologyI.SingularChains.map
      (ContinuousMap.prodMap f g)
      ((chainCross.crossMap p q X Y) a b)
  normalization_left : ∀ (q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (b : AlgebraicTopologyI.SingularChains q Y),
    AlgebraicTopologyI.SingularChains.castIdx (show 0 + q = q by omega)
      ((chainCross.crossMap 0 q X Y) (AlgebraicTopologyI.constChain x) b) =
    AlgebraicTopologyI.SingularChains.map (AlgebraicTopologyI.inclusionRight x) b
  normalization_right : ∀ (p : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) (a : AlgebraicTopologyI.SingularChains p X),
    (chainCross.crossMap p 0 X Y) a (AlgebraicTopologyI.constChain y) =
    AlgebraicTopologyI.SingularChains.map (AlgebraicTopologyI.inclusionLeft y) a

end HomologyCrossProduct

namespace HomologyCrossProduct

section SingularIntComplexConstruction

open AlgebraicTopologyI

/-- Technical cast lemma: rewriting an additive map `SingularChains (m+1) X →+
SingularChains m X` along equalities of natural-number indices behaves like
casting the input and output through the corresponding equalities on the
chain groups. -/
lemma hom_cast_apply_singular (X : Type) [TopologicalSpace X]
    (m n k : ℕ) (h1 : m + 1 = n) (h2 : m = k)
    (f : SingularChains (m + 1) X →+ SingularChains m X)
    (x : SingularChains n X) :
    (h1 ▸ h2 ▸ f : SingularChains n X →+ SingularChains k X) x =
      cast (congrArg (SingularChains · X) h2) (f (cast (congrArg (SingularChains · X) h1.symm) x)) := by
  subst h1; subst h2; simp

/-- Casting a chain along an equality of degrees gives zero iff the original
chain was zero. -/
lemma cast_singularChains_eq_zero (X : Type) [TopologicalSpace X]
    {m n : ℕ} (h : m = n) (x : SingularChains m X) :
    cast (congrArg (SingularChains · X) h) x = (0 : SingularChains n X) ↔ x = 0 := by
  subst h; simp

/-- Compatibility lemma between the boundary map and casting along an index
equality `m = k + 1`: applying `boundaryMap k` after casting `boundaryMap m y`
through `h` agrees with the composition `boundaryMap k ∘ boundaryMap (k+1)`
applied to the appropriate cast of `y`. -/
lemma cast_boundaryMap_eq (X : Type) [TopologicalSpace X]
    (m k : ℕ) (h : m = k + 1) (y : SingularChains (m + 1) X) :
    boundaryMap k X (cast (congrArg (SingularChains · X) h) (boundaryMap m X y)) =
    boundaryMap k X (boundaryMap (k + 1) X
      (cast (congrArg (SingularChains · X) (show m + 1 = (k + 1) + 1 by omega)) y)) := by
  subst h; simp

/-- Integer-indexed boundary map on singular chains: for `n ≥ 1` it is the
usual boundary `S_{n.toNat}(X) → S_{n.toNat - 1}(X)` transported along the
identifications `n.toNat - 1 + 1 = n.toNat` and `n.toNat - 1 = (n - 1).toNat`;
for `n < 1` it is zero. This is the data used to view singular chains as an
`IntChainComplex`. -/
noncomputable def singularIntBoundary (X : Type) [TopologicalSpace X] (n : ℤ) :
    SingularChains n.toNat X →+ SingularChains (n - 1).toNat X :=
  if h : 1 ≤ n then
    have h1 : (n.toNat - 1 + 1) = n.toNat := by omega
    have h2 : (n.toNat - 1) = (n - 1).toNat := by omega
    h1 ▸ h2 ▸ boundaryMap (n.toNat - 1) X
  else 0


end SingularIntComplexConstruction






end HomologyCrossProduct
