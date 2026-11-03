/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section10
import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section27
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis

open DirectSum GradedMonoid

namespace CupProduct

/-- **Definition 29.1.** A *graded $R$-algebra* (for $R$ a commutative ring) is
a $\mathbb{Z}$-graded $R$-module $A_*$ equipped with multiplication maps
$A_p \otimes_R A_q \to A_{p+q}$ and a unit $\eta : R \to A_0$ satisfying the
usual associativity and unit diagrams.

This bundles a family of $R$-modules with the graded-semiring/graded-algebra
data taken from Mathlib's `DirectSum` / `GAlgebra` API. -/
structure GradedRAlgebra (R : Type*) [CommRing R] where
  A : ℤ → Type*
  instAddCommGroup : ∀ i, AddCommGroup (A i)
  instModule : ∀ i, Module R (A i)
  instGSemiring : GSemiring A
  instGAlgebra : GAlgebra R A

attribute [instance] GradedRAlgebra.instAddCommGroup GradedRAlgebra.instModule
  GradedRAlgebra.instGSemiring GradedRAlgebra.instGAlgebra

namespace GradedRAlgebra

variable {R : Type*} [CommRing R] (GA : GradedRAlgebra R)

/-- Multiplication in a graded $R$-algebra: $A_p \otimes A_q \to A_{p + q}$. -/
def mul {p q : ℤ} (x : GA.A p) (y : GA.A q) : GA.A (p + q) :=
  GMul.mul x y

/-- The unit map $\eta : R \to A_0$ of a graded $R$-algebra. -/
def unit : R →+ GA.A 0 :=
  GAlgebra.toFun

/-- A graded $R$-algebra $A$ is *(graded) commutative* if the twist isomorphism
satisfies $\tau(x \otimes y) = (-1)^{pq} y \otimes x$, i.e.
$$x \cdot y = (-1)^{pq} y \cdot x$$
for $x \in A_p$ and $y \in A_q$. This is the Koszul sign rule, as used for
example in singular cohomology under cup product. -/
structure IsGradedCommutative : Prop where
  mul_comm : ∀ (p q : ℤ) (x : GA.A p) (y : GA.A q),
    GMul.mul x y =
      ((p * q).negOnePow : ℤ) • cast (congrArg GA.A (add_comm q p)) (GMul.mul y x)

end GradedRAlgebra

end CupProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI

noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

/-- The total cohomology ring $H^*(X; R) = \bigoplus_{n \ge 0} H^n(X; R)$ of a
space $X$ with coefficients in $R$, as a wrapper around the direct sum of
singular cohomology groups. It will be given the structure of a graded
$R$-algebra via the cup product. -/
structure CupProductAlgebra (X : TopCat.{0}) : Type where
  toDirectSum : DirectSum ℕ (fun n ↦
    (singularCohomology R X (ModuleCat.of R R) n : Type))

/-- The graded family $n \mapsto H^n(X; R)$ of singular cohomology groups,
viewed as plain types indexed by $\mathbb{N}$. -/
abbrev singularCohomologyFamily (X : TopCat.{0}) : ℕ → Type :=
  fun n => (singularCohomology R X (ModuleCat.of R R) n : Type)

/-- The additive group structure on each cohomology group $H^n(X; R)$,
inherited from its `ModuleCat` representation. -/
instance (X : TopCat.{0}) (n : ℕ) : AddCommGroup (singularCohomologyFamily R X n) :=
  ModuleCat.isAddCommGroup _






/-- The *augmentation cocycle* $\varepsilon \in C^0(X; R)$: the singular
$0$-cochain assigning $1 \in R$ to every singular $0$-simplex. Its cohomology
class is the unit of $H^*(X; R)$. -/
noncomputable def augmentationCocycle
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    (singularCochainComplex R X (ModuleCat.of R R)).X 0 :=
  Sigma.desc (fun _ => 𝟙 (ModuleCat.of R R))

set_option maxHeartbeats 6400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation cocycle $\varepsilon$ is indeed a $0$-cocycle: its
coboundary vanishes, since for each $1$-simplex $\sigma$ both endpoints map to
$1 \in R$ and cancel. Used to lift $\varepsilon$ to a cohomology class. -/
lemma augmentationCocycle_coboundary_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).d 1 0 ≫
      augmentationCocycle R X = 0 := by
  apply Sigma.hom_ext
  intro σ
  simp only [Limits.HasZeroMorphisms.comp_zero, ← Category.assoc, augmentationCocycle]
  simp only [singularChainComplexFunctor, SSet.singularChainComplexFunctor]
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.whiskeringLeft, Functor.postcompose₂]
  erw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    SimplicialObject.δ]
  erw [Sigma.ι_comp_map' _ _ σ, Sigma.ι_comp_map' _ _ σ]
  simp only [Category.id_comp, Sigma.ι_desc]
  simp [add_neg_cancel]

set_option maxHeartbeats 6400000 in
/-- The unit $1 \in H^0(X; R)$ of the cohomology ring, obtained as the
cohomology class of the augmentation cocycle $\varepsilon$. -/
noncomputable def cohomologyUnit
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularCohomologyFamily R X 0 :=
  let K := singularCochainComplex R X (ModuleCat.of R R)
  let cycleElt : ↑((forget₂ (ModuleCat.{0} R) Ab).obj (K.cycles 0)) :=
    HomologicalComplex.cyclesMk K (augmentationCocycle R X) 1
      (CochainComplex.next ℕ 0)
      (by
        change (K.d 0 1).hom (augmentationCocycle R X) = 0
        simp only [K, singularCochainComplex, ChainComplex.linearYonedaObj_d]
        exact augmentationCocycle_coboundary_zero R X)
  (ConcreteCategory.hom ((forget₂ (ModuleCat.{0} R) Ab).map
    (CochainComplex.isoHomologyπ₀ K).hom)) cycleElt

/-- The cohomology unit `cohomologyUnit` as the graded-monoid identity of
$H^*(X; R)$. -/
instance instGOneCohomologyFamily (X : TopCat.{0}) :
    GradedMonoid.GOne (singularCohomologyFamily R X) where
  one := cohomologyUnit R X
















/-- The natural-number cast $\mathbb{N} \to H^0(X; R)$, defined recursively as
$n \mapsto n \cdot 1_{H^*(X; R)}$. Provides the `natCast` field for the graded
ring structure on $H^*(X; R)$. -/
def cupProduct_natCast
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ℕ → singularCohomologyFamily R X 0
  | 0 => 0
  | n + 1 => cupProduct_natCast R X n + GradedMonoid.GOne.one

/-- Base case for the natural-number cast: $0 \in \mathbb{N}$ maps to $0 \in H^0(X; R)$. -/
theorem cupProduct_natCast_zero
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    cupProduct_natCast R X 0 = 0 := rfl

/-- Successor case for the natural-number cast: the cast of $n + 1$ is the cast of
$n$ plus the cohomology unit. -/
theorem cupProduct_natCast_succ
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cupProduct_natCast R X (n + 1) = cupProduct_natCast R X n + GradedMonoid.GOne.one := rfl


/-- The integer cast $\mathbb{Z} \to H^0(X; R)$, extending the natural-number cast
by negation on negative integers. Provides the `intCast` field for the graded
ring structure. -/
def cupProduct_intCast
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ℤ → singularCohomologyFamily R X 0
  | Int.ofNat n => cupProduct_natCast R X n
  | Int.negSucc n => -cupProduct_natCast R X (n + 1)

/-- Compatibility of the integer cast with the natural-number cast on non-negative
integers $n \ge 0$. -/
theorem cupProduct_intCast_ofNat
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cupProduct_intCast R X ↑n = cupProduct_natCast R X n := rfl

/-- Behaviour of the integer cast on a negative integer $-(n + 1)$: it returns
$-(n + 1) \cdot 1$ in $H^0(X; R)$. -/
theorem cupProduct_intCast_negSucc
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    cupProduct_intCast R X (Int.negSucc n) = -cupProduct_natCast R X (n + 1) := rfl







/-- Casting along an equality of degrees commutes with scalar multiplication:
$\mathrm{cast}_h(r \cdot z) = r \cdot \mathrm{cast}_h(z)$ in the cohomology family. -/
lemma cast_smul_family
    {R : Type} [CommRing R] {X : TopCat.{0}} {n m : ℕ} (h : n = m)
    (r : R) (z : singularCohomologyFamily R X n) :
    cast (congrArg (singularCohomologyFamily R X) h) (r • z) =
    r • cast (congrArg (singularCohomologyFamily R X) h) z := by
  subst h; rfl



/-- The wrapper structure `CupProductAlgebra R X` is canonically equivalent to the
underlying direct sum $\bigoplus_n H^n(X; R)$, used to transfer ring/algebra
instances onto it. -/
def CupProductAlgebra.equiv (X : TopCat.{0}) :
    CupProductAlgebra R X ≃
      DirectSum ℕ (singularCohomologyFamily R X) where
  toFun a := a.toDirectSum
  invFun d := ⟨d⟩
  left_inv _ := rfl
  right_inv _ := rfl
























end SingularCohomology

namespace CupProduct

section SphereCupProduct

open CategoryTheory AlgebraicTopology Limits

variable (R : Type) [CommRing R]

/-- The singular cochain complex $C^*(X; G) = \mathrm{Hom}_R(C_*(X; R), G)$ of a
topological space $X$ with coefficients in an $R$-module $G$, as an object of
`CochainComplex (ModuleCat R) ℕ`. -/
noncomputable abbrev singCochains (G : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat R) ℕ :=
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G

/-- The $n$-th singular cohomology $H^n(X; G)$ as an $R$-module, defined as the
homology of the cochain complex `singCochains R G X` in degree $n$. -/
noncomputable abbrev singCohom (G : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat R :=
  (singCochains R G X).homology n

/-- Contravariant action of a continuous map $f : X \to Y$ on singular cochains:
the pullback $f^* : C^*(Y; G) \to C^*(X; G)$ defined by precomposition with the
induced chain map on $C_*(-; R)$. -/
noncomputable def pullbackCochainMap (G : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singCochains R G Y ⟶ singCochains R G X :=
  let chainMap := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).map f
  let mapHC := (((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)).map chainMap
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map mapHC.op

/-- The induced map $f^* : H^n(Y; G) \to H^n(X; G)$ on singular cohomology,
obtained from `pullbackCochainMap` by passing to homology in degree $n$. -/
noncomputable def cohomPullback (G : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singCohom R G Y n ⟶ singCohom R G X n :=
  HomologicalComplex.homologyMap (pullbackCochainMap R G f) n

/-- The singular chain complex $C_*(S^m; \mathbb{Z})$ of the $m$-sphere with
integer coefficients, packaged as an object of `ChainComplex (ModuleCat ℤ) ℕ`. -/
noncomputable abbrev sphereChainZ (m : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.sphere.{0} m)

/-- Identification of the Mathlib sphere `TopCat.sphere m` with the
`SphereHomology.Sphere m` used elsewhere in Atlas, via the canonical `ULift`
homeomorphism. -/
noncomputable def sphereTopCatIso (m : ℕ) :
    TopCat.sphere.{0} m ≅ TopCat.of (SphereHomology.Sphere m) :=
  TopCat.isoOfHomeo Homeomorph.ulift

/-- Each chain group $C_i(S^m; \mathbb{Z})$ is a free $\mathbb{Z}$-module, being
the direct sum of copies of $\mathbb{Z}$ indexed by singular simplices. -/
theorem sphereChainZ_free (m : ℕ) (i : ℕ) :
    Module.Free ℤ ((sphereChainZ m).X i) := by
  show Module.Free ℤ
    ↑(∐ fun (_ : (TopCat.toSSet.obj (TopCat.sphere m)).obj
      (Opposite.op (SimplexCategory.mk i))) => ModuleCat.of ℤ ℤ)
  classical
  exact Module.Free.of_equiv'
    (Module.Free.directSum ℤ (fun _ => ↑(ModuleCat.of ℤ ℤ)))
    (ModuleCat.coprodIsoDirectSum _).toLinearEquiv.symm






/-- All Ext groups out of a zero object vanish: $\mathrm{Ext}^n(0, Y) = 0$ for
every $n \ge 0$ and every $\mathbb{Z}$-module $Y$. -/
lemma isZero_Ext_of_isZero {X : ModuleCat.{0} ℤ} (hX : IsZero X)
    (Y : ModuleCat.{0} ℤ) (n : ℕ) :
    IsZero (((Ext ℤ (ModuleCat.{0} ℤ) n).obj (Opposite.op X)).obj Y) := by
  haveI : CategoryTheory.Projective X := hX.projective
  cases n with
  | zero =>
    refine IsZero.of_iso ?_ ((CategoryTheory.ProjectiveResolution.self X).isoExt 0 Y)
    rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
    refine ShortComplex.exact_of_isZero_X₂ _ ?_
    dsimp [ChainComplex.linearYonedaObj]
    rw [IsZero.iff_id_eq_zero]
    ext (f : X ⟶ Y)
    exact (hX.eq_of_src f 0).symm ▸ rfl
  | succ k =>
    exact isZero_Ext_succ_of_projective X Y k












end SphereCupProduct

end CupProduct

namespace SphereHomology

open CategoryTheory AlgebraicTopology AlgebraicTopologyI

/-- Identification of the Mathlib sphere `TopCat.sphere m` with the local
`SphereHomology.Sphere m`, repeated here in the `SphereHomology` namespace for
ergonomic access. -/
noncomputable def sphereTopCatIso (m : ℕ) :
    TopCat.sphere.{0} m ≅ TopCat.of (SphereHomology.Sphere m) :=
  TopCat.isoOfHomeo Homeomorph.ulift

/-- Functoriality of the singular chain complex with $\mathbb{Z}$-coefficients:
a homeomorphism (or `TopCat`-iso) $X \simeq Y$ induces an isomorphism of chain
complexes $C_*(X; \mathbb{Z}) \simeq C_*(Y; \mathbb{Z})$. -/
noncomputable def singularChainComplexZ_iso_of_topIso {X Y : TopCat.{0}} (e : X ≅ Y) :
    singularChainComplexZ X ≅ singularChainComplexZ Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).mapIso e

end SphereHomology
