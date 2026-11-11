/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.CategoryTheory

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace UniversalCoefficientTheorem

/-- The chain complex obtained from $C_*$ by tensoring degreewise on the right with the
$R$-module $M$: $(C_* \otimes M)_n = C_n \otimes M$ with the induced differential. -/
def tensorComplex (R : Type*) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ)
    (M : ModuleCat R) : ChainComplex (ModuleCat R) ℕ :=
  (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- Functoriality of `tensorComplex` in the chain complex argument: a chain map
$\varphi : C \to D$ tensored with the identity on $M$. -/
def tensorComplexMap (R : Type*) [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ}
    (φ : C ⟶ D) (M : ModuleCat R) : tensorComplex R C M ⟶ tensorComplex R D M :=
  (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).map φ

/-- Tensoring on the right with a fixed module $M$ preserves colimits; obtained by
transporting along the symmetry isomorphism with `tensorLeft M`. -/
instance tensorRight_preservesColimits (R : Type*) [CommRing R] (M : ModuleCat R) :
    PreservesColimits ((tensoringRight (ModuleCat R)).obj M) := by
  change PreservesColimits (tensorRight M)
  exact preservesColimits_of_natIso
    (NatIso.ofComponents (fun X => (_root_.CategoryTheory.BraidedCategory.braiding M X))
      (fun {X Y} f => _root_.CategoryTheory.BraidedCategory.braiding_naturality_right M f) :
      tensorLeft M ≅ tensorRight M)

/-- In the downward $\mathbb{N}$-indexed complex shape, the successor `n + 1` has
`next = n`. -/
lemma down_next_succ (n : ℕ) : (ComplexShape.down ℕ).next (n + 1) = n :=
  ComplexShape.next_eq' _ (ComplexShape.down_mk (n + 1) n (by omega))

/-- In the downward $\mathbb{N}$-indexed complex shape, the successor `n + 1` has
`prev = n + 2`. -/
lemma down_prev_succ (n : ℕ) : (ComplexShape.down ℕ).prev (n + 1) = n + 2 :=
  ComplexShape.prev_eq' _ (ComplexShape.down_mk (n + 2) (n + 1) (by omega))

/-- The image of the cycles inclusion $Z_{n+1}(C) \hookrightarrow C_{n+1}$ under the
functor $- \otimes M$ vanishes when followed by the differential of $C \otimes M$. Used
to lift the cycles into the homology of the tensor complex. -/
lemma iCycles_tensor_comp_d (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) ≫
      (tensorComplex R C M).d (n + 1) n = 0 := by
  change _ ≫ ((tensoringRight (ModuleCat R)).obj M).map (C.d (n + 1) n) = 0
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    HomologicalComplex.iCycles_d, Functor.map_zero]

/-- The map $Z_{n+1}(C) \otimes M \to H_{n+1}(C \otimes M)$ obtained by lifting through
the cycles of the tensor complex and then quotienting by boundaries. This is the building
block of the UCT map $\alpha$. -/
def cyclesToHomologyTC (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).obj (C.cycles (n + 1)) ⟶
      (tensorComplex R C M).homology (n + 1) :=
  (tensorComplex R C M).liftCycles
    (((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)))
    n (down_next_succ n) (iCycles_tensor_comp_d R M n C) ≫
  (tensorComplex R C M).homologyπ (n + 1)

/-- The composition of the canonical map into cycles with `cyclesToHomologyTC` vanishes;
i.e. boundaries are killed. This is the relation needed to descend `cyclesToHomologyTC`
along the cokernel description of homology. -/
lemma toCycles_comp_cyclesToHomologyTC (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.toCycles (n + 2) (n + 1)) ≫
      cyclesToHomologyTC R M n C = 0 := by
  simp only [cyclesToHomologyTC, ← Category.assoc]
  rw [HomologicalComplex.comp_liftCycles]
  refine HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
    (tensorComplex R C M) _ n (down_next_succ n) (𝟙 _) ?_
  rw [Category.id_comp]
  change ((tensoringRight (ModuleCat R)).obj M).map (C.toCycles (n + 2) (n + 1)) ≫
    ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) =
    ((tensoringRight (ModuleCat R)).obj M).map (C.d (n + 2) (n + 1))
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp, HomologicalComplex.toCycles_i]

/-- The UCT map $\alpha : H_{n+1}(C) \otimes M \to H_{n+1}(C \otimes M)$, defined by
descending the cycles-to-homology map through the cokernel presentation of $H_{n+1}(C)$
(valid because tensoring with $M$ preserves the relevant cokernel for free $C$). -/
def uctAlpha (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C : ChainComplex (ModuleCat R) ℕ) (_hfree : ∀ i, Module.Free R (C.X i)) :
    C.homology (n + 1) ⊗ M ⟶ (tensorComplex R C M).homology (n + 1) := by
  have hcokerF := isColimitCoforkMapOfIsColimit'
    ((tensoringRight (ModuleCat R)).obj M)
    (C.toCycles_comp_homologyπ (n + 2) (n + 1))
    (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n))
  exact (Cofork.IsColimit.desc' hcokerF
    (cyclesToHomologyTC R M n C)
    (by rw [toCycles_comp_cyclesToHomologyTC, zero_comp])).1

/-- The defining property of `uctAlpha`: precomposing with the canonical projection from
cycles to homology recovers the basic `cyclesToHomologyTC` map. This is the universal
property of the cokernel description of homology. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_uctAlpha (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ)
    (hfree : ∀ i, Module.Free R (C.X i)) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.homologyπ (n + 1)) ≫
      uctAlpha R M n C hfree = cyclesToHomologyTC R M n C := by
  have := (Cofork.IsColimit.desc'
    (isColimitCoforkMapOfIsColimit' ((tensoringRight (ModuleCat R)).obj M)
      (C.toCycles_comp_homologyπ (n + 2) (n + 1))
      (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n)))
    (cyclesToHomologyTC R M n C)
    (by rw [toCycles_comp_cyclesToHomologyTC, zero_comp])).2
  simp only [CokernelCofork.π_ofπ] at this
  exact this


set_option maxHeartbeats 800000 in
/-- Naturality of the UCT map $\alpha$ in the chain complex variable: $\alpha$ commutes
with the maps induced by a chain map $\varphi : C \to D$ between free chain complexes. -/
theorem uctAlpha_natural (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ)
    (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D) :
    uctAlpha R M n C hfreeC ≫ HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) =
      ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
        uctAlpha R M n D hfreeD := by

  have hcokerFC := isColimitCoforkMapOfIsColimit' ((tensoringRight (ModuleCat R)).obj M)
    (C.toCycles_comp_homologyπ (n + 2) (n + 1))
    (C.homologyIsCokernel (n + 2) (n + 1) (down_prev_succ n))
  apply Cofork.IsColimit.hom_ext hcokerFC
  simp only [CokernelCofork.π_ofπ]

  erw [homologyπ_comp_uctAlpha_assoc,
    ← ((tensoringRight (ModuleCat R)).obj M).map_comp_assoc,
    HomologicalComplex.homologyπ_naturality,
    ((tensoringRight (ModuleCat R)).obj M).map_comp_assoc,
    homologyπ_comp_uctAlpha]

  simp only [cyclesToHomologyTC, Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  congr 2
  change ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) ≫
      ((tensoringRight (ModuleCat R)).obj M).map (φ.f (n + 1)) =
    ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.cyclesMap φ (n + 1)) ≫
      ((tensoringRight (ModuleCat R)).obj M).map (D.iCycles (n + 1))
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    ← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    HomologicalComplex.cyclesMap_i]

/-- Packaged data of the **Universal Coefficient Theorem** in degree $n+1$: for every
free chain complex $C_*$ over a PID $R$ and every $R$-module $M$, a natural split short
exact sequence
$$0 \to H_{n+1}(C_*) \otimes M \xrightarrow{\alpha} H_{n+1}(C_* \otimes M) \xrightarrow{\beta} \operatorname{Tor}_1^R(H_n(C_*), M) \to 0,$$
together with naturality of $\alpha$ and $\beta$ in $C_*$. -/
structure NaturalUCTData (R : Type*) [CommRing R] [IsPrincipalIdealRing R]
    (M : ModuleCat R) (n : ℕ) where
  α : (C : ChainComplex (ModuleCat R) ℕ) → (∀ i, Module.Free R (C.X i)) →
    (C.homology (n + 1) ⊗ M ⟶ (tensorComplex R C M).homology (n + 1))
  β : (C : ChainComplex (ModuleCat R) ℕ) → (∀ i, Module.Free R (C.X i)) →
    ((tensorComplex R C M).homology (n + 1) ⟶ ((Tor (ModuleCat R) 1).obj (C.homology n)).obj M)
  zero : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    α C hfree ≫ β C hfree = 0
  shortExact : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    (ShortComplex.mk (α C hfree) (β C hfree) (zero C hfree)).ShortExact
  splitting : ∀ (C : ChainComplex (ModuleCat R) ℕ) (hfree : ∀ i, Module.Free R (C.X i)),
    Nonempty (ShortComplex.mk (α C hfree) (β C hfree) (zero C hfree)).Splitting
  α_natural : ∀ (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D),
    α C hfreeC ≫ HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) =
      ((tensoringRight (ModuleCat R)).obj M).map (HomologicalComplex.homologyMap φ (n + 1)) ≫
        α D hfreeD
  β_natural : ∀ (C D : ChainComplex (ModuleCat R) ℕ)
    (hfreeC : ∀ i, Module.Free R (C.X i)) (hfreeD : ∀ i, Module.Free R (D.X i))
    (φ : C ⟶ D),
    β C hfreeC ≫ ((Tor (ModuleCat R) 1).map (HomologicalComplex.homologyMap φ n)).app M =
      HomologicalComplex.homologyMap (tensorComplexMap R φ M) (n + 1) ≫ β D hfreeD

/-- Tor as the homology of a projective resolution: for any projective resolution $P_\bullet$
of $M$,
$$\operatorname{Tor}_1(X, M) \cong H_1(X \otimes P_\bullet).$$
Used to identify the connecting map of the UCT short exact sequence with the Tor term. -/
noncomputable def torIsoHomology (R : Type*) [CommRing R]
    [HasProjectiveResolutions (ModuleCat R)]
    (X M : ModuleCat R) (P : ProjectiveResolution M) :
    ((Tor (ModuleCat R) 1).obj X).obj M ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        ((((tensoringLeft (ModuleCat R)).obj X).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj ((tensoringLeft (ModuleCat R)).obj X) 1

/-- In a projective resolution $P_\bullet \to M$, the composition $d_1 \circ \pi_0 = 0$:
the augmentation kills the image of the first differential. -/
lemma res_d_comp_pi_zero (R : Type*) [CommRing R] (M : ModuleCat R)
    (P : ProjectiveResolution M) : P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  have h := P.π.comm 1 0; simp at h; exact h.symm

/-- The short complex of chain complexes obtained by tensoring $C_*$ degreewise with the
short exact sequence $0 \to P_1 \to P_0 \to M \to 0$ extracted from a projective resolution
$P_\bullet$ of $M$. -/
def resSES (R : Type*) [CommRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R)
    (P : ProjectiveResolution M) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  CategoryTheory.ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map (P.complex.d 1 0))
      (ComplexShape.down ℕ)).app C)
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map (P.π.f 0))
      (ComplexShape.down ℕ)).app C)
    (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
        ← (tensoringRight (ModuleCat R)).map_comp, res_d_comp_pi_zero R M P, Functor.map_zero]
      ext i : 1
      simp only [NatTrans.mapHomologicalComplex, HomologicalComplex.zero_f_apply]
      rfl)








/-- Naturality of `cyclesToHomologyTC` in the module variable $M$: the construction
commutes with maps $f : M_1 \to M_2$. Used to relate $\alpha$ with the connecting map
of the tensored resolution. -/
lemma cyclesToHomologyTC_naturality (R : Type*) [CommRing R]
    {M₁ M₂ : ModuleCat R} (f : M₁ ⟶ M₂)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).map f).app (C.cycles (n + 1)) ≫
      cyclesToHomologyTC R M₂ n C =
    cyclesToHomologyTC R M₁ n C ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map f)
          (ComplexShape.down ℕ)).app C) (n + 1) := by
  simp only [cyclesToHomologyTC, Category.assoc]
  erw [HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  congr 2
  exact (((tensoringRight (ModuleCat R)).map f).naturality (C.iCycles (n + 1))).symm















end UniversalCoefficientTheorem
