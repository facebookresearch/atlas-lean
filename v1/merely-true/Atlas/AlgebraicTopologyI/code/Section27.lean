/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Projective

open CategoryTheory AlgebraicTopology Limits

noncomputable section

/-- **Definition 27.2.** The Ext-functor $\mathrm{Ext}^n_R(M, N)$ at level $n$, packaged
as a `ModuleCat R`. Concretely, this is the $n$-th cohomology of $\mathrm{Hom}_R(F_*, N)$
for any free resolution $0 \leftarrow M \leftarrow F_0 \leftarrow F_1 \leftarrow \cdots$,
realised here via the derived functor `Ext` on the abelian category of `R`-modules. -/
def ExtR (R : Type*) [CommRing R] (n : ℕ) (M N : ModuleCat R) : ModuleCat R :=
  ((Ext R (ModuleCat R) n).obj (Opposite.op M)).obj N

namespace UniversalCoefficientTheorem

/-- From an iso $A \oplus D \cong B$, manufacture a short exact sequence
$0 \to A \to B \to D \to 0$ together with a splitting. Used to package the UCT biproduct
decomposition as the split short exact sequence appearing in Theorem 27.1. -/
lemma splitting_from_biprod_iso
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    {A B D : C} [HasBinaryBiproduct A D] (φ : A ⊞ D ≅ B) :
    ∃ (S : ShortComplex C), S.X₁ = A ∧ S.X₂ = B ∧ S.X₃ = D ∧
      S.ShortExact ∧ Nonempty S.Splitting := by
  let S : ShortComplex C :=
    ShortComplex.mk (biprod.inl ≫ φ.hom) (φ.inv ≫ biprod.snd) (by simp)
  have split : S.Splitting := {
    r := φ.inv ≫ biprod.fst
    s := biprod.inr ≫ φ.hom
    f_r := by
      show (biprod.inl ≫ φ.hom) ≫ (φ.inv ≫ biprod.fst) = 𝟙 A
      simp [Category.assoc]
    s_g := by
      show (biprod.inr ≫ φ.hom) ≫ (φ.inv ≫ biprod.snd) = 𝟙 D
      simp [Category.assoc]
    id := by
      show (φ.inv ≫ biprod.fst) ≫ (biprod.inl ≫ φ.hom) +
           (φ.inv ≫ biprod.snd) ≫ (biprod.inr ≫ φ.hom) = 𝟙 B
      simp only [Category.assoc]
      rw [← Preadditive.comp_add, ← Category.assoc biprod.fst,
          ← Category.assoc biprod.snd, ← Preadditive.add_comp,
          biprod.total, Category.id_comp, Iso.inv_hom_id]
  }
  exact ⟨S, rfl, rfl, rfl, split.shortExact, ⟨split⟩⟩



/-- The cochain map $\mathrm{Hom}(D_*, N) \to \mathrm{Hom}(C_*, N)$ induced by a chain map
$\varphi : C_* \to D_*$, used to phrase naturality of the UCT in the chain-complex variable. -/
def uctInducedChainMap
    (R : Type) [CommRing R]
    {C D : ChainComplex (ModuleCat.{0} R) ℕ} (N : ModuleCat.{0} R) (φ : C ⟶ D) :
    D.linearYonedaObj R N ⟶ C.linearYonedaObj R N :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda R (ModuleCat.{0} R)).obj N).rightOp.mapHomologicalComplex _).map φ).op

/-- The cochain map $\mathrm{Hom}(C_*, N) \to \mathrm{Hom}(C_*, N')$ induced by a coefficient
map $f : N \to N'$, used to phrase naturality of the UCT in the coefficient variable. -/
def uctInducedCoefficientMap
    (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat.{0} R) ℕ) {N N' : ModuleCat.{0} R} (f : N ⟶ N') :
    C.linearYonedaObj R N ⟶ C.linearYonedaObj R N' :=
  (HomologicalComplex.unopFunctor _ _).map
    (((((linearYoneda R (ModuleCat.{0} R)).map f).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).app C).op)



end UniversalCoefficientTheorem

namespace SingularCohomology



/-- The singular chain complex $S_*(X; R)$ of a topological space $X$ with coefficients in
$R$, packaged as a chain complex of `R`-modules indexed by `ℕ`. -/
abbrev singularChains (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X


end SingularCohomology
