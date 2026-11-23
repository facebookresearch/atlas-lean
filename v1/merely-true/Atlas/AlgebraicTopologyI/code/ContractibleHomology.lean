/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian

namespace ContractibleHomology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homotopy invariance of singular homology: a homotopy equivalence $X \simeq Y$
induces an isomorphism $H_n(X; \mathbb{Z}) \cong H_n(Y; \mathbb{Z})$ for every $n$. -/
def singularHomologyIsoOfHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X) ≅
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Y) := by
  let F := ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ))
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have H_left : TopCat.Homotopy (f ≫ g) (CategoryStruct.id (TopCat.of X)) :=
    Classical.choice e.left_inv
  have H_right : TopCat.Homotopy (g ≫ f) (CategoryStruct.id (TopCat.of Y)) :=
    Classical.choice e.right_inv
  exact
    { hom := F.map f
      inv := F.map g
      hom_inv_id := by
        rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H_left _ n
      inv_hom_id := by
        rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H_right _ n }

/-- For a contractible space $X$, the augmentation gives an isomorphism
$H_0(X; \mathbb{Z}) \cong \mathbb{Z}$. Used in the proof of Corollary 5.7. -/
def singularHomologyZeroIsoZ_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] :
    ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X) ≅
      AddCommGrpCat.of ℤ :=
  let e := Classical.choice (ContractibleSpace.hequiv_unit X)
  singularHomologyIsoOfHomotopyEquiv e 0 ≪≫
    singularHomologyFunctorZeroOfTotallyDisconnectedSpace _ _ _ ≪≫
    coproductUniqueIso _

/-- For a contractible space $X$ and $n \neq 0$, the singular homology $H_n(X; \mathbb{Z})$
vanishes. Combined with `singularHomologyZeroIsoZ_of_contractible`, this yields
Corollary 5.7. -/
theorem singularHomology_isZero_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) := by
  let e := Classical.choice (ContractibleSpace.hequiv_unit X)
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hn).of_iso
    (singularHomologyIsoOfHomotopyEquiv e n)

/-- Packaged data of singular homology for a contractible space: an isomorphism
$H_0(X; \mathbb{Z}) \cong \mathbb{Z}$ together with a proof that $H_n(X; \mathbb{Z}) = 0$
for $n \neq 0$. -/
structure SingularHomologyOfContractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] where
  isoZero :
    ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X) ≅
      AddCommGrpCat.of ℤ
  isZero_pos : ∀ (n : ℕ), n ≠ 0 →
    IsZero (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

/-- **Corollary 5.7**. The singular homology of a contractible space $X$ is given by
$H_0(X; \mathbb{Z}) \cong \mathbb{Z}$ and $H_n(X; \mathbb{Z}) = 0$ for $n \neq 0$. -/
def singularHomologyOfContractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] : SingularHomologyOfContractible X where
  isoZero := singularHomologyZeroIsoZ_of_contractible X
  isZero_pos := singularHomology_isZero_of_contractible X

/-- The augmentation map $\varepsilon : H_0(Z; \mathbb{Z}) \to \mathbb{Z}$, defined as the
composition of the map induced by $Z \to \mathrm{pt}$ with the canonical identification
$H_0(\mathrm{pt}; \mathbb{Z}) \cong \mathbb{Z}$. -/
def augmentationH₀ (Z : Type) [TopologicalSpace Z] :
    ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Z) ⟶
      AddCommGrpCat.of ℤ :=
  ((singularHomologyFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℤ)).map
    (TopCat.isTerminalPUnit.from (TopCat.of Z)) ≫
  (singularHomologyFunctorZeroOfTotallyDisconnectedSpace _ _ _).hom ≫
  (coproductUniqueIso _).hom

end

end ContractibleHomology
