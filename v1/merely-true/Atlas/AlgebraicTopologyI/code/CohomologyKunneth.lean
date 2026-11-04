/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section33
import Atlas.AlgebraicTopologyI.code.Section29
import Atlas.AlgebraicTopologyI.code.Section25
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.Prod

open CategoryTheory AlgebraicTopology Limits SingularCohomology

noncomputable section

open scoped TensorProduct

namespace CohomologyKunneth

/-- Total singular cohomology of `X` with coefficients in `R`, assembled as the
direct sum `⨁_{n : ℕ} H^n(X; R)` over natural-number degrees. -/
abbrev totalSingularCohomology
    (R : Type) [CommRing R] (X : TopCat.{0}) : Type :=
  DirectSum ℕ (singularCohomologyFamily R X)







/-- Total dual of singular homology: the direct sum
`⨁_{n : ℕ} Hom_R(H_n(X; R), R)`. Under the universal coefficient theorem this
is naturally isomorphic to `totalSingularCohomology` whenever `H_*(X; R)` is
free. -/
abbrev totalDualHomology (R : Type) [CommRing R] (X : TopCat.{0}) : Type :=
  DirectSum ℕ (fun n => (singularHomologyModule R X n : Type) →ₗ[R] R)




/-- The total right edge of the comparison diagram: apply the Kronecker
pairing in each degree to convert `H^*(X × Y; R)` into the direct sum of duals
`⨁_n Hom_R(H_n(X × Y; R), R)`. -/
def diagramRightMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    totalSingularCohomology R (TopCat.of (↑X × ↑Y)) →ₗ[R]
      totalDualHomology R (TopCat.of (↑X × ↑Y)) :=
  DirectSum.toModule R ℕ (totalDualHomology R (TopCat.of (↑X × ↑Y)))
    (fun n => (DirectSum.lof R ℕ
      (fun n => (singularHomologyModule R (TopCat.of (↑X × ↑Y)) n : Type) →ₗ[R] R) n).comp
      (kroneckerPairing R (TopCat.of (↑X × ↑Y)) n))






/-- Generic helper: if `f i : M i →ₗ[R'] N i` is bijective for every index `i`,
then the assembled map `⨁ M i → ⨁ N i` built by composing each `f i` with the
direct-sum inclusion `lof` is bijective. -/
lemma directSum_toModule_lof_comp_bijective
    {R' : Type} [CommRing R'] {ι : Type} [DecidableEq ι]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R' (M i)]
    {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R' (N i)]
    (f : ∀ i, M i →ₗ[R'] N i) (hf : ∀ i, Function.Bijective (f i)) :
    Function.Bijective (DirectSum.toModule R' ι (DirectSum ι N)
      (fun n => (DirectSum.lof R' ι N n).comp (f n))) := by
  have heq : DirectSum.toModule R' ι (DirectSum ι N)
      (fun n => (DirectSum.lof R' ι N n).comp (f n)) = DirectSum.lmap (R := R') f := by
    ext i m j
    simp only [DirectSum.toModule_lof, LinearMap.comp_apply]
    change ((DirectSum.lof R' ι N i) ((f i) m)) j =
      (DFinsupp.mapRange (fun i x => (f i) x) (by intro i; simp)
        ((DirectSum.lof R' ι M i) m)) j
    conv_rhs => rw [show (DirectSum.lof R' ι M i) m = (DFinsupp.single i m : Π₀ k, M k) from rfl]
    rw [DFinsupp.mapRange_single]
    rfl
  rw [heq]
  let equivs : ∀ i, M i ≃ₗ[R'] N i := fun i => LinearEquiv.ofBijective (f i) (hf i)
  have heq2 : (DirectSum.lmap (R := R') f : (DirectSum ι M) →ₗ[R'] (DirectSum ι N)) =
    (DFinsupp.mapRange.linearEquiv equivs).toLinearMap := by
    ext i m j
    change (DFinsupp.mapRange (fun i x => (f i) x) (by intro i; simp)
      ((DirectSum.lof R' ι M i) m)) j =
      (DFinsupp.mapRange (fun i x => (equivs i) x) (by intro i; simp)
      ((DirectSum.lof R' ι M i) m)) j
    congr 2
  rw [heq2]
  exact (DFinsupp.mapRange.linearEquiv equivs).bijective











end CohomologyKunneth

end
