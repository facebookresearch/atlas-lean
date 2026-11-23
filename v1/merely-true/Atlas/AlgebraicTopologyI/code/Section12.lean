/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.Grp.Colimits

noncomputable section

open CategoryTheory AlgebraicTopology Limits

namespace BarycentricSubdivision

/-- The singular chain complex functor with integer coefficients, `X ↦ S_*(X; ℤ)`,
as a functor from topological spaces to non-negatively graded chain complexes of
abelian groups. This is the ambient functor on which the subdivision operator acts. -/
abbrev singularChainFunctorZ : TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The barycenter of the standard `n`-simplex `Δ^n`: the point all of whose
barycentric coordinates equal `1/(n+1)`. This is the cone point used in the
subdivision construction of Section 12. -/
def barycenter (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun _ => 1 / (n + 1 : ℝ), by
    constructor
    · intro i; positivity
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast
      ring⟩

/-- Each barycentric coordinate of the barycenter of `Δ^n` is `1/(n+1)`. -/
@[simp]
theorem barycenter_coord (n : ℕ) (i : Fin (n + 1)) :
    (barycenter n).val i = 1 / (n + 1 : ℝ) :=
  rfl

/-- The standard topological `n`-simplex `Δ^n`, viewed as an object of `TopCat`. -/
def stdSimplexTop (n : ℕ) : TopCat.{0} :=
  SimplexCategory.toTop.{0}.obj (SimplexCategory.mk n)

/-- The type of singular `n`-simplices of `X`, i.e. `Sin_n(X)`, accessed via the
underlying simplicial set of `X`. -/
def SingType (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.{0}.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- The chain group `S_n(X; ℤ)` is definitionally the coproduct of copies of `ℤ`
indexed by singular `n`-simplices, exhibiting it as the free abelian group on
`Sin_n(X)` (Definition 1.3). -/
lemma chainGroup_eq_coprod (X : TopCat.{0}) (n : ℕ) :
    (singularChainFunctorZ.obj X).X n =
    ∐ (fun (_ : SingType X n) => AddCommGrpCat.of ℤ) := rfl

/-- The identity map `Δ^n → Δ^n` viewed as a singular `n`-simplex of `Δ^n`. This is
the universal `n`-simplex `ι_n` on which the subdivision construction is built. -/
def identitySimplex (n : ℕ) : SingType (stdSimplexTop n) n :=
  ULift.up (𝟙 (stdSimplexTop n))

/-- The set-level cone construction `b * τ` taking a `(k+1)`-simplex of `Δ^n`. Given
a cone point `b ∈ Δ^n` and a `k`-simplex `τ : Δ^k → Δ^n`, this sends a point
`x = (t₀, t₁, …, t_{k+1})` of `Δ^{k+1}` to the linear interpolation
`t₀ · b + (1 - t₀) · τ(x₁, …, x_{k+1})` after renormalizing the tail. -/
def coneSingularSimplexFun {n k : ℕ} (b : stdSimplex ℝ (Fin (n + 1)))
    (τ : stdSimplexTop k ⟶ stdSimplexTop n)
    (x : ↑(stdSimplexTop (k + 1))) : ↑(stdSimplexTop n) := by
  have hnn := x.down.2.1
  have hsum := x.down.2.2
  let t₀ := x.down.val 0
  have ht₀_le : t₀ ≤ 1 := by
    have h1 : t₀ ≤ ∑ i, x.down.val i :=
      Finset.single_le_sum (f := x.down.val) (fun i _ => hnn i)
        (Finset.mem_univ (0 : Fin (k + 2)))
    linarith [hsum]
  exact if h : t₀ = 1 then ULift.up b
  else
    have ht₀_lt : t₀ < 1 := lt_of_le_of_ne ht₀_le h
    let s := 1 - t₀
    have hs : (0 : ℝ) < s := sub_pos.mpr ht₀_lt
    let normTail : stdSimplex ℝ (Fin (k + 1)) :=
      ⟨fun i => x.down.val (Fin.succ i) / s, by
        refine ⟨fun i => div_nonneg (hnn _) (le_of_lt hs), ?_⟩
        have htail : ∑ i : Fin (k + 1), x.down.val (Fin.succ i) = s := by
          have heq : ∑ i, x.down.val i =
              x.down.val 0 + ∑ i : Fin (k + 1), x.down.val (Fin.succ i) :=
            Fin.sum_univ_succ x.down.val
          linarith [hsum]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, htail, mul_inv_cancel₀ (ne_of_gt hs)]⟩
    let τ_applied := (τ.hom' (ULift.up normTail)).down
    ULift.up ⟨fun j => t₀ * b.val j + s * τ_applied.val j, by
      refine ⟨fun j => ?_, ?_⟩
      · apply add_nonneg
        · exact mul_nonneg (hnn 0) (b.2.1 j)
        · exact mul_nonneg (le_of_lt hs) (τ_applied.2.1 j)
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        erw [b.2.2, τ_applied.2.2]
        linarith⟩




/-- The chain `1 · σ ∈ S_n(X)` associated to a singular simplex `σ`, viewed as a free
generator in the coproduct representation of the singular chain group. -/
def chainGenerator {X : TopCat.{0}} {n : ℕ} (σ : SingType X n) :
    ↑((singularChainFunctorZ.obj X).X n) :=
  (Sigma.ι (fun (_ : SingType X n) => AddCommGrpCat.of ℤ) σ) (1 : ℤ)

/-- Push forward a chain `elem ∈ S_k(Δ^k)` along a singular `k`-simplex `σ : Δ^k → X`
to obtain a chain in `S_k(X)`. -/
def chainPushforward {X : TopCat.{0}} {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X k))
    (σ : SingType X k) :
    ↑((singularChainFunctorZ.obj X).X k) :=
  ((singularChainFunctorZ.map σ.down).f k) elem

/-- Endomorphism of `S_k(X)` built from a chosen element `elem ∈ S_k(Δ^k)`: on each
generator `σ` it returns the pushforward `σ_*(elem)`. This is the abstract pattern
used to define the subdivision operator from its values on the universal simplex. -/
def sdDegreeWithElem {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X k))
    (X : TopCat.{0}) :
    (singularChainFunctorZ.obj X).X k ⟶ (singularChainFunctorZ.obj X).X k := by
  rw [chainGroup_eq_coprod]
  exact Sigma.desc (fun σ =>
    AddCommGrpCat.ofHom ((zmultiplesHom _) (chainPushforward elem σ)))










/-- Push forward a chain `elem ∈ S_{k+1}(Δ^k)` along a singular `k`-simplex
`σ : Δ^k → X` to obtain a chain in `S_{k+1}(X)`. Used in the construction of
the chain homotopy. -/
def homotopyPushforward {X : TopCat.{0}} {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X (k + 1)))
    (σ : SingType X k) :
    ↑((singularChainFunctorZ.obj X).X (k + 1)) :=
  ((singularChainFunctorZ.map σ.down).f (k + 1)) elem

/-- Degree-raising map `S_k(X) → S_{k+1}(X)` built from a chosen element
`elem ∈ S_{k+1}(Δ^k)`: on each generator `σ` it returns `σ_*(elem)`. This is the
abstract pattern used to build the chain homotopy. -/
def homotopyDegreeWithElem {k : ℕ}
    (elem : ↑((singularChainFunctorZ.obj (stdSimplexTop k)).X (k + 1)))
    (X : TopCat.{0}) :
    (singularChainFunctorZ.obj X).X k ⟶ (singularChainFunctorZ.obj X).X (k + 1) := by
  rw [chainGroup_eq_coprod]
  exact Sigma.desc (fun σ =>
    AddCommGrpCat.ofHom ((zmultiplesHom _) (homotopyPushforward elem σ)))












end BarycentricSubdivision

end
