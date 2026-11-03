/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Geometry.Manifold.Instances.Real

open ContinuousLinearMap Finset Manifold


/-- A multi-index $\alpha = (\alpha_1, \ldots, \alpha_n) \in \mathbb{N}^n$ on $n$ variables. -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

/-- Total degree $|\alpha| = \sum_i \alpha_i$ of a multi-index. -/
def multiIndexDegree {n : ℕ} (α : MultiIndex n) : ℕ :=
  ∑ i : Fin n, α i

/-- The monomial $\xi^\alpha = \prod_i \xi_i^{\alpha_i}$ associated to multi-index $\alpha$. -/
noncomputable def multiIndexMonomial {n : ℕ} (α : MultiIndex n) (ξ : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, (ξ i) ^ (α i)

/-- The finite set of multi-indices $\alpha \in \mathbb{N}^n$ with each component $\alpha_i \le k$. -/
noncomputable def multiIndicesBounded (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  Fintype.piFinset (fun _ : Fin n => Finset.range (k + 1))

/-- The finite set of multi-indices of total degree exactly $k$. -/
noncomputable def multiIndicesOfDegree (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α = k)

/-- The finite set of multi-indices of total degree $\le k$. -/
noncomputable def multiIndicesOfDegreeLE (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α ≤ k)


/-- The principal symbol $\sigma_k(L)(\xi) = \sum_{|\alpha| = k} \xi^\alpha A_\alpha$ of a
differential operator with leading-order coefficients $A_\alpha$. -/
noncomputable def principalSymbol {n : ℕ} {k : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : MultiIndex n → (E →L[ℝ] F)) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  ∑ α ∈ multiIndicesOfDegree n k, (multiIndexMonomial α ξ) • (A α)


/-- An elliptic linear differential operator $L: \Gamma(E) \to \Gamma(F)$ of order $k$:
locally $L = \sum_{|\alpha| \le k} A_\alpha \partial^\alpha$, with bijective principal symbol
$\sigma_k(L)(\xi)$ for all $\xi \ne 0$. -/
structure IsEllipticOperator
    (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) where
  order : ℕ
  coeff : MultiIndex n → (E →L[ℝ] F)
  coeff_support : ∀ (α : MultiIndex n), multiIndexDegree α > order → coeff α = 0
  partialDeriv : MultiIndex n → (E →L[ℝ] E)
  local_expression : ∀ (s : E),
    L s = ∑ α ∈ multiIndicesOfDegreeLE n order, coeff α (partialDeriv α s)
  elliptic : ∀ (ξ : Fin n → ℝ), ξ ≠ 0 →
    Function.Bijective (principalSymbol (k := order) coeff ξ)

/-- The principal symbol $\sigma(L)(\xi)$ of an elliptic operator $L$, evaluated at cotangent
direction $\xi$. -/
noncomputable def IsEllipticOperator.symbol
    {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : E →L[ℝ] F}
    (hL : IsEllipticOperator n L) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  principalSymbol (k := hL.order) hL.coeff ξ


/-- A smoothing operator $S$: bounded for each Sobolev norm with a one-step gain in regularity,
$\|S x\|_{s+1} \le C_s \|x\|_s$. -/
structure IsSmoothingOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sobolevNorm : ℕ → E → ℝ)
    (S : E →L[ℝ] E) where
  regularity_improvement : ∀ (s : ℕ), ∃ (C : ℝ), C > 0 ∧
    ∀ (x : E), sobolevNorm (s + 1) (S x) ≤ C * sobolevNorm s x


/-- Pointwise principal symbol $\sigma_k(L)(x, \xi) = \sum_{|\alpha| = k} \xi^\alpha A_\alpha(x)$
of an operator on a manifold $M$ at point $x$ and cotangent vector $\xi$. -/
noncomputable def principalSymbolAt {n : ℕ} {k : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*}
    (A : M → MultiIndex n → (E →L[ℝ] F)) (x : M) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  ∑ α ∈ multiIndicesOfDegree n k, (multiIndexMonomial α ξ) • (A x α)


/-- An elliptic linear differential operator $L: \Gamma(E) \to \Gamma(F)$ on a compact manifold
$M$: pointwise of order $k$ with bijective principal symbol at every $(x, \xi)$, $\xi \ne 0$. -/
structure IsEllipticOperatorOnManifold
    (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M] [IsManifold (𝓡 n) ⊤ M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (M → E) → (M → F)) where
  order : ℕ
  coeff : M → MultiIndex n → (E →L[ℝ] F)
  coeff_support : ∀ (x : M) (α : MultiIndex n), multiIndexDegree α > order → coeff x α = 0
  partialDeriv : MultiIndex n → (M → E) → (M → E)
  local_expression : ∀ (s : M → E) (x : M),
    L s x = ∑ α ∈ multiIndicesOfDegreeLE n order, coeff x α (partialDeriv α s x)
  elliptic : ∀ (x : M) (ξ : Fin n → ℝ), ξ ≠ 0 →
    Function.Bijective (principalSymbolAt (k := order) coeff x ξ)

/-- The principal symbol of an elliptic operator on a manifold, evaluated at $(x, \xi)$. -/
noncomputable def IsEllipticOperatorOnManifold.symbol
    {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M] [IsManifold (𝓡 n) ⊤ M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : (M → E) → (M → F)}
    (hL : IsEllipticOperatorOnManifold n M L) (x : M) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  principalSymbolAt (k := hL.order) hL.coeff x ξ
