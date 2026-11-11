/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval

set_option autoImplicit false

namespace HodgeMathlib


/-- A differential $k$-form on $\mathbb{R}^n$: a smooth map from $\mathbb{R}^n$ to alternating $k$-multilinear forms. -/
def DiffForm (n k : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ

/-- Pointwise addition makes the space of differential $k$-forms an additive group. -/
noncomputable instance (n k : ℕ) : AddCommGroup (DiffForm n k) := Pi.addCommGroup
/-- Pointwise scalar multiplication makes the space of differential $k$-forms an $\mathbb{R}$-module. -/
noncomputable instance (n k : ℕ) : Module ℝ (DiffForm n k) := Pi.module _ _ _
/-- The product topology on the space of differential $k$-forms. -/
noncomputable instance (n k : ℕ) : TopologicalSpace (DiffForm n k) := Pi.topologicalSpace

/-- The exterior derivative $d : \Omega^k \to \Omega^{k+1}$ on differential forms on Euclidean space. -/
noncomputable def dForm {n k : ℕ} (ω : DiffForm n k) : DiffForm n (k + 1) :=
  fun x => extDeriv ω x


/-- A codifferential operator $d^* : \Omega^{k+1} \to \Omega^k$ that is linear and satisfies $d^* \circ d^* = 0$. -/
structure Codifferential (n : ℕ) where
  dstar : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n k
  dstar_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)),
    dstar (α + β) = dstar α + dstar β
  dstar_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)),
    dstar (r • α) = r • dstar α
  dstar_squared : ∀ {k : ℕ} (ω : DiffForm n (k + 2)), dstar (dstar ω) = 0


/-- The Hodge Laplacian $\Delta = dd^* + d^*d$ on differential forms. -/
noncomputable def laplacian {n : ℕ} (cod : Codifferential n)
    {k : ℕ} (α : DiffForm n (k + 1)) : DiffForm n (k + 1) :=
  dForm (cod.dstar α) + cod.dstar (dForm α)


/-- A form $\alpha$ is harmonic if $\Delta \alpha = 0$, i.e. it lies in the kernel of the Hodge Laplacian. -/
def IsHarmonic {n : ℕ} (cod : Codifferential n)
    {k : ℕ} (α : DiffForm n (k + 1)) : Prop :=
  laplacian cod α = 0


/-- An $L^2$ inner product on differential forms making $d^*$ the formal adjoint of $d$. -/
structure L2InnerProduct {n : ℕ} (cod : Codifferential n) where
  inner : ∀ {k : ℕ}, DiffForm n k → DiffForm n k → ℝ
  inner_self_eq_zero : ∀ {k : ℕ} (α : DiffForm n k), inner α α = 0 → α = 0
  inner_self_nonneg : ∀ {k : ℕ} (α : DiffForm n k), 0 ≤ inner α α
  inner_symm : ∀ {k : ℕ} (α β : DiffForm n k), inner α β = inner β α
  adjoint_d : ∀ {k : ℕ} (α : DiffForm n k) (β : DiffForm n (k + 1)),
    inner (dForm α) β = inner α (cod.dstar β)
  inner_add_left : ∀ {k : ℕ} (α β γ : DiffForm n k),
    inner (α + β) γ = inner α γ + inner β γ
  inner_smul_left : ∀ {k : ℕ} (r : ℝ) (α β : DiffForm n k),
    inner (r • α) β = r * inner α β


/-- A multi-index $\alpha = (\alpha_1, \dots, \alpha_n) \in \mathbb{N}^n$, indexing partial derivatives. -/
abbrev MultiIndex (n : ℕ) := Fin n →₀ ℕ

/-- The total degree $|\alpha| = \sum_i \alpha_i$ of a multi-index. -/
def multiIndexDegree {n : ℕ} (α : MultiIndex n) : ℕ := α.sum (fun _ k => k)

/-- The monomial $\xi^\alpha = \prod_i \xi_i^{\alpha_i}$ associated to a multi-index. -/
noncomputable def multiIndexMonomial {n : ℕ} (α : MultiIndex n) (ξ : Fin n → ℝ) : ℝ :=
  α.prod (fun i k => (ξ i) ^ k)

/-- The constant multi-index whose every entry equals $k$. -/
noncomputable def constMultiIndex (n : ℕ) (k : ℕ) : MultiIndex n :=
  Finsupp.equivFunOnFinite.symm (fun _ => k)

/-- The finite set of multi-indices componentwise bounded by $(k, \dots, k)$. -/
noncomputable def multiIndicesBounded (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  Finset.Iic (constMultiIndex n k)

/-- The finite set of multi-indices with total degree exactly $k$. -/
noncomputable def multiIndicesOfDegree (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α = k)

/-- The finite set of multi-indices with total degree at most $k$. -/
noncomputable def multiIndicesOfDegreeLE (n : ℕ) (k : ℕ) : Finset (MultiIndex n) :=
  (multiIndicesBounded n k).filter (fun α => multiIndexDegree α ≤ k)

/-- The principal symbol of a differential operator: $\sigma(L)(\xi) = \sum_{|\alpha| = \mathrm{ord}} a_\alpha \, \xi^\alpha$. -/
noncomputable def principalSymbolDiffForm {n : ℕ} (ord : ℕ)
    (coeff : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1)))
    (ξ : Fin n → ℝ) {k : ℕ} (s : DiffForm n (k + 1)) : DiffForm n (k + 1) :=
  ∑ α ∈ multiIndicesOfDegree n ord, (multiIndexMonomial α ξ) • coeff α s


/-- Data witnessing that $L$ is a linear differential operator of given order with coefficients $a_\alpha$ and local expression $L = \sum_{|\alpha| \le \mathrm{ord}} a_\alpha \partial^\alpha$. -/
structure IsDifferentialOperator {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  order : ℕ
  coeff : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1))
  coeff_support : ∀ (α : MultiIndex n), multiIndexDegree α > order →
    ∀ {k : ℕ} (ω : DiffForm n (k + 1)), coeff α ω = 0
  partialDeriv : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1))
  local_expression : ∀ {k : ℕ} (s : DiffForm n (k + 1)),
    L s = ∑ α ∈ multiIndicesOfDegreeLE n order, coeff α (partialDeriv α s)
  L_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)), L (α + β) = L α + L β
  L_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)), L (r • α) = r • L α

/-- The principal symbol $\sigma(L)(\xi)$ of a differential operator $L$, extracted from its top-order coefficients. -/
noncomputable def IsDifferentialOperator.symbol {n : ℕ}
    {L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)}
    (hL : IsDifferentialOperator (n := n) L) (ξ : Fin n → ℝ) {k : ℕ} :
    DiffForm n (k + 1) → DiffForm n (k + 1) :=
  principalSymbolDiffForm hL.order hL.coeff ξ

/-- A differential operator $L$ is elliptic if its principal symbol $\sigma(L)(\xi)$ is bijective for every nonzero covector $\xi$. -/
structure IsElliptic {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1))
    extends IsDifferentialOperator (n := n) L where
  elliptic : ∀ (ξ : Fin n → ℝ), ξ ≠ 0 →
    ∀ {k : ℕ}, Function.Bijective (principalSymbolDiffForm order coeff ξ (k := k))

/-- The principal symbol of an elliptic operator is injective at every nonzero covector. -/
theorem IsElliptic.symbol_injective {n : ℕ}
    {L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)}
    (hL : IsElliptic (n := n) L) (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) {k : ℕ} :
    Function.Injective (principalSymbolDiffForm hL.order hL.coeff ξ (k := k)) :=
  (hL.elliptic ξ hξ).injective


/-- A smoothing operator: gains one Sobolev derivative, $\|S\,x\|_{s+1} \le C\,\|x\|_s$. -/
structure IsSmoothingOp {n k : ℕ}
    (sobolevNorm : ℕ → DiffForm n (k + 1) → ℝ)
    (S : DiffForm n (k + 1) →ₗ[ℝ] DiffForm n (k + 1)) where
  regularity_improvement : ∀ (s : ℕ), ∃ (C : ℝ), C > 0 ∧
    ∀ (x : DiffForm n (k + 1)), sobolevNorm (s + 1) (S x) ≤ C * sobolevNorm s x

/-- A parametrix for $L$: an operator $P$ with $PL = I + S_{\mathrm{left}}$ and $LP = I + S_{\mathrm{right}}$ modulo smoothing operators. -/
structure HasParametrix {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  P : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  S_left : ∀ {k : ℕ}, DiffForm n (k + 1) →ₗ[ℝ] DiffForm n (k + 1)
  S_right : ∀ {k : ℕ}, DiffForm n (k + 1) →ₗ[ℝ] DiffForm n (k + 1)
  sobolevNorm : ∀ {k : ℕ}, ℕ → DiffForm n (k + 1) → ℝ
  PL_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), L (P α) = α + S_right α
  isSmoothing_S_left : ∀ {k : ℕ}, IsSmoothingOp (sobolevNorm (k := k)) (S_left (k := k))
  isSmoothing_S_right : ∀ {k : ℕ}, IsSmoothingOp (sobolevNorm (k := k)) (S_right (k := k))


/-- Typeclass providing a Sobolev regularity predicate $H^s$ on differential forms. -/
class HasSobolevSpaces (n : ℕ) where
  IsSobolevRegular : ℕ → ∀ {k : ℕ}, DiffForm n (k + 1) → Prop




/-- A Green operator decomposition: operators $G$ and $H$ with $LG = I - H$, $GL = I - H$, where $H$ projects onto $\ker L$. -/
structure HasGreenOperatorDecomp {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  G : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  H : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  H_maps_to_ker : ∀ {k : ℕ} (α : DiffForm n (k + 1)), L (H α) = 0
  LG_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), L (G α) = α + -(H α)
  GL_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), G (L α) = α + -(H α)
  H_idem : ∀ {k : ℕ} (α : DiffForm n (k + 1)), H (H α) = H α



/-- Hodge decomposition: every form $\alpha$ splits as $\alpha = h + d\beta + d^*\gamma$ with $h$ harmonic. -/
theorem hodge_decomposition_three_way {n : ℕ}
    (cod : Codifferential n)
    (h_green : Nonempty (HasGreenOperatorDecomp (n := n) (fun α => laplacian cod α)))
    {k : ℕ} (α : DiffForm n (k + 1)) :
    ∃ (h : DiffForm n (k + 1)) (β : DiffForm n k) (γ : DiffForm n (k + 2)),
      IsHarmonic cod h ∧ α = h + dForm β + cod.dstar γ := by
  obtain ⟨gd⟩ := h_green
  refine ⟨gd.H α, cod.dstar (gd.G α), dForm (gd.G α), ?_, ?_⟩
  · exact gd.H_maps_to_ker α
  · have hLG := gd.LG_eq α
    show α = gd.H α + dForm (cod.dstar (gd.G α)) + cod.dstar (dForm (gd.G α))
    have hLG' : dForm (cod.dstar (gd.G α)) + cod.dstar (dForm (gd.G α)) = α + -gd.H α := hLG
    have step : gd.H α + (dForm (cod.dstar (gd.G α)) + cod.dstar (dForm (gd.G α))) = α := by
      rw [hLG']; abel
    rw [← add_assoc] at step
    exact step.symm




/-- A differential form is smooth if it is $C^\infty$ as a function. -/
def IsSmoothForm {n k : ℕ} (ξ : DiffForm n k) : Prop :=
  ContDiff ℝ ⊤ ξ

/-- The difference of two smooth forms is smooth. -/
theorem isSmoothForm_sub {n k : ℕ} (a b : DiffForm n k)
    (ha : IsSmoothForm a) (hb : IsSmoothForm b) : IsSmoothForm (a - b) :=
  ha.sub hb

/-- Elliptic regularity: if $\xi$ is Sobolev-regular and $L\xi$ is smooth, then $\xi$ is smooth. -/
theorem elliptic_regularity {n : ℕ} [sob : HasSobolevSpaces n]
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1))
    (param : HasParametrix (n := n) L)


    (P_preserves_smooth : ∀ {k : ℕ} (β : DiffForm n (k + 1)),
      IsSmoothForm β → IsSmoothForm (param.P β))


    (S_left_maps_sobolev_to_smooth : ∀ (s : ℕ) {k : ℕ} (α : DiffForm n (k + 1)),
      sob.IsSobolevRegular s α → IsSmoothForm (param.S_left α))
    {k : ℕ} {ξ : DiffForm n (k + 1)}
    (s : ℕ) (hξ_sob : sob.IsSobolevRegular s ξ)
    (hLξ_smooth : IsSmoothForm (L ξ)) :
    IsSmoothForm ξ := by

  have hid := param.PL_eq ξ
  have hP_smooth := P_preserves_smooth (L ξ) hLξ_smooth
  have hS_smooth := S_left_maps_sobolev_to_smooth s ξ hξ_sob
  have h_eq : ξ = param.P (L ξ) - param.S_left ξ := by
    rw [hid]; simp [sub_eq_add_neg, add_assoc, add_neg_cancel]
  rw [h_eq]
  exact isSmoothForm_sub _ _ hP_smooth hS_smooth


/-- $L$ is Fredholm: there is a left parametrix $P$ with $PL = I + S_{\mathrm{left}}$, and the kernel of $L$ is finite-dimensional. -/
structure IsFredholm {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  P : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  S_left : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  PL_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)), P (L α) = α + S_left α
  ker_contained : ∀ {k : ℕ} (α : DiffForm n (k + 1)),
    L α = 0 → α + S_left α = P (0 : DiffForm n (k + 1))
  L_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)), L (α + β) = L α + L β
  L_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)), L (r • α) = r • L α








end HodgeMathlib
