/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Bases
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Algebra.Module.Basic

open scoped InnerProductSpace

namespace HilbertSpace

/-- A **pre-Hilbert space** is a vector space over $\mathbb{K} = \mathbb{R}, \mathbb{C}$ equipped
with a Hermitian inner product $\langle \cdot, \cdot \rangle : H \times H \to \mathbb{K}$ satisfying
linearity in the first argument, conjugate symmetry, and positive-definiteness. In Mathlib this is
modeled by `InnerProductSpace 𝕜 H`. -/
abbrev PreHilbertSpace (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [SeminormedAddCommGroup H] :=
  InnerProductSpace 𝕜 H

section NormFromInner

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Norm from inner product.** In a (pre-)Hilbert space $H$, the norm of any $v \in H$ satisfies
$\|v\| = \sqrt{\operatorname{Re}\,\langle v, v \rangle}$. -/
theorem norm_eq_sqrt_inner (x : H) : ‖x‖ = Real.sqrt (RCLike.re ⟪x, x⟫_𝕜) :=
  norm_eq_sqrt_re_inner x

end NormFromInner

section InnerProductInducesNorm

/-- An inner product (given as `InnerProductSpace.Core` data) induces a `NormedAddCommGroup`
structure on $H$ via the norm $\|v\| = \langle v, v \rangle^{1/2}$. Hence, if $H$ is a pre-Hilbert
space, then $\|\cdot\|$ is a genuine norm on $H$. -/
@[reducible]
noncomputable def normedAddCommGroupOfInnerProduct
    (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [AddCommGroup H] [Module 𝕜 H]
    (c : InnerProductSpace.Core 𝕜 H) : NormedAddCommGroup H :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 H _ _ _ c

end InnerProductInducesNorm

section CauchySchwarz

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Cauchy-Schwarz inequality.** In a pre-Hilbert space $H$, for all $u, v \in H$ we have
$|\langle u, v \rangle| \le \|u\|\,\|v\|$. -/
theorem cauchy_schwarz (x y : H) : ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ :=
  norm_inner_le_norm x y

end CauchySchwarz

/-- **Parallelogram law (and its converse).** A normed vector space $H$ over $\mathbb{K}$
satisfies the parallelogram law
$$\|u+v\|^2 + \|u-v\|^2 = 2(\|u\|^2 + \|v\|^2) \quad \forall u, v \in H$$
if and only if $H$ is a pre-Hilbert space, i.e. there exists an inner product on $H$ inducing
its norm. -/
theorem parallelogram_law_iff (𝕜 : Type*) [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] :
    (∀ x y : H, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) ↔
    Nonempty (InnerProductSpace 𝕜 H) := by
  constructor
  · intro h
    have h' : ∀ x y : H,
        ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
      intro x y
      have := h x y
      simp only [sq] at this
      exact this
    exact ⟨InnerProductSpace.ofNorm 𝕜 h'⟩
  · intro ⟨ip⟩ x y
    exact @parallelogram_law_with_norm 𝕜 H _ _ ip x y

section BesselInequality

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*}

/-- **Bessel's inequality.** Let $\{e_n\}$ be a (countable) orthonormal family in a pre-Hilbert
space $H$. Then for every $u \in H$,
$$\sum_n |\langle u, e_n \rangle|^2 \le \|u\|^2.$$ -/
theorem bessel_inequality {v : ι → H} (hv : Orthonormal 𝕜 v) (x : H) :
    ∑' i, ‖@inner 𝕜 H _ x (v i)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  simp_rw [norm_inner_symm x (v _)]
  exact hv.tsum_inner_products_le x

end BesselInequality

open Filter Topology

variable {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section InnerProductContinuity

/-- **Continuity of the inner product.** If $u_n \to a$ and $v_n \to b$ in a pre-Hilbert space,
then $\langle u_n, v_n \rangle \to \langle a, b \rangle$. -/
theorem inner_tendsto_of_tendsto
    {x : ℕ → E} {y : ℕ → E} {a b : E}
    (hx : Tendsto x atTop (nhds a))
    (hy : Tendsto y atTop (nhds b)) :
    Tendsto (fun n => @inner 𝕜 E _ (x n) (y n)) atTop (nhds (@inner 𝕜 E _ a b)) :=
  hx.inner hy

end InnerProductContinuity

section ParsevalIdentity

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*}

/-- **Parseval's identity (Hilbert basis version).** If $\{e_i\}_{i \in \iota}$ is a Hilbert basis
of $H$, then for all $u \in H$,
$$\sum_i |\langle u, e_i \rangle|^2 = \|u\|^2.$$ -/
theorem parseval_identity_hilbertBasis (b : HilbertBasis ι 𝕜 H) (u : H) :
    ∑' i, ‖@inner 𝕜 H _ u (b i)‖ ^ 2 = ‖u‖ ^ 2 := by
  simp_rw [norm_inner_symm u (b _)]
  simp_rw [← b.repr_apply_apply]
  rw [← b.repr.norm_map u]
  have h := lp.inner_eq_tsum (𝕜 := 𝕜) (G := fun _ : ι => 𝕜) (b.repr u) (b.repr u)
  have hlhs : @inner 𝕜 _ _ (b.repr u) (b.repr u) = (↑(‖b.repr u‖ ^ 2) : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; ring
  conv at h => rhs; arg 1; ext i; rw [inner_self_eq_norm_sq_to_K]
  rw [hlhs] at h
  exact_mod_cast h.symm

/-- **Parseval's identity.** Let $H$ be a Hilbert space and let $\{e_i\}_{i \in \iota}$ be an
orthonormal family whose span is dense in $H$ (i.e. an orthonormal basis). Then for all $u \in H$,
$$\sum_i |\langle u, e_i \rangle|^2 = \|u\|^2.$$ -/
theorem parseval_identity [CompleteSpace H] {e : ι → H} (he : Orthonormal 𝕜 e)
    (hcomplete : ⊤ ≤ (Submodule.span 𝕜 (Set.range e)).topologicalClosure)
    (u : H) :
    ∑' i, ‖@inner 𝕜 H _ u (e i)‖ ^ 2 = ‖u‖ ^ 2 := by
  let b : HilbertBasis ι 𝕜 H := HilbertBasis.mk he hcomplete
  have hbe : ∀ i, (b : ι → H) i = e i := fun i => congr_fun (HilbertBasis.coe_mk he hcomplete) i
  simp_rw [← hbe]
  exact parseval_identity_hilbertBasis b u

end ParsevalIdentity

section SeparableHilbertIsoEll2

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Separable Hilbert spaces are isometric to $\ell^2$.** If $H$ is an infinite-dimensional
separable Hilbert space (equivalently, if $H$ admits a countable Hilbert basis indexed by
$\mathbb{N}$), then $H$ is isometrically linearly isomorphic to $\ell^2$, the space of
square-summable sequences. In particular, the isomorphism preserves both norms and inner products. -/
theorem separable_hilbert_isomorphic_ell2 (b : HilbertBasis ℕ 𝕜 H) :
    Nonempty (H ≃ₗᵢ[𝕜] ↥(lp (fun _ : ℕ => 𝕜) 2)) :=
  ⟨b.repr⟩

end SeparableHilbertIsoEll2

section OrthogonalProjection

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Orthogonal projection onto a closed subspace.** Let $H$ be a Hilbert space and let
$W \subset H$ be a closed subspace. The orthogonal projection $\Pi_W : H \to H$ that sends
$v = w + w^\perp$ (with $w \in W$ and $w^\perp \in W^\perp$) to $w$ is a projection operator:
it is idempotent ($\Pi_W \circ \Pi_W = \Pi_W$) and has operator norm at most $1$. -/
theorem orthogonalProjection_is_projection (M : Submodule 𝕜 H) [M.HasOrthogonalProjection] :
    (∀ x : H, M.orthogonalProjection (M.orthogonalProjection x : H) =
      M.orthogonalProjection x) ∧
    ‖M.starProjection‖ ≤ 1 :=
  ⟨fun x => Submodule.orthogonalProjection_mem_subspace_eq_self _,
   Submodule.starProjection_norm_le M⟩

end OrthogonalProjection

section RieszRepresentation

open InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Riesz Representation Theorem.** Let $H$ be a Hilbert space. Then for every bounded linear
functional $f \in H'$, there exists a unique $y \in H$ such that
$f(x) = \langle y, x \rangle$ for all $x \in H$, and moreover $\|f\| = \|y\|$. -/
theorem riesz_representation (f : H →L[𝕜] 𝕜) :
    ∃! y : H, (∀ x : H, f x = ⟪y, x⟫_𝕜) ∧ ‖f‖ = ‖y‖ := by
  refine ⟨(toDual 𝕜 H).symm f, ⟨fun x => ?_, ?_⟩, fun y ⟨hy, _⟩ => ?_⟩
  · exact (toDual_symm_apply (𝕜 := 𝕜)).symm
  · rw [← LinearIsometryEquiv.norm_map (toDual 𝕜 H) ((toDual 𝕜 H).symm f),
         LinearIsometryEquiv.apply_symm_apply]
  · have h : (toDual 𝕜 H) y = f := by
      ext x
      rw [toDual_apply_apply, hy x]
    rw [← h, LinearIsometryEquiv.symm_apply_apply]

end RieszRepresentation

section Separability

open TopologicalSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **A Hilbert space with a countable orthonormal basis is separable.** If a Hilbert space $H$
admits a Hilbert basis indexed by a countable set, then $H$ is separable: the closure of the
$\mathbb{K}$-linear span of the basis contains a countable dense subset of $H$. -/
theorem separable_of_countable_hilbertBasis {ι : Type*} [Countable ι]
    (b : HilbertBasis ι 𝕜 H) : SeparableSpace H := by
  have hcount : (Set.range b).Countable := Set.countable_range b
  have hsep_range : IsSeparable (Set.range (b : ι → H)) := hcount.isSeparable
  have hsep_span : IsSeparable (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) :=
    hsep_range.span
  obtain ⟨c, hc_count, hc_sub⟩ := hsep_span
  refine SeparableSpace.mk ⟨c, hc_count, ?_⟩
  rw [dense_iff_closure_eq]
  have h1 : (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) ⊆ closure c := hc_sub
  have h2 : closure (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) ⊆ closure c :=
    closure_minimal h1 isClosed_closure
  have h3 : closure (Submodule.span 𝕜 (Set.range (b : ι → H)) : Set H) = Set.univ := by
    have h := b.dense_span
    have hcoe := Submodule.topologicalClosure_coe (Submodule.span 𝕜 (Set.range (b : ι → H)))
    rw [h] at hcoe
    simp only [Submodule.top_coe] at hcoe
    exact hcoe.symm
  exact Set.eq_univ_of_univ_subset (h3 ▸ h2)

end Separability

end HilbertSpace
