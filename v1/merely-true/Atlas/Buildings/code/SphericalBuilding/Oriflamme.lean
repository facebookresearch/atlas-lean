/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Atlas.Buildings.code.IsometryExtensionLemma

namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- A subspace $W \le V$ is **totally isotropic** for $B$ if $B(v, w) = 0$ for all
$v, w \in W$. -/
def IsTotallyIsotropic (W : Submodule k V) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, B v w = 0

/-- A totally isotropic subspace $W$ is **maximal** if it is not properly contained in any
larger totally isotropic subspace. -/
def IsMaximalTotallyIsotropic (W : Submodule k V) : Prop :=
  IsTotallyIsotropic k V B W ∧
  ∀ W' : Submodule k V, IsTotallyIsotropic k V B W' → W ≤ W' → W = W'

/-- The two $\mathrm{SO}(n, n)$-orbits of maximal isotropic $n$-subspaces, indexed by `Bool`
($V_1$ and $V_2$ in the oriflamme construction). -/
abbrev MaxIsotropicClass := Bool


/-- An **oriflamme vertex**: a nonzero totally isotropic subspace whose dimension is **not**
$n - 1$ (this dimension is excluded by the oriflamme construction). -/
def IsOriflammeVertex (W : Submodule k V) : Prop :=
  IsTotallyIsotropic k V B W ∧ W ≠ ⊥ ∧ Module.finrank k W ≠ n - 1

/-- **Oriflamme incidence**: two oriflamme vertices $x, y$ are incident if $x \subsetneq y$,
$y \subsetneq x$, or both are $n$-dimensional with $\dim(x \cap y) = n - 1$. -/
def OriflammeIncident (x y : Submodule k V) : Prop :=
  x < y ∨ y < x ∨
  (Module.finrank k x = n ∧ Module.finrank k y = n ∧
   Module.finrank k ↥(x ⊓ y) = n - 1)

/-- The **oriflamme complex** on $(V, B)$: a flag complex of oriflamme vertices, pairwise
incident, closed under nonempty subsets. -/
structure OriflammeComplex where
  simplices : Set (Finset (Submodule k V))
  simplex_vertices : ∀ σ ∈ simplices, ∀ W ∈ σ, IsOriflammeVertex k V B n W
  simplex_incident : ∀ σ ∈ simplices, ∀ W₁ ∈ σ, ∀ W₂ ∈ σ,
    OriflammeIncident k V n W₁ W₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (Submodule k V),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


/-- An **oriflamme chamber**: a maximal simplex in the oriflamme complex, consisting of an
isotropic chain $W_1 \subsetneq \cdots \subsetneq W_{n-2}$ of dimensions $1, \dots, n-2$
together with two distinct maximal isotropic $n$-subspaces $V_1 \ne V_2$ both containing
$W_{n-2}$ and meeting in dimension $n - 1$. -/
structure OriflammeChamber where
  chain : Fin (n - 2) → Submodule k V
  top₁ : Submodule k V
  top₂ : Submodule k V
  chain_strictMono : StrictMono chain
  chain_isotropic : ∀ i, IsTotallyIsotropic k V B (chain i)
  chain_dim : ∀ i : Fin (n - 2), Module.finrank k (chain i) = i.val + 1
  top₁_isotropic : IsTotallyIsotropic k V B top₁
  top₂_isotropic : IsTotallyIsotropic k V B top₂
  top₁_dim : Module.finrank k top₁ = n
  top₂_dim : Module.finrank k top₂ = n
  top₁_ne_top₂ : top₁ ≠ top₂
  chain_sub_tops : ∀ (h : 0 < n - 2), chain ⟨n - 3, by omega⟩ ≤ top₁ ⊓ top₂
  inter_dim : Module.finrank k ↥(top₁ ⊓ top₂) = n - 1


/-- An **oriflamme frame** of $(V, B)$: a hyperbolic frame as a decomposition into $n$
hyperbolic planes (one per index $i \in \mathrm{Fin}\, n$), each plane spanned by two isotropic
lines indexed by `Bool`. -/
structure OriflammeFrame where
  lines : Fin n × Bool → Submodule k V
  lines_isotropic : ∀ ib, IsTotallyIsotropic k V B (lines ib)
  lines_dim_one : ∀ ib, Module.finrank k (lines ib) = 1
  planes : Fin n → Submodule k V
  planes_eq : ∀ i, planes i = lines (i, true) ⊔ lines (i, false)
  span_top : ⨆ i, planes i = ⊤

/-- The **apartment** of the oriflamme complex $X$ associated to a frame $F$: the simplices
all of whose vertices are sums of frame lines. -/
def OriflammeApartment (X : OriflammeComplex k V B n) (F : OriflammeFrame k V B n) :
    Set (Finset (Submodule k V)) :=
  { σ ∈ X.simplices |
    ∀ W ∈ σ, ∃ S : Finset (Fin n × Bool),
      W = ⨆ ib ∈ S, F.lines ib }


/-- Witness that the oriflamme complex $X$ is a building of type $D_n$: a family of apartments
satisfying the common-apartment and apartment-exchange axioms. -/
structure OriflammeIsBuilding (X : OriflammeComplex k V B n) where
  apartments : Set (OriflammeFrame k V B n)
  common_apartment : ∀ σ₁ ∈ X.simplices, ∀ σ₂ ∈ X.simplices,
    ∃ F ∈ apartments, σ₁ ∈ OriflammeApartment k V B n X F ∧
      σ₂ ∈ OriflammeApartment k V B n X F
  apartment_exchange : ∀ F₁ ∈ apartments, ∀ F₂ ∈ apartments,
    (∃ C ∈ OriflammeApartment k V B n X F₁,
      C ∈ OriflammeApartment k V B n X F₂) →
    ∃ f : Submodule k V → Submodule k V,
      (∀ σ ∈ OriflammeApartment k V B n X F₁,
        σ.image f ∈ OriflammeApartment k V B n X F₂) ∧
      (∀ W, (∃ σ ∈ OriflammeApartment k V B n X F₁ ∩
        OriflammeApartment k V B n X F₂, W ∈ σ) →
        f W = W)

/-- The **isometry group** $O(V, B)$ of the bilinear form: all $k$-linear automorphisms of $V$
preserving $B$. -/
def OriflammeIsometryGroup : Set (V ≃ₗ[k] V) :=
  { g | ∀ v₁ v₂, B (g v₁) (g v₂) = B v₁ v₂ }

/-- The oriflamme building is **strongly transitive** under $\mathrm{SO}(V, B)$ if any pair
of frame/chamber data in two apartments can be mapped one to the other by an isometry. -/
def SO_StronglyTransitive (X : OriflammeComplex k V B n)
    (bldg : OriflammeIsBuilding k V B n X) : Prop :=
  ∀ (F₁ F₂ : OriflammeFrame k V B n),
    F₁ ∈ bldg.apartments → F₂ ∈ bldg.apartments →
    ∀ C₁ ∈ OriflammeApartment k V B n X F₁,
    ∀ C₂ ∈ OriflammeApartment k V B n X F₂,
    ∃ g ∈ OriflammeIsometryGroup k V B,
      (∀ ib, (F₁.lines ib).map g.toLinearMap = F₂.lines ib) ∧
      (∀ W ∈ C₁, ∃ W' ∈ C₂, W.map g.toLinearMap = W')


/-- **B-N pair data** for the oriflamme building: Borel and frame-stabiliser subsets of the
isometry group, an oriflamme chamber, a frame, and the Bruhat decomposition
$G = B \cdot W \cdot B$. -/
structure BNPairData where
  borelSet : Set (V ≃ₗ[k] V)
  frameStabSet : Set (V ≃ₗ[k] V)
  borel_sub : borelSet ⊆ OriflammeIsometryGroup k V B
  frameStab_sub : frameStabSet ⊆ OriflammeIsometryGroup k V B
  chamber : OriflammeChamber k V B n
  borel_stab_chain : ∀ g ∈ borelSet, ∀ i,
    (chamber.chain i).map g.toLinearMap = chamber.chain i
  borel_stab_top₁ : ∀ g ∈ borelSet,
    chamber.top₁.map g.toLinearMap = chamber.top₁
  borel_stab_top₂ : ∀ g ∈ borelSet,
    chamber.top₂.map g.toLinearMap = chamber.top₂
  frame : OriflammeFrame k V B n
  frameStab_permutes : ∀ g ∈ frameStabSet, ∀ ib : Fin n × Bool,
    ∃ jb : Fin n × Bool, (frame.lines ib).map g.toLinearMap = frame.lines jb
  bruhat : ∀ g ∈ OriflammeIsometryGroup k V B,
    ∃ w ∈ frameStabSet, ∃ b₁ ∈ borelSet, ∃ b₂ ∈ borelSet,
      g = b₁.trans (w.trans b₂)


/-- A Coxeter matrix is of **type $D_n$** ($n \ge 3$): linear $A_{n-2}$ chain
$1 - 2 - \cdots - (n-2)$ with two extra nodes branching off node $n-3$ at angle $3$ and
commuting with each other ($m = 2$). -/
def TypeDn (hn : n ≥ 3) : Prop :=
  ∃ (m : Fin n → Fin n → ℕ),

    (∀ i, m i i = 1) ∧

    (∀ i j, m i j = m j i) ∧

    (∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      m i j = 3) ∧

    (m ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ = 3) ∧
    (m ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ = 3) ∧

    (m ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = 2) ∧

    (∀ i j : Fin n, i ≠ j → m i j ≠ 1 →
      m i j = 2 ∨ m i j = 3)

/-- The maximal isotropic $n$-subspace $W$ belongs to **orbit class** $\mathrm{cls}$ relative
to the frame $F$ if $W$ is a sum of $n$ frame lines whose parity of `false`-indexed lines
matches $\mathrm{cls}$ (even for `true`, odd for `false`). -/
def IsInOrbitClass (F : OriflammeFrame k V B n) (W : Submodule k V)
    (cls : MaxIsotropicClass) : Prop :=
  IsTotallyIsotropic k V B W ∧
  Module.finrank k W = n ∧
  ∃ (S : Finset (Fin n × Bool)),
    S.card = n ∧
    W = ⨆ ib ∈ S, F.lines ib ∧

    (S.filter (fun ib => ib.2 = false)).card % 2 = if cls then 0 else 1


section DetIsometry

variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
         [FiniteDimensional k' V']

/-- Any isometry $g$ of a finite-dimensional non-degenerate bilinear form satisfies
$(\det g)^2 = 1$. -/
theorem isometry_det_sq_eq_one
    (B' : LinearMap.BilinForm k' V') (hnd : B'.Nondegenerate)
    (g : V' ≃ₗ[k'] V') (hiso : ∀ v w, B' (g v) (g w) = B' v w) :
    ((g : V' →ₗ[k'] V').det) ^ 2 = 1 := by
  set b := Module.Free.chooseBasis k' V'
  set Q := LinearMap.BilinForm.toMatrix b B'
  set M := LinearMap.toMatrix b b (g : V' →ₗ[k'] V')
  have hcomp : B'.comp (↑g) (↑g) = B' := by
    ext v w; simp [LinearMap.BilinForm.comp_apply, hiso]
  have hmat : Q = M.transpose * Q * M := by
    have := LinearMap.BilinForm.toMatrix_comp b b B' (↑g) (↑g)
    rw [hcomp] at this; exact this
  have hQdet : Q.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  rw [show (g : V' →ₗ[k'] V').det = M.det from by simp [M, LinearMap.det_toMatrix]]
  have h1 : Q.det = (M.transpose * Q * M).det := congr_arg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (M.det ^ 2 - 1) * Q.det = 0 := by
    have := sub_eq_zero.mpr h1.symm; ring_nf; ring_nf at this; exact this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).elim id (absurd · hQdet))

/-- Consequence of $(\det g)^2 = 1$: every isometry has determinant $\pm 1$. -/
theorem isometry_det_eq_one_or_neg_one
    (B' : LinearMap.BilinForm k' V') (hnd : B'.Nondegenerate)
    (g : V' ≃ₗ[k'] V') (hiso : ∀ v w, B' (g v) (g w) = B' v w) :
    (g : V' →ₗ[k'] V').det = 1 ∨ (g : V' →ₗ[k'] V').det = -1 := by
  have h := isometry_det_sq_eq_one B' hnd g hiso
  have h1 := sub_eq_zero.mpr h
  have h2 : ((g : V' →ₗ[k'] V').det - 1) * ((g : V' →ₗ[k'] V').det + 1) = 0 := by
    ring_nf; ring_nf at h1; exact h1
  rcases mul_eq_zero.mp h2 with h3 | h4
  · left; exact sub_eq_zero.mp h3
  · right; exact eq_neg_of_add_eq_zero_left h4

/-- The **special isometry group** $\mathrm{SO}(V, B) = \{g : g \text{ isometry}, \det g = 1\}$. -/
def SpecialIsometryGroup (B' : LinearMap.BilinForm k' V') : Set (V' ≃ₗ[k'] V') :=
  { g | (∀ v w, B' (g v) (g w) = B' v w) ∧ (g : V' →ₗ[k'] V').det = 1 }

end DetIsometry


section HypSwap

variable {k' : Type*} [Field k']

/-- The hyperbolic swap matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ has determinant $-1$. -/
theorem hyp_swap_det_neg_one :
    Matrix.det (!![0, (1 : k'); 1, 0]) = -1 := by
  rw [Matrix.det_fin_two]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A hyperbolic-plane swap isometry $g(e_1) = a \cdot e_2$, $g(e_2) = a^{-1} \cdot e_1$ has
determinant $-1$. -/
theorem hyp_plane_swap_isometry_det
    (e₁ e₂ : Fin 2 → k') (b : Module.Basis (Fin 2) k' (Fin 2 → k'))
    (hb1 : b 0 = e₁) (hb2 : b 1 = e₂)
    (g : (Fin 2 → k') ≃ₗ[k'] (Fin 2 → k'))
    (a : k') (ha : a ≠ 0) (hge1 : g e₁ = a • e₂) (hge2 : g e₂ = a⁻¹ • e₁) :
    (g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')).det = -1 := by
  rw [show (g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')).det =
    (LinearMap.toMatrix b b (↑g)).det from by simp [LinearMap.det_toMatrix]]
  have hge1' : (↑g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')) (b 0) = a • b 1 := by
    simp [hb1, hb2, hge1, LinearEquiv.coe_coe]
  have hge2' : (↑g : (Fin 2 → k') →ₗ[k'] (Fin 2 → k')) (b 1) = a⁻¹ • b 0 := by
    simp [hb1, hb2, hge2, LinearEquiv.coe_coe]
  have hM : LinearMap.toMatrix b b (↑g) = !![0, a⁻¹; a, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hge1', hge2', Module.Basis.repr_self,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  rw [hM, Matrix.det_fin_two]; simp; exact inv_mul_cancel₀ ha

end HypSwap


section DistinctOrbits

variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
         [FiniteDimensional k' V']





/-- For an isometry $g'$ fixing $Y$, the induced map on $V / Y^\perp$ is the identity, hence has
determinant $1$. -/
theorem det_quotient_VmodYperp_eq_one
    (B' : LinearMap.BilinForm k' V') (_hnd : B'.Nondegenerate)
    (Y : Submodule k' V')
    (g' : V' ≃ₗ[k'] V')
    (hiso' : ∀ v w, B' (g' v) (g' w) = B' v w)
    (hfix : ∀ v ∈ Y, g' v = v)
    (he' : B'.orthogonal Y ≤ Submodule.comap (g' : V' →ₗ[k'] V') (B'.orthogonal Y)) :
    LinearMap.det ((B'.orthogonal Y).mapQ (B'.orthogonal Y) (g' : V' →ₗ[k'] V') he') = 1 := by

  suffices h : (B'.orthogonal Y).mapQ (B'.orthogonal Y) (g' : V' →ₗ[k'] V') he' = LinearMap.id by
    rw [h, LinearMap.det_id]
  ext v
  simp only [LinearMap.comp_apply, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.mkQ_apply]

  rw [Submodule.Quotient.eq]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  unfold LinearMap.BilinForm.IsOrtho

  have h2 : g'.symm w = w := (LinearEquiv.symm_apply_eq g').mpr (hfix w hw).symm
  have h3 : (B' w) ((g' : V' →ₗ[k'] V') v) = (B' w) v := by
    show (B' w) (g' v) = (B' w) v
    calc (B' w) (g' v)
        = (B' (g' (g'.symm w))) (g' v) := by rw [g'.apply_symm_apply]
      _ = (B' (g'.symm w)) v := hiso' _ _
      _ = (B' w) v := by rw [h2]
  simp only [map_sub, h3, sub_self]


/-- The induced map of $g'$ on the quotient $Y^\perp / Y$ has determinant $-1$ (this is the
hyperbolic swap contribution that flips orientation). -/
theorem det_quotient_YperpmodY_eq_neg_one
    (B' : LinearMap.BilinForm k' V') (hnd : B'.Nondegenerate) (n : ℕ)
    (Y : Submodule k' V')
    (hY_iso : IsTotallyIsotropic k' V' B' Y)
    (hY_dim : Module.finrank k' Y = n - 1)
    (V₁ V₂ : Submodule k' V')
    (hV₁_sub : V₁ ≤ B'.orthogonal Y) (hY_le_V₁ : Y ≤ V₁)
    (hV₂_sub : V₂ ≤ B'.orthogonal Y) (hY_le_V₂ : Y ≤ V₂)
    (hV₁₂ : V₁ ≠ V₂)
    (g' : V' ≃ₗ[k'] V')
    (hiso' : ∀ v w, B' (g' v) (g' w) = B' v w)
    (hmaps' : V₁.map (g' : V' →ₗ[k'] V') = V₂)
    (hfix : ∀ v ∈ Y, g' v = v)
    (he : Y ≤ Submodule.comap (g' : V' →ₗ[k'] V') Y)
    (he' : B'.orthogonal Y ≤ Submodule.comap (g' : V' →ₗ[k'] V') (B'.orthogonal Y))
    (he_inner : Y.comap (B'.orthogonal Y).subtype ≤
      Submodule.comap ((g' : V' →ₗ[k'] V').restrict he') (Y.comap (B'.orthogonal Y).subtype))


    (hswap_basis :
      ∃ (b : Module.Basis (Fin 2) k'
            (↥(B'.orthogonal Y) ⧸ Y.comap (B'.orthogonal Y).subtype))
        (a : k'), a ≠ 0 ∧
        ((Y.comap (B'.orthogonal Y).subtype).mapQ
         (Y.comap (B'.orthogonal Y).subtype)
         ((g' : V' →ₗ[k'] V').restrict he') he_inner) (b 0) = a • b 1 ∧
        ((Y.comap (B'.orthogonal Y).subtype).mapQ
         (Y.comap (B'.orthogonal Y).subtype)
         ((g' : V' →ₗ[k'] V').restrict he') he_inner) (b 1) = a⁻¹ • b 0) :
    LinearMap.det
      ((Y.comap (B'.orthogonal Y).subtype).mapQ
       (Y.comap (B'.orthogonal Y).subtype)
       ((g' : V' →ₗ[k'] V').restrict he')
       he_inner) = -1 := by
  obtain ⟨b, a, ha, h0, h1⟩ := hswap_basis
  set f := (Y.comap (B'.orthogonal Y).subtype).mapQ
    (Y.comap (B'.orthogonal Y).subtype)
    ((g' : V' →ₗ[k'] V').restrict he') he_inner with hf_def
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b f = !![0, a⁻¹; a, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, h0, h1, Module.Basis.repr_self]
  rw [hM, Matrix.det_fin_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  exact mul_inv_cancel₀ ha




end DistinctOrbits


section TwoOrbits

variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
         [FiniteDimensional k' V']

/-- **Exactly two $\mathrm{SO}(V, B)$-orbits** on maximal isotropic $n$-subspaces: under
transitivity on codimension-$1$ isotropic subspaces, every maximal isotropic $n$-subspace lies in
the orbit of $V_+$ or of $V_-$. -/
theorem exactly_two_SO_orbits
    (B' : LinearMap.BilinForm k' V') (n : ℕ)

    (V_plus V_minus : Submodule k' V')
    (hVp_ti : IsTotallyIsotropic k' V' B' V_plus)
    (hVp_dim : Module.finrank k' V_plus = n)
    (hVm_ti : IsTotallyIsotropic k' V' B' V_minus)
    (hVm_dim : Module.finrank k' V_minus = n)
    (hVpm_ne : V_plus ≠ V_minus)

    (Y₀ : Submodule k' V')
    (_hY₀_ti : IsTotallyIsotropic k' V' B' Y₀)
    (hY₀_dim : Module.finrank k' Y₀ = n - 1)
    (_hY₀_Vp : Y₀ ≤ V_plus) (_hY₀_Vm : Y₀ ≤ V_minus)


    (prop1_transported : ∀ g ∈ SpecialIsometryGroup B', ∀ W : Submodule k' V',
      IsTotallyIsotropic k' V' B' W → Module.finrank k' W = n →
      Submodule.map (g : V' →ₗ[k'] V') Y₀ ≤ W →
      W = Submodule.map (g : V' →ₗ[k'] V') V_plus ∨
      W = Submodule.map (g : V' →ₗ[k'] V') V_minus)

    (so_transitive_codim1 : ∀ Y₁ Y₂ : Submodule k' V',
      IsTotallyIsotropic k' V' B' Y₁ → Module.finrank k' Y₁ = n - 1 →
      IsTotallyIsotropic k' V' B' Y₂ → Module.finrank k' Y₂ = n - 1 →
      ∃ g ∈ SpecialIsometryGroup B', Submodule.map (g : V' →ₗ[k'] V') Y₁ = Y₂)

    (contains_codim1 : ∀ W : Submodule k' V',
      IsTotallyIsotropic k' V' B' W → Module.finrank k' W = n →
      ∃ Y : Submodule k' V',
        IsTotallyIsotropic k' V' B' Y ∧ Module.finrank k' Y = n - 1 ∧ Y ≤ W) :
    ∀ W : Submodule k' V', IsTotallyIsotropic k' V' B' W → Module.finrank k' W = n →
      (∃ g ∈ SpecialIsometryGroup B', Submodule.map (g : V' →ₗ[k'] V') V_plus = W) ∨
      (∃ g ∈ SpecialIsometryGroup B', Submodule.map (g : V' →ₗ[k'] V') V_minus = W) := by
  intro W hW_ti hW_dim

  obtain ⟨Y_W, hYw_ti, hYw_dim, hYw_le⟩ := contains_codim1 W hW_ti hW_dim

  obtain ⟨g, hg_SO, hg_maps⟩ :=
    so_transitive_codim1 Y₀ Y_W _hY₀_ti hY₀_dim hYw_ti hYw_dim


  have hYw_le_W : Submodule.map (g : V' →ₗ[k'] V') Y₀ ≤ W := hg_maps ▸ hYw_le
  rcases prop1_transported g hg_SO W hW_ti hW_dim hYw_le_W with h | h
  · left; exact ⟨g, hg_SO, h.symm⟩
  · right; exact ⟨g, hg_SO, h.symm⟩

end TwoOrbits


section DistinctOrbitClasses

variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
         [FiniteDimensional k' V']


end DistinctOrbitClasses

end Oriflamme
