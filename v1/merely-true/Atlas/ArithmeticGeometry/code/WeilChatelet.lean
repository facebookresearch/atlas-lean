/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Torsors
import Atlas.ArithmeticGeometry.code.EllipticCurves
import Atlas.ArithmeticGeometry.code.Divisors

noncomputable section

universe u







/-- Build an `AddTorsor G P` from any bijection $e \colon P \simeq G$, by transporting the
addition: $g +_v p := e^{-1}(g + e(p))$. -/
@[reducible] def addTorsorOfEquiv (G : Type*) [AddGroup G] (P : Type*) [Nonempty P]
    (e : P ≃ G) : AddTorsor G P where
  vadd g p := e.symm (g + e p)
  zero_vadd p := by
    show e.symm (0 + e p) = p
    rw [zero_add, Equiv.symm_apply_apply]
  add_vadd g₁ g₂ p := by
    show e.symm ((g₁ + g₂) + e p) = e.symm (g₁ + e (e.symm (g₂ + e p)))
    rw [Equiv.apply_symm_apply, add_assoc]
  vsub p₁ p₂ := e p₁ - e p₂
  vsub_vadd' p₁ p₂ := by
    show e.symm (e p₁ - e p₂ + e p₂) = p₁
    rw [sub_add_cancel, Equiv.symm_apply_apply]
  vadd_vsub' g p := by
    show e (e.symm (g + e p)) - e p = g
    rw [Equiv.apply_symm_apply, add_sub_cancel_right]




variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}





/-- A $k$-rational map between two curve point types, encoded as an inductive closure under
identity, symmetry, and composition. -/
inductive IsKRationalMap (k : Type u) [Field k] :
    (C₁_pts C₂_pts : Type u) → (C₁_pts ≃ C₂_pts) → Prop where
  | refl_equiv (C_pts : Type u) :
      IsKRationalMap k C_pts C_pts (Equiv.refl C_pts)
  | symm_equiv {C₁_pts C₂_pts : Type u} {e : C₁_pts ≃ C₂_pts} :
      IsKRationalMap k C₁_pts C₂_pts e → IsKRationalMap k C₂_pts C₁_pts e.symm
  | trans_equiv {C₁_pts C₂_pts C₃_pts : Type u}
      {e₁₂ : C₁_pts ≃ C₂_pts} {e₂₃ : C₂_pts ≃ C₃_pts} :
      IsKRationalMap k C₁_pts C₂_pts e₁₂ → IsKRationalMap k C₂_pts C₃_pts e₂₃ →
      IsKRationalMap k C₁_pts C₃_pts (e₁₂.trans e₂₃)

/-- A $k$-isomorphism of curve points: a bijection $e$ that is $k$-rational as a map of
algebraic varieties. -/
class IsKIsomorphism (k : Type u) [Field k]
    (C₁_pts C₂_pts : Type u) (e : C₁_pts ≃ C₂_pts) : Prop where
  is_k_rational : IsKRationalMap k C₁_pts C₂_pts e


/-- The identity map is $k$-rational. -/
theorem IsKRationalMap.refl (k : Type u) [Field k] (C_pts : Type u) :
    IsKRationalMap k C_pts C_pts (Equiv.refl C_pts) := .refl_equiv C_pts

/-- The inverse of a $k$-rational equivalence is $k$-rational. -/
theorem IsKRationalMap.symm {k : Type u} [Field k]
    {C₁_pts C₂_pts : Type u} {e : C₁_pts ≃ C₂_pts}
    (h : IsKRationalMap k C₁_pts C₂_pts e) :
    IsKRationalMap k C₂_pts C₁_pts e.symm := .symm_equiv h

/-- The composition of two $k$-rational equivalences is $k$-rational. -/
theorem IsKRationalMap.trans {k : Type u} [Field k]
    {C₁_pts C₂_pts C₃_pts : Type u}
    {e₁₂ : C₁_pts ≃ C₂_pts} {e₂₃ : C₂_pts ≃ C₃_pts}
    (h₁ : IsKRationalMap k C₁_pts C₂_pts e₁₂)
    (h₂ : IsKRationalMap k C₂_pts C₃_pts e₂₃) :
    IsKRationalMap k C₁_pts C₃_pts (e₁₂.trans e₂₃) := .trans_equiv h₁ h₂



/-- Reflexivity of $k$-isomorphism. -/
theorem IsKIsomorphism.refl (k : Type u) [Field k] (C_pts : Type u) :
    IsKIsomorphism k C_pts C_pts (Equiv.refl C_pts) :=
  ⟨IsKRationalMap.refl k C_pts⟩

/-- The inverse of a $k$-isomorphism is a $k$-isomorphism. -/
theorem IsKIsomorphism.symm {k : Type u} [Field k]
    {C₁_pts C₂_pts : Type u} {e : C₁_pts ≃ C₂_pts}
    (h : IsKIsomorphism k C₁_pts C₂_pts e) :
    IsKIsomorphism k C₂_pts C₁_pts e.symm :=
  ⟨h.is_k_rational.symm⟩

/-- The composition of two $k$-isomorphisms is a $k$-isomorphism. -/
theorem IsKIsomorphism.trans {k : Type u} [Field k]
    {C₁_pts C₂_pts C₃_pts : Type u}
    {e₁₂ : C₁_pts ≃ C₂_pts} {e₂₃ : C₂_pts ≃ C₃_pts}
    (h₁ : IsKIsomorphism k C₁_pts C₂_pts e₁₂)
    (h₂ : IsKIsomorphism k C₂_pts C₃_pts e₂₃) :
    IsKIsomorphism k C₁_pts C₃_pts (e₁₂.trans e₂₃) :=
  ⟨h₁.is_k_rational.trans h₂.is_k_rational⟩


namespace ETorsor

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts]









end ETorsor



namespace ETorsorPic

section PiConstruction

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]

/-- The scalar multiplication $n \mapsto n \cdot e$ packaged as an additive homomorphism
$\mathbb{Z} \to E$. -/
def zsmulHom (e : E_pts) : ℤ →+ E_pts where
  toFun n := n • e
  map_zero' := zero_smul ℤ e
  map_add' m n := add_smul m n e

/-- The Abel-Jacobi map at the level of free abelian groups: $\sum n_P [P] \mapsto
\sum n_P (P -_v Q_0)$, viewed as an additive homomorphism $(C \to_0 \mathbb{Z}) \to E$. -/
def piMap (Q₀ : C_pts) : (C_pts →₀ ℤ) →+ E_pts :=
  Finsupp.liftAddHom (fun P => zsmulHom (P -ᵥ Q₀ : E_pts))

/-- The degree homomorphism on the free abelian group on $C$: $\sum n_P [P] \mapsto \sum n_P$. -/
def piDegreeMap : (C_pts →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

/-- Evaluation of `piMap` on a single basis element: $\mathrm{piMap}\,Q_0\,[P]_n = n \cdot (P -_v Q_0)$. -/
@[simp] theorem piMap_single (Q₀ P : C_pts) (n : ℤ) :
    piMap Q₀ (Finsupp.single P n) = n • (P -ᵥ Q₀ : E_pts) := by
  simp [piMap, zsmulHom]

/-- The degree map sends a single basis element $[P]_n$ to $n$. -/
@[simp] theorem piDegreeMap_single (P : C_pts) (n : ℤ) :
    piDegreeMap (Finsupp.single P n) = n := by
  simp [piDegreeMap]

/-- The Abel-Jacobi map `piMap Q₀` is surjective: every element of $E$ can be realised as the
image of a divisor of degree zero. -/
theorem piMap_surjective (Q₀ : C_pts) : Function.Surjective (piMap Q₀) := by
  intro P
  use Finsupp.single (P +ᵥ Q₀) 1 - Finsupp.single Q₀ 1
  simp only [map_sub, piMap_single, one_smul, vadd_vsub, vsub_self, sub_zero]


/-- Comparison of two base points: $\mathrm{piMap}\,Q_0(D) - \mathrm{piMap}\,Q_1(D) =
\deg(D) \cdot (Q_1 -_v Q_0)$. -/
theorem piMap_sub_eq_deg_smul (Q₀ Q₁ : C_pts) (D : C_pts →₀ ℤ) :
    piMap Q₀ D - piMap Q₁ D = piDegreeMap D • (Q₁ -ᵥ Q₀ : E_pts) := by
  induction D using Finsupp.induction_linear with
  | zero => simp [piMap, piDegreeMap]
  | add D₁ D₂ ih₁ ih₂ =>
    simp only [map_add]
    have : piMap Q₀ D₁ + piMap Q₀ D₂ - (piMap Q₁ D₁ + piMap Q₁ D₂) =
        (piMap Q₀ D₁ - piMap Q₁ D₁) + (piMap Q₀ D₂ - piMap Q₁ D₂) := by abel
    rw [this, ih₁, ih₂, ← add_smul]
  | single P n =>
    simp only [piMap_single, piDegreeMap_single]
    rw [← smul_sub, vsub_sub_vsub_cancel_left]

/-- On divisors of degree zero, the Abel-Jacobi map is independent of the chosen base point. -/
theorem piMap_independent (Q₀ Q₁ : C_pts) (D : C_pts →₀ ℤ)
    (hD : piDegreeMap D = 0) : piMap Q₀ D = piMap Q₁ D := by
  have h := piMap_sub_eq_deg_smul Q₀ Q₁ D
  rw [hD, zero_smul] at h
  exact sub_eq_zero.mp h


end PiConstruction

/-- Auxiliary data for the Abel-Jacobi isomorphism $\mathrm{Pic}^0(C) \simeq E$: a factorisation
of the Abel-Jacobi map $\pi$ through an intermediate group `DivZero_E`, together with the
inclusion of principal divisors and a "function field" compatibility condition. -/
structure EllipticCurveDivisorData
    (E_pts : Type u) [AddCommGroup E_pts]
    (DivZero : Type u) [AddCommGroup DivZero]
    (DivZero_E : Type u) [AddCommGroup DivZero_E]
    (PrincDiv : AddSubgroup DivZero) (π : DivZero →+ E_pts) where
  PrincDiv_E : AddSubgroup DivZero_E
  τ : DivZero →+ DivZero_E
  σ_E : DivZero_E →+ E_pts
  hπ_factor : ∀ D, π D = σ_E (τ D)
  abel_on_E : σ_E.ker ≤ PrincDiv_E
  func_field : ∀ D, τ D ∈ PrincDiv_E → D ∈ PrincDiv

section Pic0IsoE

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]
  {DivZero : Type u} [AddCommGroup DivZero]
  (PrincDiv : AddSubgroup DivZero)
  (π : DivZero →+ E_pts)

/-- The kernel of the Abel-Jacobi map $\pi$ is contained in the principal divisors:
$\ker(\pi) \subseteq \mathrm{Princ}$. -/
theorem abel_jacobi_ker_le_princDiv
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π) :
    π.ker ≤ PrincDiv := by
  intro D hD
  rw [AddMonoidHom.mem_ker] at hD

  have h1 : data.σ_E (data.τ D) = 0 := by rw [← data.hπ_factor]; exact hD
  have h2 : data.τ D ∈ data.σ_E.ker := by rwa [AddMonoidHom.mem_ker]

  have h3 : data.τ D ∈ data.PrincDiv_E := data.abel_on_E h2

  exact data.func_field D h3

/-- Conversely, principal divisors are contained in the kernel of $\pi$, provided the converse
versions of the `EllipticCurveDivisorData` axioms hold. -/
theorem princDiv_le_ker_pi
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    PrincDiv ≤ π.ker := by
  intro D hD
  rw [AddMonoidHom.mem_ker]

  have h1 : data.τ D ∈ data.PrincDiv_E := hfunc_field_converse D hD

  have h2 : data.τ D ∈ data.σ_E.ker := habel_converse h1
  rw [AddMonoidHom.mem_ker] at h2

  rw [data.hπ_factor D, h2]

/-- Combining the two inclusions: $\ker(\pi) = \mathrm{Princ}$. -/
theorem piMap_ker_eq_princDiv
    (hπ_ker_le : π.ker ≤ PrincDiv) (hπ_principal_in_ker : PrincDiv ≤ π.ker) :
    π.ker = PrincDiv :=
  le_antisymm hπ_ker_le hπ_principal_in_ker

/-- The Abel-Jacobi isomorphism: assuming the abstract divisor data and surjectivity of $\pi$,
one has $\mathrm{Pic}^0(C) = \mathrm{Div}^0/\mathrm{Princ} \cong E$. -/
noncomputable def pic0_addEquiv_E
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) : DivZero ⧸ PrincDiv ≃+ E_pts :=
  have hπ_ker_le : π.ker ≤ PrincDiv := abel_jacobi_ker_le_princDiv PrincDiv π data
  have hπ_principal_in_ker : PrincDiv ≤ π.ker :=
    princDiv_le_ker_pi PrincDiv π data habel_converse hfunc_field_converse
  (piMap_ker_eq_princDiv PrincDiv π hπ_ker_le hπ_principal_in_ker) ▸
    QuotientAddGroup.quotientKerEquivOfSurjective π hπ_surj

/-- Compatibility: the Abel-Jacobi isomorphism sends the class $[D]$ of a divisor $D$ to its image
$\pi(D)$ in $E$. -/
theorem pic0_addEquiv_E_mk
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) (D : DivZero) :
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj
      (QuotientAddGroup.mk' PrincDiv D) = π D := by
  unfold pic0_addEquiv_E
  generalize piMap_ker_eq_princDiv PrincDiv π
    (abel_jacobi_ker_le_princDiv PrincDiv π data)
    (princDiv_le_ker_pi PrincDiv π data habel_converse hfunc_field_converse) = hk
  subst hk
  simp [QuotientAddGroup.quotientKerEquivOfSurjective,
        QuotientAddGroup.quotientKerEquivOfRightInverse]

/-- The Abel-Jacobi isomorphism is additive: $\Phi(x + y) = \Phi(x) + \Phi(y)$. -/
theorem pic0_addEquiv_E_map_add
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) (x y : DivZero ⧸ PrincDiv) :
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj (x + y) =
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj x +
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj y :=
  map_add _ x y

/-- The Abel-Jacobi isomorphism sends $0$ to $0$. -/
theorem pic0_addEquiv_E_map_zero
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) :
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj 0 = 0 :=
  map_zero _

/-- Inverse formula: $\Phi^{-1}(P)$ is the class of any preimage of $P$ under $\pi$, chosen via
the surjectivity hypothesis. -/
theorem pic0_addEquiv_E_symm_apply
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) (P : E_pts) :
    (pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj).symm P =
    QuotientAddGroup.mk' PrincDiv ((hπ_surj P).choose) := by
  apply (pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj).injective
  rw [AddEquiv.apply_symm_apply, pic0_addEquiv_E_mk]
  exact (hπ_surj P).choose_spec.symm

end Pic0IsoE

section ConcretePic0Iso

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]
  (PrincDiv : AddSubgroup (C_pts →₀ ℤ))
  (Q₀ : C_pts)

/-- Theorem 26.17 (concrete form): the Abel-Jacobi isomorphism
$\mathrm{Pic}^0(C) \cong E$ obtained from the concrete `piMap` and a divisor data. -/
noncomputable def theorem_26_17_pic0_iso
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀))
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    (C_pts →₀ ℤ) ⧸ PrincDiv ≃+ E_pts :=
  pic0_addEquiv_E PrincDiv (piMap Q₀) data habel_converse hfunc_field_converse
    (piMap_surjective Q₀)

/-- Surjectivity statement from Theorem 26.17: `piMap Q₀` is surjective. -/
theorem theorem_26_17_surjective :
    Function.Surjective (piMap Q₀ : (C_pts →₀ ℤ) →+ E_pts) :=
  piMap_surjective Q₀

/-- Kernel-containment statement from Theorem 26.17: $\ker(\mathrm{piMap}\,Q_0) \subseteq \mathrm{Princ}$. -/
theorem theorem_26_17_ker_le_princDiv
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀)) :
    (piMap Q₀).ker ≤ PrincDiv :=
  abel_jacobi_ker_le_princDiv PrincDiv (piMap Q₀) data

/-- Reverse containment from Theorem 26.17: $\mathrm{Princ} \subseteq \ker(\mathrm{piMap}\,Q_0)$. -/
theorem theorem_26_17_princDiv_le_ker
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀))
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    PrincDiv ≤ (piMap Q₀).ker :=
  princDiv_le_ker_pi PrincDiv (piMap Q₀) data habel_converse hfunc_field_converse

/-- Base-point independence from Theorem 26.17: for divisors of degree zero, `piMap` does not
depend on the chosen base point. -/
theorem theorem_26_17_independent (Q₁ : C_pts) (D : C_pts →₀ ℤ)
    (hD : piDegreeMap D = 0) : piMap Q₀ D = piMap Q₁ D :=
  piMap_independent Q₀ Q₁ D hD

end ConcretePic0Iso

end ETorsorPic

end
