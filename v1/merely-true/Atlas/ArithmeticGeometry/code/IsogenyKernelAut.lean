/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Isogenies

open WeierstrassCurve

namespace EllipticCurveIsogeny

/-- Auxiliary data witnessing Lemma 24.4 at the level of a generic homomorphism
$\varphi_{\mathrm{hom}} \colon E_1 \to E_2$: a function field and a smaller "pullback" field
related by translation pullback maps, with separation and compatibility axioms. -/
structure KernelAutData {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ_hom : W₁.toAffine.Point →+ W₂.toAffine.Point) where
  FunctionField : Type
  PullbackField : Type
  [field_top : Field FunctionField]
  [field_bot : Field PullbackField]
  [algebra_inst : Algebra PullbackField FunctionField]
  translationPullback : W₁.toAffine.Point → RingAut FunctionField
  eval : FunctionField → W₁.toAffine.Point → FunctionField
  eval_ext : ∀ (f g : FunctionField), (∀ Q, eval f Q = eval g Q) → f = g
  eval_translationPullback : ∀ (P : W₁.toAffine.Point) (f : FunctionField)
    (Q : W₁.toAffine.Point),
    eval ((translationPullback P) f) Q = eval f (Q + P)
  eval_algebraMap_eq_of_image_eq : ∀ (x : PullbackField) (Q R : W₁.toAffine.Point),
    φ_hom Q = φ_hom R → eval (algebraMap PullbackField FunctionField x) Q =
      eval (algebraMap PullbackField FunctionField x) R
  eval_separates : ∀ (Q R : W₁.toAffine.Point), Q ≠ R →
    ∃ f : FunctionField, eval f Q ≠ eval f R

attribute [instance] KernelAutData.field_top KernelAutData.field_bot KernelAutData.algebra_inst

/-- If $P \in \ker \varphi_{\mathrm{hom}}$ then $\varphi_{\mathrm{hom}}$ is invariant under
translation by $P$: $\varphi_{\mathrm{hom}}(R + P) = \varphi_{\mathrm{hom}}(R)$ for all $R$. -/
theorem hom_invariant_under_ker_translation {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ_hom : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (P : W₁.toAffine.Point) (hP : P ∈ φ_hom.ker) :
    ∀ R : W₁.toAffine.Point, φ_hom (R + P) = φ_hom R := by
  intro R
  rw [map_add]
  have : φ_hom P = 0 := hP
  rw [this, add_zero]

namespace KernelAutData

variable {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {φ_hom : W₁.toAffine.Point →+ W₂.toAffine.Point}
    (data : KernelAutData φ_hom)

/-- Compatibility of `translationPullback` with the algebra-map image of the pullback field:
elements coming from `PullbackField` are fixed by `translationPullback P` whenever
$P \in \ker \varphi_{\mathrm{hom}}$. -/
theorem comp_translation_ker : ∀ (P : W₁.toAffine.Point), P ∈ φ_hom.ker →
    ∀ (x : data.PullbackField),
      (data.translationPullback P) (algebraMap data.PullbackField data.FunctionField x) =
        algebraMap data.PullbackField data.FunctionField x := by
  intro P hP x
  apply data.eval_ext
  intro Q
  rw [data.eval_translationPullback]
  exact data.eval_algebraMap_eq_of_image_eq x (Q + P) Q
    (hom_invariant_under_ker_translation φ_hom P hP Q)

/-- Translation-pullback is a homomorphism into the group of ring automorphisms:
$\mathrm{translationPullback}(P + Q) = \mathrm{translationPullback}(P) \cdot \mathrm{translationPullback}(Q)$. -/
theorem translation_comp_pullback : ∀ (P Q : W₁.toAffine.Point),
    data.translationPullback (P + Q) =
      (data.translationPullback P) * (data.translationPullback Q) := by
  intro P Q
  ext f : 1
  apply data.eval_ext
  intro R
  rw [data.eval_translationPullback]
  show data.eval f (R + (P + Q)) =
    data.eval (((data.translationPullback P) * (data.translationPullback Q)) f) R
  simp only [RingAut.mul_apply]
  rw [data.eval_translationPullback P (data.translationPullback Q f) R]
  rw [data.eval_translationPullback Q f (R + P)]
  rw [← add_assoc]

/-- Faithfulness on points: if $P \ne 0$, then translation pullback by $P$ is a *nontrivial* ring
automorphism. -/
theorem nontrivial_translation_nontrivial : ∀ (P : W₁.toAffine.Point),
    P ≠ 0 → data.translationPullback P ≠ 1 := by
  intro P hP h_eq
  have h_eval : ∀ f Q, data.eval f (Q + P) = data.eval f Q := by
    intro f Q
    have := data.eval_translationPullback P f Q
    rw [h_eq] at this
    simp only [RingAut.one_apply] at this
    exact this.symm
  have h_zero : ∀ f, data.eval f P = data.eval f 0 := by
    intro f
    have := h_eval f 0
    rw [zero_add] at this
    exact this
  obtain ⟨f, hf⟩ := data.eval_separates P 0 hP
  exact hf (h_zero f)

/-- Translation pullback by the zero element is the identity automorphism. -/
theorem translationPullback_zero : data.translationPullback 0 = 1 := by
  have h := data.translation_comp_pullback 0 0
  simp only [add_zero] at h
  set a := data.translationPullback 0
  have : a⁻¹ * a = a⁻¹ * (a * a) := congrArg (a⁻¹ * ·) h
  simp only [inv_mul_cancel, inv_mul_cancel_left] at this
  exact this.symm

/-- Translation pullback by $-P$ is the inverse of translation pullback by $P$. -/
theorem translationPullback_neg (P : W₁.toAffine.Point) :
    data.translationPullback (-P) = (data.translationPullback P)⁻¹ := by
  have h := data.translation_comp_pullback P (-P)
  simp only [add_neg_cancel] at h
  rw [data.translationPullback_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_inv_cancel _).symm)

/-- Translation pullback by $P - Q$ equals $\mathrm{translationPullback}(P) \cdot
\mathrm{translationPullback}(Q)^{-1}$. -/
theorem translationPullback_sub (P Q : W₁.toAffine.Point) :
    data.translationPullback (P - Q) =
      (data.translationPullback P) * (data.translationPullback Q)⁻¹ := by
  rw [sub_eq_add_neg, data.translation_comp_pullback, data.translationPullback_neg]

/-- Restated: for $P \in \ker\varphi_{\mathrm{hom}}$, translation pullback by $P$ fixes every
element in the image of the algebra map from `PullbackField`. -/
theorem translationPullback_fixes_image (P : W₁.toAffine.Point) (hP : P ∈ φ_hom.ker)
    (x : data.PullbackField) :
    (data.translationPullback P) (algebraMap data.PullbackField data.FunctionField x) =
      algebraMap data.PullbackField data.FunctionField x :=
  data.comp_translation_ker P hP x

/-- Translation pullback restricted to $\ker\varphi_{\mathrm{hom}}$, viewed as an additive
homomorphism into `Additive (RingAut FunctionField)`. -/
def translationPullbackHomOnKer :
    φ_hom.ker →+ Additive (RingAut data.FunctionField) where
  toFun P := Additive.ofMul (data.translationPullback P.val)
  map_zero' := by
    simp only [AddSubgroup.coe_zero]
    exact congrArg Additive.ofMul data.translationPullback_zero
  map_add' P Q := by
    simp only [AddSubgroup.coe_add]
    exact congrArg Additive.ofMul (data.translation_comp_pullback P.val Q.val)

/-- Translation pullback is injective: distinct points produce distinct ring automorphisms. -/
theorem translationPullback_injective :
    Function.Injective data.translationPullback := by
  intro P Q h
  suffices P - Q = 0 by exact sub_eq_zero.mp this
  have h_sub : data.translationPullback (P - Q) = 1 := by
    rw [data.translationPullback_sub]
    rw [h]
    exact mul_inv_cancel _
  by_contra h_ne
  exact data.nontrivial_translation_nontrivial (P - Q) h_ne h_sub

/-- The translation-pullback homomorphism restricted to the kernel is injective. -/
theorem translationPullback_injective_on_ker :
    Function.Injective data.translationPullbackHomOnKer := by
  intro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  have h' : data.translationPullback P = data.translationPullback Q := by
    have := congr_arg Additive.toMul h
    simp only [translationPullbackHomOnKer, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact this
  exact Subtype.ext (data.translationPullback_injective h')

/-- Core of Lemma 24.4: $\ker\varphi$ embeds into $\mathrm{Aut}(\mathrm{FunctionField})$
via translation pullback, fixing the subfield `PullbackField`. -/
theorem lemma_24_4_core :
    ∃ (f : φ_hom.ker →+ Additive (RingAut data.FunctionField)),
      Function.Injective f ∧
      ∀ (P : φ_hom.ker) (x : data.PullbackField),
        (data.translationPullback P.val) (algebraMap data.PullbackField data.FunctionField x) =
          algebraMap data.PullbackField data.FunctionField x := by
  refine ⟨data.translationPullbackHomOnKer, data.translationPullback_injective_on_ker, ?_⟩
  intro ⟨P, hP⟩ x
  exact data.translationPullback_fixes_image P hP x

end KernelAutData

variable {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]



end EllipticCurveIsogeny
