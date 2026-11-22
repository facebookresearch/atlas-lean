/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Atlas.GeometryOfManifolds.code.TwoDimDFS
import Atlas.GeometryOfManifolds.code.AlmostComplexManifolds

set_option autoImplicit false
set_option maxHeartbeats 1600000

open DifferentialFormSpace SymplecticLinearAlgebra

noncomputable section


/-- The standard almost-complex structure $J$ on the $2$-dimensional symplectic model:
$J(a, b) = (-b, a)$, modeling multiplication by $i$. -/
def symp2StdJ : Symp2VF → Symp2VF :=
  fun ⟨a, b⟩ => (-b, a)


/-- $J^2 = -\mathrm{Id}$: applying the standard $J$ twice negates both components. -/
lemma symp2StdJ_sq (X : Symp2VF) : symp2StdJ (symp2StdJ X) = (-X.1, -X.2) := by
  obtain ⟨a, b⟩ := X
  simp [symp2StdJ]

/-- The interior product $\iota$ on the $2$D symplectic model is linear under negation of
its vector-field components: $\iota_{(-a, -b)} \alpha = -\iota_{(a, b)} \alpha$. -/
lemma symp2_iota_neg_components (a b : Poly2) (α : Symp2Ω 1) :
    symp2Iota (-a, -b) α = -symp2Iota (a, b) α := by
  obtain ⟨f, g⟩ := α
  simp [symp2Iota, neg_mul]
  ring

/-- The lifted $J$ on the differential-form-space level satisfies $\iota_{J^2 X} = -\iota_X$,
i.e. the action of $J^2$ on $1$-forms is multiplication by $-1$. -/
lemma symp2_lift_sq_neg (X : Symp2VF) (α : Symp2Ω 1) :
    symp2DFS.ι (symp2StdJ (symp2StdJ X)) α = -(symp2DFS.ι X α) := by
  obtain ⟨a, b⟩ := X
  show symp2Iota (symp2StdJ (symp2StdJ (a, b))) α = -symp2Iota (a, b) α
  rw [symp2StdJ_sq]
  exact symp2_iota_neg_components a b α

/-- **$J$ preserves the symplectic form**: $\omega(JX, JY) = \omega(X, Y)$ in the
$2$-dimensional model, expressed via the lifted interior product. -/
lemma symp2_lift_preserves (u v : Symp2VF) (ω : Symp2Ω 2) :
    symp2DFS.ι (symp2StdJ u) (symp2DFS.ι (symp2StdJ v) ω) =
    symp2DFS.ι u (symp2DFS.ι v ω) := by
  obtain ⟨a₁, b₁⟩ := u
  obtain ⟨a₂, b₂⟩ := v
  show symp2Iota (-b₁, a₁) (symp2Iota (-b₂, a₂) (p := 1) ω) =
       symp2Iota (a₁, b₁) (symp2Iota (a₂, b₂) (p := 1) ω)
  simp [symp2Iota]
  ring

/-- **Taming**: the map $v \mapsto \iota_{Jv} \omega$ is injective, equivalently the bilinear
form $g(X, Y) = \omega(X, JY)$ is nondegenerate. This is the analytic content of $J$ taming
the symplectic form. -/
lemma symp2_lift_taming (S : SymplecticManifold Symp2Ω Symp2VF) :
    Function.Injective (fun (v : Symp2VF) => symp2DFS.ι (symp2StdJ v) S.ω) := by
  intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h


  apply S.nondegenerate
  show symp2Iota (a₁, b₁) (p := 1) S.ω = symp2Iota (a₂, b₂) (p := 1) S.ω

  change symp2Iota ((-b₁ : Poly2), (a₁ : Poly2)) (p := 1) S.ω =
         symp2Iota ((-b₂ : Poly2), (a₂ : Poly2)) (p := 1) S.ω at h
  simp only [symp2Iota] at h ⊢


  obtain ⟨h1, h2⟩ := Prod.mk.inj h


  have ha : S.ω * a₁ = S.ω * a₂ := by
    have := h1; rw [neg_mul, neg_mul] at this; exact neg_inj.mp this
  have hb : S.ω * b₁ = S.ω * b₂ := by
    have := h2; rw [mul_neg, mul_neg] at this; exact neg_inj.mp this
  exact Prod.ext (by rw [neg_mul, neg_mul, hb]) ha


/-- The $2$-dimensional symplectic model carries a `HasTangentSpaces` instance: the model
manifold is taken to be `Empty` (it serves only as a tangent-space scaffolding), while the
linear-algebra data (standard $J$, $J^2 = -1$, $J$ preserving $\omega$, taming) is provided
by the lemmas above. -/
noncomputable instance symp2HasTangentSpaces :
    HasTangentSpaces Symp2Ω Symp2VF where
  M := Empty
  TangentSpaceAt := Empty.elim
  instACG := fun x => x.elim
  instMod := fun x => x.elim
  instFD := fun x => x.elim
  eval₂ := fun x => x.elim
  eval₂_add := fun x => x.elim
  eval₂_smul := fun x => x.elim
  eval_is_symplectic := fun _ x => x.elim
  liftJ := fun _ => symp2StdJ
  lift_sq_neg := fun _ _ => symp2_lift_sq_neg
  lift_preserves := fun S _ _ u v => symp2_lift_preserves u v S.ω
  lift_taming := fun S _ _ => symp2_lift_taming S


end
