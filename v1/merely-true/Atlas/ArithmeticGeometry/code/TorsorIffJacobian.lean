/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.WeilChatelet
import Atlas.ArithmeticGeometry.code.JInvariant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

universe u

/-- The *absolute Galois group* $\mathrm{Gal}(\bar k / k)$ of a field $k$: ring automorphisms of an
algebraic closure of $k$. -/
abbrev AbsGaloisGroup (k : Type u) [Field k] : Type u :=
  AlgebraicClosure k ≃+* AlgebraicClosure k

/-- The absolute Galois group `AbsGaloisGroup k` is a group under composition. -/
noncomputable instance AbsGaloisGroup.instGroup (k : Type u) [Field k] :
    Group (AbsGaloisGroup k) :=
  inferInstance

/-- A `GaloisAction G E_pts C_pts` packages an action of the group $G$ on both the elliptic curve
points $E$ (as additive equivalences) and on a torsor candidate $C$ (as set equivalences). -/
structure GaloisAction (G : Type u) [Group G] (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) where
  actE : G → E_pts ≃+ E_pts
  actC : G → C_pts ≃ C_pts

/-- A Galois action is *equivariant* for the torsor structure if it commutes with $+_v$:
$\sigma(g +_v c) = \sigma(g) +_v \sigma(c)$ for all $\sigma, g, c$. -/
def GaloisAction.IsEquivariant {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} [AddTorsor E_pts C_pts] (ga : GaloisAction G E_pts C_pts) : Prop :=
  ∀ (σ : G) (g : E_pts) (c : C_pts),
    ga.actC σ (g +ᵥ c) = (ga.actE σ g) +ᵥ (ga.actC σ c)

/-- Consequence of equivariance: $\sigma$ commutes with $-_v$, i.e.
$\sigma(P - Q) = \sigma(P) - \sigma(Q)$. -/
lemma GaloisAction.vsub_compat {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} [AddTorsor E_pts C_pts]
    (ga : GaloisAction G E_pts C_pts) (hga : ga.IsEquivariant)
    (σ : G) (P Q : C_pts) :
    ga.actE σ (P -ᵥ Q) = (ga.actC σ P) -ᵥ (ga.actC σ Q) := by
  have h := hga σ (P -ᵥ Q) Q
  rw [vsub_vadd] at h
  rw [h, vadd_vsub]

/-- A bijection $\varphi \colon C \to E$ is *Galois compatible* with respect to $\mathrm{ga}$ if
for every $\sigma$ there exists $P_\sigma \in E$ such that
$\sigma(\varphi Q) = \varphi(\sigma Q) + P_\sigma$ for all $Q$; this expresses that $\varphi$
differs from a Galois-equivariant map by a cocycle. -/
def IsGaloisCompatible {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} (ga : GaloisAction G E_pts C_pts) (φ : C_pts ≃ E_pts) : Prop :=
  ∀ σ : G, ∃ P_σ : E_pts, ∀ Q : C_pts,
    (ga.actE σ) (φ Q) = φ ((ga.actC σ) Q) + P_σ








variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}

/-- Choosing a basepoint $Q_0 \in C$ in a Galois-equivariant torsor produces a Galois-compatible
bijection $(\mathrm{vaddConst}\,Q_0)^{-1} \colon C \to E$, with cocycle
$P_\sigma = Q_0 -_v \sigma(Q_0)$. -/
theorem torsor_basepoint_galois_compat
    {G : Type u} [Group G] (ga : GaloisAction G E_pts C_pts)
    [AddTorsor E_pts C_pts]
    (hga : ga.IsEquivariant)
    (Q₀ : C_pts) :
    IsGaloisCompatible ga (Equiv.vaddConst Q₀).symm := by
  intro σ
  use Q₀ -ᵥ (ga.actC σ Q₀)
  intro Q

  show ga.actE σ (Q -ᵥ Q₀) = (ga.actC σ Q -ᵥ Q₀) + (Q₀ -ᵥ ga.actC σ Q₀)

  rw [ga.vsub_compat hga σ Q Q₀]

  rw [← vsub_add_vsub_cancel (ga.actC σ Q) Q₀ (ga.actC σ Q₀)]







end
