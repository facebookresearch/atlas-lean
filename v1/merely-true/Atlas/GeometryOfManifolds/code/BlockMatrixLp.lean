/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-- Algebraic data packaging a 2×2 block-matrix symplectic form on $V \oplus W$:
an evaluation pairing $\mathrm{eval} : W \otimes V \to \mathbb{R}$, an invertible
block endomorphism $B$ on $V$ together with its transpose-inverse $B^{-T}$ on $W$,
and a skew form $C$ on $W$ realized via $\tilde C : W \to V$. -/
structure BlockSymplecticData (V W : Type*)
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] where
  eval : W →ₗ[ℝ] V →ₗ[ℝ] ℝ
  B_endo : V →ₗ[ℝ] V
  B_inv : V →ₗ[ℝ] V
  hBinv_left : ∀ v, B_inv (B_endo v) = v
  hBinv_right : ∀ v, B_endo (B_inv v) = v
  B_inv_t : W →ₗ[ℝ] W
  hBinvt : ∀ w v, eval (B_inv_t w) v = eval w (B_inv v)
  C_form : W →ₗ[ℝ] W →ₗ[ℝ] ℝ
  hC_skew : ∀ w₁ w₂, C_form w₁ w₂ = -(C_form w₂ w₁)
  C_tilde : W →ₗ[ℝ] V
  hCtilde : ∀ w₁ w₂, eval w₁ (C_tilde w₂) = C_form w₁ w₂

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The "untwisted" model symplectic form
$\omega_0((v_1,w_1),(v_2,w_2)) = \mathrm{eval}(w_1, v_2) - \mathrm{eval}(w_2, v_1)$
on $V \times W$. -/
noncomputable def BlockSymplecticData.omega0 (d : BlockSymplecticData V W)
    (p₁ p₂ : V × W) : ℝ :=
  d.eval p₁.2 p₂.1 - d.eval p₂.2 p₁.1

/-- The "twisted" symplectic form
$\omega_1((v_1,w_1),(v_2,w_2)) = \mathrm{eval}(w_1, Bv_2) - \mathrm{eval}(w_2, Bv_1) + C(w_1,w_2)$
obtained by composing the $V$-pairing with $B$ and adding the skew form $C$ on $W$. -/
noncomputable def BlockSymplecticData.omega1 (d : BlockSymplecticData V W)
    (p₁ p₂ : V × W) : ℝ :=
  d.eval p₁.2 (d.B_endo p₂.1) - d.eval p₂.2 (d.B_endo p₁.1) + d.C_form p₁.2 p₂.2

/-- Block linear change of variables $(v,w) \mapsto (v - \tfrac{1}{2} B^{-1} \tilde C (B^{-T} w), B^{-T} w)$
used to relate the twisted symplectic form $\omega_1$ back to the model form $\omega_0$. -/
noncomputable def BlockSymplecticData.correctionMap (d : BlockSymplecticData V W)
    (p : V × W) : V × W :=
  (p.1 + ((-1 : ℝ)/2) • d.B_inv (d.C_tilde (d.B_inv_t p.2)), d.B_inv_t p.2)
