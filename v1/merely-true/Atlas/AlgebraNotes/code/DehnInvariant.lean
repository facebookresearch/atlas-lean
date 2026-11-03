/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.NumberTheory.Real.Irrational

open Real TensorProduct Module

namespace DehnInvariant

abbrev tensorProduct (G : Type u) (H : Type v) [AddCommGroup G] [AddCommGroup H] :
    Type (max u v) :=
  TensorProduct ℤ G H

def tmul {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H] (g : G) (h : H) :
    tensorProduct G H :=
  TensorProduct.tmul ℤ g h

theorem tensorProduct_proposition {G : Type u} {H : Type v}
    [AddCommGroup G] [AddCommGroup H] :

    (∀ (g : G) (h : H), tmul (0 : G) h = 0 ∧ tmul g (0 : H) = 0) ∧

    (∀ (a : ℤ) (g : G) (h : H),
      tmul (a • g) h = a • (tmul g h) ∧ tmul g (a • h) = a • (tmul g h)) ∧

    (∀ (s : Set G) (t : Set H), Submodule.span ℤ s = ⊤ → Submodule.span ℤ t = ⊤ →
      Submodule.span ℤ (Set.image2 (fun g h => tmul g h) s t) = ⊤) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g h
    exact ⟨TensorProduct.zero_tmul G h, TensorProduct.tmul_zero H g⟩
  · intro a g h
    exact ⟨(TensorProduct.smul_tmul' a g h).symm, TensorProduct.tmul_smul a g h⟩
  · intro s t hs ht
    have h1 := Submodule.map₂_span_span ℤ (TensorProduct.mk ℤ G H) s t
    rw [hs, ht, TensorProduct.map₂_mk_top_top_eq_top] at h1
    exact h1.symm


noncomputable section

abbrev DehnGroup := ℝ ⊗[ℤ] (AddCircle (2 * π))

structure Edge where
  length : ℝ
  angle : ℝ

noncomputable def dehnInvariant (edges : List Edge) : DehnGroup :=
  (edges.map (fun e => e.length ⊗ₜ[ℤ] (↑e.angle : AddCircle (2 * π)))).sum

noncomputable def tetrahedralAngle : ℝ := arccos (1 / 3)

def fBar (f : ℝ →ₗ[ℚ] ℝ) (hf_pi : f π = 0) : AddCircle (2 * π) →+ ℝ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (2 * π)) f.toAddMonoidHom (by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    obtain ⟨n, hn⟩ := (AddSubgroup.mem_zmultiples_iff).mp hx
    rw [← hn]; change f (n • (2 * π)) = 0
    have h2pi : f (2 * π) = 0 := by
      have : (2 : ℝ) * π = π + π := by ring
      rw [this, map_add, hf_pi, add_zero]
    rw [map_zsmul, h2pi, smul_zero])

@[simp]
lemma fBar_mk (f : ℝ →ₗ[ℚ] ℝ) (hf_pi : f π = 0) (x : ℝ) :
    fBar f hf_pi (↑x : AddCircle (2 * π)) = f x := by
  simp [fBar, QuotientAddGroup.lift_mk]

lemma exists_linearMap_of_irrational {α : ℝ} (hirr : Irrational (α / π)) :
    ∃ f : ℝ →ₗ[ℚ] ℝ, f π = 0 ∧ f α ≠ 0 := by
  set S := Submodule.span ℚ ({π} : Set ℝ)
  have hα_not : α ∉ S := by
    rw [Submodule.mem_span_singleton]
    intro ⟨q, hq⟩
    have key : (q : ℝ) * π = α := by
      change q • π = α at hq; rwa [Rat.smul_def] at hq
    have : α / π = (q : ℝ) := by field_simp; linarith
    exact hirr ⟨q, this.symm⟩
  have hα_quot : (Submodule.Quotient.mk (p := S) α) ≠ 0 := by
    rwa [ne_eq, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℚ hα_quot
  refine ⟨(Algebra.linearMap ℚ ℝ).comp (φ.comp S.mkQ), ?_, ?_⟩
  · simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    have : (Submodule.Quotient.mk (p := S) π) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span (Set.mem_singleton π)
    simp [this]
  · simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    intro h
    apply hφ
    have : (φ (Submodule.Quotient.mk α) : ℝ) = 0 := h
    exact_mod_cast this

theorem tmul_ne_zero_of_irrational {α : ℝ} {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) (hirr : Irrational (α / π)) :
    ℓ ⊗ₜ[ℤ] (↑α : AddCircle (2 * π)) ≠ (0 : DehnGroup) := by
  obtain ⟨f, hfπ, hfα⟩ := exists_linearMap_of_irrational hirr
  intro h
  have := congr_arg (TensorProduct.liftAddHom (R := ℤ)
    { toFun := fun x => {
        toFun := fun y => x * (fBar f hfπ y)
        map_zero' := by simp
        map_add' := by intro a b; simp [mul_add] }
      map_zero' := by ext; simp
      map_add' := by intro a b; ext y; simp [add_mul] }
    (by intro n x y; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [zsmul_eq_mul, map_zsmul, zsmul_eq_mul]; ring)) h
  simp only [TensorProduct.liftAddHom_tmul, map_zero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    fBar_mk] at this
  exact absurd this (mul_ne_zero hℓ hfα)

theorem dehn_cube (ℓ : ℝ) :
    (12 • ℓ) ⊗ₜ[ℤ] (↑(π / 2) : AddCircle (2 * π)) = (0 : DehnGroup) := by
  rw [← smul_tmul', ← TensorProduct.tmul_smul]
  change ℓ ⊗ₜ[ℤ] ((12 : ℤ) • (↑(π / 2) : AddCircle (2 * π))) = 0
  have key : (12 : ℤ) • (↑(π / 2) : AddCircle (2 * π)) = 0 := by
    rw [← AddCircle.coe_zsmul (2 * π)]
    simp only [zsmul_eq_mul, Int.cast_ofNat]
    rw [show (12 : ℝ) * (π / 2) = 3 * (2 * π) from by ring, AddCircle.coe_eq_zero_iff]
    exact ⟨3, by ring⟩
  rw [key, TensorProduct.tmul_zero]


