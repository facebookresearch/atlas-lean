/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial

/-- Algebra map underlying the Segre embedding `ℙ¹ × ℙ¹ → ℙ³`:
sends the coordinates `(z₀, z₁, z₂, z₃)` of `ℙ³` to the bilinear monomials
`(x₀y₀, x₀y₁, x₁y₀, x₁y₁)` in the coordinates of `ℙ¹ × ℙ¹`. -/
noncomputable def segreMap (k : Type*) [CommRing k] :
    MvPolynomial (Fin 4) k →ₐ[k] MvPolynomial (Fin 4) k :=
  MvPolynomial.aeval (fun i => match i with
    | 0 => MvPolynomial.X (R := k) (σ := Fin 4) 0 * MvPolynomial.X 2
    | 1 => MvPolynomial.X (R := k) (σ := Fin 4) 0 * MvPolynomial.X 3
    | 2 => MvPolynomial.X (R := k) (σ := Fin 4) 1 * MvPolynomial.X 2
    | 3 => MvPolynomial.X (R := k) (σ := Fin 4) 1 * MvPolynomial.X 3)

/-- Defining relation of the Segre quadric in `ℙ³`: `z₀ z₃ − z₁ z₂`. -/
noncomputable def segreRelation (k : Type*) [CommRing k] :
    MvPolynomial (Fin 4) k :=
  MvPolynomial.X (R := k) (σ := Fin 4) 0 * MvPolynomial.X 3 -
    MvPolynomial.X 1 * MvPolynomial.X 2

/-- The Segre relation `z₀ z₃ − z₁ z₂` lies in the kernel of the Segre
embedding: pulling it back along `segreMap` gives zero. -/
theorem segre_relation_in_kernel (k : Type*) [CommRing k] :
    segreMap k (segreRelation k) = 0 := by
  simp only [segreRelation, segreMap, map_sub, map_mul, MvPolynomial.aeval_X]
  ring

/-- Polynomial identity behind the Segre relation:
`(x₀ y₀)(x₁ y₁) − (x₀ y₁)(x₁ y₀) = 0` in any commutative ring. -/
theorem segre_algebraic_identity {R : Type*} [CommRing R]
    (x₀ x₁ y₀ y₁ : R) :
    (x₀ * y₀) * (x₁ * y₁) - (x₀ * y₁) * (x₁ * y₀) = 0 := by
  ring
