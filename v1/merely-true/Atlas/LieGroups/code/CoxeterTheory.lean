/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryO
import Atlas.LieGroups.code.HeckeKL

noncomputable section

open scoped BigOperators

namespace CoxeterGroupData

variable (C : CoxeterGroupData)

structure ReducedWord (w : C.W) where
  word : List C.W
  mem_simple : ∀ s ∈ word, s ∈ C.simpleReflections
  prod_eq : word.prod = w
  length_eq : word.length = C.length w

theorem descentRefl_length_eq (y : C.W) (hy : y ≠ 1) :
    C.length (C.descentRefl y * y) + 1 = C.length y := by
  have hs := C.descentRefl_simple y hy
  have hlt := C.descentRefl_length y hy
  have hex := C.exchange_left (C.descentRefl y) hs y
  omega

def IsReducedWord (word : List C.W) : Prop :=
  (∀ s ∈ word, s ∈ C.simpleReflections) ∧ word.length = C.length word.prod

theorem length_mul_le (v w : C.W) :
    C.length (v * w) ≤ C.length v + C.length w := by
  suffices h : ∀ (n : ℕ) (v w : C.W), C.length v = n →
      C.length (v * w) ≤ C.length v + C.length w from
    h (C.length v) v w rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro v w hv
    by_cases hv1 : v = 1
    · subst hv1; simp only [one_mul]; omega
    · set s := C.descentRefl v with s_def
      have hs := C.descentRefl_simple v hv1
      have hlen_v : C.length (s * v) + 1 = C.length v :=
        C.descentRefl_length_eq v hv1

      have hsq : s * s = 1 := C.simple_sq s hs
      have hv_eq : v = s * (s * v) := by
        calc v = 1 * v := by rw [one_mul]
          _ = (s * s) * v := by rw [hsq]
          _ = s * (s * v) := by rw [mul_assoc]

      have hvw_eq : v * w = s * ((s * v) * w) := by
        conv_lhs => rw [hv_eq]
        rw [mul_assoc]

      have hex := C.exchange_left s hs ((s * v) * w)

      have hlen_sv_lt : C.length (s * v) < n := by omega
      have ih_app := ih (C.length (s * v)) hlen_sv_lt (s * v) w rfl
      rw [hvw_eq]
      omega

theorem length_inv_le (w : C.W) : C.length w⁻¹ ≤ C.length w := by
  suffices h : ∀ (n : ℕ) (w : C.W), C.length w = n → C.length w⁻¹ ≤ C.length w from
    h (C.length w) w rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w hw
    by_cases hw1 : w = 1
    · subst hw1; simp [inv_one]
    · set s := C.descentRefl w with s_def
      have hs := C.descentRefl_simple w hw1
      have hlen : C.length (s * w) + 1 = C.length w := C.descentRefl_length_eq w hw1
      have hsq : s * s = 1 := C.simple_sq s hs
      have hs_inv : s⁻¹ = s := by
        rw [inv_eq_of_mul_eq_one_right hsq]
      have hw_eq : w = s * (s * w) := by
        calc w = 1 * w := by rw [one_mul]
          _ = (s * s) * w := by rw [hsq]
          _ = s * (s * w) := by rw [mul_assoc]
      have hinv_eq : w⁻¹ = (s * w)⁻¹ * s := by
        conv_lhs => rw [hw_eq]
        rw [mul_inv_rev, hs_inv]
      have h1 : C.length w⁻¹ ≤ C.length (s * w)⁻¹ + C.length s := by
        rw [hinv_eq]; exact C.length_mul_le (s * w)⁻¹ s
      have h2 : C.length s = 1 := C.length_simple s hs
      have hlen_lt : C.length (s * w) < n := by omega
      have h3 : C.length (s * w)⁻¹ ≤ C.length (s * w) :=
        ih (C.length (s * w)) hlen_lt (s * w) rfl
      omega

end CoxeterGroupData

namespace WeylGroupData

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}

def weylLength (wg : WeylGroupData Δ) (C : CoxeterGroupData)
    (rd : PositiveRootData Δ) (compat : CoxeterWeylCompatibility C rd wg)
    (w : wg.W) : ℕ :=
  C.length (compat.ι.symm w)

end WeylGroupData

namespace RootSystemWithReflections

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}
variable {rd : PositiveRootData Δ}
variable {wg : WeylGroupData Δ}

def inversions (_rs : RootSystemWithReflections rd wg)
    (w : wg.W) : Finset (Δ.𝔥 →ₗ[R] R) := by
  classical
  exact rd.posRoots.filter (fun α => -(wg.dualAction w α) ∈ rd.posRoots)

end RootSystemWithReflections

structure SimpleRootData
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (C : CoxeterGroupData)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (compat : CoxeterWeylCompatibility C rd wg) where
  simpleRoot : C.W → Δ.𝔥 →ₗ[R] R
  simpleRoot_pos : ∀ s ∈ C.simpleReflections, simpleRoot s ∈ rd.posRoots
  simpleRoot_mem : ∀ s ∈ C.simpleReflections, simpleRoot s ∈ rs.allRoots
  simpleRoot_refl : ∀ s ∈ C.simpleReflections, rs.reflection (simpleRoot s) = compat.ι s
  simpleRoot_injective : ∀ s₁ ∈ C.simpleReflections, ∀ s₂ ∈ C.simpleReflections,
    simpleRoot s₁ = simpleRoot s₂ → s₁ = s₂

end
