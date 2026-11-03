/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank

open ExteriorAlgebra

namespace Lec4Grassmannian

section GrassmannianDef

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

/-- Lecture 4: the Grassmannian `Gr(k, V)` of `k`-dimensional subspaces of `V`. -/
def Gr (k : ℕ) := {W : Submodule K V // Module.finrank K W = k}

end GrassmannianDef

section PluckerEmbedding

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- Dimension of the ambient space of the Plücker embedding: `dim (⋀^k V) = C(dim V, k)`. -/
theorem plucker_ambient_finrank (k : ℕ) :
    Module.finrank K (⋀[K]^k V) = Nat.choose (Module.finrank K V) k := by
  rw [exteriorPower.finrank_eq]

end PluckerEmbedding

section Lemma6Forward

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A 2-vector `ω ∈ ⋀^2 M` is *decomposable* if it can be written as a single wedge `v₁ ∧ v₂`. -/
def IsDecomposableTwo (ω : ExteriorAlgebra R M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι R v₁ * ι R v₂

/-- Anticommutativity of the canonical map `ι` into the exterior algebra: `x ∧ y = -(y ∧ x)`. -/
theorem ι_anticommute (x y : M) :
    (ι R (M := M)) x * (ι R) y = -((ι R) y * (ι R (M := M)) x) := by
  have h := @ι_add_mul_swap R _ M _ _ y x
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The wedge square of a decomposable 2-vector vanishes: `(v₁ ∧ v₂) ∧ (v₁ ∧ v₂) = 0`. -/
theorem wedge_sq_zero_of_decomp (v₁ v₂ : M) :
    (ι R v₁ * ι R v₂) * (ι R v₁ * ι R v₂) = (0 : ExteriorAlgebra R M) := by
  have anticomm : ι R v₂ * ι R v₁ = -((ι R (M := M)) v₁ * ι R v₂) := by
    have h := @ι_add_mul_swap R _ M _ _ v₁ v₂
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [mul_assoc, ← mul_assoc (ι R v₂) (ι R v₁) (ι R v₂)]
  rw [anticomm]
  rw [neg_mul, mul_neg, mul_assoc, ← mul_assoc (ι R v₁) (ι R v₁)]
  rw [ι_sq_zero, zero_mul, neg_zero]

/-- Easy direction of Lecture 4, Lemma 6: any decomposable 2-vector has zero wedge square. -/
theorem lemma6_forward {ω : ExteriorAlgebra R M}
    (h : IsDecomposableTwo ω) : ω * ω = 0 := by
  obtain ⟨v₁, v₂, rfl⟩ := h
  exact wedge_sq_zero_of_decomp v₁ v₂

end Lemma6Forward

section Lemma6Converse

variable {K : Type*} [Field K]

/-- Two wedge-products of pairs commute: `(a ∧ b) ∧ (c ∧ d) = (c ∧ d) ∧ (a ∧ b)`. -/
theorem ι_pair_commute {M : Type*} [AddCommGroup M] [Module K M] (a b c d : M) :
    (ι K a * ι K b) * (ι K c * ι K d) =
    (ι K c * ι K d) * ((ι K (M := M)) a * ι K b) := by
  have hAC := ι_anticommute (R := K) a c
  have hBC := ι_anticommute (R := K) b c
  have hBD := ι_anticommute (R := K) b d
  have hAD := ι_anticommute (R := K) a d
  calc (ι K a * ι K b) * (ι K c * ι K d)
      = ι K a * (ι K b * ι K c) * ι K d := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = ι K a * (-(ι K c * ι K b)) * ι K d := by rw [hBC]
    _ = -(ι K a * (ι K c * ι K b) * ι K d) := by rw [mul_neg, neg_mul]
    _ = -((ι K a * ι K c) * ι K b * ι K d) := by rw [mul_assoc (ι K a) (ι K c)]
    _ = -((-(ι K c * ι K a)) * ι K b * ι K d) := by rw [hAC]
    _ = (ι K c * ι K a) * ι K b * ι K d := by simp [neg_mul, neg_neg]
    _ = ι K c * (ι K a * (ι K b * ι K d)) := by rw [mul_assoc, mul_assoc]
    _ = ι K c * (ι K a * (-(ι K d * ι K b))) := by rw [hBD]
    _ = -(ι K c * (ι K a * (ι K d * ι K b))) := by rw [mul_neg, mul_neg]
    _ = -(ι K c * ((ι K a * ι K d) * ι K b)) := by rw [mul_assoc (ι K a)]
    _ = -(ι K c * ((-(ι K d * ι K a)) * ι K b)) := by rw [hAD]
    _ = ι K c * (ι K d * ι K a * ι K b) := by simp [neg_mul, mul_neg, neg_neg]
    _ = ι K c * (ι K d * (ι K a * ι K b)) := by rw [mul_assoc (ι K d)]
    _ = ι K c * ι K d * (ι K a * ι K b) := by rw [mul_assoc]

/-- Expansion of the wedge square of a sum of two decomposables:
`(v₁ ∧ v₂ + v₃ ∧ v₄)^2 = 2 · (v₁ ∧ v₂ ∧ v₃ ∧ v₄)`. -/
theorem wedge_sq_sum_decomp {M : Type*} [AddCommGroup M] [Module K M]
    (v₁ v₂ v₃ v₄ : M) :
    (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄) * (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄)
    = 2 * ((ι K (M := M)) v₁ * ι K v₂ * (ι K v₃ * ι K v₄)) := by
  rw [add_mul, mul_add, mul_add]
  rw [wedge_sq_zero_of_decomp v₁ v₂,
      wedge_sq_zero_of_decomp v₃ v₄]
  rw [zero_add, add_zero]
  rw [ι_pair_commute v₁ v₂ v₃ v₄]
  rw [two_mul]

/-- For a 4-dimensional `V`, `dim (⋀^2 V) = 6`. -/
theorem extPower_two_finrank_of_four
    (V : Type*) [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V]
    (hdim : Module.finrank K V = 4) :
    Module.finrank K (⋀[K]^2 V) = 6 := by
  rw [exteriorPower.finrank_eq, hdim]
  decide

/-- For a 4-dimensional `V`, the top exterior power is 1-dimensional: `dim (⋀^4 V) = 1`. -/
theorem extPower_four_finrank_of_four
    (V : Type*) [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V]
    (hdim : Module.finrank K V = 4) :
    Module.finrank K (⋀[K]^4 V) = 1 := by
  rw [exteriorPower.finrank_eq, hdim]
  decide


/-- An order-embedding `Fin n ↪o Fin n` is necessarily the identity. -/
lemma orderEmb_fin_eq_id (n : ℕ) (f : Fin n ↪o Fin n) (i : Fin n) : f i = i := by
  have hf := f.strictMono
  have h_surj : Function.Surjective f := Finite.surjective_of_injective f.injective
  have h_ge : ∀ j : Fin n, (j : ℕ) ≤ (f j : ℕ) := by
    intro ⟨j, hj⟩
    induction j with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk : k < n := Nat.lt_of_succ_lt hj
      have hih := ih hk
      have hlt : (f ⟨k, hk⟩ : ℕ) < (f ⟨k + 1, hj⟩ : ℕ) :=
        hf (show (⟨k, hk⟩ : Fin n) < ⟨k + 1, hj⟩ by simp [Fin.lt_def])
      simp only at hih hlt ⊢; omega
  have h_le : ∀ j : Fin n, (f j : ℕ) ≤ (j : ℕ) := by
    by_contra h; push Not at h; obtain ⟨j, hj⟩ := h
    set e := Equiv.ofBijective f ⟨f.injective, h_surj⟩
    have hsum : ∑ i : Fin n, (f i : ℕ) = ∑ i : Fin n, (i : ℕ) := by
      conv_rhs => rw [show (fun i : Fin n => (i : ℕ)) =
        (fun i => (e (e.symm i) : ℕ)) from by ext; simp]
      rw [← Equiv.sum_comp e.symm]; simp [e, Equiv.ofBijective]
    exact absurd hsum (Nat.ne_of_gt
      (Finset.sum_lt_sum (fun i _ => h_ge i) ⟨j, Finset.mem_univ j, by omega⟩))
  exact Fin.ext (Nat.le_antisymm (h_le i) (h_ge i))

/-- The product `v₁ ∧ v₂ ∧ v₃ ∧ v₄` in the exterior algebra agrees with the multilinear map
`ιMulti K 4` applied to the 4-tuple. -/
theorem product_eq_ιMulti {V : Type*} [AddCommGroup V] [Module K V]
    (v₁ v₂ v₃ v₄ : V) :
    ι K v₁ * ι K v₂ * (ι K v₃ * ι K v₄) = ιMulti K 4 ![v₁, v₂, v₃, v₄] := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_assoc]

set_option maxHeartbeats 800000 in
/-- A linearly independent 4-tuple in a 4-dimensional `V` has nonzero top wedge product. -/
theorem ιMulti_ne_zero_of_linearIndependent
    {V : Type*} [AddCommGroup V] [Module K V]
    (hdim : Module.finrank K V = 4) (v : Fin 4 → V)
    (hli : LinearIndependent K v) :
    ιMulti K 4 v ≠ 0 := by
  intro h

  have hcard : Fintype.card (Fin 4) = Module.finrank K V := by simp [hdim]
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb_coe : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard

  set s : Set.powersetCard (Fin 4) 4 := ⟨Finset.univ, Finset.card_fin 4⟩
  have hdiag := exteriorPower.ιMultiDual_apply_diag K 4 b s


  have key : (exteriorPower.ιMulti_family K 4 (⇑b) s : ⋀[K]^4 V) =
      exteriorPower.ιMulti K 4 (⇑b) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1
    funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1
    exact orderEmb_fin_eq_id 4 (Set.powersetCard.ofFinEmbEquiv.symm s) i
  rw [key] at hdiag

  have h_sub : exteriorPower.ιMulti K 4 (⇑b) = 0 := by
    apply Subtype.val_injective
    simp only [hb_coe, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero, h]

  rw [h_sub, map_zero] at hdiag
  exact zero_ne_one hdiag

variable [CharZero K]




end Lemma6Converse

section Gr24

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- Lecture 4, Theorem 4.1 applied to `Gr(2, 4)`: the Plücker ambient space has dimension 6. -/
theorem gr24_ambient_dim (hdim : Module.finrank K V = 4) :
    Module.finrank K (⋀[K]^2 V) = 6 :=
  extPower_two_finrank_of_four V hdim

end Gr24

end Lec4Grassmannian
