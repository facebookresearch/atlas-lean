/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SimpleGraph

variable {V : Type*} {W : Type*}

abbrev cartesianProduct (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) :=
  G □ H

end SimpleGraph

namespace SpectraCommonGraphs

open Real SimpleGraph Matrix

noncomputable section

abbrev ringGraph (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.cycleGraph n

def ringEigenvalue (n : ℕ) (k : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ))

def cosEigenvector (n : ℕ) (k : ℕ) (u : Fin n) : ℝ :=
  Real.cos (2 * Real.pi * (k : ℝ) * (u.val : ℝ) / (n : ℝ))

def sinEigenvector (n : ℕ) (k : ℕ) (u : Fin n) : ℝ :=
  Real.sin (2 * Real.pi * (k : ℝ) * (u.val : ℝ) / (n : ℝ))


lemma cos_nat_mod_period (k n : ℕ) (hn : (n : ℝ) ≠ 0) (a : ℕ) :
    cos (2 * π * ↑k * ↑(a % n) / ↑n) = cos (2 * π * ↑k * ↑a / ↑n) := by
  have hdiv : a = a % n + n * (a / n) := by have := Nat.div_add_mod a n; omega
  have heq : (↑a : ℝ) = ↑(a % n) + ↑n * ↑(a / n) := by exact_mod_cast hdiv
  conv_rhs => rw [heq]
  have heq2 : 2 * π * ↑k * (↑(a % n) + ↑n * ↑(a / n)) / ↑n
            = 2 * π * ↑k * ↑(a % n) / ↑n + ↑(a / n) * (↑k * (2 * π)) := by field_simp
  rw [heq2]
  exact ((cos_periodic.nat_mul k).nat_mul (a / n) _).symm

lemma sin_nat_mod_period (k n : ℕ) (hn : (n : ℝ) ≠ 0) (a : ℕ) :
    sin (2 * π * ↑k * ↑(a % n) / ↑n) = sin (2 * π * ↑k * ↑a / ↑n) := by
  have hdiv : a = a % n + n * (a / n) := by have := Nat.div_add_mod a n; omega
  have heq : (↑a : ℝ) = ↑(a % n) + ↑n * ↑(a / n) := by exact_mod_cast hdiv
  conv_rhs => rw [heq]
  have heq2 : 2 * π * ↑k * (↑(a % n) + ↑n * ↑(a / n)) / ↑n
            = 2 * π * ↑k * ↑(a % n) / ↑n + ↑(a / n) * (↑k * (2 * π)) := by field_simp
  rw [heq2]
  exact ((sin_periodic.nat_mul k).nat_mul (a / n) _).symm

lemma cos_real_periodic_add (k m : ℕ) (hm : (m : ℝ) ≠ 0) (a : ℝ) :
    cos (2 * π * ↑k * (a + ↑m) / ↑m) = cos (2 * π * ↑k * a / ↑m) := by
  have heq : 2 * π * (↑k : ℝ) * (a + ↑m) / ↑m
           = 2 * π * (↑k : ℝ) * a / ↑m + ↑k * (2 * π) := by field_simp
  rw [heq]; exact (cos_periodic.nat_mul k) _

lemma sin_real_periodic_add (k m : ℕ) (hm : (m : ℝ) ≠ 0) (a : ℝ) :
    sin (2 * π * ↑k * (a + ↑m) / ↑m) = sin (2 * π * ↑k * a / ↑m) := by
  have heq : 2 * π * (↑k : ℝ) * (a + ↑m) / ↑m
           = 2 * π * (↑k : ℝ) * a / ↑m + ↑k * (2 * π) := by field_simp
  rw [heq]; exact (sin_periodic.nat_mul k) _

lemma fin_sub_one_ne_add_one {n : ℕ} (v : Fin (n + 3)) : v - 1 ≠ v + 1 := by
  intro h
  have h2 : (-1 : Fin (n + 3)) = 1 := by
    have : (v - 1) - v = (v + 1) - v := congrArg (· - v) h; simpa using this
  exact absurd (Fin.val_eq_of_eq h2) (by simp [Fin.val_neg])

theorem lapMatrix_mulVec_cosEigenvector (n : ℕ) (k : ℕ) :
    (lapMatrix ℝ (ringGraph (n + 3))).mulVec (cosEigenvector (n + 3) k)
    = ringEigenvalue (n + 3) k • cosEigenvector (n + 3) k := by
  ext ⟨u, hu⟩
  simp only [Pi.smul_apply, smul_eq_mul, ringGraph]
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
      Finset.sum_pair (fin_sub_one_ne_add_one ⟨u, hu⟩)]
  simp only [cosEigenvector, ringEigenvalue]

  conv_lhs =>
    rw [show ((⟨u, hu⟩ - 1 : Fin (n + 3)).val : ℝ) = (((u + (n + 2)) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_sub]; ring_nf)]
    rw [show ((⟨u, hu⟩ + 1 : Fin (n + 3)).val : ℝ) = (((u + 1) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_add])]
  rw [cos_nat_mod_period k (n + 3) (by positivity) (u + (n + 2))]
  rw [cos_nat_mod_period k (n + 3) (by positivity) (u + 1)]
  rw [show (↑(u + (n + 2)) : ℝ) = ↑u - 1 + ↑(n + 3) from by push_cast; ring]
  rw [show (↑(u + 1) : ℝ) = (↑u : ℝ) + 1 from by push_cast; ring]
  rw [cos_real_periodic_add k (n + 3) (by positivity)]

  have hplus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) + 1) / ↑(n + 3)
             = 2 * π * ↑k * ↑u / ↑(n + 3) + 2 * π * ↑k / ↑(n + 3) := by ring
  have hminus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) - 1) / ↑(n + 3)
              = 2 * π * ↑k * ↑u / ↑(n + 3) - 2 * π * ↑k / ↑(n + 3) := by ring
  rw [hplus, hminus, cos_add, cos_sub]
  push_cast
  ring

theorem lapMatrix_mulVec_sinEigenvector (n : ℕ) (k : ℕ) :
    (lapMatrix ℝ (ringGraph (n + 3))).mulVec (sinEigenvector (n + 3) k)
    = ringEigenvalue (n + 3) k • sinEigenvector (n + 3) k := by
  ext ⟨u, hu⟩
  simp only [Pi.smul_apply, smul_eq_mul, ringGraph]
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
      Finset.sum_pair (fin_sub_one_ne_add_one ⟨u, hu⟩)]
  simp only [sinEigenvector, ringEigenvalue]
  conv_lhs =>
    rw [show ((⟨u, hu⟩ - 1 : Fin (n + 3)).val : ℝ) = (((u + (n + 2)) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_sub]; ring_nf)]
    rw [show ((⟨u, hu⟩ + 1 : Fin (n + 3)).val : ℝ) = (((u + 1) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_add])]
  rw [sin_nat_mod_period k (n + 3) (by positivity) (u + (n + 2))]
  rw [sin_nat_mod_period k (n + 3) (by positivity) (u + 1)]
  rw [show (↑(u + (n + 2)) : ℝ) = ↑u - 1 + ↑(n + 3) from by push_cast; ring]
  rw [show (↑(u + 1) : ℝ) = (↑u : ℝ) + 1 from by push_cast; ring]
  rw [sin_real_periodic_add k (n + 3) (by positivity)]
  have hplus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) + 1) / ↑(n + 3)
             = 2 * π * ↑k * ↑u / ↑(n + 3) + 2 * π * ↑k / ↑(n + 3) := by ring
  have hminus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) - 1) / ↑(n + 3)
              = 2 * π * ↑k * ↑u / ↑(n + 3) - 2 * π * ↑k / ↑(n + 3) := by ring
  rw [hplus, hminus, sin_add, sin_sub]
  push_cast
  ring

theorem ringGraph_lapMatrix_eigenvectors (n : ℕ) (k : ℕ) :
    (lapMatrix ℝ (ringGraph (n + 3))).mulVec (cosEigenvector (n + 3) k)
      = ringEigenvalue (n + 3) k • cosEigenvector (n + 3) k ∧
    (lapMatrix ℝ (ringGraph (n + 3))).mulVec (sinEigenvector (n + 3) k)
      = ringEigenvalue (n + 3) k • sinEigenvector (n + 3) k :=
  ⟨lapMatrix_mulVec_cosEigenvector n k, lapMatrix_mulVec_sinEigenvector n k⟩

end

end SpectraCommonGraphs

namespace GraphProductSpectrum

open Matrix Finset

def vecTensor {V W : Type*} (v : V → ℝ) (w : W → ℝ) : V × W → ℝ :=
  fun p => v p.1 * w p.2

theorem kronecker_one_mulVec_tensor
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : Matrix V V ℝ) (v : V → ℝ) (w : W → ℝ) :
    (kroneckerMap (· * ·) A (1 : Matrix W W ℝ)).mulVec (vecTensor v w) =
    vecTensor (A.mulVec v) w := by
  ext ⟨a, b⟩
  simp only [vecTensor, mulVec, dotProduct, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  congr 1; funext c
  have h : ∀ d : W, (A a c * if b = d then 1 else 0) * (v c * w d) =
      if b = d then A a c * v c * w b else 0 := by
    intro d; split_ifs with h; subst h; ring; ring
  simp_rw [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem one_kronecker_mulVec_tensor
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (B : Matrix W W ℝ) (v : V → ℝ) (w : W → ℝ) :
    (kroneckerMap (· * ·) (1 : Matrix V V ℝ) B).mulVec (vecTensor v w) =
    vecTensor v (B.mulVec w) := by
  ext ⟨a, b⟩
  simp only [vecTensor, mulVec, dotProduct, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type]
  trans (∑ c : V, if a = c then ∑ d : W, v a * (B b d * w d) else 0)
  · apply Finset.sum_congr rfl; intro c _
    split_ifs with h
    · subst h; apply Finset.sum_congr rfl; intro d _; ring
    · apply Finset.sum_eq_zero; intro d _; simp
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]

theorem kronecker_sum_eigenvector
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (A : Matrix V V ℝ) (B : Matrix W W ℝ)
    (v : V → ℝ) (w : W → ℝ) (eigA eigB : ℝ)
    (hv : A.mulVec v = eigA • v)
    (hw : B.mulVec w = eigB • w) :
    (kroneckerMap (· * ·) A (1 : Matrix W W ℝ) +
     kroneckerMap (· * ·) (1 : Matrix V V ℝ) B).mulVec (vecTensor v w) =
    (eigA + eigB) • vecTensor v w := by
  rw [add_mulVec, kronecker_one_mulVec_tensor, one_kronecker_mulVec_tensor, hv, hw]
  ext ⟨a, b⟩
  simp only [vecTensor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

open SimpleGraph in
instance boxProd_decidableAdj
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := by
  intro ⟨v₁, w₁⟩ ⟨v₂, w₂⟩; rw [SimpleGraph.boxProd_adj]; infer_instance

theorem boxProd_degree_eq
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (v : V) (w : W) :
    (G □ H).degree (v, w) = G.degree v + H.degree w := by
  simp only [SimpleGraph.degree]
  rw [show (G □ H).neighborFinset (v, w) =
    ((G.neighborFinset v).map ⟨fun v' => (v', w), fun a b h => by simpa using h⟩) ∪
    ((H.neighborFinset w).map ⟨fun w' => (v, w'), fun a b h => by simpa using h⟩) from ?_]
  · rw [Finset.card_union_of_disjoint]
    · simp [Finset.card_map]
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx1 hx2
      obtain ⟨a, ha, rfl⟩ := hx1
      obtain ⟨b, _, heq⟩ := hx2
      have h1 : a = v := congr_arg Prod.fst heq.symm
      subst h1; rw [SimpleGraph.mem_neighborFinset] at ha; exact G.irrefl ha
  · ext ⟨v', w'⟩
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk, SimpleGraph.boxProd_adj]
    constructor
    · rintro (⟨hG, rfl⟩ | ⟨hH, rfl⟩)
      · left; exact ⟨v', hG, rfl⟩
      · right; exact ⟨w', hH, rfl⟩
    · rintro (⟨a, ha, h⟩ | ⟨b, hb, h⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; left; exact ⟨ha, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; right; exact ⟨hb, rfl⟩

theorem lapMatrix_boxProd_eq_kronecker_sum
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (G □ H).lapMatrix ℝ =
      kroneckerMap (· * ·) (G.lapMatrix ℝ) (1 : Matrix W W ℝ) +
      kroneckerMap (· * ·) (1 : Matrix V V ℝ) (H.lapMatrix ℝ) := by
  ext ⟨v₁, w₁⟩ ⟨v₂, w₂⟩
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
    Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply,
    Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases hv : v₁ = v₂ <;> by_cases hw : w₁ = w₂
  · subst hv; subst hw
    simp only [and_self, ite_true, mul_one, one_mul]
    have hadj : ¬(G □ H).Adj (v₁, w₁) (v₁, w₁) := (G □ H).irrefl
    simp only [hadj, G.irrefl, H.irrefl, ite_false, sub_zero]
    norm_cast; convert boxProd_degree_eq G H v₁ w₁ using 2
  · subst hv
    simp only [hw, and_false, ite_true, ite_false, mul_zero, zero_add, one_mul]
    have hadj : (G □ H).Adj (v₁, w₁) (v₁, w₂) ↔ H.Adj w₁ w₂ := by
      simp [SimpleGraph.boxProd_adj, hw]
    simp only [show (G □ H).Adj (v₁, w₁) (v₁, w₂) = H.Adj w₁ w₂ from propext hadj]
  · subst hw
    simp only [hv, and_true, ite_true, ite_false, mul_one, zero_mul, add_zero]
    have hadj : (G □ H).Adj (v₁, w₁) (v₂, w₁) ↔ G.Adj v₁ v₂ := by
      simp [SimpleGraph.boxProd_adj, hv]
    simp only [show (G □ H).Adj (v₁, w₁) (v₂, w₁) = G.Adj v₁ v₂ from propext hadj]
  · have hadj : ¬(G □ H).Adj (v₁, w₁) (v₂, w₂) := by
      rw [SimpleGraph.boxProd_adj]; push Not; exact ⟨fun _ => hw, fun _ => hv⟩
    simp only [hv, hw, and_false, ite_false, hadj, mul_zero, zero_mul, add_zero,
      sub_zero]

theorem lapMatrix_boxProd_eigenvector
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (v : V → ℝ) (w : W → ℝ) (eigG eigH : ℝ)
    (hv : (G.lapMatrix ℝ).mulVec v = eigG • v)
    (hw : (H.lapMatrix ℝ).mulVec w = eigH • w) :
    ((G □ H).lapMatrix ℝ).mulVec (vecTensor v w) =
    (eigG + eigH) • vecTensor v w := by
  rw [lapMatrix_boxProd_eq_kronecker_sum]
  exact kronecker_sum_eigenvector (G.lapMatrix ℝ) (H.lapMatrix ℝ) v w eigG eigH hv hw

end GraphProductSpectrum
