/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.ProductFormula

noncomputable section

open scoped Classical

structure ArakelovDivisor (K : Type*) [Field K] (hG : IsGlobalField K) where
  val : hG.PlaceType → ℝ
  pos : ∀ v, 0 < val v
  finite_support : Set.Finite {v | val v ≠ 1}

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

def one : ArakelovDivisor K hG where
  val := fun _ => 1
  pos := fun _ => one_pos
  finite_support := by simp

def mul (c d : ArakelovDivisor K hG) : ArakelovDivisor K hG where
  val := fun v => c.val v * d.val v
  pos := fun v => mul_pos (c.pos v) (d.pos v)
  finite_support := by
    apply Set.Finite.subset (c.finite_support.union d.finite_support)
    intro v hv
    simp only [Set.mem_setOf_eq, Set.mem_union] at hv ⊢
    by_contra h
    push Not at h
    exact hv (by rw [h.1, h.2, mul_one])

def inv (c : ArakelovDivisor K hG) : ArakelovDivisor K hG where
  val := fun v => (c.val v)⁻¹
  pos := fun v => inv_pos.mpr (c.pos v)
  finite_support := by
    apply Set.Finite.subset c.finite_support
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro h
    exact hv (by rw [h, inv_one])

instance : One (ArakelovDivisor K hG) := ⟨one⟩
instance : Mul (ArakelovDivisor K hG) := ⟨mul⟩
instance : Inv (ArakelovDivisor K hG) := ⟨inv⟩

@[simp] theorem one_val (v : hG.PlaceType) : (1 : ArakelovDivisor K hG).val v = 1 := rfl
@[simp] theorem mul_val (c d : ArakelovDivisor K hG) (v : hG.PlaceType) :
    (c * d).val v = c.val v * d.val v := rfl
@[simp] theorem inv_val (c : ArakelovDivisor K hG) (v : hG.PlaceType) :
    c⁻¹.val v = (c.val v)⁻¹ := rfl

@[ext] theorem ext {c d : ArakelovDivisor K hG} (h : ∀ v, c.val v = d.val v) : c = d := by
  cases c; cases d; simp only [mk.injEq]; ext v; exact h v

instance : CommGroup (ArakelovDivisor K hG) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc a b c := by ext v; simp [mul_assoc]
  one_mul a := by ext v; simp
  mul_one a := by ext v; simp
  mul_comm a b := by ext v; simp [mul_comm]
  inv_mul_cancel a := by
    ext v
    show (a.val v)⁻¹ * a.val v = 1
    exact inv_mul_cancel₀ (ne_of_gt (a.pos v))

def principal (x : K) (hx : x ≠ 0) : ArakelovDivisor K hG where
  val := fun v => hG.normAbsVal v x
  pos := by
    intro v
    rw [hG.normAbsVal_eq]
    exact Real.rpow_pos_of_pos ((hG.absVal v).pos hx) _
  finite_support := hG.normAbsVal_eq_one_of_finite x hx

theorem hasFiniteMulSupport (c : ArakelovDivisor K hG) :
    (Function.mulSupport c.val).Finite :=
  c.finite_support

def size (c : ArakelovDivisor K hG) : ℝ :=
  ∏ᶠ v, c.val v

@[simp] theorem size_one : (1 : ArakelovDivisor K hG).size = 1 := by
  simp [size, finprod_one]

theorem size_mul (c d : ArakelovDivisor K hG) :
    (c * d).size = c.size * d.size := by
  simp only [size, mul_val]
  exact finprod_mul_distrib c.hasFiniteMulSupport d.hasFiniteMulSupport

def sizeHom : ArakelovDivisor K hG →* ℝ where
  toFun := size
  map_one' := size_one
  map_mul' := size_mul

@[simp] theorem sizeHom_apply (c : ArakelovDivisor K hG) :
    sizeHom c = c.size := rfl

def L (c : ArakelovDivisor K hG) : Set K :=
  {x : K | ∀ v, hG.normAbsVal v x ≤ c.val v}

end ArakelovDivisor

end
