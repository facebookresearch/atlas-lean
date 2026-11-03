/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions

/-- Concrete model of Sweedler's 4-dimensional Hopf algebra `H₄` over a field `k`: an element is
recorded as a tuple of 4 coefficients in the basis `(1, g, x, gx)`. -/
@[ext]
structure SweedlerH4 (k : Type*) [Field k] where
  coeff : Fin 4 → k

variable {k : Type*} [Field k]

namespace SweedlerH4

/-- Zero element of `SweedlerH4 k`, with all coefficients zero. -/
noncomputable instance : Zero (SweedlerH4 k) := ⟨⟨0⟩⟩
/-- Addition on `SweedlerH4 k`, componentwise on coefficients. -/
noncomputable instance : Add (SweedlerH4 k) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩
/-- Negation on `SweedlerH4 k`, componentwise on coefficients. -/
noncomputable instance : Neg (SweedlerH4 k) := ⟨fun a => ⟨-a.coeff⟩⟩
/-- Subtraction on `SweedlerH4 k`, componentwise on coefficients. -/
noncomputable instance : Sub (SweedlerH4 k) := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩
/-- Scalar multiplication by `k` on `SweedlerH4 k`, scaling each coefficient. -/
noncomputable instance instSMul : SMul k (SweedlerH4 k) := ⟨fun r a => ⟨r • a.coeff⟩⟩

/-- All coefficients of `0 : SweedlerH4 k` are zero. -/
@[simp] lemma coeff_zero' (i : Fin 4) : (0 : SweedlerH4 k).coeff i = 0 := rfl
/-- Componentwise formula for addition coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_add (a b : SweedlerH4 k) (i : Fin 4) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl
/-- Componentwise formula for negation coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_neg (a : SweedlerH4 k) (i : Fin 4) :
    (-a).coeff i = -a.coeff i := rfl
/-- Componentwise formula for subtraction coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_sub (a b : SweedlerH4 k) (i : Fin 4) :
    (a - b).coeff i = a.coeff i - b.coeff i := rfl
/-- Componentwise formula for scalar multiplication coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_smul (r : k) (a : SweedlerH4 k) (i : Fin 4) :
    (r • a).coeff i = r * a.coeff i := rfl

/-- Structure constants of `SweedlerH4 k` in the basis `e₀ = 1, e₁ = g, e₂ = x, e₃ = gx`: for
each pair `(i, j)`, gives the coefficient of `e_m` in `e_i · e_j`. -/
noncomputable def basisMul (i j : Fin 4) : Fin 4 → k := fun m =>
  match i, j, m with
  | 0, j, m => if j = m then 1 else 0
  | i, 0, m => if i = m then 1 else 0
  | 1, 1, 0 => 1
  | 1, 2, 3 => 1
  | 1, 3, 2 => 1
  | 2, 1, 3 => -1
  | 3, 1, 2 => -1
  | _, _, _ => 0

/-- Multiplication on `SweedlerH4 k`, given by bilinearly extending the basis structure
constants `basisMul`. -/
noncomputable instance : Mul (SweedlerH4 k) where
  mul a b := ⟨fun m => ∑ i : Fin 4, ∑ j : Fin 4, a.coeff i * b.coeff j * basisMul i j m⟩

/-- The unit element of `SweedlerH4 k`, the basis vector `e₀`. -/
noncomputable instance : One (SweedlerH4 k) where
  one := ⟨fun i => if i = 0 then 1 else 0⟩

/-- The natural-number cast into `SweedlerH4 k`, sending `n` to `n · e₀`. -/
noncomputable instance : NatCast (SweedlerH4 k) where
  natCast n := ⟨fun i => if i = 0 then (n : k) else 0⟩

/-- The integer cast into `SweedlerH4 k`, sending `n` to `n · e₀`. -/
noncomputable instance : IntCast (SweedlerH4 k) where
  intCast n := ⟨fun i => if i = 0 then (n : k) else 0⟩

/-- Componentwise formula for multiplication coefficients in `SweedlerH4 k`, in terms of the
basis structure constants. -/
@[simp] lemma coeff_mul (a b : SweedlerH4 k) (m : Fin 4) :
    (a * b).coeff m = ∑ i : Fin 4, ∑ j : Fin 4, a.coeff i * b.coeff j * basisMul i j m := rfl

/-- Componentwise formula for the unit coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_one (m : Fin 4) :
    (1 : SweedlerH4 k).coeff m = if m = 0 then 1 else 0 := rfl

/-- Componentwise formula for natural-cast coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_natCast (n : ℕ) (m : Fin 4) :
    (n : SweedlerH4 k).coeff m = if m = 0 then (n : k) else 0 := rfl

/-- Componentwise formula for integer-cast coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_intCast (n : ℤ) (m : Fin 4) :
    (n : SweedlerH4 k).coeff m = if m = 0 then (n : k) else 0 := rfl

/-- A finite sum over `Fin 4` expands as the sum of the four values at `0, 1, 2, 3`. -/
@[simp] lemma Fin4_sum (f : Fin 4 → k) :
    ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

private lemma one_mul' (a : SweedlerH4 k) : 1 * a = a := by
  ext m; simp only [coeff_mul, coeff_one, Fin4_sum, basisMul]; fin_cases m <;> simp

private lemma mul_one' (a : SweedlerH4 k) : a * 1 = a := by
  ext m; simp only [coeff_mul, coeff_one, Fin4_sum, basisMul]; fin_cases m <;> simp

set_option maxHeartbeats 800000 in
private lemma mul_assoc' (a b c : SweedlerH4 k) : a * b * c = a * (b * c) := by
  ext m; simp only [coeff_mul, Fin4_sum, basisMul]; fin_cases m <;> simp <;> ring

private lemma left_distrib' (a b c : SweedlerH4 k) : a * (b + c) = a * b + a * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

private lemma right_distrib' (a b c : SweedlerH4 k) : (a + b) * c = a * c + b * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- `SweedlerH4 k` is an additive abelian group under componentwise operations. -/
noncomputable instance : AddCommGroup (SweedlerH4 k) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  neg_add_cancel a := by ext i; simp
  sub_eq_add_neg a b := by ext i; simp [sub_eq_add_neg]
  nsmul := fun n a => ⟨fun i => n • a.coeff i⟩
  nsmul_zero a := by ext i; simp
  nsmul_succ n a := by ext i; simp [add_mul, add_comm]
  zsmul := fun n a => ⟨fun i => n • a.coeff i⟩
  zsmul_zero' a := by ext i; simp
  zsmul_succ' n a := by ext i; simp [add_mul, add_comm]
  zsmul_neg' n a := by ext i; simp [Int.negSucc_eq]; ring

/-- `SweedlerH4 k` is a (noncommutative) ring with multiplication given by the basis structure
constants `basisMul`. -/
noncomputable instance : Ring (SweedlerH4 k) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul a := by ext m; simp [zero_mul, Finset.sum_const_zero]
  mul_zero a := by ext m; simp [mul_zero, Finset.sum_const_zero]
  natCast_zero := by ext m; simp
  natCast_succ n := by ext m; simp; split <;> simp
  intCast_ofNat n := by ext m; simp
  intCast_negSucc n := by ext m; simp [Int.negSucc_eq]; split <;> simp

/-- `SweedlerH4 k` is a `k`-module under componentwise scaling. -/
noncomputable instance : Module k (SweedlerH4 k) where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

/-- `SweedlerH4 k` is a `k`-algebra with scalar action factoring through multiplication by `e₀`. -/
noncomputable instance : Algebra k (SweedlerH4 k) :=
  Algebra.ofModule
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)

/-- The canonical `k`-linear equivalence between `SweedlerH4 k` and `Fin 4 → k` extracting the
coefficient tuple. -/
noncomputable def toFunEquiv : SweedlerH4 k ≃ₗ[k] (Fin 4 → k) where
  toFun a := a.coeff
  invFun f := ⟨f⟩
  map_add' a b := rfl
  map_smul' r a := by ext i; simp [Pi.smul_apply, smul_eq_mul]
  left_inv a := rfl
  right_inv f := rfl

/-- `SweedlerH4 k` has `k`-dimension exactly 4, matching its basis `(1, g, x, gx)`. -/
lemma finrank_eq : Module.finrank k (SweedlerH4 k) = 4 := by
  rw [LinearEquiv.finrank_eq toFunEquiv, Module.finrank_fin_fun]

/-- The standard basis vector `e i` of `SweedlerH4 k`, with coefficient `1` at `i` and `0`
elsewhere. -/
def e (i : Fin 4) : SweedlerH4 k where
  coeff := fun j => if i = j then 1 else 0

/-- The Sweedler generator `g`, identified with the basis vector `e 1`. -/
def gen_g : SweedlerH4 k := e 1

/-- The Sweedler generator `x`, identified with the basis vector `e 2`. -/
def gen_x : SweedlerH4 k := e 2

/-- Coefficient formula for the basis vector `e i`. -/
@[simp] lemma coeff_e (i j : Fin 4) :
    (e i : SweedlerH4 k).coeff j = if i = j then 1 else 0 := rfl

/-- Coefficient formula for the generator `g = e 1`. -/
@[simp] lemma coeff_gen_g (j : Fin 4) :
    (gen_g : SweedlerH4 k).coeff j = if (1 : Fin 4) = j then 1 else 0 := rfl

/-- Coefficient formula for the generator `x = e 2`. -/
@[simp] lemma coeff_gen_x (j : Fin 4) :
    (gen_x : SweedlerH4 k).coeff j = if (2 : Fin 4) = j then 1 else 0 := rfl

/-- Defining relation of `H₄`: `g² = 1`. -/
lemma gen_g_sq : (gen_g : SweedlerH4 k) * gen_g = 1 := by
  ext m; simp only [gen_g, coeff_mul, coeff_e, coeff_one, Fin4_sum, basisMul]
  fin_cases m <;> simp

/-- Defining relation of `H₄`: `x² = 0`. -/
lemma gen_x_sq : (gen_x : SweedlerH4 k) * gen_x = 0 := by
  ext m; simp only [gen_x, coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]
  fin_cases m <;> simp

/-- Defining anti-commutation relation of `H₄`: `gx = -xg`. -/
lemma gen_gx_comm : (gen_g : SweedlerH4 k) * gen_x = -(gen_x * gen_g) := by
  ext m; simp only [gen_g, gen_x, coeff_mul, coeff_e, coeff_neg, Fin4_sum, basisMul]
  fin_cases m <;> simp

/-- The product `g · x` is the fourth basis vector `e 3`, i.e. the basis element usually denoted
`gx`. -/
lemma gen_g_mul_x : (gen_g : SweedlerH4 k) * gen_x = e 3 := by
  ext m; simp only [gen_g, gen_x, coeff_mul, coeff_e, Fin4_sum, basisMul]
  fin_cases m <;> simp

/-- The first basis vector `e 0` is the multiplicative unit `1` of `SweedlerH4 k`. -/
lemma e_zero_eq_one : (e 0 : SweedlerH4 k) = 1 := by
  ext m; simp only [coeff_e, coeff_one, eq_comm]

end SweedlerH4
