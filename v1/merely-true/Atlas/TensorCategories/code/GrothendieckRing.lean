/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs

set_option maxHeartbeats 800000

open Finset

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Integer-valued version of the fusion ring unit-left-multiplication axiom. -/
lemma unit_mul_int (j k : ι) :
    (R.N R.unit j k : ℤ) = if j = k then 1 else 0 := by
  rw [R.unit_mul]; split <;> simp

/-- Integer-valued version of the fusion ring unit-right-multiplication axiom. -/
lemma mul_unit_int (i k : ι) :
    (R.N i R.unit k : ℤ) = if i = k then 1 else 0 := by
  rw [R.mul_unit]; split <;> simp

/-- Integer-valued version of the associativity identity for fusion coefficients. -/
lemma assoc_int (i j k l : ι) :
    (univ.sum fun m => (R.N i j m : ℤ) * (R.N m k l : ℤ)) =
    (univ.sum fun m => (R.N j k m : ℤ) * (R.N i m l : ℤ)) := by
  exact_mod_cast R.assoc i j k l

/-- The underlying integer-valued function space `ι → ℤ` of the Grothendieck ring on basis
`ι`. Elements are interpreted as formal `ℤ`-linear combinations of basis vectors. -/
def GrRing (ι : Type*) [DecidableEq ι] [Fintype ι] := ι → ℤ

/-- Multiplication on `GrRing ι` defined by the fusion structure constants `N i j k`,
implementing `X_i X_j = ∑_k N_{ij}^k X_k`. -/
def grMul (f g : GrRing ι) : GrRing ι :=
  fun k => univ.sum fun i => univ.sum fun j => f i * g j * (R.N i j k : ℤ)

/-- The multiplicative identity of `GrRing ι`: the indicator function of the unit basis element. -/
def grOne : GrRing ι := fun k => if k = R.unit then 1 else 0

/-- A sum of a constant `if`-expression equals the same `if` applied to the unconditional sum. -/
lemma sum_ite_const_zero {α : Type*} [AddCommMonoid α] {ι' : Type*}
    {p : Prop} [Decidable p] (s : Finset ι') (f : ι' → α) :
    (∑ x ∈ s, if p then f x else 0) = if p then ∑ x ∈ s, f x else 0 := by
  split <;> simp_all

/-- Left identity for `grMul`: the unit element acts as the multiplicative identity. -/
theorem grMul_one_left (f : GrRing ι) : R.grMul R.grOne f = f := by
  funext k; unfold grMul grOne
  simp_rw [ite_mul, one_mul, zero_mul, sum_ite_const_zero,
    sum_ite_eq', mem_univ, if_true, R.unit_mul_int,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

/-- Right identity for `grMul`: the unit element acts as the multiplicative identity. -/
theorem grMul_one_right (f : GrRing ι) : R.grMul f R.grOne = f := by
  funext k; unfold grMul grOne
  simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true, R.mul_unit_int,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

/-- Auxiliary rearrangement used in the proof of associativity: rewriting the inner
sum using the integer-valued associativity identity. -/
lemma inner_sum_eq (a b c : GrRing ι) (l i j k : ι) :
    (∑ m : ι, a i * (b j * (c k * ((R.N i j m : ℤ) * (R.N m k l : ℤ))))) =
    (∑ q : ι, a i * (b j * (c k * ((R.N j k q : ℤ) * (R.N i q l : ℤ))))) := by
  simp_rw [← Finset.mul_sum]
  congr 3
  exact R.assoc_int i j k l

/-- Associativity of `grMul` on `GrRing ι`, coming from the associativity of fusion coefficients
(Lemma 1.16.1). -/
theorem grMul_assoc (a b c : GrRing ι) :
    R.grMul (R.grMul a b) c = R.grMul a (R.grMul b c) := by
  funext l; simp only [grMul]

  simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, mul_assoc]


  trans (∑ i : ι, ∑ j, ∑ k, ∑ m,
    a i * (b j * (c k * ((R.N i j m : ℤ) * (R.N m k l : ℤ)))))
  ·
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k; congr 1; ext m; ring
  ·
    conv_rhs => arg 2; ext _; rw [Finset.sum_comm]
    conv_rhs => arg 2; ext _; arg 2; ext _; rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; congr 1; ext k
    exact R.inner_sum_eq a b c l i j k

/-- Left distributivity of `grMul` over pointwise addition. -/
theorem grMul_left_distrib (a b c : GrRing ι) :
    R.grMul a (fun k => b k + c k) = fun k => R.grMul a b k + R.grMul a c k := by
  funext l; simp only [grMul]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

/-- Right distributivity of `grMul` over pointwise addition. -/
theorem grMul_right_distrib (a b c : GrRing ι) :
    R.grMul (fun k => a k + b k) c = fun k => R.grMul a c k + R.grMul b c k := by
  funext l; simp only [grMul]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- Multiplying by the zero function on the right yields zero. -/
theorem grMul_zero (a : GrRing ι) :
    R.grMul a (fun _ => 0) = fun _ => 0 := by
  funext l; simp only [grMul]; simp

/-- Multiplying by the zero function on the left yields zero. -/
theorem grZero_mul (a : GrRing ι) :
    R.grMul (fun _ => 0) a = fun _ => 0 := by
  funext l; simp only [grMul]; simp

/-- Bundled form of the Grothendieck ring of a fusion ring `R`: an element is identified
with its integer-valued coefficient function on the basis. -/
@[ext]
structure GrRingOf (R : FusionRing ι) where
  coeff : ι → ℤ

namespace GrRingOf

variable {R : FusionRing ι}

/-- Zero element of `GrRingOf R`. -/
instance : Zero (GrRingOf R) := ⟨⟨fun _ => 0⟩⟩
/-- Multiplicative identity of `GrRingOf R`, given by `R.grOne`. -/
instance : One (GrRingOf R) := ⟨⟨R.grOne⟩⟩

/-- Pointwise addition on `GrRingOf R`. -/
instance : Add (GrRingOf R) := ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
/-- Pointwise negation on `GrRingOf R`. -/
instance : Neg (GrRingOf R) := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩
/-- Pointwise subtraction on `GrRingOf R`. -/
instance : Sub (GrRingOf R) := ⟨fun a b => ⟨fun k => a.coeff k - b.coeff k⟩⟩
/-- Fusion multiplication on `GrRingOf R`. -/
instance : Mul (GrRingOf R) := ⟨fun a b => ⟨R.grMul a.coeff b.coeff⟩⟩

/-- Pointwise `ℕ`-scalar multiplication on `GrRingOf R`. -/
instance : SMul ℕ (GrRingOf R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩
/-- Pointwise `ℤ`-scalar multiplication on `GrRingOf R`. -/
instance : SMul ℤ (GrRingOf R) := ⟨fun n a => ⟨fun k => n • a.coeff k⟩⟩

/-- Embedding of `ℕ` into `GrRingOf R` as multiples of the unit basis element. -/
instance : NatCast (GrRingOf R) := ⟨fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩⟩
/-- Embedding of `ℤ` into `GrRingOf R` as multiples of the unit basis element. -/
instance : IntCast (GrRingOf R) := ⟨fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩⟩

/-- The coefficient of the zero element is zero. -/
@[simp] lemma coeff_zero (k : ι) : (0 : GrRingOf R).coeff k = 0 := rfl
/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : GrRingOf R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl
/-- Coefficients distribute over negation. -/
@[simp] lemma coeff_neg (a : GrRingOf R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl
/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : GrRingOf R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

/-- The Grothendieck ring `GrRingOf R` of a fusion ring `R` is a `Ring`. -/
instance instRing : Ring (GrRingOf R) where
  add_assoc a b c := by ext k; simp [add_assoc]
  zero_add a := by ext k; simp
  add_zero a := by ext k; simp
  nsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  nsmul_zero a := by ext k; simp
  nsmul_succ n a := by ext k; simp [add_mul, add_comm]
  add_comm a b := by ext k; simp [add_comm]
  mul_assoc a b c := by
    ext k
    show (R.grMul (R.grMul a.coeff b.coeff) c.coeff) k =
         (R.grMul a.coeff (R.grMul b.coeff c.coeff)) k
    rw [R.grMul_assoc]
  one_mul a := by
    ext k
    show (R.grMul R.grOne a.coeff) k = a.coeff k
    rw [R.grMul_one_left]
  mul_one a := by
    ext k
    show (R.grMul a.coeff R.grOne) k = a.coeff k
    rw [R.grMul_one_right]
  left_distrib a b c := by
    ext k
    show (R.grMul a.coeff (fun k => b.coeff k + c.coeff k)) k =
         (R.grMul a.coeff b.coeff) k + (R.grMul a.coeff c.coeff) k
    rw [R.grMul_left_distrib]
  right_distrib a b c := by
    ext k
    show (R.grMul (fun k => a.coeff k + b.coeff k) c.coeff) k =
         (R.grMul a.coeff c.coeff) k + (R.grMul b.coeff c.coeff) k
    rw [R.grMul_right_distrib]
  zero_mul a := by
    ext k
    show (R.grMul (fun _ => 0) a.coeff) k = 0
    rw [R.grZero_mul]
  mul_zero a := by
    ext k
    show (R.grMul a.coeff (fun _ => 0)) k = 0
    rw [R.grMul_zero]
  neg_add_cancel a := by ext k; simp
  sub_eq_add_neg a b := by ext k; simp [sub_eq_add_neg]
  zsmul := fun n a => ⟨fun k => n • a.coeff k⟩
  zsmul_zero' a := by ext k; simp
  zsmul_succ' n a := by ext k; simp [add_mul, add_comm]
  zsmul_neg' n a := by
    ext k
    show Int.negSucc n • a.coeff k = -((↑(n + 1) : ℤ) • a.coeff k)
    simp [Int.negSucc_eq, Nat.cast_succ]
    ring
  natCast := fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩
  natCast_zero := by
    ext k
    show (if k = R.unit then (0 : ℤ) else 0) = 0
    split <;> rfl
  natCast_succ m := by
    ext k
    show (if k = R.unit then ((m + 1 : ℕ) : ℤ) else 0) =
         (if k = R.unit then (m : ℤ) else 0) + (if k = R.unit then 1 else 0)
    split <;> simp
  intCast := fun m => ⟨fun k => if k = R.unit then (m : ℤ) else 0⟩
  intCast_ofNat m := by ext k; rfl
  intCast_negSucc m := by
    ext k
    show (if k = R.unit then (Int.negSucc m : ℤ) else 0) =
         -(if k = R.unit then ((m + 1 : ℕ) : ℤ) else 0)
    split <;> simp [Int.negSucc_eq]

end GrRingOf

/-- The basis vector indexed by `i ∈ ι`, given by the indicator function of `{i}`. -/
def basisVec (i : ι) : GrRing ι :=
  fun k => if k = i then 1 else 0

/-- The basis vector at the unit equals the multiplicative identity `grOne`. -/
lemma basisVec_unit_eq_grOne : basisVec R.unit = R.grOne := by
  funext k; simp [basisVec, grOne]

/-- Associativity of multiplication in the Grothendieck ring, packaged at the bundled level. -/
theorem grothendieckRing_mul_assoc (a b c : GrRingOf R) :
    a * b * c = a * (b * c) :=
  mul_assoc a b c

/-- Lemma 1.16.1: The multiplication on `Gr(C)` defined by fusion coefficients is associative. -/
theorem Lemma_1_16_1 (a b c : GrRingOf R) :
    a * b * c = a * (b * c) :=
  R.grothendieckRing_mul_assoc a b c

/-- A homomorphism of fusion rings, represented combinatorially by an integer matrix `M`
on the bases satisfying unit-preservation and a fusion-multiplication identity. -/
structure FusionRingHom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (R : FusionRing ι) (S : FusionRing κ) where
  M : ι → κ → ℤ
  map_unit : ∀ l, M R.unit l = if l = S.unit then 1 else 0
  map_mul : ∀ i j l,
    (Finset.univ.sum fun k => (R.N i j k : ℤ) * M k l) =
    (Finset.univ.sum fun p => Finset.univ.sum fun q => M i p * M j q * (S.N p q l : ℤ))

/-- The integer-valued action of a `FusionRingHom` on `GrRing` elements: linear extension
of the matrix `φ.M` along the basis. -/
def FusionRingHom.grMap
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) (f : GrRing ι) : GrRing κ :=
  fun l => Finset.univ.sum fun i => f i * φ.M i l

/-- `grMap` sends the multiplicative identity of `GrRing R` to that of `GrRing S`. -/
theorem FusionRingHom.grMap_one
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) :
    φ.grMap R.grOne = S.grOne := by
  funext l; simp only [grMap, grOne]
  simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact φ.map_unit l

/-- `grMap` is additive in its function argument. -/
theorem FusionRingHom.grMap_add
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) (f g : GrRing ι) :
    φ.grMap (fun k => f k + g k) = fun l => φ.grMap f l + φ.grMap g l := by
  funext l; simp only [grMap]
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- `grMap` is multiplicative with respect to the fusion product on the source and target. -/
theorem FusionRingHom.grMap_mul
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) (f g : GrRing ι) :
    φ.grMap (R.grMul f g) = S.grMul (φ.grMap f) (φ.grMap g) := by
  funext l; simp only [grMap, grMul]

  trans (∑ i : ι, ∑ j : ι, f i * g j *
    (Finset.univ.sum fun k => (R.N i j k : ℤ) * φ.M k l))
  ·
    simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  ·
    simp_rw [φ.map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext p; arg 2; ext q; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
    congr 1; ext p; congr 1; ext q; congr 1; ext i; congr 1; ext j; ring

/-- The ring homomorphism `GrRingOf R →+* GrRingOf S` induced by a `FusionRingHom`. -/
def FusionRingHom.inducedRingHom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) :
    GrRingOf R →+* GrRingOf S where
  toFun a := ⟨φ.grMap a.coeff⟩
  map_one' := by
    ext l; show φ.grMap R.grOne l = S.grOne l
    rw [φ.grMap_one]
  map_mul' a b := by
    ext l
    show φ.grMap (R.grMul a.coeff b.coeff) l = S.grMul (φ.grMap a.coeff) (φ.grMap b.coeff) l
    rw [φ.grMap_mul]
  map_zero' := by
    ext l; show (Finset.univ.sum fun i => (0 : GrRingOf R).coeff i * φ.M i l) = 0
    simp
  map_add' a b := by
    ext l
    show φ.grMap (fun k => a.coeff k + b.coeff k) l =
         φ.grMap a.coeff l + φ.grMap b.coeff l
    rw [φ.grMap_add]

end FusionRing

/-- The fusion ring of representations of `ℤ/2`, with basis `Fin 2` and product
given by addition modulo 2. -/
def repZ2 : FusionRing (Fin 2) where
  unit := 0
  N i j k := if (i.val + j.val) % 2 = k.val then 1 else 0
  star := id
  star_star := by decide
  unit_mul := by decide
  mul_unit := by decide
  duality := by decide
  assoc := by decide
  N_star_transpose := by decide

namespace repZ2

open FusionRing

/-- In `Gr(Rep(ℤ/2))`, the nontrivial sign object squares to the unit. -/
theorem mul_e1_e1 :
    grMul repZ2 (basisVec 1) (basisVec 1) = basisVec 0 := by
  funext k; simp only [grMul, basisVec]
  revert k; decide

end repZ2
