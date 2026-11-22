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
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Atlas.TensorCategories.code.QuantumSl2


/-- A concrete representative of the small quantum group `u_q(sl_2)` as a
`k`-vector space, recording an element by its coefficients on a finite
`n × n × n` PBW basis. -/
@[ext]
structure SmallQuantumSl2 (n : ℕ) (k : Type*) [Field k] where
  coeff : Fin n × Fin n × Fin n → k

variable {n : ℕ} {k : Type*} [Field k]

namespace SmallQuantumSl2

/-- Zero element: the all-zero coefficient vector. -/
noncomputable instance : Zero (SmallQuantumSl2 n k) := ⟨⟨0⟩⟩
/-- Coefficient-wise addition. -/
noncomputable instance : Add (SmallQuantumSl2 n k) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩
/-- Coefficient-wise negation. -/
noncomputable instance : Neg (SmallQuantumSl2 n k) := ⟨fun a => ⟨-a.coeff⟩⟩
/-- Coefficient-wise subtraction. -/
noncomputable instance : Sub (SmallQuantumSl2 n k) := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩
/-- Scalar multiplication by `k` on coefficients. -/
noncomputable instance instSMul : SMul k (SmallQuantumSl2 n k) := ⟨fun r a => ⟨r • a.coeff⟩⟩

/-- Coefficients of the zero element vanish. -/
@[simp] lemma coeff_zero' (i : Fin n × Fin n × Fin n) :
    (0 : SmallQuantumSl2 n k).coeff i = 0 := rfl
/-- Coefficients of a sum are sums of coefficients. -/
@[simp] lemma coeff_add (a b : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl
/-- Coefficients of a negation are negations of coefficients. -/
@[simp] lemma coeff_neg (a : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (-a).coeff i = -a.coeff i := rfl
/-- Coefficients of a difference are differences of coefficients. -/
@[simp] lemma coeff_sub (a b : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (a - b).coeff i = a.coeff i - b.coeff i := rfl
/-- Coefficients of a scalar multiple. -/
@[simp] lemma coeff_smul (r : k) (a : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (r • a).coeff i = r * a.coeff i := rfl

/-- Componentwise additive abelian group structure. -/
noncomputable instance : AddCommGroup (SmallQuantumSl2 n k) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  neg_add_cancel a := by ext i; simp
  sub_eq_add_neg a b := by ext i; simp [sub_eq_add_neg]
  nsmul := fun m a => ⟨fun i => m • a.coeff i⟩
  nsmul_zero a := by ext i; simp
  nsmul_succ m a := by ext i; simp [add_mul, add_comm]
  zsmul := fun m a => ⟨fun i => m • a.coeff i⟩
  zsmul_zero' a := by ext i; simp
  zsmul_succ' m a := by ext i; simp [add_mul, add_comm]
  zsmul_neg' m a := by ext i; simp [Int.negSucc_eq]; ring

/-- Componentwise `k`-module structure. -/
noncomputable instance : Module k (SmallQuantumSl2 n k) where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

/-- Linear equivalence between `SmallQuantumSl2 n k` and the coordinate space
`Fin n × Fin n × Fin n → k`. -/
noncomputable def toFunEquiv :
    SmallQuantumSl2 n k ≃ₗ[k] (Fin n × Fin n × Fin n → k) where
  toFun a := a.coeff
  invFun f := ⟨f⟩
  map_add' a b := rfl
  map_smul' r a := by ext i; simp [Pi.smul_apply, smul_eq_mul]
  left_inv a := rfl
  right_inv f := rfl

/-- `SmallQuantumSl2 n k` is a finite `k`-module. -/
noncomputable instance : Module.Finite k (SmallQuantumSl2 n k) :=
  Module.Finite.equiv toFunEquiv.symm

/-- `SmallQuantumSl2 n k` is finite-dimensional over `k`. -/
instance finiteDimensional : FiniteDimensional k (SmallQuantumSl2 n k) := inferInstance

/-- The standard basis vector indexed by `i`, with coefficient `1` at `i` and `0` elsewhere. -/
noncomputable def basisVec (i : Fin n × Fin n × Fin n) : SmallQuantumSl2 n k where
  coeff := fun j => if i = j then 1 else 0

/-- Coefficient formula for `basisVec`. -/
@[simp] lemma coeff_basisVec (i j : Fin n × Fin n × Fin n) :
    (basisVec i : SmallQuantumSl2 n k).coeff j = if i = j then 1 else 0 := rfl

/-- Coefficients commute with finite sums. -/
lemma coeff_finset_sum (s : Finset (Fin n × Fin n × Fin n))
    (f : Fin n × Fin n × Fin n → SmallQuantumSl2 n k)
    (j : Fin n × Fin n × Fin n) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  induction s using Finset.cons_induction with
  | empty => simp [Finset.sum_empty]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, coeff_add, ih]

end SmallQuantumSl2


/-- Relations defining the small quantum `sl_2` algebra `u_q(sl_2)` of dimension `n`:
nilpotency relations `K^n = 1`, `E^n = 0`, `F^n = 0` together with the `q`-commutation
relations between `K, E, F` adapted to the small quantum group setting. -/
inductive SmallQuantumRel (n : ℕ) (k : Type*) [Field k] (q : k) :
    FreeAlgebra k (Fin 3) → FreeAlgebra k (Fin 3) → Prop where
  | K_pow_n : SmallQuantumRel n k q
      ((FreeAlgebra.ι k (0 : Fin 3)) ^ n) 1
  | E_pow_n : SmallQuantumRel n k q
      ((FreeAlgebra.ι k (1 : Fin 3)) ^ n) 0
  | F_pow_n : SmallQuantumRel n k q
      ((FreeAlgebra.ι k (2 : Fin 3)) ^ n) 0
  | KE_comm : SmallQuantumRel n k q
      (FreeAlgebra.ι k (0 : Fin 3) * FreeAlgebra.ι k (1 : Fin 3))
      (q ^ 2 • (FreeAlgebra.ι k (1 : Fin 3) * FreeAlgebra.ι k (0 : Fin 3)))
  | KF_comm : SmallQuantumRel n k q
      (FreeAlgebra.ι k (0 : Fin 3) * FreeAlgebra.ι k (2 : Fin 3))
      ((q ^ 2)⁻¹ • (FreeAlgebra.ι k (2 : Fin 3) * FreeAlgebra.ι k (0 : Fin 3)))
  | EF_comm : SmallQuantumRel n k q
      (FreeAlgebra.ι k (1 : Fin 3) * FreeAlgebra.ι k (2 : Fin 3) -
       FreeAlgebra.ι k (2 : Fin 3) * FreeAlgebra.ι k (1 : Fin 3))
      ((q - q⁻¹)⁻¹ • (FreeAlgebra.ι k (0 : Fin 3) -
       FreeAlgebra.ι k (0 : Fin 3) ^ (n - 1)))

/-- The small quantum `sl_2` algebra: the quotient of the free `k`-algebra on
three generators by the small quantum relations `SmallQuantumRel n k q`. -/
abbrev SmallQuantumSl2Alg (n : ℕ) (k : Type*) [Field k] (q : k) :=
  RingQuot (SmallQuantumRel n k q)

variable (n : ℕ) (k : Type*) [Field k] (q : k)

namespace SmallQuantumSl2Alg

/-- The canonical algebra projection from the free algebra to the small quantum algebra. -/
noncomputable abbrev π : FreeAlgebra k (Fin 3) →ₐ[k] SmallQuantumSl2Alg n k q :=
  RingQuot.mkAlgHom k _

/-- The generator `K` of the small quantum group `u_q(sl_2)`. -/
noncomputable def K : SmallQuantumSl2Alg n k q := π n k q (FreeAlgebra.ι k 0)

/-- The generator `E` of the small quantum group `u_q(sl_2)`. -/
noncomputable def E : SmallQuantumSl2Alg n k q := π n k q (FreeAlgebra.ι k 1)

/-- The generator `F` of the small quantum group `u_q(sl_2)`. -/
noncomputable def F : SmallQuantumSl2Alg n k q := π n k q (FreeAlgebra.ι k 2)

/-- The inverse `K⁻¹` of `K`, realized as `K^{n-1}` (using `K^n = 1`). -/
noncomputable def Kinv : SmallQuantumSl2Alg n k q := K n k q ^ (n - 1)

/-- The defining relation `K^n = 1` in `u_q(sl_2)`. -/
lemma K_pow_n_eq : (K n k q) ^ n = 1 := by
  unfold K; rw [← map_pow, ← map_one (π n k q)]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.K_pow_n

/-- The nilpotency relation `E^n = 0` in `u_q(sl_2)`. -/
lemma E_pow_n_eq : (E n k q) ^ n = 0 := by
  unfold E; rw [← map_pow, ← map_zero (π n k q)]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.E_pow_n

/-- The nilpotency relation `F^n = 0` in `u_q(sl_2)`. -/
lemma F_pow_n_eq : (F n k q) ^ n = 0 := by
  unfold F; rw [← map_pow, ← map_zero (π n k q)]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.F_pow_n

/-- The commutation relation `K E = q^2 (E K)` in `u_q(sl_2)`. -/
lemma K_mul_E_eq :
    K n k q * E n k q = q ^ 2 • (E n k q * K n k q) := by
  unfold K E
  conv_lhs => rw [← map_mul]
  conv_rhs => rw [← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.KE_comm

/-- The commutation relation `K F = q^{-2} (F K)` in `u_q(sl_2)`. -/
lemma K_mul_F_eq :
    K n k q * F n k q = (q ^ 2)⁻¹ • (F n k q * K n k q) := by
  unfold K F
  conv_lhs => rw [← map_mul]
  conv_rhs => rw [← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.KF_comm

/-- The commutator relation `[E, F] = (K - K^{-1})/(q - q^{-1})` in `u_q(sl_2)`,
written using `K^{n-1}` as the explicit inverse of `K`. -/
lemma E_mul_F_comm :
    E n k q * F n k q - F n k q * E n k q =
    (q - q⁻¹)⁻¹ • (K n k q - K n k q ^ (n - 1)) := by
  unfold K E F
  conv_lhs => rw [← map_mul, ← map_mul, ← map_sub]
  conv_rhs => rw [← map_pow, ← map_sub, ← map_smul]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.EF_comm

/-- `K · K^{-1} = 1` (right inverse property) when `1 ≤ n`. -/
lemma K_mul_Kinv (hn : 1 ≤ n) :
    K n k q * Kinv n k q = 1 := by
  unfold Kinv
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← pow_succ', h]
  exact K_pow_n_eq n k q

/-- `K^{-1} · K = 1` (left inverse property) when `1 ≤ n`. -/
lemma Kinv_mul_K (hn : 1 ≤ n) :
    Kinv n k q * K n k q = 1 := by
  unfold Kinv
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← pow_succ, h]
  exact K_pow_n_eq n k q

/-- Universal property of `SmallQuantumSl2Alg`: any choice of images `K', E', F'`
in a `k`-algebra `A` satisfying the small quantum relations extends uniquely to
a `k`-algebra homomorphism from `SmallQuantumSl2Alg n k q`. -/
noncomputable def lift {A : Type*} [Ring A] [Algebra k A]
    (K' E' F' : A)
    (hK : K' ^ n = 1)
    (hE : E' ^ n = 0)
    (hF : F' ^ n = 0)
    (hKE : K' * E' = q ^ 2 • (E' * K'))
    (hKF : K' * F' = (q ^ 2)⁻¹ • (F' * K'))
    (hEF : E' * F' - F' * E' = (q - q⁻¹)⁻¹ • (K' - K' ^ (n - 1))) :
    SmallQuantumSl2Alg n k q →ₐ[k] A :=
  (RingQuot.liftAlgHom k).toFun
    ⟨FreeAlgebra.lift k (fun i => match i with | 0 => K' | 1 => E' | 2 => F'), by
      intro a b hab
      cases hab with
      | K_pow_n =>
        simp [map_pow, map_one, FreeAlgebra.lift_ι_apply, hK]
      | E_pow_n =>
        simp [map_pow, map_zero, FreeAlgebra.lift_ι_apply, hE]
      | F_pow_n =>
        simp [map_pow, map_zero, FreeAlgebra.lift_ι_apply, hF]
      | KE_comm =>
        simp [map_mul, map_smul, FreeAlgebra.lift_ι_apply, hKE]
      | KF_comm =>
        simp [map_mul, map_smul, FreeAlgebra.lift_ι_apply, hKF]
      | EF_comm =>
        simp [map_mul, map_sub, map_smul, map_pow, FreeAlgebra.lift_ι_apply, hEF]⟩

end SmallQuantumSl2Alg


open Coalgebra HopfAlgebra
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000

/-- A bundle of data witnessing that `SmallQuantumSl2Alg n k q` carries a
bialgebra/Hopf-algebra structure with prescribed values of the comultiplication,
counit, and antipode on the generators `K, E, F`, together with the coherence axioms. -/
class SmallQuantumSl2HopfData (n : ℕ) (k : Type*) [Field k] (q : k) where
  comulHom : SmallQuantumSl2Alg n k q →ₐ[k]
    SmallQuantumSl2Alg n k q ⊗[k] SmallQuantumSl2Alg n k q
  counitHom : SmallQuantumSl2Alg n k q →ₐ[k] k
  antipodeLin : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q
  comulHom_K : comulHom (SmallQuantumSl2Alg.K n k q) =
    SmallQuantumSl2Alg.K n k q ⊗ₜ[k] SmallQuantumSl2Alg.K n k q
  comulHom_E : comulHom (SmallQuantumSl2Alg.E n k q) =
    SmallQuantumSl2Alg.E n k q ⊗ₜ[k] SmallQuantumSl2Alg.K n k q +
    1 ⊗ₜ[k] SmallQuantumSl2Alg.E n k q
  comulHom_F : comulHom (SmallQuantumSl2Alg.F n k q) =
    SmallQuantumSl2Alg.F n k q ⊗ₜ[k] 1 +
    SmallQuantumSl2Alg.Kinv n k q ⊗ₜ[k] SmallQuantumSl2Alg.F n k q
  counitHom_K : counitHom (SmallQuantumSl2Alg.K n k q) = 1
  counitHom_E : counitHom (SmallQuantumSl2Alg.E n k q) = 0
  counitHom_F : counitHom (SmallQuantumSl2Alg.F n k q) = 0
  antipodeLin_K : antipodeLin (SmallQuantumSl2Alg.K n k q) =
    SmallQuantumSl2Alg.Kinv n k q
  antipodeLin_E : antipodeLin (SmallQuantumSl2Alg.E n k q) =
    -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q)
  antipodeLin_F : antipodeLin (SmallQuantumSl2Alg.F n k q) =
    -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q)
  coassoc_axiom :
    (Algebra.TensorProduct.assoc k k k
      (SmallQuantumSl2Alg n k q) (SmallQuantumSl2Alg n k q)
      (SmallQuantumSl2Alg n k q)).toAlgHom.comp
      ((Algebra.TensorProduct.map comulHom (AlgHom.id k _)).comp comulHom) =
    (Algebra.TensorProduct.map (AlgHom.id k _) comulHom).comp comulHom
  rTensor_counit_axiom :
    (Algebra.TensorProduct.map counitHom (AlgHom.id k _)).comp comulHom =
    (Algebra.TensorProduct.lid k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  lTensor_counit_axiom :
    (Algebra.TensorProduct.map (AlgHom.id k _) counitHom).comp comulHom =
    (Algebra.TensorProduct.rid k k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  mul_antipode_rTensor_axiom : LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
    LinearMap.rTensor _ antipodeLin ∘ₗ comulHom.toLinearMap =
    Algebra.linearMap k _ ∘ₗ counitHom.toLinearMap
  mul_antipode_lTensor_axiom : LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
    LinearMap.lTensor _ antipodeLin ∘ₗ comulHom.toLinearMap =
    Algebra.linearMap k _ ∘ₗ counitHom.toLinearMap

namespace SmallQuantumSl2Alg

variable {n : ℕ} {k : Type*} [Field k] {q : k}

/-- Given `SmallQuantumSl2HopfData`, the small quantum algebra becomes a `k`-bialgebra. -/
noncomputable instance instBialgebra [hd : SmallQuantumSl2HopfData n k q] :
    Bialgebra k (SmallQuantumSl2Alg n k q) :=
  Bialgebra.ofAlgHom hd.comulHom hd.counitHom
    hd.coassoc_axiom hd.rTensor_counit_axiom hd.lTensor_counit_axiom

/-- Given `SmallQuantumSl2HopfData`, the small quantum algebra becomes a `k`-Hopf algebra. -/
noncomputable instance instHopfAlgebra [hd : SmallQuantumSl2HopfData n k q] :
    HopfAlgebra k (SmallQuantumSl2Alg n k q) := by
  letI : HopfAlgebraStruct k (SmallQuantumSl2Alg n k q) := ⟨hd.antipodeLin⟩
  exact HopfAlgebra.mk hd.mul_antipode_rTensor_axiom hd.mul_antipode_lTensor_axiom

/-- The bialgebra `comul` agrees with the comultiplication supplied in `hd`. -/
lemma comul_eq [hd : SmallQuantumSl2HopfData n k q] (x : SmallQuantumSl2Alg n k q) :
    comul (R := k) x = hd.comulHom x := rfl

/-- The bialgebra `counit` agrees with the counit supplied in `hd`. -/
lemma counit_eq [hd : SmallQuantumSl2HopfData n k q] (x : SmallQuantumSl2Alg n k q) :
    counit (R := k) x = hd.counitHom x := rfl

/-- The Hopf algebra `antipode` agrees with the antipode supplied in `hd`. -/
lemma antipode_eq [hd : SmallQuantumSl2HopfData n k q] (x : SmallQuantumSl2Alg n k q) :
    antipode k x = hd.antipodeLin x := rfl

/-- Given Hopf data and `n ≥ 2`, `q ≠ 0`, `q^2 ≠ 1`, the small quantum algebra
`SmallQuantumSl2Alg n k q` is a `QuantumSl2`. -/
noncomputable instance instQuantumSl2
    [hd : SmallQuantumSl2HopfData n k q]
    (hn : 2 ≤ n) (hq : q ≠ 0) (hq2 : q ^ 2 ≠ 1) :
    QuantumSl2 k (SmallQuantumSl2Alg n k q) where
  q := q
  hq_ne_zero := hq
  hq_sq_ne_one := hq2
  K := K n k q
  Kinv := Kinv n k q
  E := E n k q
  F := F n k q
  K_mul_Kinv := K_mul_Kinv n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
  Kinv_mul_K := Kinv_mul_K n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
  K_E_Kinv := by

    have hKE := K_mul_E_eq n k q
    have hKKinv := K_mul_Kinv n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
    rw [hKE, smul_mul_assoc, mul_assoc, hKKinv, mul_one]
  K_F_Kinv := by

    have hKF := K_mul_F_eq n k q
    have hKKinv := K_mul_Kinv n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
    rw [hKF, smul_mul_assoc, mul_assoc, hKKinv, mul_one]
  EF_comm := E_mul_F_comm n k q
  comul_K := by rw [comul_eq]; exact hd.comulHom_K
  comul_E := by rw [comul_eq]; exact hd.comulHom_E
  comul_F := by rw [comul_eq]; exact hd.comulHom_F
  counit_K := by rw [counit_eq]; exact hd.counitHom_K
  counit_E := by rw [counit_eq]; exact hd.counitHom_E
  counit_F := by rw [counit_eq]; exact hd.counitHom_F
  antipode_K := by rw [antipode_eq]; exact hd.antipodeLin_K
  antipode_E := by rw [antipode_eq]; exact hd.antipodeLin_E
  antipode_F := by rw [antipode_eq]; exact hd.antipodeLin_F

end SmallQuantumSl2Alg
