/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.QuantumSl2Concrete
import Atlas.TensorCategories.code.QBinomial

open Coalgebra HopfAlgebra
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000

namespace SmallQuantumSl2Instance

variable (n : ℕ) (k : Type*) [Field k] (q : k)

local notation "A" => SmallQuantumSl2Alg n k q
local notation "KK" => SmallQuantumSl2Alg.K n k q
local notation "EE" => SmallQuantumSl2Alg.E n k q
local notation "FF" => SmallQuantumSl2Alg.F n k q
local notation "Kinv" => SmallQuantumSl2Alg.Kinv n k q

/-- Standing hypotheses needed to construct the Hopf algebra structure on the small
quantum group `u_q(sl_2)`: `n ≥ 2`, `q` is a primitive `n`-th root of unity, and so is `q^2`. -/
class QuantumSl2Hypotheses (n : ℕ) (k : Type*) [Field k] (q : k) : Prop where
  hn : 2 ≤ n
  hq_prim : IsPrimitiveRoot q n
  hq2_prim : IsPrimitiveRoot (q ^ 2) n

variable [hyp : QuantumSl2Hypotheses n k q]
include hyp

/-- A primitive `n`-th root of unity (`n ≥ 2`) is nonzero. -/
lemma q_ne_zero : q ≠ 0 := by
  intro h
  have hpow := hyp.hq_prim.pow_eq_one
  have hn := hyp.hn
  rw [h, zero_pow (by omega : n ≠ 0)] at hpow
  exact zero_ne_one hpow

/-- The relation `(q^2)^n = 1`, from primitivity of `q^2`. -/
lemma q2_pow_n : (q ^ 2) ^ n = 1 := hyp.hq2_prim.pow_eq_one

/-- From `n ≥ 2`, `1 < n`. -/
lemma one_lt_n : 1 < n := by have := hyp.hn; omega

/-- From `n ≥ 2`, `1 ≤ n`. -/
lemma one_le_n : 1 ≤ n := by have := hyp.hn; omega

/-- From `n ≥ 2`, `n ≠ 0`. -/
lemma n_ne_zero : n ≠ 0 := by have := hyp.hn; omega

/-- The candidate comultiplication of `K`: `K ⊗ K`. -/
noncomputable def DeltaK : A ⊗[k] A := KK ⊗ₜ[k] KK

/-- The candidate comultiplication of `E`: `E ⊗ K + 1 ⊗ E`. -/
noncomputable def DeltaE : A ⊗[k] A := EE ⊗ₜ[k] KK + 1 ⊗ₜ[k] EE

/-- The candidate comultiplication of `F`: `F ⊗ 1 + K^{-1} ⊗ F`. -/
noncomputable def DeltaF : A ⊗[k] A := FF ⊗ₜ[k] 1 + Kinv ⊗ₜ[k] FF

omit hyp in
/-- Verification: `(K ⊗ K)^n = 1` follows from `K^n = 1`. -/
lemma DeltaK_pow_n : DeltaK n k q ^ n = 1 := by
  unfold DeltaK
  rw [Algebra.TensorProduct.tmul_pow, SmallQuantumSl2Alg.K_pow_n_eq]
  exact Algebra.TensorProduct.one_def.symm

/-- Verification: `(DeltaE)^n = 0` follows from `E^n = 0` and the q-binomial identity. -/
lemma DeltaE_pow_n : DeltaE n k q ^ n = 0 := by
  unfold DeltaE
  set a := EE ⊗ₜ[k] KK
  set b := (1 : A) ⊗ₜ[k] EE
  have ha_pow : a ^ n = 0 := by
    simp only [a, Algebra.TensorProduct.tmul_pow, SmallQuantumSl2Alg.E_pow_n_eq]
    exact TensorProduct.zero_tmul _ _
  have hb_pow : b ^ n = 0 := by
    simp only [b, Algebra.TensorProduct.tmul_pow, SmallQuantumSl2Alg.E_pow_n_eq]
    rw [one_pow]
    exact TensorProduct.tmul_zero _ _
  have hcomm : b * a = algebraMap k (A ⊗[k] A) (q ^ 2)⁻¹ * (a * b) := by
    simp only [a, b, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [SmallQuantumSl2Alg.K_mul_E_eq]
    rw [TensorProduct.tmul_smul]
    rw [Algebra.algebraMap_eq_smul_one (R := k)]
    rw [smul_mul_assoc, one_mul, smul_smul, inv_mul_cancel₀, one_smul]
    exact pow_ne_zero 2 (q_ne_zero n k q)
  have hq_inv : IsPrimitiveRoot (q ^ 2)⁻¹ n := hyp.hq2_prim.inv
  have := q_comm_power (k := k) (q ^ 2)⁻¹ n (one_lt_n n k q) hq_inv a b hcomm
  rw [ha_pow, hb_pow, add_zero] at this
  exact this

omit hyp in
/-- Iterated commutation: `K^j · F = q^{-2j} · (F · K^j)`. -/
lemma K_pow_mul_F (j : ℕ) : KK ^ j * FF = ((q ^ 2)⁻¹) ^ j • (FF * KK ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hKF := SmallQuantumSl2Alg.K_mul_F_eq n k q


    conv_lhs => rw [pow_succ]
    rw [mul_assoc, hKF, mul_smul_comm, ← mul_assoc, ih,
        smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ]
    congr 1
    exact (pow_succ' ((q ^ 2)⁻¹) j).symm

/-- Identity at a root of unity: `((q^2)⁻¹)^{n-1} = q^2`. -/
lemma inv_q2_pow_pred : ((q ^ 2)⁻¹) ^ (n - 1) = q ^ 2 := by
  rw [inv_pow]
  have hq2n := q2_pow_n n k q
  have h1 : (q ^ 2) * (q ^ 2) ^ (n - 1) = 1 := by
    rw [← pow_succ']
    have : n - 1 + 1 = n := Nat.sub_add_cancel (one_le_n n k q)
    rw [this]
    exact hq2n
  have h2 : (q ^ 2) ^ (n - 1) = (q ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right h1
  rw [h2, inv_inv]

/-- `K^{-1} · F = q^2 · (F · K^{-1})`. -/
lemma Kinv_mul_F : Kinv * FF = (q ^ 2) • (FF * Kinv) := by
  unfold SmallQuantumSl2Alg.Kinv
  have h := K_pow_mul_F n k q (n - 1)
  rw [inv_q2_pow_pred n k q] at h
  exact h

/-- Verification: `(DeltaF)^n = 0` follows from `F^n = 0` and the q-binomial identity. -/
lemma DeltaF_pow_n : DeltaF n k q ^ n = 0 := by
  unfold DeltaF
  set a := FF ⊗ₜ[k] (1 : A)
  set b := Kinv ⊗ₜ[k] FF
  have ha_pow : a ^ n = 0 := by
    simp only [a, Algebra.TensorProduct.tmul_pow, SmallQuantumSl2Alg.F_pow_n_eq]
    exact TensorProduct.zero_tmul _ _
  have hb_pow : b ^ n = 0 := by
    simp only [b, Algebra.TensorProduct.tmul_pow, SmallQuantumSl2Alg.F_pow_n_eq]
    exact TensorProduct.tmul_zero _ _
  have hcomm : b * a = algebraMap k (A ⊗[k] A) (q ^ 2) * (a * b) := by
    simp only [a, b, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Kinv_mul_F n k q, ← TensorProduct.smul_tmul',
        Algebra.algebraMap_eq_smul_one (R := k), smul_mul_assoc, one_mul]
  have hq2 : IsPrimitiveRoot (q ^ 2) n := hyp.hq2_prim
  have := q_comm_power (k := k) (q ^ 2) n (one_lt_n n k q) hq2 a b hcomm
  rw [ha_pow, hb_pow, add_zero] at this
  exact this

omit hyp in
/-- Verification: `DeltaK · DeltaE = q^2 · (DeltaE · DeltaK)`. -/
lemma DeltaKE_comm :
    DeltaK n k q * DeltaE n k q = q ^ 2 • (DeltaE n k q * DeltaK n k q) := by
  unfold DeltaK DeltaE
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [SmallQuantumSl2Alg.K_mul_E_eq, smul_add]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- Verification: `DeltaK · DeltaF = q^{-2} · (DeltaF · DeltaK)`. -/
lemma DeltaKF_comm :
    DeltaK n k q * DeltaF n k q = (q ^ 2)⁻¹ • (DeltaF n k q * DeltaK n k q) := by
  unfold DeltaK DeltaF
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [SmallQuantumSl2Alg.K_mul_F_eq,
      SmallQuantumSl2Alg.K_mul_Kinv n k q (one_le_n n k q),
      SmallQuantumSl2Alg.Kinv_mul_K n k q (one_le_n n k q)]
  rw [smul_add]
  simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


omit hyp in
/-- Iterated commutation: `K^j · E = q^{2j} · (E · K^j)`. -/
lemma K_pow_mul_E (j : ℕ) : KK ^ j * EE = (q ^ 2) ^ j • (EE * KK ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hKE := SmallQuantumSl2Alg.K_mul_E_eq n k q
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, hKE, mul_smul_comm, ← mul_assoc, ih,
        smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ]
    congr 1
    exact (pow_succ' (q ^ 2) j).symm

/-- Iterated commutation: `E · K^j = q^{-2j} · (K^j · E)`. -/
lemma E_mul_K_pow (j : ℕ) : EE * KK ^ j = ((q ^ 2)⁻¹) ^ j • (KK ^ j * EE) := by
  have h := K_pow_mul_E n k q j
  rw [h, smul_smul]
  have : ((q ^ 2)⁻¹) ^ j * (q ^ 2) ^ j = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (pow_ne_zero 2 (q_ne_zero n k q)), one_pow]
  rw [this, one_smul]

/-- Commutation: `E · K^{-1} = q^2 · (K^{-1} · E)`. -/
lemma E_mul_Kinv : EE * Kinv = (q ^ 2) • (Kinv * EE) := by
  unfold SmallQuantumSl2Alg.Kinv
  rw [E_mul_K_pow n k q (n - 1), inv_q2_pow_pred n k q]

/-- Cross term identity used in the verification of the comultiplication EF relation. -/
lemma cross_term_eq :
    (EE * Kinv) ⊗ₜ[k] (KK * FF) = (Kinv * EE) ⊗ₜ[k] (FF * KK) := by
  rw [E_mul_Kinv n k q, SmallQuantumSl2Alg.K_mul_F_eq n k q]
  rw [← TensorProduct.smul_tmul]
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (q_ne_zero n k q)), one_smul]

omit hyp in
/-- `DeltaK^{n-1} = K^{-1} ⊗ K^{-1}` (using `K^n = 1`). -/
lemma DeltaK_pow_pred :
    DeltaK n k q ^ (n - 1) = Kinv ⊗ₜ[k] Kinv := by
  unfold DeltaK SmallQuantumSl2Alg.Kinv
  rw [Algebra.TensorProduct.tmul_pow]

/-- Verification of the EF commutator for the candidate comultiplications:
`[DeltaE, DeltaF] = (q - q^{-1})^{-1}(DeltaK - DeltaK^{n-1})`. -/
lemma DeltaEF_comm :
    DeltaE n k q * DeltaF n k q - DeltaF n k q * DeltaE n k q =
    (q - q⁻¹)⁻¹ • (DeltaK n k q - DeltaK n k q ^ (n - 1)) := by


  have hEF := SmallQuantumSl2Alg.E_mul_F_comm n k q
  set c := (q - q⁻¹)⁻¹ with hc_def
  have hEF' : EE * FF = FF * EE + c • (KK - Kinv) := by
    have h := hEF
    unfold SmallQuantumSl2Alg.Kinv at h ⊢
    rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  rw [DeltaK_pow_pred n k q]
  unfold DeltaE DeltaF DeltaK
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

  have hcross := cross_term_eq n k q
  rw [hcross]

  rw [hEF']

  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
             TensorProduct.smul_tmul', TensorProduct.tmul_smul,
             smul_sub, TensorProduct.sub_tmul, TensorProduct.tmul_sub]

  abel


/-- The candidate comultiplication on `SmallQuantumSl2Alg`, obtained by lifting
the prescribed values `DeltaK, DeltaE, DeltaF` through the universal property. -/
noncomputable def comulHomAux :
    A →ₐ[k] A ⊗[k] A :=
  SmallQuantumSl2Alg.lift n k q
    (DeltaK n k q) (DeltaE n k q) (DeltaF n k q)
    (DeltaK_pow_n n k q) (DeltaE_pow_n n k q) (DeltaF_pow_n n k q)
    (DeltaKE_comm n k q) (DeltaKF_comm n k q)
    (DeltaEF_comm n k q)

/-- The candidate counit on `SmallQuantumSl2Alg`: `K ↦ 1`, `E ↦ 0`, `F ↦ 0`. -/
noncomputable def counitHomAux : A →ₐ[k] k :=
  SmallQuantumSl2Alg.lift n k q (1 : k) (0 : k) (0 : k)
    (by simp)
    (by simp [n_ne_zero n k q])
    (by simp [n_ne_zero n k q])
    (by simp) (by simp) (by simp)

/-- Auxiliary structural axioms packaging the existence of an antipode and the
coassociativity / counitality / Hopf-algebra axioms for the candidate `comulHomAux`,
`counitHomAux` on the small quantum group. -/
class QuantumSl2StructuralAxioms (n : ℕ) (k : Type*) [Field k] (q : k)
    [QuantumSl2Hypotheses n k q] : Prop where
  antipode_exists :
    ∃ (S : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q),
      S (SmallQuantumSl2Alg.K n k q) = SmallQuantumSl2Alg.Kinv n k q ∧
      S (SmallQuantumSl2Alg.E n k q) =
        -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q) ∧
      S (SmallQuantumSl2Alg.F n k q) =
        -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q)
  coassoc :
    (Algebra.TensorProduct.assoc k k k
      (SmallQuantumSl2Alg n k q) (SmallQuantumSl2Alg n k q)
      (SmallQuantumSl2Alg n k q)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulHomAux n k q) (AlgHom.id k _)).comp
        (comulHomAux n k q)) =
    (Algebra.TensorProduct.map (AlgHom.id k _) (comulHomAux n k q)).comp
      (comulHomAux n k q)
  rTensor_counit :
    (Algebra.TensorProduct.map (counitHomAux n k q) (AlgHom.id k _)).comp
      (comulHomAux n k q) =
    (Algebra.TensorProduct.lid k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id k _) (counitHomAux n k q)).comp
      (comulHomAux n k q) =
    (Algebra.TensorProduct.rid k k (SmallQuantumSl2Alg n k q)).symm.toAlgHom
  hopf_right :
    ∀ (S : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q),
      S (SmallQuantumSl2Alg.K n k q) = SmallQuantumSl2Alg.Kinv n k q →
      S (SmallQuantumSl2Alg.E n k q) =
        -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q) →
      S (SmallQuantumSl2Alg.F n k q) =
        -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q) →
      LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
        LinearMap.rTensor _ S ∘ₗ (comulHomAux n k q).toLinearMap =
      Algebra.linearMap k _ ∘ₗ (counitHomAux n k q).toLinearMap
  hopf_left :
    ∀ (S : SmallQuantumSl2Alg n k q →ₗ[k] SmallQuantumSl2Alg n k q),
      S (SmallQuantumSl2Alg.K n k q) = SmallQuantumSl2Alg.Kinv n k q →
      S (SmallQuantumSl2Alg.E n k q) =
        -(SmallQuantumSl2Alg.E n k q * SmallQuantumSl2Alg.Kinv n k q) →
      S (SmallQuantumSl2Alg.F n k q) =
        -(SmallQuantumSl2Alg.K n k q * SmallQuantumSl2Alg.F n k q) →
      LinearMap.mul' k (SmallQuantumSl2Alg n k q) ∘ₗ
        LinearMap.lTensor _ S ∘ₗ (comulHomAux n k q).toLinearMap =
      Algebra.linearMap k _ ∘ₗ (counitHomAux n k q).toLinearMap

variable [QuantumSl2StructuralAxioms n k q]

/-- A linear antipode for the small quantum group, extracted from the
structural axioms `QuantumSl2StructuralAxioms`. -/
noncomputable def antipodeLinAux : A →ₗ[k] A :=
  (QuantumSl2StructuralAxioms.antipode_exists (n := n) (k := k) (q := q)).choose

/-- The antipode satisfies `S(K) = K^{-1}`. -/
lemma antipodeLinAux_K :
    antipodeLinAux n k q KK = Kinv :=
  (QuantumSl2StructuralAxioms.antipode_exists
    (n := n) (k := k) (q := q)).choose_spec.1

/-- The antipode satisfies `S(E) = -E · K^{-1}`. -/
lemma antipodeLinAux_E :
    antipodeLinAux n k q EE = -(EE * Kinv) :=
  (QuantumSl2StructuralAxioms.antipode_exists
    (n := n) (k := k) (q := q)).choose_spec.2.1

/-- The antipode satisfies `S(F) = -K · F`. -/
lemma antipodeLinAux_F :
    antipodeLinAux n k q FF = -(KK * FF) :=
  (QuantumSl2StructuralAxioms.antipode_exists
    (n := n) (k := k) (q := q)).choose_spec.2.2

omit [QuantumSl2StructuralAxioms n k q] in
/-- `comulHomAux(K) = K ⊗ K`. -/
lemma comulHomAux_K :
    comulHomAux n k q KK = KK ⊗ₜ[k] KK := by
  unfold comulHomAux SmallQuantumSl2Alg.K SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π DeltaK
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  dsimp only []
  rfl

omit [QuantumSl2StructuralAxioms n k q] in
/-- `comulHomAux(E) = E ⊗ K + 1 ⊗ E`. -/
lemma comulHomAux_E :
    comulHomAux n k q EE = EE ⊗ₜ[k] KK + 1 ⊗ₜ[k] EE := by
  unfold comulHomAux SmallQuantumSl2Alg.E SmallQuantumSl2Alg.K SmallQuantumSl2Alg.lift
    SmallQuantumSl2Alg.π DeltaE
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  dsimp only []
  rfl

omit [QuantumSl2StructuralAxioms n k q] in
/-- `comulHomAux(F) = F ⊗ 1 + K^{-1} ⊗ F`. -/
lemma comulHomAux_F :
    comulHomAux n k q FF = FF ⊗ₜ[k] 1 + Kinv ⊗ₜ[k] FF := by
  unfold comulHomAux SmallQuantumSl2Alg.F SmallQuantumSl2Alg.Kinv SmallQuantumSl2Alg.lift
    SmallQuantumSl2Alg.π DeltaF
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]
  dsimp only []
  rfl

omit [QuantumSl2StructuralAxioms n k q] in
/-- `counitHomAux(K) = 1`. -/
lemma counitHomAux_K :
    counitHomAux n k q KK = 1 := by
  unfold counitHomAux SmallQuantumSl2Alg.K SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

omit [QuantumSl2StructuralAxioms n k q] in
/-- `counitHomAux(E) = 0`. -/
lemma counitHomAux_E :
    counitHomAux n k q EE = 0 := by
  unfold counitHomAux SmallQuantumSl2Alg.E SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

omit [QuantumSl2StructuralAxioms n k q] in
/-- `counitHomAux(F) = 0`. -/
lemma counitHomAux_F :
    counitHomAux n k q FF = 0 := by
  unfold counitHomAux SmallQuantumSl2Alg.F SmallQuantumSl2Alg.lift SmallQuantumSl2Alg.π
  erw [RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply]

/-- Assembles the candidate comultiplication, counit, and antipode together with the
structural axioms into a `SmallQuantumSl2HopfData` instance. -/
noncomputable instance instSmallQuantumSl2HopfData :
    SmallQuantumSl2HopfData n k q where
  comulHom := comulHomAux n k q
  counitHom := counitHomAux n k q
  antipodeLin := antipodeLinAux n k q
  comulHom_K := comulHomAux_K n k q
  comulHom_E := comulHomAux_E n k q
  comulHom_F := comulHomAux_F n k q
  counitHom_K := counitHomAux_K n k q
  counitHom_E := counitHomAux_E n k q
  counitHom_F := counitHomAux_F n k q
  antipodeLin_K := antipodeLinAux_K n k q
  antipodeLin_E := antipodeLinAux_E n k q
  antipodeLin_F := antipodeLinAux_F n k q
  coassoc_axiom := QuantumSl2StructuralAxioms.coassoc
  rTensor_counit_axiom := QuantumSl2StructuralAxioms.rTensor_counit
  lTensor_counit_axiom := QuantumSl2StructuralAxioms.lTensor_counit
  mul_antipode_rTensor_axiom :=
    QuantumSl2StructuralAxioms.hopf_right
      (antipodeLinAux n k q)
      (antipodeLinAux_K n k q)
      (antipodeLinAux_E n k q)
      (antipodeLinAux_F n k q)
  mul_antipode_lTensor_axiom :=
    QuantumSl2StructuralAxioms.hopf_left
      (antipodeLinAux n k q)
      (antipodeLinAux_K n k q)
      (antipodeLinAux_E n k q)
      (antipodeLinAux_F n k q)


end SmallQuantumSl2Instance
