/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped LinearAlgebra.Projectivization
open ExteriorAlgebra

namespace GrassmannianProjective

/-- Any order embedding `Fin n ↪o Fin n` is the identity, since a strictly increasing bijection
on `Fin n` must be the identity. -/
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

variable {K : Type*} [Field K]

/-- The exterior power of a basis is nonzero: `e_1 ∧ ... ∧ e_n ≠ 0`. -/
lemma ιMulti_basis_ne_zero {n : ℕ} {W : Type*} [AddCommGroup W] [Module K W]
    (b : Module.Basis (Fin n) K W) :
    (exteriorPower.ιMulti K n (fun i => b i)) ≠ 0 := by
  intro h
  set s : Set.powersetCard (Fin n) n := ⟨Finset.univ, Finset.card_fin n⟩
  have hdiag := exteriorPower.ιMultiDual_apply_diag K n b s
  have key : exteriorPower.ιMulti_family K n (⇑b) s =
      exteriorPower.ιMulti K n (fun i => b i) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1; funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1; exact orderEmb_fin_eq_id n (Set.powersetCard.ofFinEmbEquiv.symm s) i
  rw [key] at hdiag
  rw [show exteriorPower.ιMulti K n (fun i => b i) = (0 : ↥(⋀[K]^n W)) from
    Subtype.val_injective (by simp [h]), map_zero] at hdiag
  exact zero_ne_one hdiag

section GrassmannianDef

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

/-- The Grassmannian `Gr(k, V)` as a set of `k`-dimensional subspaces of `V`. -/
def SubspaceGr (k : ℕ) := {W : Submodule K V // Module.finrank K W = k}

end GrassmannianDef

section PluckerEmbedding

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- Choose a basis `Fin k → W` for a `k`-dimensional subspace `W` of `V`. -/
noncomputable def subspaceBasis (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) : Module.Basis (Fin k) K W :=
  (Module.finBasis K W).reindex (Fin.castOrderIso hk).toEquiv

/-- Plücker coordinate of `W`: the image of `e_1 ∧ ... ∧ e_k` in `⋀^k V` under the inclusion. -/
noncomputable def pluckerCoord (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) : ↥(⋀[K]^k V) :=
  let b := subspaceBasis K V k W hk
  exteriorPower.map k W.subtype (exteriorPower.ιMulti K k (fun i => b i))

omit [Module.Free K V] in
/-- The Plücker coordinate of a `k`-dimensional subspace is nonzero, so it defines a point in `P(⋀^k V)`. -/
theorem plucker_coord_ne_zero (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) :
    pluckerCoord K V k W hk ≠ 0 := by
  unfold pluckerCoord
  intro h

  obtain ⟨Q, hQ⟩ := W.exists_isCompl
  have hinj := exteriorPower.map_injective
    (Submodule.linearProjOfIsCompl W Q hQ)
    (Submodule.linearProjOfIsCompl_comp_subtype hQ) (n := k)

  have hne : (exteriorPower.ιMulti K k
      (fun i => (subspaceBasis K V k W hk) i)) ≠ 0 :=
    ιMulti_basis_ne_zero (subspaceBasis K V k W hk)
  exact hne (hinj (by rwa [map_zero]))

/-- Plücker map `Gr(k, V) → P(⋀^k V)` sending `W` to the projective class of `e_1 ∧ ... ∧ e_k`. -/
noncomputable def pluckerMap (k : ℕ) : SubspaceGr K V k → ℙ K (⋀[K]^k V) :=
  fun ⟨W, hk⟩ => Projectivization.mk K (pluckerCoord K V k W hk) (plucker_coord_ne_zero K V k W hk)

/-- A `k`-vector `ω ∈ ⋀^k V` is decomposable if it can be written as a wedge `v_1 ∧ ... ∧ v_k`. -/
def IsDecomposableExtPower (k : ℕ) (ω : ⋀[K]^k V) : Prop :=
  ∃ (v : Fin k → V), ω = exteriorPower.ιMulti K k v

/-- The locus of decomposable classes in `P(⋀^k V)`, i.e. the image of the Plücker map. -/
def DecomposableProjective (k : ℕ) : Set (ℙ K (⋀[K]^k V)) :=
  {p | ∃ (v : Fin k → V) (hv : exteriorPower.ιMulti K k v ≠ 0),
    p = Projectivization.mk K (exteriorPower.ιMulti K k v) hv}




/-- Ambient projective dimension: `dim ⋀^k V = C(n, k)` where `n = dim V`. -/
theorem plucker_ambient_dim (k : ℕ) :
    Module.finrank K (⋀[K]^k V) = Nat.choose (Module.finrank K V) k := by
  rw [exteriorPower.finrank_eq]

/-- Specialization of `plucker_ambient_dim` to a given ambient dimension `n`. -/
theorem plucker_target_finrank (k n : ℕ) (hdim : Module.finrank K V = n) :
    Module.finrank K (⋀[K]^k V) = Nat.choose n k := by
  rw [exteriorPower.finrank_eq, hdim]

/-- A subset of `P(⋀^k V)` is Zariski closed by quadratics if it is the zero locus of
homogeneous degree-2 polynomial functions (the Plücker relations). -/
def IsZariskiClosedByQuadratics (k : ℕ) (S : Set (ℙ K (⋀[K]^k V))) : Prop :=
  ∃ (ι : Type) (polys : ι → (⋀[K]^k V) → K),
    (∀ i, ∀ (c : K) (v : ⋀[K]^k V), polys i (c • v) = c ^ 2 * polys i v) ∧
    S = {p : ℙ K (⋀[K]^k V) | ∃ (v : ⋀[K]^k V) (hv : v ≠ 0),
      p = Projectivization.mk K v hv ∧ ∀ i, polys i v = 0}


end PluckerEmbedding

section PluckerRelation

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M] [Module K M]

/-- A degree-2 element of the exterior algebra is decomposable if it equals a single wedge `v₁ ∧ v₂`. -/
def IsDecomposableDeg2 (ω : ExteriorAlgebra K M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι K v₁ * ι K v₂

/-- Anti-commutativity of the embedding `ι : M → ΛM`: `ι x ∧ ι y = -(ι y ∧ ι x)`. -/
theorem ι_anticomm_ext (x y : M) :
    (ι K (M := M)) x * (ι K) y = -((ι K) y * (ι K (M := M)) x) := by
  have h := @ι_add_mul_swap K _ M _ _ y x
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A pure wedge squares to zero: `(v₁ ∧ v₂)^2 = 0` in the exterior algebra. -/
theorem wedge_sq_zero_decomp (v₁ v₂ : M) :
    (ι K v₁ * ι K v₂) * (ι K v₁ * ι K v₂) = (0 : ExteriorAlgebra K M) := by
  have anticomm : ι K v₂ * ι K v₁ = -((ι K (M := M)) v₁ * ι K v₂) := by
    have h := @ι_add_mul_swap K _ M _ _ v₁ v₂
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [mul_assoc, ← mul_assoc (ι K v₂) (ι K v₁) (ι K v₂)]
  rw [anticomm]
  rw [neg_mul, mul_neg, mul_assoc, ← mul_assoc (ι K v₁) (ι K v₁)]
  rw [ι_sq_zero, zero_mul, neg_zero]

/-- Decomposable degree-2 elements square to zero (necessary condition for the Plücker relation). -/
theorem wedge_sq_zero_of_isDecomposableDeg2 {ω : ExteriorAlgebra K M}
    (h : IsDecomposableDeg2 ω) : ω * ω = 0 := by
  obtain ⟨v₁, v₂, rfl⟩ := h
  exact wedge_sq_zero_decomp v₁ v₂

end PluckerRelation

section GradedCommutativity

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M] [Module K M]

/-- Two degree-2 wedges commute in the exterior algebra (graded commutativity, even × even). -/
theorem ι_pair_comm_deg2 (a b c d : M) :
    (ι K a * ι K b) * (ι K c * ι K d) =
    (ι K c * ι K d) * ((ι K (M := M)) a * ι K b) := by
  have hAC := ι_anticomm_ext (K := K) a c
  have hBC := ι_anticomm_ext (K := K) b c
  have hBD := ι_anticomm_ext (K := K) b d
  have hAD := ι_anticomm_ext (K := K) a d
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

/-- For `ω = v₁ ∧ v₂ + v₃ ∧ v₄`, the square `ω ∧ ω` equals `2 (v₁ ∧ v₂ ∧ v₃ ∧ v₄)`. -/
theorem wedge_sq_sum_decomp_pair (v₁ v₂ v₃ v₄ : M) :
    (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄) * (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄)
    = 2 * ((ι K (M := M)) v₁ * ι K v₂ * (ι K v₃ * ι K v₄)) := by
  rw [add_mul, mul_add, mul_add]
  rw [wedge_sq_zero_decomp v₁ v₂, wedge_sq_zero_decomp v₃ v₄]
  rw [zero_add, add_zero]
  rw [ι_pair_comm_deg2 v₁ v₂ v₃ v₄]
  rw [two_mul]

end GradedCommutativity

section Lemma6Converse

variable {K : Type*} [Field K]


/-- Iterated product of four `ι`'s coincides with `ιMulti K 4` applied to a 4-tuple. -/
theorem product_eq_ιMulti {V : Type*} [AddCommGroup V] [Module K V]
    (v₁ v₂ v₃ v₄ : V) :
    ι K v₁ * ι K v₂ * (ι K v₃ * ι K v₄) = ιMulti K 4 ![v₁, v₂, v₃, v₄] := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_assoc]

set_option maxHeartbeats 800000 in
/-- A linearly independent 4-tuple in a 4-dimensional space wedges to a nonzero top form. -/
theorem ιMulti_ne_zero_of_linearIndependent
    {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V]
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
    congr 1; funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1; exact orderEmb_fin_eq_id 4 (Set.powersetCard.ofFinEmbEquiv.symm s) i
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

/-- The Plücker target for `Gr(2, 4)` has dimension `C(4, 2) = 6`. -/
theorem gr24_plucker_target_dim (hdim : Module.finrank K V = 4) :
    Module.finrank K (⋀[K]^2 V) = 6 := by
  rw [exteriorPower.finrank_eq, hdim]; decide

/-- `⋀^4 V` is one-dimensional when `dim V = 4`. -/
theorem extPower_four_dim_one (hdim : Module.finrank K V = 4) :
    Module.finrank K (⋀[K]^4 V) = 1 := by
  rw [exteriorPower.finrank_eq, hdim]; decide

variable {K}

set_option maxHeartbeats 400000 in
/-- The wedge of standard basis vectors `e_0 ∧ e_1 ∧ e_2 ∧ e_3` in `(K^4)` is nonzero. -/
theorem ιMulti_stdBasis_nonzero :
    ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4) : Fin 4 → Fin 4 → K) ≠ 0 := by
  intro h
  set b := Pi.basisFun K (Fin 4)
  set s : Set.powersetCard (Fin 4) 4 := ⟨Finset.univ, Finset.card_fin 4⟩
  have key : (exteriorPower.ιMulti_family K 4 (⇑b) s : ⋀[K]^4 (Fin 4 → K)) =
      exteriorPower.ιMulti K 4 (⇑b) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1; funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1; exact orderEmb_fin_eq_id 4 (Set.powersetCard.ofFinEmbEquiv.symm s) i
  have hdiag := exteriorPower.ιMultiDual_apply_diag K 4 b s
  rw [key] at hdiag
  have h_sub : exteriorPower.ιMulti K 4 (⇑b) = 0 := by
    apply Subtype.val_injective; simp [exteriorPower.ιMulti_apply_coe, h]
  rw [h_sub, map_zero] at hdiag
  exact zero_ne_one hdiag

/-- The product of `ι` on the four standard basis vectors equals the top wedge `e_0 ∧ e_1 ∧ e_2 ∧ e_3`. -/
theorem basis_product_is_ιMulti :
    ι K (Pi.single 0 1 : Fin 4 → K) * ι K (Pi.single 1 1) *
      (ι K (Pi.single 2 1) * ι K (Pi.single 3 1)) =
    ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4) : Fin 4 → Fin 4 → K) := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero]
  rw [mul_assoc]

variable [CharZero K]

/-- The sum `e_0 ∧ e_1 + e_2 ∧ e_3` in `⋀^2 (K^4)` has nonzero square, hence it is not decomposable. -/
theorem non_decomp_wedge_sq_ne_zero :
    (ι K (Pi.single 0 1 : Fin 4 → K) * ι K (Pi.single 1 1) +
     ι K (Pi.single 2 1 : Fin 4 → K) * ι K (Pi.single 3 1)) *
    (ι K (Pi.single 0 1 : Fin 4 → K) * ι K (Pi.single 1 1) +
     ι K (Pi.single 2 1 : Fin 4 → K) * ι K (Pi.single 3 1)) ≠ 0 := by
  intro h
  rw [wedge_sq_sum_decomp_pair] at h
  rw [basis_product_is_ιMulti] at h
  have hne : ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4) : Fin 4 → Fin 4 → K) ≠ 0 :=
    ιMulti_stdBasis_nonzero
  have hunit : IsUnit (2 : ExteriorAlgebra K (Fin 4 → K)) :=
    (IsUnit.mk0 (2 : K) two_ne_zero).map (algebraMap K _)
  exact hne (hunit.mul_left_cancel (by rw [mul_zero]; exact h))


end Gr24

end GrassmannianProjective
