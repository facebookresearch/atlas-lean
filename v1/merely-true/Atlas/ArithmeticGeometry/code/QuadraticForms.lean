/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.GroupTheory.QuotientGroup.Basic

open LinearMap (BilinMap BilinForm)

noncomputable instance instInvertibleTwoOfNeZero (k : Type*) [Field k] [NeZero (2 : k)] :
    Invertible (2 : k) :=
  invertibleOfNonzero (NeZero.ne 2)

namespace QuadraticFormEquiv

section BasicProperties

variable {k : Type*} [CommSemiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]


end BasicProperties

section BilinQuadEquiv

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V]

theorem associated_bilinForm_isSymm (Q : QuadraticForm k V) :
    (QuadraticMap.associated (R := k) Q).IsSymm :=
  QuadraticForm.associated_isSymm k Q

theorem quadForm_eq_associated_self (Q : QuadraticForm k V) (x : V) :
    Q x = QuadraticMap.associated (R := k) Q x x :=
  (QuadraticMap.associated_eq_self_apply k Q x).symm

theorem associated_eq_half_polar (Q : QuadraticForm k V) (x y : V) :
    QuadraticMap.associated (R := k) Q x y =
      ⅟(2 : k) * (Q (x + y) - Q x - Q y) := by
  rw [QuadraticMap.associated_apply]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul]

theorem associated_toQuadraticMap_eq (Q : QuadraticForm k V) :
    (QuadraticMap.associated (R := k) Q).toQuadraticMap = Q :=
  QuadraticMap.toQuadraticMap_associated k Q

theorem associated_of_symm_bilinForm (B : BilinForm k V) (hB : B.IsSymm) :
    QuadraticMap.associated (R := k) B.toQuadraticMap = B :=
  QuadraticMap.associated_left_inverse k hB.eq

theorem quadForm_add_expansion (Q : QuadraticForm k V) (x y : V) :
    Q (x + y) = Q x + Q y + 2 * (QuadraticMap.associated (R := k) Q x y) := by
  rw [QuadraticMap.associated_apply]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul]
  rw [show (2 : k) * (⅟(2 : k) * (Q (x + y) - Q x - Q y)) = Q (x + y) - Q x - Q y from by
    rw [← mul_assoc, mul_invOf_self', one_mul]]
  ring

end BilinQuadEquiv

section MatrixBilinEquiv

variable {k : Type*} [Field k]
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def matrixBilinEquiv :
    Matrix n n k ≃ₗ[k] BilinMap k (n → k) k :=
  Matrix.toLinearMap₂' k

noncomputable def bilinFormToMatrix :
    BilinMap k (n → k) k ≃ₗ[k] Matrix n n k :=
  LinearMap.toMatrix₂' k

theorem matrix_to_bilinForm_apply (A : Matrix n n k) (x y : n → k) :
    matrixBilinEquiv A x y = dotProduct x (A.mulVec y) :=
  Matrix.toLinearMap₂'_apply' A x y

theorem toMatrix_toLinearMap₂ (A : Matrix n n k) :
    bilinFormToMatrix (matrixBilinEquiv A) = A :=
  bilinFormToMatrix.apply_symm_apply A

theorem toLinearMap₂_toMatrix (B : BilinMap k (n → k) k) :
    matrixBilinEquiv (bilinFormToMatrix B) = B :=
  matrixBilinEquiv.apply_symm_apply B

end MatrixBilinEquiv

section MatrixQuadEquiv

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def matrixToQuadraticForm (A : Matrix n n k) : QuadraticForm k (n → k) :=
  A.toQuadraticMap'

noncomputable def quadraticFormToMatrix (Q : QuadraticForm k (n → k)) : Matrix n n k :=
  Q.toMatrix'

theorem quadraticFormToMatrix_isSymm (Q : QuadraticForm k (n → k)) :
    Q.toMatrix'.IsSymm :=
  QuadraticMap.isSymm_toMatrix' Q

end MatrixQuadEquiv

section SymmetryPreservation

variable {k : Type*} [Field k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem bilinForm_symm_to_matrix_symm (B : BilinForm k (n → k)) (hB : B.IsSymm) :
    (LinearMap.toMatrix₂' k B).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply]
  exact (hB.eq (Pi.single i 1) (Pi.single j 1)).symm

theorem matrix_symm_to_bilinForm_symm (A : Matrix n n k) (hA : A.IsSymm) :
    (Matrix.toLinearMap₂' k A).IsSymm := by
  constructor
  intro x y
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hij : A j i = A i j := by
    have h := congr_fun (congr_fun hA.symm i) j
    simp only [Matrix.transpose_apply] at h
    exact h.symm
  rw [hij]; ring

end SymmetryPreservation

section EquivalentQuadraticForms

open QuadraticMap

variable {k : Type*} [CommSemiring k]
variable {V : Type*} [AddCommMonoid V] [Module k V]

theorem equivalent_def (f g : QuadraticMap k V k) :
    f.Equivalent g ↔ Nonempty (f.IsometryEquiv g) :=
  Iff.rfl

theorem equivalent_iff_exists_linearEquiv (f g : QuadraticMap k V k) :
    f.Equivalent g ↔ ∃ T : V ≃ₗ[k] V, ∀ v, g (T v) = f v := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearEquiv, e.map_app⟩
  · rintro ⟨T, hT⟩
    exact ⟨⟨T, hT⟩⟩

theorem isometryEquiv_map_app (f g : QuadraticMap k V k)
    (e : f.IsometryEquiv g) (v : V) : g (e v) = f v :=
  e.map_app v

theorem equivalent_refl (f : QuadraticMap k V k) : f.Equivalent f :=
  Equivalent.refl f

theorem equivalent_symm {f g : QuadraticMap k V k} (h : f.Equivalent g) :
    g.Equivalent f :=
  h.symm

theorem equivalent_comm (f g : QuadraticMap k V k) :
    f.Equivalent g ↔ g.Equivalent f :=
  ⟨Equivalent.symm, Equivalent.symm⟩

theorem equivalent_trans {f g h : QuadraticMap k V k}
    (hfg : f.Equivalent g) (hgh : g.Equivalent h) : f.Equivalent h :=
  hfg.trans hgh

theorem equivalent_isEquiv :
    Equivalence (QuadraticMap.Equivalent (R := k) (M₁ := V) (M₂ := V) (N := k)) :=
  ⟨Equivalent.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end EquivalentQuadraticForms

section DiagonalFormBasic

variable {k : Type*} [Field k]

theorem weightedSumSquares_is_diagonal {n : ℕ} (w : Fin n → k) (v : Fin n → k) :
    QuadraticMap.weightedSumSquares k w v = ∑ i, w i * (v i * v i) := by
  simp [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]

end DiagonalFormBasic

section DiagonalizationConstructive

open Module

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V]

theorem diagonalization_via_orthogonal_basis (Q : QuadraticForm k V)
    (v : Basis (Fin (finrank k V)) k V)
    (hv : (QuadraticMap.associated (R := k) Q).IsOrthoᵢ v) :
    Q.Equivalent (QuadraticMap.weightedSumSquares k (fun i => Q (v i))) :=
  ⟨Q.isometryEquivWeightedSumSquares v hv⟩

end DiagonalizationConstructive

section Diagonalization

open Module

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem diagonalization_of_quadratic_forms (Q : QuadraticForm k V) :
    ∃ w : Fin (finrank k V) → k,
      Q.Equivalent (QuadraticMap.weightedSumSquares k w) :=
  Q.equivalent_weightedSumSquares

theorem exists_orthogonal_basis_for_quadForm (Q : QuadraticForm k V) :
    ∃ v : Basis (Fin (finrank k V)) k V,
      (QuadraticMap.associated (R := k) Q).IsOrthoᵢ v :=
  LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm k Q)

end Diagonalization

end QuadraticFormEquiv

namespace QuadraticMap

def Represents {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (Q : QuadraticForm R M) (a : R) : Prop :=
  ∃ v : M, v ≠ 0 ∧ Q v = a

theorem Represents.of_isometryEquiv {R M₁ M₂ : Type*}
    [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) {a : R} (h : Q₁.Represents a) : Q₂.Represents a := by
  obtain ⟨v, hv_ne, hv⟩ := h
  refine ⟨e v, ?_, by rw [e.map_app, hv]⟩
  intro h_eq
  exact hv_ne (e.toLinearEquiv.injective (by simp [h_eq]))

theorem represents_iff_of_isometryEquiv {R M₁ M₂ : Type*}
    [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) {a : R} : Q₁.Represents a ↔ Q₂.Represents a :=
  ⟨Represents.of_isometryEquiv e, Represents.of_isometryEquiv e.symm⟩


section Theorem99

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

lemma eval_smul_isotropic_add (Q : QuadraticForm k V) (v w : V) (x : k) (hv : Q v = 0) :
    Q (x • v + w) = Q w + x * QuadraticMap.polar (↑Q) v w := by
  have h1 := QuadraticMap.map_add (↑Q) (x • v) w
  rw [QuadraticMap.map_smul, hv, smul_zero, zero_add,
      QuadraticMap.polar_smul_left, smul_eq_mul] at h1
  exact h1

theorem nondegenerate_represents_zero_represents_all
    (Q : QuadraticForm k V)
    (hnd : Q.Nondegenerate)
    (hiso : Q.Represents 0) :
    ∀ c : k, Q.Represents c := by
  intro c
  obtain ⟨v, hv_ne, hv_zero⟩ := hiso

  have hv_not_rad : v ∉ Q.radical := by
    intro hv_rad
    rw [hnd.radical_eq_bot] at hv_rad
    exact hv_ne hv_rad

  have hpol_ne : Q.polarBilin v ≠ 0 :=
    fun hpol => hv_not_rad ⟨hv_zero, hpol⟩
  rw [Ne, LinearMap.ext_iff, not_forall] at hpol_ne
  push Not at hpol_ne
  obtain ⟨w, hw⟩ := hpol_ne
  rw [LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply] at hw

  by_cases hc : c = 0
  · exact hc ▸ ⟨v, hv_ne, hv_zero⟩
  ·
    let x := (c - Q w) * (QuadraticMap.polar (↑Q) v w)⁻¹
    have heval : Q (x • v + w) = c := by
      rw [eval_smul_isotropic_add Q v w x hv_zero]
      show Q w + (c - Q w) * (QuadraticMap.polar (↑Q) v w)⁻¹ *
        QuadraticMap.polar (↑Q) v w = c
      rw [mul_assoc, inv_mul_cancel₀ hw, mul_one]
      ring
    exact ⟨x • v + w, fun h_eq => hc (by rw [← heval, h_eq, QuadraticMap.map_zero]), heval⟩

end Theorem99

end QuadraticMap

namespace QuadraticFormDef93

open LinearMap (BilinMap BilinForm)

section MatrixRank

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_fullRank_iff_det_ne_zero [Nonempty n] (A : Matrix n n k) :
    A.rank = Fintype.card n ↔ A.det ≠ 0 := by
  constructor
  · intro hA hdet
    rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
    obtain ⟨v, hv, hAv⟩ := hdet
    have hrange : A.mulVecLin.range = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [show Module.finrank k A.mulVecLin.range = Fintype.card n from hA,
          Module.finrank_pi k]
    rw [LinearMap.range_eq_top] at hrange
    exact hv ((LinearMap.injective_iff_surjective.mpr hrange)
      (show A.mulVecLin v = A.mulVecLin 0 by simp [hAv]))
  · intro h
    exact Matrix.rank_of_isUnit A
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))

end MatrixRank

section SymmetricKernel

variable {k : Type*} [Field k] {n : Type*} [Fintype n]

lemma symmetric_dotProduct_zero_implies_mulVec_zero
    (M : Matrix n n k) (hM : M.IsSymm) (x : n → k)
    (h : ∀ y, x ⬝ᵥ (M.mulVec y) = 0) : M.mulVec x = 0 := by
  have h1 : ∀ y, (Matrix.vecMul x M) ⬝ᵥ y = 0 := by
    intro y; rw [← Matrix.dotProduct_mulVec]; exact h y
  have h2 : Matrix.vecMul x M = 0 := dotProduct_eq_zero_iff.mp h1
  rw [← Matrix.vecMul_transpose M x, hM.eq]
  exact h2

end SymmetricKernel

section Def93

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def quadraticFormRank (Q : QuadraticForm k (n → k)) : ℕ :=
  Q.toMatrix'.rank

def quadraticFormIsNondegenerate (Q : QuadraticForm k (n → k)) : Prop :=
  quadraticFormRank Q = Fintype.card n

theorem quadraticForm_nondegenerate_iff_det_ne_zero [Nonempty n]
    (Q : QuadraticForm k (n → k)) :
    quadraticFormIsNondegenerate Q ↔ Q.toMatrix'.det ≠ 0 :=
  matrix_fullRank_iff_det_ne_zero Q.toMatrix'

theorem toLinearMap₂'_toMatrix'_eq_associated
    (Q : QuadraticForm k (n → k)) :
    (Matrix.toLinearMap₂' k) Q.toMatrix' = QuadraticMap.associated (R := k) Q := by
  unfold QuadraticMap.toMatrix'
  exact (Matrix.toLinearMap₂' k).apply_symm_apply _

theorem matrix_eq_associated_apply
    (Q : QuadraticForm k (n → k)) (x y : n → k) :
    (Matrix.toLinearMap₂' k) Q.toMatrix' x y =
      (QuadraticMap.associated (R := k) Q) x y := by
  rw [toLinearMap₂'_toMatrix'_eq_associated]

theorem nondegenerate_associated_ne_zero [Nonempty n]
    (Q : QuadraticForm k (n → k)) (hQ : quadraticFormIsNondegenerate Q)
    (x : n → k) (hx : x ≠ 0) :
    ∃ y : n → k, (QuadraticMap.associated (R := k) Q) x y ≠ 0 := by
  by_contra hall
  push Not at hall

  have hmat : ∀ y, x ⬝ᵥ (Q.toMatrix'.mulVec y) = 0 := by
    intro y
    have := hall y
    rw [← matrix_eq_associated_apply] at this
    rwa [Matrix.toLinearMap₂'_apply'] at this
  have hAx : Q.toMatrix'.mulVec x = 0 :=
    symmetric_dotProduct_zero_implies_mulVec_zero Q.toMatrix'
      (QuadraticMap.isSymm_toMatrix' Q) x hmat
  rw [quadraticForm_nondegenerate_iff_det_ne_zero] at hQ
  exact hx (Matrix.eq_zero_of_mulVec_eq_zero hQ hAx)

end Def93

end QuadraticFormDef93

namespace QuadraticFormDef94

variable (k : Type*) [Field k]

noncomputable def sqMonoidHom : kˣ →* kˣ where
  toFun u := u ^ 2
  map_one' := one_pow 2
  map_mul' a b := mul_pow a b 2

noncomputable def squaresSubgroup : Subgroup kˣ := (sqMonoidHom k).range

def SquareClassGroup := kˣ ⧸ squaresSubgroup k

instance squaresSubgroupNormal : (squaresSubgroup k).Normal := Subgroup.normal_of_comm _

noncomputable def toSquareClass : kˣ → SquareClassGroup k := QuotientGroup.mk

lemma toSquareClass_sq_mul (c a : kˣ) :
    toSquareClass k (c ^ 2 * a) = toSquareClass k a := by
  show QuotientGroup.mk _ = QuotientGroup.mk _
  rw [show c ^ 2 * a = a * c ^ 2 from mul_comm _ _]
  exact QuotientGroup.mk_mul_of_mem a ⟨c, rfl⟩

section Discriminant

variable [NeZero (2 : k)]
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def discrUnit (Q : QuadraticMap k (n → k) k) (hQ : Q.discr ≠ 0) : kˣ :=
  Units.mk0 Q.discr hQ

noncomputable def discriminant (Q : QuadraticMap k (n → k) k) (hQ : Q.discr ≠ 0) :
    SquareClassGroup k :=
  toSquareClass k (discrUnit k Q hQ)

lemma linearEquiv_toMatrix'_det_ne_zero {k' : Type*} [Field k']
    {m : Type*} [Fintype m] [DecidableEq m] (T : (m → k') ≃ₗ[k'] (m → k')) :
    (LinearMap.toMatrix' T.toLinearMap).det ≠ 0 := by
  have h : (LinearMap.toMatrix' T.toLinearMap) *
      (LinearMap.toMatrix' T.symm.toLinearMap) = 1 := by
    rw [← LinearMap.toMatrix'_comp]; simp
  exact left_ne_zero_of_mul
    (by rw [← Matrix.det_mul, h, Matrix.det_one]; exact one_ne_zero)

lemma discr_isometryEquiv_eq
    {Q₁ Q₂ : QuadraticMap k (n → k) k} (e : Q₁.IsometryEquiv Q₂) :
    Q₁.discr = (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det *
               (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det * Q₂.discr := by
  have h : Q₁ = Q₂.comp e.toLinearEquiv.toLinearMap := by
    ext v; simp [QuadraticMap.comp_apply, e.map_app v]
  conv_lhs => rw [h]
  exact QuadraticMap.discr_comp _

theorem discriminant_preserved_by_isometryEquiv
    {Q₁ Q₂ : QuadraticMap k (n → k) k}
    (e : Q₁.IsometryEquiv Q₂)
    (hQ₁ : Q₁.discr ≠ 0) (hQ₂ : Q₂.discr ≠ 0) :
    discriminant k Q₁ hQ₁ = discriminant k Q₂ hQ₂ := by
  unfold discriminant discrUnit
  have hdet := linearEquiv_toMatrix'_det_ne_zero e.toLinearEquiv
  have heq := discr_isometryEquiv_eq k e
  have : Units.mk0 Q₁.discr hQ₁ =
    (Units.mk0 ((LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det) hdet) ^ 2 *
    Units.mk0 Q₂.discr hQ₂ := by
    ext; simp [heq, sq]
  rw [this]
  exact toSquareClass_sq_mul k _ _


end Discriminant

end QuadraticFormDef94
