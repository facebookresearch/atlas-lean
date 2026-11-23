/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.TorsionEndomorphism
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic

universe u

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- The restriction of an endomorphism `α : E → E` to the `n`-torsion subgroup,
viewed as an additive group homomorphism `E[n] →+ E[n]`. -/
noncomputable def Isogeny.restrictTorsion
    (α : Isogeny E E) (n : ℤ) :
    (torsionSubgroup E n) →+ (torsionSubgroup E n) where
  toFun P := ⟨α.toAddMonoidHom P.val,
    map_mem_torsionSubgroup α.toAddMonoidHom n P.val P.property⟩
  map_zero' := by
    ext
    exact α.toAddMonoidHom.map_zero
  map_add' x y := by
    ext
    exact α.toAddMonoidHom.map_add x.val y.val

/-- The restriction to torsion commutes with the inclusion `E[n] ↪ E`: the
underlying point of `α.restrictTorsion n P` is just `α(P)`. -/
@[simp]
theorem Isogeny.restrictTorsion_coe
    (α : Isogeny E E) (n : ℤ) (P : torsionSubgroup E n) :
    (α.restrictTorsion n P).val = α.toAddMonoidHom P.val :=
  rfl

/-- Given an additive endomorphism `f` of `(ZMod n)²`, extract its matrix
`Mat₂(ZMod n)` with respect to the standard basis `(1,0), (0,1)`. -/
noncomputable def torsionMatrixFromEndomorphism (n : ℕ)
    (f : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) :
    Matrix (Fin 2) (Fin 2) (ZMod n) :=
  Matrix.of fun i j =>
    let basisVec : ZMod n × ZMod n := if j = (0 : Fin 2) then (1, 0) else (0, 1)
    let img := f basisVec
    if i = (0 : Fin 2) then img.1 else img.2

/-- The matrix of `α` acting on the `n`-torsion `E[n]`, computed by conjugating
the restriction with an isomorphism `e : E[n] ≃+ (ZMod n)²` to standard basis. -/
noncomputable def Isogeny.torsionMatrix
    (α : Isogeny E E) (n : ℕ)
    (e : (torsionSubgroup E (n : ℤ)) ≃+ (ZMod n × ZMod n)) :
    Matrix (Fin 2) (Fin 2) (ZMod n) :=
  torsionMatrixFromEndomorphism n
    (e.toAddMonoidHom.comp ((α.restrictTorsion (n : ℤ)).comp e.symm.toAddMonoidHom))

/-- The trace mod `n` of `α` on the `n`-torsion: the trace of `α.torsionMatrix n e`. -/
noncomputable def Isogeny.torsionTrace
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E) (n : ℕ)
    (e : (torsionSubgroup E (n : ℤ)) ≃+ (ZMod n × ZMod n)) : ZMod n :=
  Matrix.trace (α.torsionMatrix n e)

/-- The determinant mod `n` of `α` on the `n`-torsion: the determinant of
`α.torsionMatrix n e`. -/
noncomputable def Isogeny.torsionDet
    {F : Type u} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F}
    (α : Isogeny E E) (n : ℕ)
    (e : (torsionSubgroup E (n : ℤ)) ≃+ (ZMod n × ZMod n)) : ZMod n :=
  Matrix.det (α.torsionMatrix n e)

/-- The Cayley–Hamilton theorem for `2 × 2` matrices over `ZMod n`: every such
matrix `M` satisfies `M² - tr(M) • M + det(M) • I = 0`. -/
theorem Matrix.cayleyHamilton_fin_two (n : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (ZMod n)) :
    M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0 := by
  have htr : M.trace = M 0 0 + M 1 1 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    simp [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, htr, hdet] <;>
    ring


/-- If `M` satisfies two characteristic equations `M² - t•M + d•I = 0` and
`M² - tr(M)•M + det(M)•I = 0` (Cayley–Hamilton), then their difference yields
`(tr M - t)•M + (d - det M)•I = 0`. -/
theorem Matrix.constraint_from_two_char_polys (n : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (ZMod n))
    (t d : ZMod n)
    (hrestr : M * M - t • M + d • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0)
    (hCH : M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0) :
    (M.trace - t) • M + (d - M.det) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0 := by
  have key : M * M - M.trace • M + M.det • 1 - (M * M - t • M + d • 1) =
    (t - M.trace) • M + (M.det - d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
               Matrix.mul_apply, Matrix.one_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  have h_eq : (t - M.trace) • M + (M.det - d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) = 0 := by
    rw [← key, hCH, hrestr, sub_zero]
  have : (M.trace - t) • M + (d - M.det) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) =
    -((t - M.trace) • M + (M.det - d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n))) := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
               Matrix.one_apply, smul_eq_mul]
    ring
  rw [this, h_eq, neg_zero]



