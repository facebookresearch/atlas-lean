/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Heights

open TateTheorem CanonicalHeight Filter

noncomputable section

attribute [local instance] Classical.dec

variable {K : Type*} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]
set_option linter.unusedSectionVars false in
/-- Northcott property for the canonical (Néron-Tate) height: the set of points $P \in E(K)$ with $\hat{h}(P) \leq B$ is finite for any bound $B$. -/
theorem bounded_canonical_height_finite
    (h : W.toAffine.Point → ℝ)
    (hWeil : IsWeilHeightOnCurve W h)
    (B : ℝ) :
    {P : W.toAffine.Point | EllipticCurve.NeronTateHeight W h hWeil P ≤ B}.Finite := by

  obtain ⟨C, hC⟩ := hWeil.doubling_bound

  let φ : W.toAffine.Point → W.toAffine.Point := fun P => (2 : ℤ) • P

  have hbound : ∀ P, |h (φ P) - 4 * h P| ≤ C := hC


  have htate := tate_theorem φ h 4 (by norm_num : (1 : ℝ) < 4) C hbound
  have hcompare := htate.2.1


  have key : ∀ Q : W.toAffine.Point,
      atTop.limUnder (tateSeq φ h 4 Q) =
      EllipticCurve.NeronTateHeight W h hWeil Q := by
    intro Q
    unfold EllipticCurve.NeronTateHeight canonicalHeight
    congr 1
    funext n
    unfold tateSeq canonicalHeightSeq
    congr 1


    congr 1
    induction n with
    | zero => simp [Function.iterate_zero]
    | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]

      show (2 : ℤ) • ((2 : ℤ) ^ n • Q) = (2 : ℤ) ^ (n + 1) • Q
      rw [← mul_smul, pow_succ']

  apply Set.Finite.subset (hWeil.northcott (B + C / (4 - 1)))
  intro P hP
  simp only [Set.mem_setOf_eq] at hP ⊢


  rw [← key P] at hP
  have hab := hcompare P
  rw [abs_le] at hab
  linarith [hab.2]

end
