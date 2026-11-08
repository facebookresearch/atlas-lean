/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.QCohProjective
import Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof

set_option maxHeartbeats 4000000

open MvPolynomial QCohProjective

noncomputable section

namespace TwistSheaf

variable (k : Type*) [Field k] (n : ℕ)


/-- The `k`-module structure on the multivariate polynomial ring `k[X₀,…,Xₙ]`. -/
noncomputable instance mvPolyModule :
    Module k (MvPolynomial (Fin (n + 1)) k) := Algebra.toModule

/-- The `k`-submodule of polynomials of homogeneous degree `d`, defined for
all integers `d` by setting it to `⊥` for `d < 0`. -/
def polyGrSub (d : ℤ) : Submodule k (HomogCoordRing k n) :=
  if 0 ≤ d then homogeneousSubmodule (Fin (n + 1)) k d.toNat else ⊥

/-- The degree-`d` graded component as a type. -/
abbrev polyGrComp (d : ℤ) : Type _ := ↥(polyGrSub k n d)

/-- For `d ≥ 0`, the degree-`d` graded piece agrees with the usual
homogeneous submodule of degree `d.toNat`. -/
theorem polyGrSub_nonneg (d : ℤ) (hd : 0 ≤ d) :
    polyGrSub k n d = homogeneousSubmodule (Fin (n + 1)) k d.toNat :=
  if_pos hd

/-- For `d < 0`, the degree-`d` graded piece is trivial. -/
theorem polyGrSub_neg (d : ℤ) (hd : d < 0) :
    polyGrSub k n d = ⊥ :=
  if_neg (by omega)

/-- Identifies the integer-indexed graded component at a natural number `d`
with the standard nat-indexed homogeneous submodule. -/
theorem polyGrComp_nat (d : ℕ) :
    polyGrComp k n (d : ℤ) = ↥(homogeneousSubmodule (Fin (n + 1)) k d) := by
  show ↥(polyGrSub k n ↑d) = ↥(homogeneousSubmodule (Fin (n + 1)) k d)
  rw [polyGrSub_nonneg k n ↑d (Int.natCast_nonneg d), Int.toNat_natCast]

/-- Graded multiplication: multiplying a degree-`i` homogeneous polynomial
with a degree-`j` graded element gives a degree-`(i+j)` graded element. -/
def polyGsmul (i : ℕ) (j : ℤ) :
    gradedComponent k n i → polyGrComp k n j → polyGrComp k n (↑i + j) :=
  fun ⟨s, hs⟩ ⟨m, hm⟩ => by
    refine ⟨s * m, ?_⟩
    by_cases hj : 0 ≤ j
    ·
      simp only [polyGrSub, if_pos hj] at hm
      simp only [polyGrSub, if_pos (by omega : (0 : ℤ) ≤ ↑i + j)]
      show (s * m).IsHomogeneous (↑i + j).toNat
      have hs' : s.IsHomogeneous i := hs
      have hm' : m.IsHomogeneous j.toNat := hm
      convert hs'.mul hm' using 1
      omega
    ·
      push Not at hj
      simp only [polyGrSub, if_neg (by omega : ¬(0 ≤ j))] at hm
      replace hm : m = 0 := by simpa using hm
      rw [hm, mul_zero]
      exact Submodule.zero_mem _

/-- Graded-module data realizing the structure sheaf of `P^n` as the trivial
shift: the graded pieces are the homogeneous components of `k[X₀,…,Xₙ]`. -/
def structureSheafData : GradedModuleData k n where
  component := polyGrComp k n
  instACG := fun _ => inferInstance
  instMod := fun _ => inferInstance
  gsmul := polyGsmul k n

/-- The Serre twist `O(d)` on `P^n`, expressed as the graded-module data
obtained by shifting the structure sheaf by `d`. -/
def serreTwist (d : ℤ) : GradedModuleData k n :=
  (structureSheafData k n).twist d

/-- `O(0)` recovers the structure sheaf component-wise. -/
theorem serreTwist_zero_component (i : ℤ) :
    (serreTwist k n 0).component i = (structureSheafData k n).component i := by
  simp [serreTwist, GradedModuleData.twist]

/-- Tensor product of twists: `O(d₁) ⊗ O(d₂) = O(d₁ + d₂)` at the level of
graded components. -/
theorem serreTwist_double (d₁ d₂ : ℤ) (i : ℤ) :
    ((serreTwist k n d₁).twist d₂).component i =
    (serreTwist k n (d₁ + d₂)).component i := by
  simp [serreTwist, GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

/-- Inverse twist: `O(d) ⊗ O(-d) = O`, witnessing that `O(d)` is invertible
in the Picard group. -/
theorem serreTwist_neg_cancel (d : ℤ) (i : ℤ) :
    ((serreTwist k n d).twist (-d)).component i =
    (structureSheafData k n).component i := by
  simp [serreTwist, GradedModuleData.twist, add_assoc]

/-- Global sections of `O(d)`: the degree-0 graded piece of `O(d)` equals the
degree-`d` piece of the structure sheaf. -/
theorem globalSections_serreTwist (d : ℤ) :
    (serreTwist k n d).component 0 = (structureSheafData k n).component d := by
  simp [serreTwist, GradedModuleData.twist]

/-- Global sections of `O(d)` for `d ≥ 0` are the homogeneous degree-`d`
polynomials in `k[X₀,…,Xₙ]`. -/
theorem globalSections_serreTwist_eq (d : ℕ) :
    (serreTwist k n (d : ℤ)).component 0 =
    ↥(homogeneousSubmodule (Fin (n + 1)) k d) := by
  trans (structureSheafData k n).component ↑d
  · exact globalSections_serreTwist k n ↑d
  · exact polyGrComp_nat k n d

/-- `dim_k H⁰(P^n, O(d)) = C(n+d, n)`: the dimension formula for global
sections of `O(d)`. -/
theorem serreTwist_globalSections_finrank (d : ℕ) :
    Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k d) =
    (n + d).choose n :=
  globalSections_Od_finrank k n d

/-- Symmetric form: `dim_k H⁰(P^n, O(d)) = C(n+d, d)`. -/
theorem serreTwist_globalSections_finrank_symm (d : ℕ) :
    Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k d) =
    (n + d).choose d := by
  rw [serreTwist_globalSections_finrank]
  exact Nat.choose_symm_add

/-- `H⁰(P^n, O) = k`: the structure sheaf has one-dimensional global sections. -/
theorem globalSections_O0_finrank :
    Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k 0) = 1 := by
  rw [serreTwist_globalSections_finrank]
  simp

/-- `H⁰(P^n, O(1))` has dimension `n + 1`, matching the linear forms in
`n + 1` variables. -/
theorem globalSections_O1_finrank :
    Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k 1) = n + 1 := by
  rw [serreTwist_globalSections_finrank]
  simp

/-- Addition formula for twists: `O(d₁ + d₂) = O(d₁) ⊗ O(d₂)` component-wise. -/
theorem twist_shift_add (d₁ d₂ : ℤ) (i : ℤ) :
    (serreTwist k n (d₁ + d₂)).component i =
    ((serreTwist k n d₁).twist d₂).component i := by
  simp [serreTwist, GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

/-- Deprecated alias witnessing Picard-group additivity of twists; use
`twist_shift_add` instead. -/
@[deprecated twist_shift_add (since := "2025-01-01")]
theorem picard_group_twist (d₁ d₂ : ℤ) (i : ℤ) :
    (serreTwist k n (d₁ + d₂)).component i =
    ((serreTwist k n d₁).twist d₂).component i :=
  twist_shift_add k n d₁ d₂ i

/-- Monotonicity of global sections: `dim H⁰(P^n, O(d))` is nondecreasing
in `d`. -/
theorem globalSections_mono (d : ℕ) :
    Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k d) ≤
    Module.finrank k ↥(homogeneousSubmodule (Fin (n + 1)) k (d + 1)) := by
  rw [serreTwist_globalSections_finrank, serreTwist_globalSections_finrank]
  exact Nat.choose_le_choose n (by omega)

/-- Negative twists have no nonzero global sections at the polynomial level. -/
theorem globalSections_negative_trivial (d : ℤ) (hd : d < 0) :
    polyGrSub k n d = ⊥ :=
  polyGrSub_neg k n d hd

end TwistSheaf

end
