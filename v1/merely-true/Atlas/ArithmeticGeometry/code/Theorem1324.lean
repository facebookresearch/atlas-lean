/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.ProjectiveVarieties

noncomputable section

set_option maxHeartbeats 400000

open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization

namespace Thm1324

variable {n : ℕ} (k : Type*) [Field k]

/-- Evaluation–dehomogenization compatibility: for any index $i$, evaluating the dehomogenization
of a polynomial $g \in k[X_0, \dots, X_n]$ at an affine point $P \in k^n$ equals evaluating $g$
itself at the projective representative $(P_0, \dots, P_{i-1}, 1, P_i, \dots, P_{n-1})$ obtained
by inserting $1$ in the $i$-th coordinate. -/
theorem eval_dehomogenize_eq_general (i : Fin (n + 1))
    (g : MvPolynomial (Fin (n + 1)) k) (P : Fin n → k) :
    eval P (AffineParts.dehomogenize k i g) =
    eval (i.insertNth (1 : k) P) g := by
  have hcomp : (eval P).comp (AffineParts.dehomogenize k i) =
      eval (i.insertNth (1 : k) P) := by
    apply ringHom_ext
    · intro a; simp [AffineParts.dehomogenize]
    · intro j
      simp only [RingHom.comp_apply, AffineParts.dehomogenize, eval₂Hom_X']
      by_cases hj : j = i
      · subst hj; simp [Fin.insertNth_apply_same]
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj; simp
  rw [← RingHom.comp_apply, hcomp]

/-- Specialization of `eval_dehomogenize_eq_general` to the standard affine chart $i = 0$:
evaluating the dehomogenization at $X_0 = 1$ of $g$ at $P$ equals evaluating $g$ at $(1, P)$. -/
theorem eval_dehomogenize_eq (g : MvPolynomial (Fin (n + 1)) k) (P : Fin n → k) :
    eval P (AffineParts.dehomogenize k (0 : Fin (n + 1)) g) =
    eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g :=
  eval_dehomogenize_eq_general k 0 g P

/-- The dehomogenization ring map $k[X_0, \dots, X_n] \twoheadrightarrow k[Y_1, \dots, Y_n]$
that sets $X_i = 1$ is surjective: every polynomial in the affine chart variables lifts to a
polynomial in the projective variables. -/
theorem dehomogenize_surjective (i : Fin (n + 1)) :
    Function.Surjective (AffineParts.dehomogenize k i) :=
  Theorem1324.dehomogenize_surjective k i


/-- The dehomogenization of a prime ideal is prime, provided the kernel of the dehomogenization
map is contained in $I$. This is the ideal-theoretic content of passing from a projective
prime ideal to its affine part. -/
theorem dehomogenizedIdeal_isPrime
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    [hI : I.IsPrime]
    (i : Fin (n + 1))
    (hker : RingHom.ker (AffineParts.dehomogenize k i) ≤ I) :
    (I.map (AffineParts.dehomogenize k i)).IsPrime :=
  Ideal.map_isPrime_of_surjective (dehomogenize_surjective k i) hker


/-- Set-theoretic identification of the affine part of the zero locus of $I$ (in the chart
$X_i = 1$) with the zero locus of the dehomogenized ideal $I \cdot k[\text{affine vars}]$:
$\{P : f(\dots,1,\dots,P) = 0 \text{ for all } f \in I\} = \{P : h(P) = 0 \text{ for all } h \in
\mathrm{dehom}_i(I)\}$. -/
theorem projective_closure_of_affinePart_eq
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (i : Fin (n + 1)) :
    {P : Fin n → k | ∀ f ∈ I,
      eval (i.insertNth (1 : k) P) f = 0} =
    {P : Fin n → k | ∀ h ∈ I.map (AffineParts.dehomogenize k i),
      eval P h = 0} := by
  ext P
  simp only [Set.mem_setOf_eq]
  constructor
  ·
    intro hP h hh

    have : I.map (AffineParts.dehomogenize k i) ≤ RingHom.ker (eval P) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      rw [eval_dehomogenize_eq_general]
      exact hP f hf
    exact this hh
  ·
    intro hP f hf
    rw [← eval_dehomogenize_eq_general k i f P]
    exact hP _ (Ideal.mem_map_of_mem _ hf)

/-- Theorem 13.24: for a prime ideal $I \subseteq k[X_0, \dots, X_n]$ whose dehomogenization
kernel lies in $I$, the dehomogenized ideal $\mathrm{dehom}_i(I)$ is prime, its zero set agrees
with the affine part of $V(I)$ in the chart $X_i = 1$, and re-homogenizing recovers the
projective closure: $V(I) \cap \{X_0 = 1\} = V(\mathrm{hom}(\mathrm{dehom}_0 I))$. This packages
the affine–projective correspondence on prime ideals. -/
theorem theorem_13_24
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    [hI : I.IsPrime]
    (i : Fin (n + 1))
    (hker : RingHom.ker (AffineParts.dehomogenize k i) ≤ I) :

    (I.map (AffineParts.dehomogenize k i)).IsPrime ∧

    ({P : Fin n → k | ∀ f ∈ I,
      eval (i.insertNth (1 : k) P) f = 0} =
    {P : Fin n → k | ∀ h ∈ I.map (AffineParts.dehomogenize k i),
      eval P h = 0}) ∧


    ({P : Fin n → k | ∀ f ∈ I,
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} =
    {P : Fin n → k | ∀ g ∈ ProjectiveClosure.homogenizeIdeal
        (I.map (AffineParts.dehomogenize k 0)),
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) :=
  ⟨dehomogenizedIdeal_isPrime k I i hker,
   projective_closure_of_affinePart_eq k I i,
   Theorem1324.projective_closure_of_affinePart_eq k I⟩


end Thm1324

end

noncomputable section

set_option maxHeartbeats 400000

open MvPolynomial Finsupp
open scoped LinearAlgebra.Projectivization

namespace Thm1324Geometric

variable {n : ℕ} (k : Type*) [Field k]

open ProjectiveVarietyDef ProjectiveVanishingIdeal AffineParts




end Thm1324Geometric

end
