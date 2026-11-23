/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.PascalCurves

open Polynomial

set_option autoImplicit false

namespace ProjectivePascal

/-- A projective conic on P^2: a function on k^3 that is homogeneous of degree 2. -/
structure Conic (k : Type*) [Field k] where
  eval : (Fin 3 → k) → k
  homog : ∀ (c : k) (v : Fin 3 → k), eval (c • v) = c ^ 2 * eval v

/-- A projective line on P^2: a k-linear function k^3 → k. -/
structure Line (k : Type*) [Field k] where
  eval : (Fin 3 → k) → k
  map_add : ∀ (v w : Fin 3 → k), eval (v + w) = eval v + eval w
  map_smul : ∀ (c : k) (v : Fin 3 → k), eval (c • v) = c * eval v

/-- A conic is irreducible if its defining function is not a product of two linear
forms (i.e. it is not the union of two projective lines). -/
def Conic.IsIrreducible {k : Type*} [Field k] (Q : Conic k) : Prop :=
  ∀ (L₁ L₂ : Line k), Q.eval ≠ fun v => L₁.eval v * L₂.eval v

/-- The point P (in k^3) lies on the conic Q if Q vanishes on P. -/
def OnConic {k : Type*} [Field k] (Q : Conic k) (P : Fin 3 → k) : Prop :=
  Q.eval P = 0

/-- A line passes through a pair of points P_1, P_2 if it vanishes on both and is not
identically zero. -/
def Line.ThroughPair {k : Type*} [Field k] (L : Line k)
    (P₁ P₂ : Fin 3 → k) : Prop :=
  L.eval P₁ = 0 ∧ L.eval P₂ = 0 ∧ L.eval ≠ 0

/-- The point R is an intersection of two lines L_1 and L_2 if it lies on both and is
a nonzero vector. -/
def IsIntersectionOf {k : Type*} [Field k]
    (R : Fin 3 → k) (L₁ L₂ : Line k) : Prop :=
  L₁.eval R = 0 ∧ L₂.eval R = 0 ∧ R ≠ 0

/-- Three points are collinear if there exists a nonzero line passing through all three. -/
def AreCollinear {k : Type*} [Field k]
    (R₁ R₂ R₃ : Fin 3 → k) : Prop :=
  ∃ (L : Line k), L.eval ≠ 0 ∧ L.eval R₁ = 0 ∧ L.eval R₂ = 0 ∧ L.eval R₃ = 0

/-- Six points (as vectors in k^3) are pairwise projectively distinct if no two
represent the same point of projective space. -/
def PairwiseProjectivelyDistinct {k : Type*} [Field k]
    (P : Fin 6 → (Fin 3 → k)) : Prop :=
  ∀ i j : Fin 6, i ≠ j → ¬∃ (c : k), c ≠ 0 ∧ P i = c • P j

/-- All six points are nonzero vectors (so represent honest projective points). -/
def AllNonzero {k : Type*} [Field k]
    (P : Fin 6 → (Fin 3 → k)) : Prop :=
  ∀ i : Fin 6, P i ≠ 0

/-- All six points lie on the conic Q. -/
def AllOnConic {k : Type*} [Field k]
    (Q : Conic k) (P : Fin 6 → (Fin 3 → k)) : Prop :=
  ∀ i : Fin 6, OnConic Q (P i)



end ProjectivePascal

namespace PascalTheoremConics

/-- A product of three polynomials of degree ≤ 1 has degree ≤ 3. -/
lemma natDegree_triple_linear_le {R : Type*} [CommRing R]
    {p₁ p₂ p₃ : Polynomial R}
    (h₁ : p₁.natDegree ≤ 1) (h₂ : p₂.natDegree ≤ 1) (h₃ : p₃.natDegree ≤ 1) :
    (p₁ * p₂ * p₃).natDegree ≤ 3 :=
  calc (p₁ * p₂ * p₃).natDegree
      ≤ (p₁ * p₂).natDegree + p₃.natDegree := natDegree_mul_le
    _ ≤ (p₁.natDegree + p₂.natDegree) + p₃.natDegree :=
        Nat.add_le_add_right natDegree_mul_le _
    _ ≤ 3 := by omega

/-- If two factors of the cubic both vanish at x, then the cubic
p*r*s - t*(q*u*v) vanishes at x. -/
theorem eval_cubic_vanish {k : Type*} [Field k]
    (p r s q u v : Polynomial k) (t : k) (x : k)
    (hp : p.eval x = 0) (hq : q.eval x = 0) :
    (p * r * s - Polynomial.C t * (q * u * v)).eval x = 0 := by
  simp [eval_sub, eval_mul, eval_C, hp, hq]

/-- If the product Q*L vanishes at x and Q does not, then L vanishes at x. -/
theorem eval_factor_vanish {k : Type*} [Field k]
    (Q L : Polynomial k) (x : k)
    (hP : (Q * L).eval x = 0) (hQ : Q.eval x ≠ 0) :
    L.eval x = 0 := by
  rw [eval_mul] at hP
  exact (mul_eq_zero.mp hP).resolve_left hQ

/-- For a monic divisor g of f, we have f = g * (f /ₘ g). -/
theorem monic_dvd_eq_mul_divByMonic {k : Type*} [Field k]
    (f g : Polynomial k) (hg : g.Monic) (h : g ∣ f) :
    f = g * (f /ₘ g) := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_divByMonic_cancel_left _ hg]

/-- A projective conic given by an irreducible monic polynomial of degree 2. -/
structure ProjectiveConic (k : Type*) [Field k] where
  poly : Polynomial k
  irred : Irreducible poly
  monic : poly.Monic
  deg : poly.natDegree = 2

/-- An inscribed hexagon in a conic: three "sides" and three "opposite sides", each a
polynomial of degree ≤ 1, together with a scalar t making the cubic difference
non-coprime to the conic. -/
structure InscribedHexagon (k : Type*) [Field k] (conic : ProjectiveConic k) where
  sideA : Polynomial k
  sideB : Polynomial k
  sideC : Polynomial k
  oppA : Polynomial k
  oppB : Polynomial k
  oppC : Polynomial k
  sideA_deg : sideA.natDegree ≤ 1
  sideB_deg : sideB.natDegree ≤ 1
  sideC_deg : sideC.natDegree ≤ 1
  oppA_deg : oppA.natDegree ≤ 1
  oppB_deg : oppB.natDegree ≤ 1
  oppC_deg : oppC.natDegree ≤ 1
  t : k
  not_coprime : ¬ IsCoprime conic.poly
    (sideA * sideB * sideC - Polynomial.C t * (oppA * oppB * oppC))

/-- The cubic associated to an inscribed hexagon: side_A·side_B·side_C - t·opp_A·opp_B·opp_C. -/
noncomputable def InscribedHexagon.cubicP {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) : Polynomial k :=
  hex.sideA * hex.sideB * hex.sideC - Polynomial.C hex.t * (hex.oppA * hex.oppB * hex.oppC)

/-- The hexagon cubic has degree at most 3. -/
theorem InscribedHexagon.cubicP_deg_le {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) : hex.cubicP.natDegree ≤ 3 := by
  unfold cubicP
  have h1 := natDegree_triple_linear_le hex.sideA_deg hex.sideB_deg hex.sideC_deg
  have h2 : (Polynomial.C hex.t * (hex.oppA * hex.oppB * hex.oppC)).natDegree ≤ 3 :=
    calc (Polynomial.C hex.t * (hex.oppA * hex.oppB * hex.oppC)).natDegree
        ≤ (Polynomial.C hex.t).natDegree + (hex.oppA * hex.oppB * hex.oppC).natDegree :=
          natDegree_mul_le
      _ ≤ 0 + 3 := Nat.add_le_add (le_of_eq (natDegree_C hex.t))
            (natDegree_triple_linear_le hex.oppA_deg hex.oppB_deg hex.oppC_deg)
      _ = 3 := by omega
  exact (natDegree_sub_le _ _).trans (max_le h1 h2)

/-- The conic divides the hexagon cubic, by the irreducibility / non-coprimality
condition in `InscribedHexagon`. -/
theorem pascal_divisibility {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) :
    conic.poly ∣ hex.cubicP :=
  conic.irred.dvd_iff_not_isCoprime.mpr hex.not_coprime

/-- The Pascal line of a hexagon: the quotient of the hexagon cubic by the conic. -/
noncomputable def InscribedHexagon.pascalLine {k : Type*} [Field k]
    {conic : ProjectiveConic k} (hex : InscribedHexagon k conic) : Polynomial k :=
  hex.cubicP /ₘ conic.poly

/-- The Pascal line has degree ≤ 1, confirming it is indeed a (projective) line. -/
theorem pascal_quotient_is_line {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) :
    hex.pascalLine.natDegree ≤ 1 := by
  unfold InscribedHexagon.pascalLine
  rw [Polynomial.natDegree_divByMonic _ conic.monic, conic.deg]
  have := hex.cubicP_deg_le
  omega

/-- Factorization: the hexagon cubic equals the conic times the Pascal line. -/
theorem pascal_factorization {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) :
    hex.cubicP = conic.poly * hex.pascalLine := by
  unfold InscribedHexagon.pascalLine
  exact monic_dvd_eq_mul_divByMonic _ _ conic.monic (pascal_divisibility hex)

/-- If a point lies on the hexagon cubic but not on the conic, then it lies on the
Pascal line. -/
theorem point_on_line_of_on_cubic_not_on_conic {k : Type*} [Field k]
    {conic : ProjectiveConic k} (hex : InscribedHexagon k conic) (x : k)
    (hP : hex.cubicP.eval x = 0) (hQ : conic.poly.eval x ≠ 0) :
    hex.pascalLine.eval x = 0 := by
  have hfact := pascal_factorization hex
  rw [hfact] at hP
  exact eval_factor_vanish conic.poly hex.pascalLine x hP hQ

/-- The intersection point of side A and its opposite lies on the Pascal line. -/
theorem pascal_collinear_A {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) (x : k)
    (h_sideA : hex.sideA.eval x = 0)
    (h_oppA : hex.oppA.eval x = 0)
    (h_not_on_conic : conic.poly.eval x ≠ 0) :
    hex.pascalLine.eval x = 0 := by
  apply point_on_line_of_on_cubic_not_on_conic hex x _ h_not_on_conic
  exact eval_cubic_vanish hex.sideA hex.sideB hex.sideC hex.oppA hex.oppB hex.oppC hex.t x
    h_sideA h_oppA

/-- The intersection point of side B and its opposite lies on the Pascal line. -/
theorem pascal_collinear_B {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) (x : k)
    (h_sideB : hex.sideB.eval x = 0)
    (h_oppB : hex.oppB.eval x = 0)
    (h_not_on_conic : conic.poly.eval x ≠ 0) :
    hex.pascalLine.eval x = 0 := by
  apply point_on_line_of_on_cubic_not_on_conic hex x _ h_not_on_conic
  unfold InscribedHexagon.cubicP
  simp [eval_sub, eval_mul, eval_C, h_sideB, h_oppB]

/-- The intersection point of side C and its opposite lies on the Pascal line. -/
theorem pascal_collinear_C {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic) (x : k)
    (h_sideC : hex.sideC.eval x = 0)
    (h_oppC : hex.oppC.eval x = 0)
    (h_not_on_conic : conic.poly.eval x ≠ 0) :
    hex.pascalLine.eval x = 0 := by
  apply point_on_line_of_on_cubic_not_on_conic hex x _ h_not_on_conic
  unfold InscribedHexagon.cubicP
  simp [eval_sub, eval_mul, eval_C, h_sideC, h_oppC]

/-- Pascal's theorem for conics in the curve formulation: the three opposite-side
intersection points x_A, x_B, x_C all lie on the Pascal line, which is a line of
degree ≤ 1. -/
theorem pascal_theorem_conics {k : Type*} [Field k] {conic : ProjectiveConic k}
    (hex : InscribedHexagon k conic)
    (xA xB xC : k)

    (hA_side : hex.sideA.eval xA = 0) (hA_opp : hex.oppA.eval xA = 0)

    (hB_side : hex.sideB.eval xB = 0) (hB_opp : hex.oppB.eval xB = 0)

    (hC_side : hex.sideC.eval xC = 0) (hC_opp : hex.oppC.eval xC = 0)

    (hA_conic : conic.poly.eval xA ≠ 0)
    (hB_conic : conic.poly.eval xB ≠ 0)
    (hC_conic : conic.poly.eval xC ≠ 0) :

    hex.pascalLine.eval xA = 0 ∧
    hex.pascalLine.eval xB = 0 ∧
    hex.pascalLine.eval xC = 0 ∧
    hex.pascalLine.natDegree ≤ 1 :=
  ⟨pascal_collinear_A hex xA hA_side hA_opp hA_conic,
   pascal_collinear_B hex xB hB_side hB_opp hB_conic,
   pascal_collinear_C hex xC hC_side hC_opp hC_conic,
   pascal_quotient_is_line hex⟩

end PascalTheoremConics
