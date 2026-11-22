/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic

set_option maxHeartbeats 400000

namespace CYHyp

/-- Auxiliary record of numerical invariants of a smooth complete curve: its genus `g` and
canonical degree `degK`. -/
structure SmoothCompleteCurve' where
  g : ℤ
  degK : ℤ

/-- Build a `SmoothCompleteCurve'` of genus `g` with canonical degree `2g - 2`. -/
def mkCurve' (g : ℕ) : SmoothCompleteCurve' where
  g := g
  degK := 2 * (g : ℤ) - 2

/-- `mkCurve' g` has canonical degree `2g - 2`. -/
@[simp] theorem mkCurve'_degK (g : ℕ) : (mkCurve' g).degK = 2 * (g : ℤ) - 2 := rfl

/-- An elliptic curve (genus `1`) has canonical degree `0`. -/
theorem mkCurve'_elliptic : (mkCurve' 1).degK = 0 := by norm_num [mkCurve']

/-- Arithmetic genus of a smooth plane curve of degree `d`: `(d-1)(d-2)/2`. -/
def genus_plane_curve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2



end CYHyp

open CYHyp

noncomputable section

/-- A smooth projective hypersurface in `P^n` of degree `d`, with `n, d ≥ 1`. -/
structure SmoothProjectiveHypersurface where
  n : ℕ
  d : ℕ
  hn : 1 ≤ n
  hd : 1 ≤ d

namespace SmoothProjectiveHypersurface

/-- Canonical twist `d - n - 1` of a smooth hypersurface `Y ⊂ P^n` of degree `d` (so
`K_Y = O_Y(d - n - 1)` by the adjunction formula). -/
def canonicalTwist (Y : SmoothProjectiveHypersurface) : ℤ :=
  (Y.d : ℤ) - (Y.n : ℤ) - 1

/-- Adjunction formula for a hypersurface: `canonicalTwist = d - n - 1`. -/
theorem adjunction_formula_hypersurface (Y : SmoothProjectiveHypersurface) :
    Y.canonicalTwist = (Y.d : ℤ) - (Y.n : ℤ) - 1 := rfl

/-- Rewriting of the canonical twist using the Euler sequence: `K_Y = -(n + 1) + d`. -/
theorem canonicalTwist_from_euler (Y : SmoothProjectiveHypersurface) :
    Y.canonicalTwist = -((Y.n : ℤ) + 1) + (Y.d : ℤ) := by
  simp only [canonicalTwist]; ring

/-- Combined Euler/normal-bundle derivation of the canonical twist. -/
theorem adjunction_formula_from_euler_and_normal (Y : SmoothProjectiveHypersurface) :
    Y.canonicalTwist =
      (-(↑Y.n + 1) : ℤ)
      + (↑Y.d : ℤ)
      := by
  simp only [canonicalTwist]; ring

/-- Degree of the canonical bundle of `Y`: `d · (d - n - 1)`. -/
def degCanonical (Y : SmoothProjectiveHypersurface) : ℤ :=
  (Y.d : ℤ) * Y.canonicalTwist

/-- Definitional unfolding of `degCanonical` as `d · (d - n - 1)`. -/
theorem degCanonical_eq (Y : SmoothProjectiveHypersurface) :
    Y.degCanonical = (Y.d : ℤ) * ((Y.d : ℤ) - (Y.n : ℤ) - 1) := rfl

/-- Expanded polynomial form of the canonical degree: `d² - d(n + 1)`. -/
theorem degCanonical_expand (Y : SmoothProjectiveHypersurface) :
    Y.degCanonical = (Y.d : ℤ) ^ 2 - (Y.d : ℤ) * ((Y.n : ℤ) + 1) := by
  simp only [degCanonical, canonicalTwist]; ring

/-- Calabi-Yau predicate for a hypersurface: `d = n + 1`, equivalent to trivial canonical bundle. -/
def isCalabiYau (Y : SmoothProjectiveHypersurface) : Prop :=
  Y.d = Y.n + 1

/-- A hypersurface has zero canonical twist iff it is Calabi-Yau. -/
theorem canonicalTwist_zero_iff_calabiYau (Y : SmoothProjectiveHypersurface) :
    Y.canonicalTwist = 0 ↔ Y.isCalabiYau := by
  constructor
  · intro h; simp only [canonicalTwist, isCalabiYau] at *; omega
  · intro h; simp only [canonicalTwist, isCalabiYau] at *; omega

/-- The canonical degree vanishes on a Calabi-Yau hypersurface. -/
theorem degCanonical_zero_of_calabiYau (Y : SmoothProjectiveHypersurface)
    (h : Y.isCalabiYau) : Y.degCanonical = 0 := by
  simp only [degCanonical]
  rw [(canonicalTwist_zero_iff_calabiYau Y).mpr h, mul_zero]

/-- Converse: a hypersurface with vanishing canonical degree is Calabi-Yau. -/
theorem calabiYau_of_degCanonical_zero (Y : SmoothProjectiveHypersurface)
    (h : Y.degCanonical = 0) : Y.isCalabiYau := by
  simp only [degCanonical, canonicalTwist] at h
  have hd_pos : (Y.d : ℤ) ≠ 0 := by have := Y.hd; omega
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hd_pos
  · simp only [isCalabiYau]
    have : (Y.d : ℤ) - (Y.n : ℤ) - 1 = 0 := h1
    omega

/-- The smooth cubic in `P²` (an elliptic curve) as a `SmoothProjectiveHypersurface`. -/
def ellipticCurve : SmoothProjectiveHypersurface :=
  { n := 2, d := 3, hn := by omega, hd := by omega }

/-- A smooth quartic in `P³`, i.e. a K3 surface, as a `SmoothProjectiveHypersurface`. -/
def K3surface : SmoothProjectiveHypersurface :=
  { n := 3, d := 4, hn := by omega, hd := by omega }

/-- A smooth quintic in `P⁴`, i.e. a Calabi-Yau threefold, as a `SmoothProjectiveHypersurface`. -/
def CY3fold : SmoothProjectiveHypersurface :=
  { n := 4, d := 5, hn := by omega, hd := by omega }

/-- The elliptic curve `(n, d) = (2, 3)` is Calabi-Yau. -/
theorem ellipticCurve_isCalabiYau : ellipticCurve.isCalabiYau := by
  unfold isCalabiYau ellipticCurve; rfl

/-- The K3 surface `(n, d) = (3, 4)` is Calabi-Yau. -/
theorem K3surface_isCalabiYau : K3surface.isCalabiYau := by
  unfold isCalabiYau K3surface; rfl

/-- The quintic threefold `(n, d) = (4, 5)` is Calabi-Yau. -/
theorem CY3fold_isCalabiYau : CY3fold.isCalabiYau := by
  unfold isCalabiYau CY3fold; rfl

/-- The canonical twist of the elliptic curve is `0`. -/
theorem ellipticCurve_canonicalTwist : ellipticCurve.canonicalTwist = 0 := by
  simp [canonicalTwist, ellipticCurve]

/-- The canonical degree of the elliptic curve is `0`. -/
theorem ellipticCurve_degCanonical_zero : ellipticCurve.degCanonical = 0 :=
  degCanonical_zero_of_calabiYau _ ellipticCurve_isCalabiYau

/-- The canonical degree of the K3 surface is `0`. -/
theorem K3surface_degCanonical_zero : K3surface.degCanonical = 0 :=
  degCanonical_zero_of_calabiYau _ K3surface_isCalabiYau

/-- General Calabi-Yau result: a smooth degree-`(n+1)` hypersurface in `P^n` has trivial
canonical twist. -/
theorem calabiYau_general (n : ℕ) (hn : 1 ≤ n) :
    let Y : SmoothProjectiveHypersurface :=
      { n := n, d := n + 1, hn := hn, hd := by omega }
    Y.canonicalTwist = 0 := by
  simp [canonicalTwist]

/-- Plane curve canonical degree: a smooth plane curve of degree `d` has `deg K = d(d - 3)`. -/
theorem degCanonical_plane_curve (d : ℕ) (hd : 1 ≤ d) :
    let Y : SmoothProjectiveHypersurface :=
      { n := 2, d := d, hn := by omega, hd := hd }
    Y.degCanonical = (d : ℤ) * ((d : ℤ) - 3) := by
  simp only [degCanonical, canonicalTwist]
  ring

/-- Genus from adjunction: if `2g - 2` equals the canonical degree of a smooth plane curve of
degree `d`, then `2g = (d - 1)(d - 2)`. -/
theorem genus_from_adjunction (d : ℕ) (hd : 1 ≤ d) (g : ℤ)
    (hg : 2 * g - 2 =
      (SmoothProjectiveHypersurface.mk 2 d (by omega) hd).degCanonical) :
    2 * g = ((d : ℤ) - 1) * ((d : ℤ) - 2) := by
  simp only [degCanonical, canonicalTwist] at hg
  push_cast at hg ⊢
  nlinarith

/-- A line in `P²` has canonical degree `-2`. -/
theorem degCanonical_line : (mk 2 1 (by omega) (by omega)).degCanonical = -2 := by
  simp [degCanonical, canonicalTwist]

/-- A smooth conic in `P²` has canonical degree `-2`. -/
theorem degCanonical_conic : (mk 2 2 (by omega) (by omega)).degCanonical = -2 := by
  simp [degCanonical, canonicalTwist]

/-- A smooth cubic in `P²` (an elliptic curve) has canonical degree `0`. -/
theorem degCanonical_cubic : (mk 2 3 (by omega) (by omega)).degCanonical = 0 := by
  simp [degCanonical, canonicalTwist]

/-- A smooth plane quartic has canonical degree `4`. -/
theorem degCanonical_quartic : (mk 2 4 (by omega) (by omega)).degCanonical = 4 := by
  simp [degCanonical, canonicalTwist]

/-- Consistency check: both formulations agree that the elliptic curve has `degK = 0`. -/
theorem elliptic_degK_consistent :
    ellipticCurve.degCanonical = 0
    ∧ (mkCurve' 1).degK = 0 :=
  ⟨ellipticCurve_degCanonical_zero, mkCurve'_elliptic⟩


/-- Canonical degree of a smooth degree-`d` hypersurface in `P^n` as a function of `(n, d)`. -/
def degK_hypersurface (n : ℤ) (d : ℤ) : ℤ := d * (d - (n + 1))

/-- Unfolding the integer-formulated `degK_hypersurface`. -/
theorem degK_hypersurface_formula (n d : ℤ) :
    degK_hypersurface n d = d * (d - (n + 1)) := rfl

/-- The structured canonical degree agrees with the integer-valued `degK_hypersurface` formula. -/
theorem degCanonical_eq_degK_hypersurface (Y : SmoothProjectiveHypersurface) :
    Y.degCanonical = degK_hypersurface (Y.n : ℤ) (Y.d : ℤ) := by
  simp only [degCanonical, degK_hypersurface, canonicalTwist]; ring

end SmoothProjectiveHypersurface

end
