/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Real.Basic

open MvPolynomial

variable {R : Type*} [CommSemiring R]

noncomputable def newtonPolygon (f : MvPolynomial (Fin 2) R) : Set (Fin 2 → ℝ) :=
  (convexHull ℝ) ((fun s : Fin 2 →₀ ℕ => fun i : Fin 2 => (s i : ℝ)) '' ↑f.support)
