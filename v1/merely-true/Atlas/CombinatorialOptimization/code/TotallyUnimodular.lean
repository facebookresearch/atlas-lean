/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix

def Matrix.TotallyUnimodular {m n : Type*} (A : Matrix m n ℤ) : Prop :=
  ∀ (k : ℕ) (f : Fin k → m) (g : Fin k → n),
    Function.Injective f → Function.Injective g →
    (A.submatrix f g).det ∈ ({-1, 0, 1} : Set ℤ)
