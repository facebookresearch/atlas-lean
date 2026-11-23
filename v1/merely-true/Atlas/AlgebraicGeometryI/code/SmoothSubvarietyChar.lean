/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Basic

open KaehlerDifferential Algebra

/-- **Smoothness of a closed subscheme**: if `R` is a formally smooth `k`-algebra
and `I ⊆ R`, then the quotient `R/I` is formally smooth over `k` iff the natural
map `I/I² → Ω_{R/k} ⊗_R R/I` admits a left-inverse. Geometrically: a closed
subscheme of a smooth scheme is smooth iff its conormal sequence splits. -/
theorem smooth_subvariety_char
    (k : Type*) [Field k]
    (R : Type*) [CommRing R] [Algebra k R]
    [FormallySmooth k R]
    (I : Ideal R) :
    FormallySmooth k (R ⧸ I) ↔
      ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id :=
  FormallySmooth.iff_split_injection Ideal.Quotient.mk_surjective
