/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Lem225

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

open IsDedekindDomain

lemma exists_ringOfIntegers_cong_mod_primes
    {ι : Type*} {s : Finset ι}
    (P : ι → FinitePlace K) (e : ι → ℕ)
    (hP_inj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i ≠ P j)
    (x : s → 𝓞 K) :
    ∃ y : 𝓞 K, ∀ (i : ι) (hi : i ∈ s),
      y - x ⟨i, hi⟩ ∈ (P i).asIdeal ^ e i := by
  have hprime : ∀ i ∈ s, Prime ((P i).asIdeal) := fun i _ => (P i).prime
  have hcoprime : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (P i).asIdeal ≠ (P j).asIdeal := by
    intro i hi j hj hij h
    exact absurd (HeightOneSpectrum.ext h) (hP_inj i hi j hj hij)
  exact IsDedekindDomain.exists_forall_sub_mem_ideal
    (fun i => (P i).asIdeal) e hprime hcoprime x

end RayClassField
