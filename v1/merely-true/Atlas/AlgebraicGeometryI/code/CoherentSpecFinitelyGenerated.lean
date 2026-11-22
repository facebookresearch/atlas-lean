/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Basic

namespace CoherentSpecFinitelyGenerated

/-- An `R`-module `M` is locally finitely generated if there exists a finite set of elements
of `R` generating the unit ideal such that each corresponding localization of `M` is finitely
generated. -/
def IsLocallyFinitelyGenerated
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (s : Finset R), Ideal.span (s : Set R) = ⊤ ∧
    ∀ (r : s), Module.Finite (Localization.Away r.val)
      (LocalizedModule (Submonoid.powers r.val) M)

/-- Lemma 23 (Lec 12): on `Spec A` the sheaf `M̃` is coherent (i.e. locally finitely generated)
iff the module `M` is finitely generated as an `R`-module. -/
theorem lemma23_coherent_tilde_iff_fg
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    IsLocallyFinitelyGenerated R M ↔ Module.Finite R M := by
  constructor
  ·


    rintro ⟨s, hs, hfin⟩
    exact Module.Finite.of_localizationSpan_finite s hs hfin
  ·

    intro hfg
    refine ⟨{1}, by simp, ?_⟩
    intro ⟨r, hr⟩
    simp at hr; subst hr
    exact Module.Finite.of_isLocalizedModule (Submonoid.powers (1 : R))
      (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)

end CoherentSpecFinitelyGenerated
