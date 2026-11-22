/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.NumberTheory.DirichletCharacter.Basic

abbrev CharacterGroup (G : Type*) [CommGroup G] [Fintype G] := G →* ℂˣ

namespace CharacterGroup

variable {G : Type*} [CommGroup G] [Fintype G]

instance instCommGroup : CommGroup (CharacterGroup G) :=
  inferInstance

instance hasEnoughRootsOfUnity_complex_exponent :
    HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := by
  haveI : NeZero (Monoid.exponent G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  infer_instance

instance instFinite : Finite (CharacterGroup G) :=
  Finite.of_equiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.symm.toEquiv

theorem prop_18_33_mulEquiv : Nonempty (CharacterGroup G ≃* G) :=
  CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ

theorem cor_18_34 (g : G) : g = 1 ↔ ∀ χ : CharacterGroup G, χ g = 1 := by
  constructor
  · rintro rfl; intro χ; exact map_one χ
  · intro h
    exact (CommGroup.forall_apply_eq_apply_iff G (M := ℂ) (g := g) (g' := 1)).mp
      fun φ => by simp [h φ]

theorem cor_18_34_part2 (χ : CharacterGroup G) :
    χ = 1 ↔ ∀ g : G, χ g = 1 := by
  constructor
  · intro h g
    simp [h]
  · intro h
    ext g
    simp [h g]

theorem characters_separate_points :
    (∀ g : G, g = 1 ↔ ∀ χ : CharacterGroup G, χ g = 1) ∧
    (∀ χ : CharacterGroup G, χ = 1 ↔ ∀ g : G, χ g = 1) :=
  ⟨cor_18_34, cor_18_34_part2⟩

end CharacterGroup

open DirichletCharacter in
noncomputable def conductorOfDirichletChar {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) : ℕ :=
  χ.conductor

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

end DirichletCharacter

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]

theorem thm_18_13_existence {n : ℕ} (χ : DirichletCharacter R n) :
    χ.primitiveCharacter.IsPrimitive ∧
    changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ :=
  ⟨χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩

theorem thm_18_13_unique_level {n : ℕ} (χ : DirichletCharacter R n) (hn : n ≠ 0)
    {m : ℕ} (hm : m ∣ n) (χ' : DirichletCharacter R m)
    (hind : changeLevel hm χ' = χ) (hprim : χ'.IsPrimitive) :
    m = χ.conductor := by
  have hm_cond : m ∈ χ.conductorSet := ⟨hm, χ', hind.symm⟩
  have hc_dvd_m : χ.conductor ∣ m := conductor_dvd_of_mem_conductorSet χ hn hm_cond
  have hm_ne : m ≠ 0 := fun h => hn (Nat.eq_zero_of_zero_dvd (h ▸ hm))
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero m := ⟨hm_ne⟩
  have key : χ' = changeLevel hc_dvd_m χ.primitiveCharacter := by
    apply changeLevel_injective hm
    rw [hind, ← changeLevel_trans χ.primitiveCharacter hc_dvd_m hm,
        changeLevel_primitiveCharacter]
  have hft : χ'.FactorsThrough χ.conductor := ⟨hc_dvd_m, χ.primitiveCharacter, key⟩
  have h_cond_le : χ'.conductor ≤ χ.conductor := Nat.sInf_le hft
  rw [(isPrimitive_def χ').mp hprim] at h_cond_le
  exact ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne) hc_dvd_m).antisymm h_cond_le).symm

theorem thm_18_13_unique_char {n : ℕ} (χ : DirichletCharacter R n) (hn : n ≠ 0)
    (hm : χ.conductor ∣ n) (χ' : DirichletCharacter R χ.conductor)
    (hind : changeLevel hm χ' = χ) (hprim : χ'.IsPrimitive) :
    χ' = χ.primitiveCharacter := by
  haveI : NeZero n := ⟨hn⟩
  apply changeLevel_injective hm
  rw [hind, changeLevel_primitiveCharacter]

theorem thm_18_13 {n : ℕ} (χ : DirichletCharacter R n) (hn : n ≠ 0) :

    (χ.primitiveCharacter.IsPrimitive ∧
     changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ) ∧

    (∀ {m : ℕ} (hm : m ∣ n) (χ' : DirichletCharacter R m),
      changeLevel hm χ' = χ → χ'.IsPrimitive →
      ∃ (heq : m = χ.conductor), heq ▸ χ' = χ.primitiveCharacter) := by
  refine ⟨thm_18_13_existence χ, ?_⟩
  intro m hm χ' hind hprim
  have heq : m = χ.conductor := thm_18_13_unique_level χ hn hm χ' hind hprim
  exact ⟨heq, by subst heq; exact thm_18_13_unique_char χ hn hm χ' hind hprim⟩

end DirichletCharacter

open Filter Topology

noncomputable def primeSumOver (S : Set Nat.Primes) (s : ℝ) : ℝ :=
  ∑' (p : S), ((p : ℕ) : ℝ) ^ (-s)

noncomputable def primeSumAll (s : ℝ) : ℝ :=
  ∑' (p : Nat.Primes), ((p : ℕ) : ℝ) ^ (-s)

noncomputable def dirichletDensityRatio (S : Set Nat.Primes) (s : ℝ) : ℝ :=
  primeSumOver S s / primeSumAll s

def HasDirichletDensity (S : Set Nat.Primes) (d : ℝ) : Prop :=
  Tendsto (dirichletDensityRatio S) (nhdsWithin 1 (Set.Ioi 1)) (nhds d)

noncomputable def dirichletDensity (S : Set Nat.Primes) : ℝ :=
  (nhdsWithin 1 (Set.Ioi 1)).limUnder (dirichletDensityRatio S)
