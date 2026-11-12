/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.DirichletCharacters

open DirichletCharacter

structure PrimCharDvd (R : Type*) [CommMonoidWithZero R] (m : ℕ) where
  d : ℕ
  hdvd : d ∣ m
  χ : DirichletCharacter R d
  hprim : χ.IsPrimitive

namespace PrimCharDvd

variable {R : Type*} [CommMonoidWithZero R] {m : ℕ}

theorem ext' {p q : PrimCharDvd R m} (hd : p.d = q.d)
    (hχ : hd ▸ p.χ = q.χ) : p = q := by
  rcases p with ⟨d₁, hd₁, χ₁, hp₁⟩
  rcases q with ⟨d₂, hd₂, χ₂, hp₂⟩
  dsimp at hd hχ
  subst hd
  simp only at hχ
  subst hχ
  rfl

end PrimCharDvd

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]


lemma changeLevel_cast_eq {m d₁ d₂ : ℕ} (heq : d₁ = d₂)
    (hd₂ : d₂ ∣ m) (ψ : DirichletCharacter R d₁) :
    changeLevel hd₂ (heq ▸ ψ) = changeLevel (show d₁ ∣ m from heq ▸ hd₂) ψ := by
  subst heq; rfl


noncomputable def toPrimCharDvd {m : ℕ} (χ : DirichletCharacter R m) : PrimCharDvd R m where
  d := χ.conductor
  hdvd := χ.conductor_dvd_level
  χ := χ.primitiveCharacter
  hprim := χ.primitiveCharacter_isPrimitive


noncomputable def fromPrimCharDvd {m : ℕ} (p : PrimCharDvd R m) : DirichletCharacter R m :=
  changeLevel p.hdvd p.χ


theorem fromPrimCharDvd_toPrimCharDvd {m : ℕ} (χ : DirichletCharacter R m) :
    fromPrimCharDvd (toPrimCharDvd χ) = χ := by
  unfold fromPrimCharDvd toPrimCharDvd
  exact χ.changeLevel_primitiveCharacter


theorem conductor_changeLevel_of_isPrimitive {m d : ℕ} (hm : m ≠ 0)
    (hd : d ∣ m) (ψ : DirichletCharacter R d) (hprim : ψ.IsPrimitive) :
    (changeLevel hd ψ).conductor = d := by
  haveI : NeZero m := ⟨hm⟩
  have hd_ne : d ≠ 0 := fun h => hm (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hmem : d ∈ (changeLevel hd ψ).conductorSet := ⟨hd, ψ, rfl⟩
  have hcond_dvd : (changeLevel hd ψ).conductor ∣ d :=
    conductor_dvd_of_mem_conductorSet _ hm hmem
  have hft : ψ.FactorsThrough (changeLevel hd ψ).conductor := by
    refine ⟨hcond_dvd, (changeLevel hd ψ).primitiveCharacter, ?_⟩
    haveI : NeZero d := ⟨hd_ne⟩
    apply changeLevel_injective hd
    rw [← changeLevel_trans _ hcond_dvd hd, changeLevel_primitiveCharacter]
  have hle : ψ.conductor ≤ (changeLevel hd ψ).conductor := Nat.sInf_le hft
  rw [show ψ.conductor = d from hprim] at hle
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hd_ne) hcond_dvd).antisymm hle


theorem toPrimCharDvd_fromPrimCharDvd {m : ℕ} (hm : m ≠ 0) (p : PrimCharDvd R m) :
    toPrimCharDvd (fromPrimCharDvd p) = p := by
  have heq_d : (toPrimCharDvd (fromPrimCharDvd p)).d = p.d :=
    conductor_changeLevel_of_isPrimitive hm p.hdvd p.χ p.hprim
  apply PrimCharDvd.ext' heq_d
  haveI : NeZero m := ⟨hm⟩
  have hd_ne : p.d ≠ 0 := fun h => hm (Nat.eq_zero_of_zero_dvd (h ▸ p.hdvd))
  haveI : NeZero p.d := ⟨hd_ne⟩
  apply changeLevel_injective p.hdvd
  rw [changeLevel_cast_eq heq_d p.hdvd]
  change changeLevel _ (fromPrimCharDvd p).primitiveCharacter = fromPrimCharDvd p
  exact (fromPrimCharDvd p).changeLevel_primitiveCharacter


noncomputable def cor_18_16_M_equivMul_Ghat (m : ℕ) :
    DirichletCharacter R m ≃* ((ZMod m)ˣ →* Rˣ) :=
  MulChar.mulEquivToUnitHom


noncomputable def cor_18_16_M_equiv_X (m : ℕ) (hm : m ≠ 0) :
    DirichletCharacter R m ≃ PrimCharDvd R m where
  toFun := toPrimCharDvd
  invFun := fromPrimCharDvd
  left_inv := fromPrimCharDvd_toPrimCharDvd
  right_inv := toPrimCharDvd_fromPrimCharDvd hm

end DirichletCharacter
