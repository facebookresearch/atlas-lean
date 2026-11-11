/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Order.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient

open scoped Nat
open Finset Real Filter Asymptotics


open ArithmeticFunction


def ArithFuncZ : Type := ℤ → ℂ

namespace ArithFuncZ

instance : CoeFun ArithFuncZ (fun _ => ℤ → ℂ) := ⟨id⟩

structure IsMultiplicative (f : ArithFuncZ) : Prop where
  map_one : f 1 = 1
  map_mul_of_coprime : ∀ m n : ℤ, Int.gcd m n = 1 → f (m * n) = f m * f n

structure IsTotallyMultiplicative (f : ArithFuncZ) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ m n : ℤ, f (m * n) = f m * f n

def IsPeriodic (f : ArithFuncZ) (m : ℤ) : Prop :=
  ∀ n : ℤ, f (n + m) = f n

noncomputable def period (f : ArithFuncZ) : ℤ := by
  classical
  exact if h : ∃ m : ℕ, 0 < m ∧ f.IsPeriodic (m : ℤ) then (Nat.find h : ℤ) else 0

structure IsDirichletCharacter (χ : ArithFuncZ) (q : ℤ) : Prop where
  modulus_pos : 0 < q
  totallyMultiplicative : IsTotallyMultiplicative χ
  periodic : IsPeriodic χ q

structure IsDirichletCharacterMod (χ : ArithFuncZ) (m : ℤ) : Prop extends IsDirichletCharacter χ m where
  vanish_iff : ∀ n : ℤ, χ n = 0 ↔ Int.gcd n m > 1

end ArithFuncZ


abbrev ArithFunc := ArithmeticFunction ℂ

structure ArithFunc.IsTotallyMultiplicative (f : ArithFunc) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ m n : ℕ, f (m * n) = f m * f n

def ArithFunc.IsPeriodic (f : ArithFunc) (m : ℕ) : Prop :=
  ∀ n : ℕ, f (n + m) = f n

noncomputable def ArithFunc.period (f : ArithFunc) : ℕ := by
  classical
  exact if h : ∃ m, 0 < m ∧ f.IsPeriodic m then Nat.find h else 0


structure ArithFunc.IsDirichletCharacter (χ : ArithFunc) : Prop where
  totallyMultiplicative : χ.IsTotallyMultiplicative
  periodic : ∃ m, 0 < m ∧ χ.IsPeriodic m


noncomputable def ArithFunc.one : ArithFunc :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ)

noncomputable def ArithFunc.vonMangoldt : ArithFunc :=
  Complex.ofRealHom.toZeroHom.comp ArithmeticFunction.vonMangoldt

def DirichletCharacter.IsInducedBy {R : Type*} [CommMonoidWithZero R]
    {m₁ m₂ : ℕ} (χ₂ : DirichletCharacter R m₂) (χ₁ : DirichletCharacter R m₁)
    (h : m₁ ∣ m₂) : Prop :=
  χ₂ = DirichletCharacter.changeLevel h χ₁

open DirichletCharacter in

open DirichletCharacter in

open DirichletCharacter in
theorem dirichletChar_factorsThrough_iff_ker_and_unique {R : Type*} [CommMonoidWithZero R]
    {m₂ : ℕ} [NeZero m₂] (χ₂ : DirichletCharacter R m₂) {m₁ : ℕ} (h : m₁ ∣ m₂) :
    (χ₂.FactorsThrough m₁ ↔ (ZMod.unitsMap h).ker ≤ χ₂.toUnitHom.ker) ∧
    (χ₂.FactorsThrough m₁ → ∃! χ₁ : DirichletCharacter R m₁, χ₂ = changeLevel h χ₁) :=
  ⟨factorsThrough_iff_ker_unitsMap h, fun hf => hf.existsUnique⟩


def DirichletCharacter.IsPrincipal {R : Type*} [CommMonoidWithZero R]
    {m : ℕ} (χ : DirichletCharacter R m) : Prop :=
  χ = 1

noncomputable def principalDirichletChar (R : Type*) [CommMonoidWithZero R] (m : ℕ) :
    DirichletCharacter R m :=
  1
