/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

universe u

noncomputable section

namespace EGNO.Prop1271


/-- An element `g` of a coalgebra is grouplike if `Δ(g) = g ⊗ g` and `ε(g) = 1`. -/
def IsGrouplike {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g : C) : Prop :=
  Coalgebra.comul (R := R) g = g ⊗ₜ g ∧ Coalgebra.counit (R := R) g = 1

/-- An element `x` of a coalgebra is skew-primitive of type `(g, h)` if
`Δ(x) = x ⊗ g + h ⊗ x` (Definition 1.24.6). -/
def IsSkewPrimitive {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g h x : C) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x

/-- The submodule of skew-primitive elements `Prim_{g,h}(C)` of a coalgebra. -/
def skewPrimitiveSpace {R : Type*} {C : Type*} [CommSemiring R] [AddCommGroup C] [Module R C]
    [Coalgebra R C] (g h : C) : Submodule R C where
  carrier := {x : C | IsSkewPrimitive (R := R) g h x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]; unfold IsSkewPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


section TrivialSkewPrimitive

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The "trivial" skew-primitive subspace `k(h - g)` whose quotient in
`skewPrimitiveSpace g h` is identified with `Ext¹(g, h)`. -/
def trivialSkewPrimitiveSubspace (g h : C) : Submodule k C :=
  Submodule.span k {h - g}

end TrivialSkewPrimitive


section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A representative of a comodule extension of grouplikes `g` by `h`: a skew-primitive
element `x` of type `(g, h)`. -/
structure ComoduleExtension (g h : C) where
  x : C
  skew_prim : IsSkewPrimitive (R := k) g h x

/-- Two comodule extensions are equivalent if their underlying skew-primitive elements
differ by a multiple of `h - g`. -/
def ComoduleExtension.Equiv {g h : C} (E₁ E₂ : ComoduleExtension (k := k) g h) : Prop :=
  E₁.x - E₂.x ∈ trivialSkewPrimitiveSubspace (k := k) g h

/-- Equivalence of comodule extensions is reflexive. -/
theorem ComoduleExtension.Equiv.refl {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExtension.Equiv E E := by
  unfold ComoduleExtension.Equiv
  simp [trivialSkewPrimitiveSubspace]

/-- Equivalence of comodule extensions is symmetric. -/
theorem ComoduleExtension.Equiv.symm {g h : C}
    {E₁ E₂ : ComoduleExtension (k := k) g h} (h_eq : ComoduleExtension.Equiv E₁ E₂) :
    ComoduleExtension.Equiv E₂ E₁ := by
  unfold ComoduleExtension.Equiv at *
  rwa [show E₂.x - E₁.x = -(E₁.x - E₂.x) from (neg_sub E₁.x E₂.x).symm, neg_mem_iff]

/-- Equivalence of comodule extensions is transitive. -/
theorem ComoduleExtension.Equiv.trans {g h : C}
    {E₁ E₂ E₃ : ComoduleExtension (k := k) g h}
    (h₁₂ : ComoduleExtension.Equiv E₁ E₂) (h₂₃ : ComoduleExtension.Equiv E₂ E₃) :
    ComoduleExtension.Equiv E₁ E₃ := by
  unfold ComoduleExtension.Equiv at *
  have : E₁.x - E₃.x = (E₁.x - E₂.x) + (E₂.x - E₃.x) := by abel
  rw [this]
  exact Submodule.add_mem _ h₁₂ h₂₃

/-- Setoid structure on comodule extensions of `g` by `h` given by `ComoduleExtension.Equiv`. -/
instance ComoduleExtension.setoid (g h : C) :
    Setoid (ComoduleExtension (k := k) g h) where
  r := ComoduleExtension.Equiv
  iseqv := {
    refl := ComoduleExtension.Equiv.refl
    symm := ComoduleExtension.Equiv.symm
    trans := ComoduleExtension.Equiv.trans
  }

/-- The space of comodule extensions `Ext¹(g, h)` realized as equivalence classes of
skew-primitive elements. -/
def ComoduleExt1 (g h : C) : Type u :=
  Quotient (ComoduleExtension.setoid (k := k) g h)

end ComoduleExt


section Proof

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

private abbrev SkewQuot (g h : C) :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

private def ext1ToSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h → SkewQuot (k := k) g h :=
  Quotient.lift
    (fun E => Submodule.Quotient.mk (p := Submodule.comap
      (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))
      ⟨E.x, E.skew_prim⟩)
    (by
      intro E₁ E₂ (hE : ComoduleExtension.Equiv E₁ E₂)
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      simp only [Submodule.subtype_apply, Submodule.coe_sub]
      exact hE)

private def skewQuotToExt1 {g h : C} :
    SkewQuot (k := k) g h → ComoduleExt1 (k := k) g h :=
  Quotient.lift
    (fun (p : skewPrimitiveSpace (R := k) g h) =>
      @Quotient.mk _ (ComoduleExtension.setoid (k := k) g h) ⟨p.val, p.property⟩)
    (by
      intro a b hab
      apply Quotient.sound
      show ComoduleExtension.Equiv _ _
      unfold ComoduleExtension.Equiv; simp only
      have hab' : a - b ∈ Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
          (trivialSkewPrimitiveSubspace (k := k) g h) :=
        (Submodule.quotientRel_def _).mp hab
      rw [Submodule.mem_comap] at hab'
      simp only [Submodule.subtype_apply, Submodule.coe_sub] at hab'
      exact hab')

/-- The canonical bijection between `ComoduleExt1 g h` and the quotient
`Prim_{g,h}(C)/k(h-g)`. -/
def ext1EquivSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h ≃ SkewQuot (k := k) g h where
  toFun := ext1ToSkewQuot
  invFun := skewQuotToExt1
  left_inv := by
    intro q; induction q using Quotient.inductionOn with
    | h E => simp only [ext1ToSkewQuot, skewQuotToExt1]; rfl
  right_inv := by
    intro q; induction q using Quotient.inductionOn with
    | h p => simp only [ext1ToSkewQuot, skewQuotToExt1]; rfl

/-- Additive group structure on `ComoduleExt1 g h` transported from the quotient module. -/
noncomputable instance ComoduleExt1.instAddCommGroup {g h : C} :
    AddCommGroup (ComoduleExt1 (k := k) g h) :=
  (ext1EquivSkewQuot (k := k)).addCommGroup

/-- `k`-module structure on `ComoduleExt1 g h` transported from the quotient module. -/
noncomputable instance ComoduleExt1.instModule {g h : C} :
    Module k (ComoduleExt1 (k := k) g h) :=
  Equiv.module k (ext1EquivSkewQuot (k := k))

end Proof

end EGNO.Prop1271


open EGNO.Prop1271 in
/-- Proposition 1.27.1: For grouplike elements `g, h` in a coalgebra, the quotient
`Prim_{g,h}(C)/k(h - g)` is naturally isomorphic to `Ext¹(g, h)`, realized here as
`ComoduleExt1 g h`. -/
theorem EGNO.Proposition_1_27_1
    (k : Type u) [Field k] (C : Type u) [AddCommGroup C] [Module k C] [Coalgebra k C]
    (g h : C) (_hg : IsGrouplike (R := k) g) (_hh : IsGrouplike (R := k) h) :
    Nonempty ((skewPrimitiveSpace (R := k) g h ⧸
        Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
          (trivialSkewPrimitiveSubspace (k := k) g h)) ≃ₗ[k]
      ComoduleExt1 (k := k) g h) :=
  ⟨(Equiv.linearEquiv k ext1EquivSkewQuot).symm⟩
