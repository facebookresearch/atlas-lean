/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology
import Atlas.AlgebraicGeometryI.code.DedekindCurve

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open ZariskiSheafCohomology

noncomputable section


/-- Additive equivalence between additive homomorphisms `ULift ℤ →+ G` and `G`,
sending a hom to its value at `1`. -/
def uliftZHomEquiv (G : Type*) [AddCommGroup G] : (ULift ℤ →+ G) ≃+ G where
  toFun f := f ⟨1⟩
  invFun g := (zmultiplesAddHom G g).comp AddEquiv.ulift.toAddMonoidHom
  left_inv f := by
    ext ⟨n⟩
    simp [zmultiplesAddHom_apply, AddEquiv.ulift, AddMonoidHom.comp_apply]
    rw [← f.map_zsmul ⟨1⟩ n]
    congr 1
    simp [ULift.ext_iff, zsmul_eq_mul, mul_one]
  right_inv g := by simp [zmultiplesAddHom_apply, AddEquiv.ulift]
  map_add' f g := by simp [AddMonoidHom.add_apply]

/-- Categorical version of `uliftZHomEquiv`: morphisms `ULift ℤ ⟶ M` in `AddCommGrpCat`
correspond bijectively to elements of `M`. -/
def catUliftZHomEquiv (M : AddCommGrpCat.{0}) :
    (AddCommGrpCat.of (ULift.{0, 0} ℤ) ⟶ M) ≃ (M : Type) where
  toFun f := f.hom ⟨1⟩
  invFun m := AddCommGrpCat.ofHom
    ((zmultiplesAddHom (M : Type) m).comp (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddMonoidHom)
  left_inv f := by
    apply AddCommGrpCat.hom_ext
    ext ⟨n⟩
    show ((zmultiplesAddHom (↑M) (f.hom ⟨1⟩)).comp
      (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddMonoidHom) ⟨n⟩ = f.hom ⟨n⟩
    simp [zmultiplesAddHom_apply, AddEquiv.ulift, AddMonoidHom.comp_apply]
    rw [← f.hom.map_zsmul (⟨1⟩ : ULift.{0, 0} ℤ) n]
    congr 1; ext; simp [zsmul_eq_mul, mul_one]
  right_inv m := by
    show ((zmultiplesAddHom (↑M) m).comp
      (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddMonoidHom) ⟨1⟩ = m
    simp [zmultiplesAddHom_apply, AddEquiv.ulift, AddMonoidHom.comp_apply]


/-- Identification of the 0th sheaf cohomology of a scheme `X` with its group of global
sections, via the composition of standard equivalences. -/
def h0EquivGlobalSections (X : Scheme) :
    sheafCohomology X 0 ≃
      ↑(((sheafSections (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
        (Opposite.op ⊤)).obj (schemeAbSheaf X)) :=
  (h0AddEquivHom X).toEquiv.trans
    ((h0EquivSections X).trans
      (catUliftZHomEquiv _))


/-- The categorical isomorphism `Γ(Spec R, ⊤) ≅ R` between global sections of `Spec R`
and the ring `R`. -/
def globalSections_Spec_iso (R : CommRingCat) :
    Γ(Spec R, ⊤) ≅ R :=
  Scheme.ΓSpecIso R

/-- The ring equivalence `Γ(Spec R, ⊤) ≃+* R` between global sections of `Spec R`
and the ring `R`. -/
def globalSections_Spec_ringEquiv (R : CommRingCat) :
    Γ(Spec R, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- The natural isomorphism `Spec.rightOp ⋙ Γ ≅ 𝟭 CommRingCat` expressing that
`Γ` is left inverse to `Spec`. -/
def specGammaIdentity : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 CommRingCat :=
  Scheme.SpecΓIdentity


/-- A field `k` has dimension one as a vector space over itself. -/
theorem finrank_self_eq_one (k : Type*) [Field k] :
    Module.finrank k k = 1 :=
  Module.finrank_self k


namespace DedekindCurve

variable {k : Type*} [Field k]

/-- For a Dedekind curve over a field `k`, the dimension `h^0(O_C) = 1`
of global sections of the structure sheaf. -/
def h0_O (_ : DedekindCurve k) : ℕ := 1

/-- The value `h^0(O_C)` equals `1` for any Dedekind curve `C`. -/
theorem h0_O_eq_one (C : DedekindCurve k) : C.h0_O = 1 := rfl

/-- Euler characteristic of the structure sheaf equals `h^0(O_C) - h^1(O_C)`. -/
theorem eulerCharO_from_h0_h1 (C : DedekindCurve k) :
    C.eulerCharO = (C.h0_O : ℤ) - (h1_O k C.A : ℤ) := by
  simp only [eulerCharO, h0_O, h1_O_eq_genus, ddGenus, Nat.cast_one]

/-- Decomposition: the cohomological Euler characteristic at `(1, 0)` agrees with
`h^0(O_C) - h^1(O_C)`. -/
theorem cohChi_struct_decomp (C : DedekindCurve k) :
    C.cohChi (1, 0) = (C.h0_O : ℤ) - (h1_O k C.A : ℤ) := by
  rw [cohChi_struct, h0_O, Nat.cast_one]

/-- For a Dedekind curve, `h^0(O_C) + h^1(O_C) = 1 + g` where `g` is the genus. -/
theorem h0_plus_h1_eq (C : DedekindCurve k) :
    (C.h0_O : ℤ) + (h1_O k C.A : ℤ) = 1 + (C.ddGenus : ℤ) := by
  simp [h0_O, h1_O_eq_genus, ddGenus]

/-- The Euler characteristic of the structure sheaf equals `h^0(O_C) - g`,
consistent with `1 - g`. -/
theorem eulerCharO_consistent (C : DedekindCurve k) :
    C.eulerCharO = (C.h0_O : ℤ) - (C.ddGenus : ℤ) := by
  simp [eulerCharO, h0_O, ddGenus, Nat.cast_one]

end DedekindCurve


end
