/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.GradedVec
import Mathlib.GroupTheory.GroupAction.Basic

set_option maxHeartbeats 800000

open CategoryTheory

universe u v

section GroupCochains

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- A 1-cochain on the group `G` with values in the commutative group `A`: a function
`G → A`. -/
def Cochain1 := G → A

/-- A 2-cochain on the group `G` with values in the commutative group `A`: a function
`G × G → A`. -/
def Cochain2 := G → G → A

/-- A 3-cochain on the group `G` with values in the commutative group `A`: a function
`G × G × G → A`. -/
def Cochain3' := G → G → G → A

/-- A 4-cochain on the group `G` with values in the commutative group `A`: a function
`G⁴ → A`. -/
def Cochain4 := G → G → G → G → A

/-- The group coboundary `d¹η(g, h) = η(g) η(h) η(gh)⁻¹` sending a 1-cochain to a
2-cochain. -/
def d1 (η : Cochain1 G A) : Cochain2 G A :=
  fun g h => η g * η h * (η (g * h))⁻¹

/-- The group coboundary `d²μ(g, h, l) = μ(h,l) μ(g, hl) μ(gh, l)⁻¹ μ(g, h)⁻¹` sending a
2-cochain to a 3-cochain. -/
def d2 (μ : Cochain2 G A) : Cochain3' G A :=
  fun g h l => μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹

/-- The group coboundary `d³ω` sending a 3-cochain to a 4-cochain. -/
def d3 (ω : Cochain3' G A) : Cochain4 G A :=
  fun g₁ g₂ g₃ g₄ =>
    ω g₂ g₃ g₄ * ω g₁ (g₂ * g₃) g₄ * ω g₁ g₂ g₃ *
    (ω g₁ g₂ (g₃ * g₄))⁻¹ * (ω (g₁ * g₂) g₃ g₄)⁻¹

end GroupCochains

section CommGroupLemmas

variable {A : Type*} [CommGroup A]

/-- Rearrangement lemma: `a * b * c * d⁻¹ * e⁻¹ = 1` is equivalent to `e * d = a * b * c`
in a commutative group. -/
lemma prod5_eq_one_iff {a b c d e : A} :
    a * b * c * d⁻¹ * e⁻¹ = 1 ↔ e * d = a * b * c := by
  rw [eq_comm (a := e * d)]
  show a * b * c * d⁻¹ * e⁻¹ = 1 ↔ a * b * c = e * d
  rw [show (a * b * c * d⁻¹ * e⁻¹ : A) = a * b * c / (e * d) from by
    simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]]
  exact div_eq_one

/-- Rearrangement lemma: `a * b * c⁻¹ * d⁻¹ = 1` is equivalent to `d * c = a * b` in a
commutative group. -/
lemma prod4_eq_one_iff {a b c d : A} :
    a * b * c⁻¹ * d⁻¹ = 1 ↔ d * c = a * b := by
  rw [eq_comm (a := d * c)]
  show a * b * c⁻¹ * d⁻¹ = 1 ↔ a * b = d * c
  rw [show (a * b * c⁻¹ * d⁻¹ : A) = a * b / (d * c) from by
    simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]]
  exact div_eq_one

/-- Rearrangement lemma in a commutative group: `x * (a * b * c⁻¹ * d⁻¹) * d * c = x * a * b`. -/
lemma comm_group_rearrange {x a b c d : A} :
    x * (a * b * c⁻¹ * d⁻¹) * d * c = x * a * b := by
  simp [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel]

end CommGroupLemmas

section CoboundarySquare

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- The cochain identity `d² ∘ d¹ = 0`: applying `d²` to a coboundary `d¹η` yields the
trivial 3-cochain. -/
theorem d2_comp_d1 (η : Cochain1 G A) (g h l : G) :
    d2 G A (d1 G A η) g h l = 1 := by
  unfold d2 d1
  rw [show g * (h * l) = g * h * l from (mul_assoc g h l).symm]
  set a := η g; set b := η h; set c := η l
  set d := η (h * l); set e := η (g * h * l); set f := η (g * h)

  simp only [mul_inv_rev, inv_inv]

  calc b * c * d⁻¹ * (a * d * e⁻¹) * (e * (c⁻¹ * f⁻¹)) * (f * (b⁻¹ * a⁻¹))
      = (a * a⁻¹) * (b * b⁻¹) * (c * c⁻¹) * (d * d⁻¹) * (e * e⁻¹) * (f * f⁻¹) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
      _ = 1 := by simp [mul_inv_cancel]

/-- `d¹` of the pointwise inverse of a 1-cochain is the pointwise inverse of `d¹`. -/
lemma d1_inv (η : Cochain1 G A) (g h : G) :
    d1 G A (fun x => (η x)⁻¹) g h = (d1 G A η g h)⁻¹ := by
  simp [d1, mul_inv_rev, mul_comm, inv_inv]

/-- `d²` of the pointwise inverse of a 2-cochain is the pointwise inverse of `d²`. -/
lemma d2_inv (μ : Cochain2 G A) (g h l : G) :
    d2 G A (fun x y => (μ x y)⁻¹) g h l = (d2 G A μ g h l)⁻¹ := by
  simp [d2, mul_inv_rev, mul_comm, mul_left_comm, inv_inv, mul_assoc]

end CoboundarySquare

section Cohomology

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- A 2-cochain is a 2-cocycle if its coboundary `d²μ` vanishes identically. -/
def IsCocycle2 (μ : Cochain2 G A) : Prop :=
  ∀ g h l : G, d2 G A μ g h l = 1

/-- A 2-cochain is a 2-coboundary if it equals `d¹η` for some 1-cochain `η`. -/
def IsCoboundary2 (μ : Cochain2 G A) : Prop :=
  ∃ η : Cochain1 G A, ∀ g h, μ g h = d1 G A η g h

/-- A 3-cochain is a 3-cocycle if its coboundary `d³ω` vanishes identically. -/
def IsCocycle3 (ω : Cochain3' G A) : Prop :=
  ∀ g₁ g₂ g₃ g₄ : G, d3 G A ω g₁ g₂ g₃ g₄ = 1

/-- A 3-cochain is a 3-coboundary if it equals `d²μ` for some 2-cochain `μ`. -/
def IsCoboundary3 (ω : Cochain3' G A) : Prop :=
  ∃ μ : Cochain2 G A, ∀ g h l, ω g h l = d2 G A μ g h l

/-- Reformulation of the 3-cocycle condition in the form used to define monoidal
associativity: `ω(g₁g₂, g₃, g₄) ω(g₁, g₂, g₃g₄) = ω(g₁, g₂, g₃) ω(g₁, g₂g₃, g₄) ω(g₂, g₃, g₄)`. -/
theorem isCocycle3_iff_cocycleCond (ω : Cochain3' G A) :
    IsCocycle3 G A ω ↔ ∀ g₁ g₂ g₃ g₄ : G,
      ω (g₁ * g₂) g₃ g₄ * ω g₁ g₂ (g₃ * g₄) =
      ω g₁ g₂ g₃ * ω g₁ (g₂ * g₃) g₄ * ω g₂ g₃ g₄ := by
  unfold IsCocycle3 d3
  constructor
  · intro h g₁ g₂ g₃ g₄
    have := prod5_eq_one_iff.mp (h g₁ g₂ g₃ g₄)

    rw [this]
    simp [mul_comm, mul_left_comm]
  · intro h g₁ g₂ g₃ g₄
    rw [prod5_eq_one_iff]
    have := h g₁ g₂ g₃ g₄
    rw [this]
    simp [mul_comm, mul_left_comm]

/-- Reformulation of the 2-cocycle condition: `μ(g, h) μ(gh, l) = μ(h, l) μ(g, hl)`. -/
theorem isCocycle2_iff_assoc (μ : Cochain2 G A) :
    IsCocycle2 G A μ ↔ ∀ g h l : G,
      μ g h * μ (g * h) l = μ h l * μ g (h * l) := by
  unfold IsCocycle2 d2
  constructor
  · intro hμ g h l
    have := hμ g h l
    rw [prod4_eq_one_iff] at this
    exact this
  · intro hμ g h l
    rw [prod4_eq_one_iff]
    exact hμ g h l

/-- Two 2-cochains are cohomologous if they differ by a coboundary `d¹η`. -/
def Cohomologous2 (μ₁ μ₂ : Cochain2 G A) : Prop :=
  ∃ η : Cochain1 G A, ∀ g h : G, μ₂ g h = μ₁ g h * d1 G A η g h

/-- Two 3-cochains are cohomologous if they differ by a coboundary `d²μ`. -/
def Cohomologous3 (ω₁ ω₂ : Cochain3' G A) : Prop :=
  ∃ μ : Cochain2 G A, ∀ g h l : G, ω₂ g h l = ω₁ g h l * d2 G A μ g h l

/-- The equivalence relation on 2-cochains given by being cohomologous, packaged as a
`Setoid`. -/
def cohomologous2Setoid : Setoid (Cochain2 G A) where
  r := Cohomologous2 G A
  iseqv := {
    refl := fun μ => ⟨fun _ => 1, fun g h => by simp [d1]⟩
    symm := fun {μ₁ μ₂} ⟨η, hη⟩ =>
      ⟨fun g => (η g)⁻¹, fun g h => by
        have := hη g h
        rw [this, d1_inv, mul_inv_cancel_right]⟩
    trans := fun {μ₁ μ₂ μ₃} ⟨η₁, h₁⟩ ⟨η₂, h₂⟩ =>
      ⟨fun g => η₁ g * η₂ g, fun g h => by
        rw [h₂ g h, h₁ g h]; simp [d1, mul_assoc, mul_comm, mul_left_comm]⟩
  }

/-- The equivalence relation on 3-cochains given by being cohomologous, packaged as a
`Setoid`. -/
def cohomologous3Setoid : Setoid (Cochain3' G A) where
  r := Cohomologous3 G A
  iseqv := {
    refl := fun ω => ⟨fun _ _ => 1, fun g h l => by simp [d2]⟩
    symm := fun {ω₁ ω₂} ⟨μ, hμ⟩ =>
      ⟨fun g h => (μ g h)⁻¹, fun g h l => by
        have := hμ g h l
        rw [this, d2_inv, mul_inv_cancel_right]⟩
    trans := fun {ω₁ ω₂ ω₃} ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩ =>
      ⟨fun g h => μ₁ g h * μ₂ g h, fun g h l => by
        rw [h₂ g h l, h₁ g h l]; simp [d2, mul_assoc, mul_comm, mul_left_comm]⟩
  }

/-- The second group cohomology `H²(G, A)` realised as the quotient of 2-cochains by the
cohomologous relation. -/
def H2 := Quotient (cohomologous2Setoid G A)

/-- The third group cohomology `H³(G, A)` realised as the quotient of 3-cochains by the
cohomologous relation. -/
def H3 := Quotient (cohomologous3Setoid G A)

end Cohomology

section MonoidalStructureFromCocycle

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

end MonoidalStructureFromCocycle

section MonoidalFunctors

variable (G₁ : Type u) [Group G₁] (G₂ : Type u) [Group G₂]
variable (A : Type v) [CommGroup A]

/-- The pullback of a 3-cochain on `G₂` along a group homomorphism `f : G₁ →* G₂`. -/
def pullback3 (f : G₁ →* G₂) (ω : Cochain3' G₂ A) : Cochain3' G₁ A :=
  fun g h l => ω (f g) (f h) (f l)

/-- The compatibility condition relating the 2-cochain data `μ` of a monoidal functor to
the source and target 3-cocycles, expressing the hexagon-type axiom of EGNO §1.7. -/
def IsMonoidalFunctorData (ω₁ : Cochain3' G₁ A) (ω₂ : Cochain3' G₂ A)
    (f : G₁ →* G₂) (μ : Cochain2 G₁ A) : Prop :=
  ∀ g h l : G₁,
    ω₁ g h l * μ h l * μ g (h * l) = ω₂ (f g) (f h) (f l) * μ g h * μ (g * h) l

/-- Equivalent reformulation: `μ` witnesses that the pullback of `ω₂` along `f` and the
3-cocycle `ω₁` are cohomologous via `d²μ`. -/
theorem isMonoidalFunctorData_iff_pullback (ω₁ : Cochain3' G₁ A) (ω₂ : Cochain3' G₂ A)
    (f : G₁ →* G₂) (μ : Cochain2 G₁ A) :
    IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f μ ↔
    ∀ g h l : G₁, pullback3 G₁ G₂ A f ω₂ g h l = ω₁ g h l * d2 G₁ A μ g h l := by
  unfold IsMonoidalFunctorData pullback3 d2
  constructor
  ·

    intro hnat g h l
    have := hnat g h l

    calc ω₂ (f g) (f h) (f l)
        = ω₂ (f g) (f h) (f l) * μ g h * μ (g * h) l * (μ (g * h) l)⁻¹ * (μ g h)⁻¹ := by
          simp [mul_assoc, mul_inv_cancel]
      _ = ω₁ g h l * μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹ := by rw [← this]
      _ = ω₁ g h l * (μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
  ·

    intro hpb g h l
    have := hpb g h l

    calc ω₁ g h l * μ h l * μ g (h * l)
        = ω₁ g h l * (μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹) * μ g h * μ (g * h) l :=
          comm_group_rearrange.symm
      _ = ω₂ (f g) (f h) (f l) * μ g h * μ (g * h) l := by rw [← this]

/-- A monoidal functor `(G₁, ω₁) → (G₂, ω₂)` with underlying group homomorphism `f` exists
if and only if `ω₁` and the pullback of `ω₂` are cohomologous. -/
theorem monoidalFunctor_exists_iff_cohomologous (ω₁ : Cochain3' G₁ A) (ω₂ : Cochain3' G₂ A)
    (f : G₁ →* G₂) :
    (∃ μ : Cochain2 G₁ A, IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f μ) ↔
    Cohomologous3 G₁ A ω₁ (pullback3 G₁ G₂ A f ω₂) := by
  constructor
  ·

    rintro ⟨μ, hμ⟩
    exact ⟨μ, fun g h l =>
      ((isMonoidalFunctorData_iff_pullback G₁ G₂ A ω₁ ω₂ f μ).mp hμ) g h l⟩
  ·

    rintro ⟨μ, hμ⟩
    exact ⟨μ, (isMonoidalFunctorData_iff_pullback G₁ G₂ A ω₁ ω₂ f μ).mpr hμ⟩

end MonoidalFunctors

section MonoidalNatTrans

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- The compatibility condition `η(g) η(h) μ(g,h) = μ'(g,h) η(gh)` on a 1-cochain `η`
relating two 2-cochains `μ` and `μ'`; this is the condition that `η` is a monoidal natural
transformation between the corresponding monoidal structures. -/
def IsMonoidalNatTransData (μ μ' : Cochain2 G A) (η : Cochain1 G A) : Prop :=
  ∀ g h : G, η g * η h * μ g h = μ' g h * η (g * h)

/-- The compatibility condition for `η` is equivalent to `μ'` being `μ` shifted by `d¹η`. -/
lemma isMonoidalNatTransData_iff_coboundary (μ μ' : Cochain2 G A) (η : Cochain1 G A) :
    IsMonoidalNatTransData G A μ μ' η ↔
    ∀ g h : G, μ' g h = μ g h * d1 G A η g h := by
  unfold IsMonoidalNatTransData d1
  constructor
  · intro H g h


    have key : μ' g h * η (g * h) = μ g h * η g * η h := by
      rw [← H g h]; simp [mul_comm, mul_left_comm]
    calc μ' g h = μ' g h * η (g * h) * (η (g * h))⁻¹ := by
            simp
          _ = μ g h * η g * η h * (η (g * h))⁻¹ := by rw [key]
          _ = μ g h * (η g * η h * (η (g * h))⁻¹) := by
            simp [mul_assoc]
  · intro H g h

    rw [H g h]
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- A monoidal natural transformation between the monoidal structures on `Vec_G` defined
by `μ` and `μ'` exists if and only if `μ` and `μ'` are cohomologous as 2-cochains. -/
theorem monoidalNatTrans_iff_cohomologous2 (μ μ' : Cochain2 G A) :
    (∃ η : Cochain1 G A, IsMonoidalNatTransData G A μ μ' η) ↔
    Cohomologous2 G A μ μ' := by
  unfold Cohomologous2
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨η, (isMonoidalNatTransData_iff_coboundary G A μ μ' η).mp hη⟩
  · rintro ⟨η, hη⟩
    exact ⟨η, (isMonoidalNatTransData_iff_coboundary G A μ μ' η).mpr hη⟩

end MonoidalNatTrans

section Classification

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- A monoidal natural isomorphism is monoidal natural transformation data `η` together
with a pointwise inverse 1-cochain `η_inv`. -/
def IsMonoidalNatIso (μ μ' : Cochain2 G A) (η : Cochain1 G A) : Prop :=
  IsMonoidalNatTransData G A μ μ' η ∧
  ∃ η_inv : Cochain1 G A, ∀ g : G, η g * η_inv g = 1 ∧ η_inv g * η g = 1

/-- Any monoidal natural transformation data `η` is automatically a monoidal natural
isomorphism, since values in a commutative group are always invertible. -/
lemma isMonoidalNatIso_of_isMonoidalNatTransData (μ μ' : Cochain2 G A)
    (η : Cochain1 G A) (h : IsMonoidalNatTransData G A μ μ' η) :
    IsMonoidalNatIso G A μ μ' η :=
  ⟨h, fun _ => (η _)⁻¹, fun _ => ⟨mul_inv_cancel _, inv_mul_cancel _⟩⟩

/-- A monoidal natural isomorphism between the monoidal structures defined by `μ` and `μ'`
exists if and only if `μ` and `μ'` are cohomologous. -/
theorem monoidal_iso_iff_cohomologous2 (μ μ' : Cochain2 G A) :
    (∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔
    Cohomologous2 G A μ μ' := by
  constructor
  ·
    rintro ⟨η, h_trans, _⟩
    exact (monoidalNatTrans_iff_cohomologous2 G A μ μ').mp ⟨η, h_trans⟩
  ·
    intro h_cohom
    obtain ⟨η, hη⟩ := (monoidalNatTrans_iff_cohomologous2 G A μ μ').mpr h_cohom
    exact ⟨η, isMonoidalNatIso_of_isMonoidalNatTransData G A μ μ' η hη⟩

/-- The classes of monoidal auto-equivalences with the same underlying monoidal structure
are classified by `H²(G, A)`. -/
theorem monoidal_autoequiv_classes_H2 (μ₁ μ₂ : Cochain2 G A) :
    (∃ η : Cochain1 G A, ∀ g h : G, μ₂ g h = μ₁ g h * d1 G A η g h) ↔
    @Quotient.mk _ (cohomologous2Setoid G A) μ₁ =
    @Quotient.mk _ (cohomologous2Setoid G A) μ₂ := by
  constructor
  · intro ⟨η, hη⟩
    apply Quotient.sound
    exact ⟨η, hη⟩
  · intro h
    exact Quotient.exact h

/-- Pullback along the identity homomorphism leaves a 3-cochain unchanged. -/
lemma pullback3_id (ω : Cochain3' G A) :
    pullback3 G G A (MonoidHom.id G) ω = ω := by
  funext g h l
  simp [pullback3]

/-- A monoidal equivalence (over the identity homomorphism) between `(G, ω₁)` and
`(G, ω₂)` exists if and only if `ω₁` and `ω₂` are cohomologous as 3-cochains. -/
theorem monoidal_equiv_iff_cohomologous3 (ω₁ ω₂ : Cochain3' G A) :
    (∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔
    Cohomologous3 G A ω₁ ω₂ := by
  rw [monoidalFunctor_exists_iff_cohomologous G G A ω₁ ω₂ (MonoidHom.id G),
      pullback3_id G A ω₂]

/-- Monoidal structures on the category of `G`-graded vector spaces with values in `A` are
parametrized by `H³(G, A)`. -/
theorem monoidal_structure_parametrized_by_H3 (ω₁ ω₂ : Cochain3' G A) :
    (∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔
    @Quotient.mk _ (cohomologous3Setoid G A) ω₁ =
    @Quotient.mk _ (cohomologous3Setoid G A) ω₂ := by
  rw [monoidal_equiv_iff_cohomologous3 G A ω₁ ω₂]
  constructor
  · intro h
    exact Quotient.sound h
  · intro h
    exact Quotient.exact h

end Classification

section GradedVecConnection

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

/-- Repackage a 3-cocycle as a `GroupCocycle3`, the structure consumed by the
`GradedVec` machinery to produce a monoidal structure on graded vector spaces. -/
def groupCocycle3_of_isCocycle3 (ω : Cochain3' G A) (h : IsCocycle3 G A ω) :
    GroupCocycle3 G A where
  toFun := ω
  cocycle_cond := (isCocycle3_iff_cocycleCond G A ω).mp h

end GradedVecConnection

section MonoidalFunctorComposition

/-- The identity homomorphism together with the trivial 2-cochain provides identity
monoidal functor data on `(G, ω)`. -/
theorem isMonoidalFunctorData_id (G : Type u) [Group G] (A : Type v) [CommGroup A]
    (ω : Cochain3' G A) :
    IsMonoidalFunctorData G G A ω ω (MonoidHom.id G) (fun _ _ => 1) := by
  intro g h l
  simp [MonoidHom.id_apply]

/-- Composition of 2-cochains along a group homomorphism `f₁ : G₁ →* G₂`: the
2-cochain `μ₂(f₁ g, f₁ h) * μ₁(g, h)` on `G₁`. -/
def compCochain2 {G₁ G₂ : Type u} [Group G₁] [Group G₂] {A : Type v} [CommGroup A]
    (f₁ : G₁ →* G₂) (μ₁ : Cochain2 G₁ A) (μ₂ : Cochain2 G₂ A) : Cochain2 G₁ A :=
  fun g h => μ₂ (f₁ g) (f₁ h) * μ₁ g h

/-- Composition of monoidal functor data: composing the underlying group homomorphisms
together with `compCochain2` yields monoidal functor data for the composite. -/
theorem isMonoidalFunctorData_comp {G₁ G₂ G₃ : Type u} [Group G₁] [Group G₂] [Group G₃]
    {A : Type v} [CommGroup A]
    {ω₁ : Cochain3' G₁ A} {ω₂ : Cochain3' G₂ A} {ω₃ : Cochain3' G₃ A}
    {f₁ : G₁ →* G₂} {f₂ : G₂ →* G₃} {μ₁ : Cochain2 G₁ A} {μ₂ : Cochain2 G₂ A}
    (h₁ : IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f₁ μ₁)
    (h₂ : IsMonoidalFunctorData G₂ G₃ A ω₂ ω₃ f₂ μ₂) :
    IsMonoidalFunctorData G₁ G₃ A ω₁ ω₃ (f₂.comp f₁) (compCochain2 f₁ μ₁ μ₂) := by
  intro g h l
  unfold IsMonoidalFunctorData at *
  simp only [compCochain2, MonoidHom.comp_apply] at *
  have eq₁ := h₁ g h l
  have eq₂ := h₂ (f₁ g) (f₁ h) (f₁ l)
  rw [← map_mul f₁ h l, ← map_mul f₁ g h] at eq₂
  calc ω₁ g h l * (μ₂ (f₁ h) (f₁ l) * μ₁ h l) * (μ₂ (f₁ g) (f₁ (h * l)) * μ₁ g (h * l))
      = (ω₁ g h l * μ₁ h l * μ₁ g (h * l)) *
        (μ₂ (f₁ h) (f₁ l) * μ₂ (f₁ g) (f₁ (h * l))) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (ω₂ (f₁ g) (f₁ h) (f₁ l) * μ₁ g h * μ₁ (g * h) l) *
        (μ₂ (f₁ h) (f₁ l) * μ₂ (f₁ g) (f₁ (h * l))) := by rw [eq₁]
    _ = (ω₂ (f₁ g) (f₁ h) (f₁ l) * μ₂ (f₁ h) (f₁ l) * μ₂ (f₁ g) (f₁ (h * l))) *
        (μ₁ g h * μ₁ (g * h) l) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ = (ω₃ (f₂ (f₁ g)) (f₂ (f₁ h)) (f₂ (f₁ l)) * μ₂ (f₁ g) (f₁ h) * μ₂ (f₁ (g * h)) (f₁ l)) *
        (μ₁ g h * μ₁ (g * h) l) := by rw [eq₂]
    _ = ω₃ (f₂ (f₁ g)) (f₂ (f₁ h)) (f₂ (f₁ l)) *
        (μ₂ (f₁ g) (f₁ h) * μ₁ g h) * (μ₂ (f₁ (g * h)) (f₁ l) * μ₁ (g * h) l) := by
          simp [mul_assoc, mul_comm, mul_left_comm]

/-- Bundled data of a monoidal functor from `(G₁, ω₁)` to `(G₂, ω₂)`: a group
homomorphism `f`, a 2-cochain `μ`, and the monoidal compatibility condition. -/
structure MonoidalFunctorCocycleData (G₁ G₂ : Type u) [Group G₁] [Group G₂]
    (A : Type v) [CommGroup A] (ω₁ : Cochain3' G₁ A) (ω₂ : Cochain3' G₂ A) where
  f : G₁ →* G₂
  μ : Cochain2 G₁ A
  isMonoidal : IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f μ

/-- The identity monoidal functor on `(G, ω)`. -/
def MonoidalFunctorCocycleData.id (G : Type u) [Group G] (A : Type v) [CommGroup A]
    (ω : Cochain3' G A) : MonoidalFunctorCocycleData G G A ω ω where
  f := MonoidHom.id G
  μ := fun _ _ => 1
  isMonoidal := isMonoidalFunctorData_id G A ω

/-- Composition of monoidal functor cocycle data. -/
def MonoidalFunctorCocycleData.comp {G₁ G₂ G₃ : Type u}
    [Group G₁] [Group G₂] [Group G₃]
    {A : Type v} [CommGroup A]
    {ω₁ : Cochain3' G₁ A} {ω₂ : Cochain3' G₂ A} {ω₃ : Cochain3' G₃ A}
    (D₁ : MonoidalFunctorCocycleData G₁ G₂ A ω₁ ω₂)
    (D₂ : MonoidalFunctorCocycleData G₂ G₃ A ω₂ ω₃) :
    MonoidalFunctorCocycleData G₁ G₃ A ω₁ ω₃ where
  f := D₂.f.comp D₁.f
  μ := compCochain2 D₁.f D₁.μ D₂.μ
  isMonoidal := isMonoidalFunctorData_comp D₁.isMonoidal D₂.isMonoidal

end MonoidalFunctorComposition

/-- EGNO Proposition 1.7.1 (i): monoidal natural transformations between the monoidal
structures defined by `μ` and `μ'` exist iff `μ` and `μ'` are cohomologous as 2-cochains. -/
theorem Proposition_1_7_1_i (G : Type u) [Group G] (A : Type v) [CommGroup A]
    (μ μ' : Cochain2 G A) :
    (∃ η : Cochain1 G A, IsMonoidalNatTransData G A μ μ' η) ↔
    Cohomologous2 G A μ μ' :=
  monoidalNatTrans_iff_cohomologous2 G A μ μ'

/-- EGNO Proposition 1.7.1 (ii): monoidal natural isomorphisms exist iff `μ` and `μ'` are
cohomologous as 2-cochains. -/
theorem Proposition_1_7_1_ii (G : Type u) [Group G] (A : Type v) [CommGroup A]
    (μ μ' : Cochain2 G A) :
    (∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔
    Cohomologous2 G A μ μ' :=
  monoidal_iso_iff_cohomologous2 G A μ μ'

/-- EGNO Proposition 1.7.1 (iii): equivalence classes of monoidal structures on `Vec_G^A`
under monoidal equivalence are in bijection with `H³(G, A)`. -/
theorem Proposition_1_7_1_iii (G : Type u) [Group G] (A : Type v) [CommGroup A]
    (ω₁ ω₂ : Cochain3' G A) :
    (∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔
    @Quotient.mk _ (cohomologous3Setoid G A) ω₁ =
    @Quotient.mk _ (cohomologous3Setoid G A) ω₂ :=
  monoidal_structure_parametrized_by_H3 G A ω₁ ω₂
