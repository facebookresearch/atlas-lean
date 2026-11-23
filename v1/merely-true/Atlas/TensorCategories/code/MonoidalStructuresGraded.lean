/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.MonoidalFunctorsCohomology

set_option maxHeartbeats 400000

universe u v

section PartI

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

/-- Twisting a monoidal natural transformation `η` by a character `χ : G →* A` yields
another monoidal natural transformation between the same monoidal structures. -/
theorem monoidalNatTransData_mul_character
    {μ μ' : Cochain2 G A} {η : Cochain1 G A}
    (hη : IsMonoidalNatTransData G A μ μ' η)
    (χ : G →* A) :
    IsMonoidalNatTransData G A μ μ' (fun g => χ g * η g) := by
  intro g h
  have hχ : χ (g * h) = χ g * χ h := map_mul χ g h
  have := hη g h
  calc χ g * η g * (χ h * η h) * μ g h
      = χ g * χ h * (η g * η h * μ g h) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ = χ g * χ h * (μ' g h * η (g * h)) := by rw [this]
    _ = μ' g h * (χ g * χ h * η (g * h)) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ = μ' g h * (χ (g * h) * η (g * h)) := by rw [hχ]

/-- The ratio of two monoidal natural transformations between the same monoidal
structures is a group character `G →* A`. -/
theorem monoidalNatTrans_ratio_is_character
    {μ μ' : Cochain2 G A} {η η' : Cochain1 G A}
    (hη : IsMonoidalNatTransData G A μ μ' η)
    (hη' : IsMonoidalNatTransData G A μ μ' η') :
    ∃ χ : G →* A, ∀ g : G, η' g = χ g * η g := by
  have hd : ∀ g h : G, d1 G A η g h = d1 G A η' g h := by
    intro g h
    have h1 := (isMonoidalNatTransData_iff_coboundary G A μ μ' η).mp hη g h
    have h2 := (isMonoidalNatTransData_iff_coboundary G A μ μ' η').mp hη' g h
    rw [h1] at h2
    exact mul_left_cancel h2
  refine ⟨{
    toFun := fun g => η' g * (η g)⁻¹
    map_one' := ?_
    map_mul' := ?_
  }, fun g => ?_⟩
  · have h1 := hd 1 1
    unfold d1 at h1
    simp [mul_one] at h1
    simp [h1]
  · intro g h
    have key := hd g h
    unfold d1 at key
    have step : η g * η h * η' (g * h) = η' g * η' h * η (g * h) := by
      calc η g * η h * η' (g * h)
          = η g * η h * (η (g * h))⁻¹ * η (g * h) * η' (g * h) := by
            simp [mul_assoc, mul_inv_cancel]
        _ = η' g * η' h * (η' (g * h))⁻¹ * η (g * h) * η' (g * h) := by
            rw [key]
        _ = η' g * η' h * η (g * h) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
    have factor : η' (g * h) = (η g * η h)⁻¹ * (η' g * η' h * η (g * h)) := by
      calc η' (g * h)
          = (η g * η h)⁻¹ * (η g * η h * η' (g * h)) := by
            simp [mul_assoc, inv_mul_cancel]
        _ = (η g * η h)⁻¹ * (η' g * η' h * η (g * h)) := by rw [step]
    calc η' (g * h) * (η (g * h))⁻¹
        = (η g * η h)⁻¹ * (η' g * η' h * η (g * h)) * (η (g * h))⁻¹ := by
          rw [factor]
      _ = (η g * η h)⁻¹ * (η' g * η' h) := by
          simp [mul_assoc, mul_inv_cancel]
      _ = (η' g * (η g)⁻¹) * (η' h * (η h)⁻¹) := by
          simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  · simp [mul_comm]

/-- EGNO Proposition 1.7.1 (i) (torsor refinement): existence of a monoidal natural
transformation between graded vector spaces is equivalent to `Cohomologous2`, and the set
of such transformations forms a torsor under the group of characters `G →* A`. -/
theorem Proposition_1_7_1_i_torsor
    {G₁ : Type u} [Group G₁] {A : Type v} [CommGroup A]
    (μ μ' : Cochain2 G₁ A) :
    ((∃ η : Cochain1 G₁ A, IsMonoidalNatTransData G₁ A μ μ' η) ↔
      Cohomologous2 G₁ A μ μ') ∧
    (∀ {η η' : Cochain1 G₁ A},
      IsMonoidalNatTransData G₁ A μ μ' η →
      IsMonoidalNatTransData G₁ A μ μ' η' →
      ∃ χ : G₁ →* A, ∀ g : G₁, η' g = χ g * η g) ∧
    (∀ {η : Cochain1 G₁ A},
      IsMonoidalNatTransData G₁ A μ μ' η →
      ∀ χ : G₁ →* A, IsMonoidalNatTransData G₁ A μ μ' (fun g => χ g * η g)) :=
  ⟨monoidalNatTrans_iff_cohomologous2 G₁ A μ μ',
   fun hη hη' => monoidalNatTrans_ratio_is_character hη hη',
   fun hη χ => monoidalNatTransData_mul_character hη χ⟩

end PartI

section PartII

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- EGNO Proposition 1.7.1 (ii) (torsor refinement): existence of monoidal natural
isomorphisms is equivalent to `Cohomologous2`, and equivalence classes of monoidal
structures are classified by `H²(G, A)`. -/
theorem Proposition_1_7_1_ii_torsor (μ μ' : Cochain2 G A) :

    ((∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔
      Cohomologous2 G A μ μ') ∧

    ((∃ η : Cochain1 G A, ∀ g h : G, μ' g h = μ g h * d1 G A η g h) ↔
      @Quotient.mk _ (cohomologous2Setoid G A) μ =
      @Quotient.mk _ (cohomologous2Setoid G A) μ') :=
  ⟨monoidal_iso_iff_cohomologous2 G A μ μ',
   monoidal_autoequiv_classes_H2 G A μ μ'⟩

end PartII

section PartIII

variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/-- The pullback of a 3-cochain `ω` along a group automorphism `φ`. -/
def autPullback3 (φ : G ≃* G) (ω : Cochain3' G A) : Cochain3' G A :=
  fun g h l => ω (φ g) (φ h) (φ l)

/-- The automorphism pullback agrees with the homomorphism pullback applied to the
underlying `MonoidHom`. -/
lemma autPullback3_eq_pullback3 (φ : G ≃* G) (ω : Cochain3' G A) :
    autPullback3 G A φ ω = pullback3 G G A φ.toMonoidHom ω := by
  rfl

/-- Two 3-cochains are in the same automorphism orbit if some automorphism of `G` maps the
class of one to the class of the other in `H³(G, A)`. -/
def AutOrbitCohomologous3 (ω₁ ω₂ : Cochain3' G A) : Prop :=
  ∃ (φ : G ≃* G), Cohomologous3 G A ω₁ (autPullback3 G A φ ω₂)

/-- A monoidal equivalence between graded categories with arbitrary underlying automorphism
exists if and only if the source and target 3-cocycles lie in the same `Aut(G)`-orbit on
`H³(G, A)`. -/
theorem monoidal_equiv_general_iff_autOrbit (ω₁ ω₂ : Cochain3' G A) :
    (∃ (φ : G ≃* G) (μ : Cochain2 G A),
      IsMonoidalFunctorData G G A ω₁ ω₂ φ.toMonoidHom μ) ↔
    AutOrbitCohomologous3 G A ω₁ ω₂ := by
  unfold AutOrbitCohomologous3
  simp_rw [autPullback3_eq_pullback3]
  constructor
  · rintro ⟨φ, μ, hμ⟩
    exact ⟨φ, (monoidalFunctor_exists_iff_cohomologous G G A ω₁ ω₂ φ.toMonoidHom).mp ⟨μ, hμ⟩⟩
  · rintro ⟨φ, hcohom⟩
    obtain ⟨μ, hμ⟩ := (monoidalFunctor_exists_iff_cohomologous G G A ω₁ ω₂ φ.toMonoidHom).mpr hcohom
    exact ⟨φ, μ, hμ⟩


/-- EGNO Proposition 1.7.1 (iii) refined: combining the `H³`-classification with the
`Out(G)`-action describing the general monoidal-equivalence orbits. -/
theorem Proposition_1_7_1_iii_with_OutG (ω₁ ω₂ : Cochain3' G A) :

    ((∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔
      Cohomologous3 G A ω₁ ω₂) ∧

    ((∃ (φ : G ≃* G) (μ : Cochain2 G A),
        IsMonoidalFunctorData G G A ω₁ ω₂ φ.toMonoidHom μ) ↔
      AutOrbitCohomologous3 G A ω₁ ω₂) :=
  ⟨monoidal_equiv_iff_cohomologous3 G A ω₁ ω₂,
   monoidal_equiv_general_iff_autOrbit G A ω₁ ω₂⟩

end PartIII

/-- EGNO Proposition 1.7.1 combined statement: assembling parts (i), (ii) (with torsor
refinement), and (iii) (with `Out(G)` action) into a single theorem. -/
theorem Proposition_1_7_1_combined (G : Type u) [Group G] (A : Type v) [CommGroup A] :

    (∀ μ μ' : Cochain2 G A,
      ((∃ η : Cochain1 G A, IsMonoidalNatTransData G A μ μ' η) ↔
        Cohomologous2 G A μ μ') ∧
      (∀ {η η' : Cochain1 G A},
        IsMonoidalNatTransData G A μ μ' η →
        IsMonoidalNatTransData G A μ μ' η' →
        ∃ χ : G →* A, ∀ g : G, η' g = χ g * η g) ∧
      (∀ {η : Cochain1 G A},
        IsMonoidalNatTransData G A μ μ' η →
        ∀ χ : G →* A, IsMonoidalNatTransData G A μ μ' (fun g => χ g * η g))) ∧

    (∀ μ μ' : Cochain2 G A,

      ((∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔
        Cohomologous2 G A μ μ') ∧

      ((∃ η : Cochain1 G A, ∀ g h : G, μ' g h = μ g h * d1 G A η g h) ↔
        @Quotient.mk _ (cohomologous2Setoid G A) μ =
        @Quotient.mk _ (cohomologous2Setoid G A) μ')) ∧

    (∀ ω₁ ω₂ : Cochain3' G A,

      ((∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔
        Cohomologous3 G A ω₁ ω₂) ∧

      ((∃ (φ : G ≃* G) (μ : Cochain2 G A),
          IsMonoidalFunctorData G G A ω₁ ω₂ φ.toMonoidHom μ) ↔
        AutOrbitCohomologous3 G A ω₁ ω₂)) :=
  ⟨fun μ μ' => Proposition_1_7_1_i_torsor μ μ',
   fun μ μ' => Proposition_1_7_1_ii_torsor G A μ μ',
   fun ω₁ ω₂ => Proposition_1_7_1_iii_with_OutG G A ω₁ ω₂⟩
