/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.SymplecticStandardBasis

set_option autoImplicit false

open Module FiniteDimensional

namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A linear map $J: V \to V$ is a complex structure iff $J^2 = -I$. -/
structure IsComplexStructure (J : V →ₗ[ℝ] V) : Prop where
  sq_eq_neg : J.comp J = -LinearMap.id

/-- Pointwise form of $J^2 = -I$: $J(J v) = -v$ for every $v \in V$. -/
lemma IsComplexStructure.apply_apply {J : V →ₗ[ℝ] V} (hJ : IsComplexStructure J) (v : V) :
    J (J v) = -v := by
  have := LinearMap.ext_iff.mp hJ.sq_eq_neg v
  simp [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] at this
  exact this

/-- A complex structure $J$ is compatible with a symplectic form $\Omega$ iff $J^2 = -I$,
$\Omega(Ju, Jv) = \Omega(u, v)$ (preservation), and $\Omega(u, Ju) > 0$ for $u \neq 0$ (taming). -/
structure IsCompatibleComplexStr (Ω : LinearMap.BilinForm ℝ V) (J : V →ₗ[ℝ] V) : Prop where
  complex_str : IsComplexStructure J
  preserves : ∀ u v, Ω (J u) (J v) = Ω u v
  positive : ∀ u, u ≠ 0 → Ω u (J u) > 0

/-- Every finite-dimensional symplectic vector space admits a compatible complex structure,
constructed in a symplectic standard basis by sending $e_i \mapsto f_i$, $f_i \mapsto -e_i$. -/
theorem exists_compatible_complex_structure [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω) :
    ∃ J : V →ₗ[ℝ] V, IsCompatibleComplexStr Ω J := by

  obtain ⟨n, e, f, _, hee, hff, hef, hli, hspan⟩ := symplectic_standard_basis hΩ

  let B : Basis (Fin n ⊕ Fin n) ℝ V := Basis.mk hli hspan

  let J : V →ₗ[ℝ] V := B.constr ℝ (Sum.elim f (fun i => -e i))

  have hBe : ∀ i, B (Sum.inl i) = e i := fun i => Basis.mk_apply hli hspan (Sum.inl i)
  have hBf : ∀ i, B (Sum.inr i) = f i := fun i => Basis.mk_apply hli hspan (Sum.inr i)

  have hJe : ∀ i, J (e i) = f i := by
    intro i; rw [← hBe]; exact Basis.constr_basis B ℝ _ (Sum.inl i)
  have hJf : ∀ i, J (f i) = -e i := by
    intro i; rw [← hBf]; exact Basis.constr_basis B ℝ _ (Sum.inr i)

  have hfe : ∀ i j, Ω (f i) (e j) = if i = j then -1 else 0 := by
    intro i j; rw [sympl_skew hΩ.alt, hef j i]
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]

  have hG_diag : ∀ i j : Fin n ⊕ Fin n, Ω (B i) (J (B j)) = if i = j then 1 else 0 := by
    intro i j
    cases i with
    | inl a =>
      cases j with
      | inl b => rw [hBe, hBe, hJe, hef]; simp [Sum.inl.injEq]
      | inr b => rw [hBe, hBf, hJf, map_neg, hee]; simp
    | inr a =>
      cases j with
      | inl b => rw [hBf, hBe, hJe, hff]; simp
      | inr b =>
        rw [hBf, hBf, hJf, map_neg, sympl_skew hΩ.alt, hef b a, neg_neg]
        simp [Sum.inr.injEq, @eq_comm _ a b]
  refine ⟨J, ?_, ?_, ?_⟩

  · constructor
    apply B.ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply]
    cases i with
    | inl i => rw [hBe, hJe, hJf]
    | inr i => rw [hBf, hJf, map_neg, hJe]

  ·
    suffices h : Ω.compl₁₂ J J = Ω from by
      intro u v
      have := LinearMap.ext_iff.mp (LinearMap.ext_iff.mp h u) v
      simp [LinearMap.compl₁₂_apply] at this
      exact this
    apply LinearMap.BilinForm.ext_basis B
    intro i j
    simp only [LinearMap.compl₁₂_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j => rw [hBe, hBe, hJe, hJe, hff, hee]
      | inr j =>
        rw [hBe, hBf, hJe, hJf]
        simp only [map_neg]
        rw [hfe i j, hef i j]
        split_ifs <;> simp
    | inr i =>
      cases j with
      | inl j =>
        rw [hBf, hBe, hJf, hJe]
        simp only [map_neg, LinearMap.neg_apply]
        rw [hef i j, hfe i j]
        split_ifs <;> simp
      | inr j =>
        rw [hBf, hBf, hJf, hJf]
        simp only [map_neg, LinearMap.neg_apply, neg_neg]
        rw [hee i j, hff i j]

  · intro u hu

    have key : Ω u (J u) = ∑ i : Fin n ⊕ Fin n, (B.repr u i) ^ 2 := by
      conv_lhs => rw [← B.sum_repr u]
      simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul,
                 LinearMap.sum_apply, map_sum, map_smul, smul_eq_mul]
      simp_rw [hG_diag, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
               ite_true, sq]
    rw [key]
    apply (Finset.sum_pos_iff_of_nonneg (fun i _ => sq_nonneg _)).mpr
    have hne : B.repr u ≠ 0 := by
      intro h
      exact hu (B.repr.injective (show B.repr u = B.repr 0 from by rw [h, map_zero]))
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    rw [Finsupp.coe_zero, Pi.zero_apply] at hi
    exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- Convexity (Proposition 3): the set of symplectic forms compatible with a fixed $J$ is
convex—if $J$ is compatible with $\Omega_0$ and $\Omega_1$ then it is compatible with
$(1 - t)\Omega_0 + t\Omega_1$ for every $t \in [0,1]$. -/
theorem compatible_forms_convex_linear
    {Ω₀ Ω₁ : LinearMap.BilinForm ℝ V} {J : V →ₗ[ℝ] V}
    (h₀ : IsCompatibleComplexStr Ω₀ J) (h₁ : IsCompatibleComplexStr Ω₁ J)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    IsCompatibleComplexStr ((1 - t) • Ω₀ + t • Ω₁) J := by
  constructor
  · exact h₀.complex_str
  · intro u v
    simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [h₀.preserves u v, h₁.preserves u v]
  · intro u hu
    simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have h0_pos := h₀.positive u hu
    have h1_pos := h₁.positive u hu
    obtain ⟨h_le0, h_le1⟩ := ht
    by_cases ht0 : t = 0
    · subst ht0; simp; linarith
    by_cases ht1 : t = 1
    · subst ht1; simp; linarith
    · have ht_pos : 0 < t := lt_of_le_of_ne h_le0 (Ne.symm ht0)
      have h1t_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne h_le1 ht1]
      have term1 : 0 < (1 - t) * Ω₀ u (J u) := mul_pos h1t_pos h0_pos
      have term2 : 0 < t * Ω₁ u (J u) := mul_pos ht_pos h1_pos
      linarith

end SymplecticLinearAlgebra
