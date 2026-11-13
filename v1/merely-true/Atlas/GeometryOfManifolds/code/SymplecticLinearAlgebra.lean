/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Module

namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A bilinear form $\Omega$ on a real vector space $V$ is symplectic iff it is alternating
($\Omega(v,v) = 0$) and nondegenerate (its left radical is trivial). -/
structure IsSymplecticForm (Ω : LinearMap.BilinForm ℝ V) : Prop where
  alt : Ω.IsAlt
  nondeg : Ω.SeparatingLeft

/-- The symplectic orthogonal $E^\Omega = \{v \in V : \Omega(v, e) = 0 \text{ for all } e \in E\}$. -/
def symplecticOrtho (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) : Submodule ℝ V :=
  Ω.orthogonal E

/-- A subspace $E$ is symplectic with respect to $\Omega$ iff $E \cap E^\Omega = \{0\}$
(Definition 4 in the textbook). -/
def IsSymplecticSubspace (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) : Prop :=
  E ⊓ symplecticOrtho Ω E = ⊥

/-- A subspace $E$ is Lagrangian iff $E^\Omega = E$, equivalently isotropic and half-dimensional
(Definition 5 in the textbook). -/
def IsLagrangian (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) : Prop :=
  symplecticOrtho Ω E = E

/-- An alternating bilinear form is skew-symmetric: $\Omega(x, y) = -\Omega(y, x)$. -/
theorem sympl_skew {Ω : LinearMap.BilinForm ℝ V} (hAlt : Ω.IsAlt) (x y : V) :
    Ω x y = -(Ω y x) := by
  have h := hAlt (x + y)
  simp [map_add, LinearMap.add_apply] at h
  linarith [hAlt x, hAlt y]

/-- For a symplectic form on a finite-dimensional space, the orthogonal of the whole space is
trivial: $V^\Omega = \{0\}$ (equivalent to nondegeneracy). -/
lemma IsSymplecticForm.orthogonal_top_eq_bot [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω) :
    Ω.orthogonal ⊤ = ⊥ :=
  LinearMap.BilinForm.orthogonal_top_eq_bot
    ((LinearMap.IsRefl.nondegenerate_iff_separatingLeft hΩ.alt.isRefl).mpr hΩ.nondeg)

/-- Dimension formula for the symplectic orthogonal: $\dim E + \dim E^\Omega = \dim V$. -/
lemma symplecticOrtho_finrank_add [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    (E : Submodule ℝ V) :
    finrank ℝ ↥E + finrank ℝ ↥(symplecticOrtho Ω E) = finrank ℝ V := by
  have hRefl : Ω.IsRefl := hΩ.alt.isRefl
  have key := LinearMap.BilinForm.finrank_add_finrank_orthogonal hRefl E
  have htop : Ω.orthogonal ⊤ = ⊥ := hΩ.orthogonal_top_eq_bot
  rw [htop] at key
  have hbot : finrank ℝ ↥(E ⊓ ⊥) = 0 := by rw [inf_bot_eq]; exact finrank_bot ℝ V
  unfold symplecticOrtho
  linarith

/-- $E$ is a symplectic subspace iff $E$ and $E^\Omega$ are complementary: $V = E \oplus E^\Omega$. -/
theorem symplectic_subspace_iff [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    (E : Submodule ℝ V) :
    IsSymplecticSubspace Ω E ↔ IsCompl E (symplecticOrtho Ω E) := by
  unfold IsSymplecticSubspace
  constructor
  · intro hE
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]; exact hE
    · rw [codisjoint_iff]
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq E (symplecticOrtho Ω E)
      rw [hE] at hsup
      simp at hsup
      have hadd := symplecticOrtho_finrank_add hΩ E
      exact Submodule.eq_top_of_finrank_eq (by linarith)
  · intro ⟨hd, _⟩
    exact hd.eq_bot

/-- A Lagrangian subspace has half the dimension of the ambient symplectic space:
$2 \dim E = \dim V$. -/
theorem lagrangian_half_dim [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    2 * finrank ℝ ↥E = finrank ℝ V := by
  unfold IsLagrangian symplecticOrtho at hE
  have hadd := symplecticOrtho_finrank_add hΩ E
  unfold symplecticOrtho at hadd
  rw [hE] at hadd
  omega

/-- The linear map $V \to E^*$ sending $v \mapsto \Omega(\cdot, v)|_E$, used to identify $V/E$ with
the dual of a Lagrangian. -/
noncomputable def symplRestrict (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) :
    V →ₗ[ℝ] (↥E →ₗ[ℝ] ℝ) where
  toFun v := (Ω.flip v).domRestrict E
  map_add' x y := by ext e; simp [LinearMap.domRestrict, map_add, LinearMap.add_apply]
  map_smul' r x := by ext e; simp [LinearMap.domRestrict, map_smul, LinearMap.smul_apply]

/-- The kernel of `symplRestrict Ω E` is exactly the symplectic orthogonal $E^\Omega$. -/
lemma ker_symplRestrict (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) :
    LinearMap.ker (symplRestrict Ω E) = Ω.orthogonal E := by
  ext v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hv u hu
    have := LinearMap.ext_iff.mp hv ⟨u, hu⟩
    simp [symplRestrict] at this
    exact this
  · intro hv
    ext ⟨u, hu⟩
    simp [symplRestrict]
    exact hv u hu


/-- For a Lagrangian subspace $E$, the symplectic form induces a canonical isomorphism
$V/E \simeq E^*$. -/
noncomputable def lagrangianQuotientDualEquiv [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    (V ⧸ E) ≃ₗ[ℝ] (↥E →ₗ[ℝ] ℝ) := by

  set φ := symplRestrict Ω E

  have hker : E = LinearMap.ker φ := by
    rw [ker_symplRestrict]
    exact hE.symm

  have hinj : Function.Injective (E.liftQ φ (le_of_eq hker)) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' E φ hker


  have hdim_quot : finrank ℝ (V ⧸ E) + finrank ℝ ↥E = finrank ℝ V :=
    Submodule.finrank_quotient_add_finrank E
  have hdim_lag : 2 * finrank ℝ ↥E = finrank ℝ V :=
    lagrangian_half_dim hΩ hE
  have hdim_dual : finrank ℝ (↥E →ₗ[ℝ] ℝ) = finrank ℝ ↥E :=
    Subspace.dual_finrank_eq
  have hdim_eq : finrank ℝ (V ⧸ E) = finrank ℝ (↥E →ₗ[ℝ] ℝ) := by omega

  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim_eq).mp hinj

  exact LinearEquiv.ofBijective (E.liftQ φ (le_of_eq hker)) ⟨hinj, hsurj⟩

open TensorProduct in
/-- Recursive construction of the $n$-fold wedge power $\Omega^{\wedge n}$ as an alternating
$2n$-form, built by inductively wedging with the $2$-form $\Omega$. -/
noncomputable def wedgePowBilinFormAux (Ω : LinearMap.BilinForm ℝ V) (hAlt : Ω.IsAlt) :
    (n : ℕ) → AlternatingMap ℝ V ℝ (Fin (2 * n))
  | 0 => haveI : IsEmpty (Fin (2 * 0)) := ⟨fun h => absurd h.isLt (by omega)⟩
    AlternatingMap.constOfIsEmpty ℝ V (Fin (2 * 0)) 1
  | n + 1 =>
    let Ω₂ : AlternatingMap ℝ V ℝ (Fin 2) :=
      { toFun := fun v => Ω (v 0) (v 1)
        map_update_add' := by
          intro _ v i x y
          fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
        map_update_smul' := by
          intro _ v i c x
          fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
        map_eq_zero_of_eq' := by
          intro v i j h hij
          fin_cases i <;> fin_cases j <;> simp_all <;> exact hAlt _ }
    let prev := wedgePowBilinFormAux Ω hAlt n

    let wedgeTensor := Ω₂.domCoprod prev

    let wedgeR := (TensorProduct.lid ℝ ℝ).toLinearMap.compAlternatingMap wedgeTensor

    wedgeR.domDomCongr ((finSumFinEquiv).trans (finCongr (by omega)))

/-- Wedge power $\Omega^{\wedge n}$ packaged as an alternating $m$-form: equals
`wedgePowBilinFormAux` when $m = 2n$ is even, and zero otherwise. -/
noncomputable def wedgePowBilinForm (Ω : LinearMap.BilinForm ℝ V) (hAlt : Ω.IsAlt) (m : ℕ) :
    AlternatingMap ℝ V ℝ (Fin m) :=
  let n := m / 2
  if h : m = 2 * n then
    (wedgePowBilinFormAux Ω hAlt n).domDomCongr (finCongr (by omega))
  else
    0


/-- The symplectic volume form $\frac{1}{n!}\Omega^{\wedge n}$ where $\dim V = 2n$
(Definition 6 in the textbook). -/
noncomputable def symplecticVolumeForm [FiniteDimensional ℝ V]
    (Ω : LinearMap.BilinForm ℝ V) (hΩ : IsSymplecticForm Ω) :
    AlternatingMap ℝ V ℝ (Fin (finrank ℝ V)) :=
  let n := finrank ℝ V / 2

  (1 / (Nat.factorial n : ℝ)) • wedgePowBilinForm Ω hΩ.alt (finrank ℝ V)

end SymplecticLinearAlgebra
