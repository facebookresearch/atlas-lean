/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Atlas.GeometryOfManifolds.code.SymplecticEvenDim

open Module FiniteDimensional

namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A standard symplectic basis $\{e_i, f_i\}_{i=1}^n$ for $(V, \Omega)$: the $e_i, f_i$ form a
basis of $V$ and satisfy $\Omega(e_i, e_j) = \Omega(f_i, f_j) = 0$ and $\Omega(e_i, f_j) =
\delta_{ij}$. -/
structure SymplecticBasis {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Ω : LinearMap.BilinForm ℝ V) where
  n : ℕ
  e : Fin n → V
  f : Fin n → V
  basis : Basis (Fin n ⊕ Fin n) ℝ V
  basis_eq_e : ∀ i, basis (Sum.inl i) = e i
  basis_eq_f : ∀ i, basis (Sum.inr i) = f i
  omega_ee : ∀ i j, Ω (e i) (e j) = 0
  omega_ff : ∀ i j, Ω (f i) (f j) = 0
  omega_ef : ∀ i j, Ω (e i) (f j) = if i = j then 1 else 0

/-- Existence of a symplectic pair: on a nontrivial finite-dimensional symplectic space, there
exist $e_1, f_1$ with $\Omega(e_1, f_1) = 1$ spanning a 2-dimensional symplectic subspace. -/
theorem exists_symplectic_pair [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    (hne : Nontrivial V) :
    ∃ (e₁ f₁ : V), Ω e₁ f₁ = 1 ∧
      IsSymplecticSubspace Ω (Submodule.span ℝ {e₁, f₁}) := by
  obtain ⟨e₁, he₁⟩ := exists_ne (0 : V)
  have hne_y : ∃ y, Ω e₁ y ≠ 0 := by
    by_contra h; push Not at h; exact he₁ (hΩ.nondeg e₁ (fun y => h y))
  obtain ⟨y, hy⟩ := hne_y
  set f₁ := (Ω e₁ y)⁻¹ • y
  have hΩef : Ω e₁ f₁ = 1 := by
    simp [f₁, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  refine ⟨e₁, f₁, hΩef, ?_⟩
  set P := Submodule.span ℝ {e₁, f₁}
  unfold IsSymplecticSubspace symplecticOrtho
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hv_P, hv_orth⟩ := hv
  rw [Submodule.mem_span_pair] at hv_P
  obtain ⟨a, b, hab⟩ := hv_P
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv_orth
  have he₁_P : e₁ ∈ P := Submodule.subset_span (Set.mem_insert e₁ {f₁})
  have hf₁_P : f₁ ∈ P := Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
  have hΩe₁v : Ω e₁ v = 0 := by
    have h := hv_orth e₁ he₁_P; change Ω.IsOrtho e₁ v at h; exact h
  have hΩf₁v : Ω f₁ v = 0 := by
    have h := hv_orth f₁ hf₁_P; change Ω.IsOrtho f₁ v at h; exact h
  rw [← hab] at hΩe₁v hΩf₁v
  simp only [map_add, map_smul, smul_eq_mul] at hΩe₁v hΩf₁v
  rw [hΩ.alt e₁, hΩef] at hΩe₁v
  have hΩf₁e₁ : Ω f₁ e₁ = -1 := by rw [sympl_skew hΩ.alt f₁ e₁, hΩef]
  rw [hΩf₁e₁, hΩ.alt f₁] at hΩf₁v
  have hb : b = 0 := by linarith
  have ha : a = 0 := by linarith
  rw [Submodule.mem_bot]
  rw [ha, hb] at hab; simp at hab; exact hab.symm

/-- If $P$ and its symplectic orthogonal $P^\Omega$ form a complementary decomposition of $V$,
then $\Omega$ restricted to $P^\Omega$ is itself symplectic. -/
lemma restrict_symplecticOrtho_symplectic [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {P : Submodule ℝ V} (hCompl : IsCompl P (symplecticOrtho Ω P)) :
    IsSymplecticForm (Ω.restrict (symplecticOrtho Ω P)) := by
  set W := symplecticOrtho Ω P
  constructor
  · intro v; exact hΩ.alt v
  · intro x hx
    have hx_val : ∀ (v : V), Ω (↑x : V) v = 0 := by
      intro v
      have htop : v ∈ (⊤ : Submodule ℝ V) := Submodule.mem_top
      rw [← hCompl.2.eq_top] at htop
      obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.mp htop
      rw [map_add]
      have hxw : Ω (↑x : V) w = 0 := hx ⟨w, hw⟩
      have hxp : Ω (↑x : V) p = 0 := by
        have hx_in_orth := x.2
        change (x : V) ∈ Ω.orthogonal P at hx_in_orth
        rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx_in_orth
        have h := hx_in_orth p hp
        change (Ω p) ↑x = 0 at h
        have hskew := hΩ.alt ((↑x : V) + p)
        simp [map_add, LinearMap.add_apply] at hskew
        linarith [hΩ.alt (↑x : V), hΩ.alt p]
      linarith
    exact_mod_cast hΩ.nondeg (↑x : V) hx_val

/-- An element of the symplectic orthogonal $P^\Omega$ pairs trivially with every $p \in P$:
$\Omega(u, p) = 0$. -/
lemma ortho_of_mem_symplecticOrtho [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {P : Submodule ℝ V} {u : V} (hu : u ∈ symplecticOrtho Ω P)
    {p : V} (hp : p ∈ P) : Ω u p = 0 := by
  unfold symplecticOrtho at hu
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu
  have h := hu p hp
  change (Ω p) u = 0 at h
  have hskew := hΩ.alt (u + p)
  simp [map_add, LinearMap.add_apply] at hskew
  linarith [hΩ.alt u, hΩ.alt p]

/-- Standard symplectic basis theorem: every finite-dimensional symplectic space $(V, \Omega)$
has even dimension $2n$ and admits a basis $\{e_i, f_i\}_{i=1}^n$ with $\Omega(e_i, e_j) =
\Omega(f_i, f_j) = 0$ and $\Omega(e_i, f_j) = \delta_{ij}$. -/
theorem symplectic_standard_basis [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω) :
    ∃ n : ℕ, ∃ e f : Fin n → V,
      finrank ℝ V = 2 * n ∧
      (∀ i j, Ω (e i) (e j) = 0) ∧
      (∀ i j, Ω (f i) (f j) = 0) ∧
      (∀ i j, Ω (e i) (f j) = if i = j then 1 else 0) ∧
      LinearIndependent ℝ (Sum.elim e f) ∧
      ⊤ ≤ Submodule.span ℝ (Set.range (Sum.elim e f)) := by
  induction h : finrank ℝ V using Nat.strongRecOn generalizing V with
  | _ d ih =>
  by_cases hd : d = 0
  ·
    refine ⟨0, Fin.elim0, Fin.elim0, by omega, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, linearIndependent_empty_type, ?_⟩
    intro v _
    have : Subsingleton V := by
      rw [← not_nontrivial_iff_subsingleton]
      intro hnt; exact absurd (Module.finrank_pos (R := ℝ) (M := V)) (by omega)
    rw [Subsingleton.elim v 0]; exact Submodule.zero_mem _
  ·
    have hV_nt : Nontrivial V := by rw [← finrank_pos_iff (R := ℝ)]; omega
    obtain ⟨e₁, f₁, hΩef, hSympl⟩ := exists_symplectic_pair hΩ hV_nt
    set P := Submodule.span ℝ {e₁, f₁}
    set W := symplecticOrtho Ω P
    have hCompl : IsCompl P W := by rwa [← symplectic_subspace_iff hΩ P]

    have hP_finrank : finrank ℝ P = 2 := by
      have hli : LinearIndependent ℝ ![e₁, f₁] := by
        rw [linearIndependent_fin2]
        constructor
        · simp; intro hf₁
          have h0 : Ω e₁ 0 = 0 := by simp [map_zero]
          rw [← hf₁] at h0; linarith
        · simp; intro a ha
          have : Ω (a • f₁) f₁ = Ω e₁ f₁ := by rw [ha]
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hΩ.alt f₁, mul_zero] at this
          linarith
      have hrange : Set.range ![e₁, f₁] = {e₁, f₁} := by
        simp [Matrix.range_cons, Matrix.range_empty]; exact Set.pair_comm f₁ e₁
      show finrank ℝ ↥(Submodule.span ℝ {e₁, f₁}) = 2
      rw [← hrange]; exact finrank_span_eq_card hli

    have hW_add : finrank ℝ ↥P + finrank ℝ ↥W = finrank ℝ V :=
      symplecticOrtho_finrank_add hΩ P
    have hd_ge_2 : d ≥ 2 := by omega
    have hW_finrank : finrank ℝ ↥W = d - 2 := by omega

    have hΩW : IsSymplecticForm (Ω.restrict W) := restrict_symplecticOrtho_symplectic hΩ hCompl

    obtain ⟨n, e', f', hdimW, hee', hff', hef', hli', hspan'⟩ :=
      ih (finrank ℝ ↥W) (by omega) hΩW rfl

    let e : Fin (n + 1) → V := Fin.cons e₁ (fun i => (e' i : V))
    let f : Fin (n + 1) → V := Fin.cons f₁ (fun i => (f' i : V))

    have he₁_P : e₁ ∈ P := Submodule.subset_span (Set.mem_insert e₁ {f₁})
    have hf₁_P : f₁ ∈ P := Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
    have he'_orth_P : ∀ i (p : V), p ∈ P → Ω (e' i : V) p = 0 :=
      fun i p hp => ortho_of_mem_symplecticOrtho hΩ (e' i).2 hp
    have hf'_orth_P : ∀ i (p : V), p ∈ P → Ω (f' i : V) p = 0 :=
      fun i p hp => ortho_of_mem_symplecticOrtho hΩ (f' i).2 hp

    have hspan_V : ⊤ ≤ Submodule.span ℝ (Set.range (Sum.elim e f)) := by
      rw [← hCompl.2.eq_top]
      apply sup_le
      · apply Submodule.span_le.mpr
        intro v hv
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        cases hv with
        | inl hv => rw [hv]; exact Submodule.subset_span ⟨Sum.inl 0, by simp [e]⟩
        | inr hv => rw [hv]; exact Submodule.subset_span ⟨Sum.inr 0, by simp [f]⟩
      · rw [← Submodule.map_subtype_top W]
        apply (Submodule.map_mono hspan').trans
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro x ⟨w, ⟨i, rfl⟩, rfl⟩
        cases i with
        | inl i => exact ⟨Sum.inl i.succ, by simp [e]⟩
        | inr i => exact ⟨Sum.inr i.succ, by simp [f]⟩
    refine ⟨n + 1, e, f, ?_, ?_, ?_, ?_, ?_, hspan_V⟩

    · omega

    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · exact hΩ.alt e₁
      · show Ω e₁ (e' j : V) = 0
        rw [sympl_skew hΩ.alt]; exact neg_eq_zero.mpr (he'_orth_P j e₁ he₁_P)
      · show Ω (e' i : V) e₁ = 0; exact he'_orth_P i e₁ he₁_P
      · show Ω (e' i : V) (e' j : V) = 0; exact hee' i j

    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · exact hΩ.alt f₁
      · show Ω f₁ (f' j : V) = 0
        rw [sympl_skew hΩ.alt]; exact neg_eq_zero.mpr (hf'_orth_P j f₁ hf₁_P)
      · show Ω (f' i : V) f₁ = 0; exact hf'_orth_P i f₁ hf₁_P
      · show Ω (f' i : V) (f' j : V) = 0; exact hff' i j

    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      ·
        simp [e, f, hΩef]
      ·
        show Ω e₁ (f' j : V) = if (0 : Fin (n + 1)) = j.succ then 1 else 0
        have : (0 : Fin (n+1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
        simp [this]
        rw [sympl_skew hΩ.alt]; exact neg_eq_zero.mpr (hf'_orth_P j e₁ he₁_P)
      ·
        show Ω (e' i : V) f₁ = if (i.succ : Fin (n + 1)) = (0 : Fin (n + 1)) then 1 else 0
        simp [Fin.succ_ne_zero]; exact he'_orth_P i f₁ hf₁_P
      ·
        show Ω (e' i : V) (f' j : V) =
            if (i.succ : Fin (n + 1)) = j.succ then 1 else 0
        simp only [Fin.succ_inj]; exact hef' i j

    · apply linearIndependent_of_top_le_span_of_card_eq_finrank hspan_V
      simp [Fintype.card_sum, Fintype.card_fin]; omega

end SymplecticLinearAlgebra
