/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryO
import Atlas.LieGroups.code.TensorHomAxiom

noncomputable section

open Classical

universe uCatO
universe u_V u_M u_P

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def IsDominantWeightLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    WeightLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

def IsDominantWeightBruhat {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    BruhatLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

theorem bruhatLE_implies_weightLE
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (μ wt : Δ.𝔥 →ₗ[R] R)
    (h : BruhatLE rd μ wt) : WeightLE rd μ wt := by
  classical
  unfold BruhatLE at h
  unfold WeightLE PositiveRootData.IsInQPlus
  induction h with
  | refl => exact ⟨fun _ => 0, by simp⟩
  | @tail b c _hab hbc ih =>
    obtain ⟨α, hα_mem, n, _hn_pos, _hpair, hb_eq⟩ := hbc
    obtain ⟨coeff, hcoeff⟩ := ih
    refine ⟨Function.update coeff α (coeff α + n), ?_⟩
    have hcmu : c - μ = (b - μ) + n • α := by
      have hc : c = b + n • α := by rw [hb_eq]; abel
      rw [hc]; abel
    rw [hcmu, hcoeff]
    symm
    have lhs_eq : ∑ β ∈ rd.posRoots, (Function.update coeff α (coeff α + n) β) • β =
        (coeff α + n) • α + ∑ β ∈ rd.posRoots.erase α, coeff β • β := by
      rw [← Finset.add_sum_erase rd.posRoots
          (fun β => (Function.update coeff α (coeff α + n) β) • β) hα_mem]
      congr 1
      · simp [Function.update_self]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_erase] at hx
        rw [Function.update_of_ne hx.1]
    have rhs_eq : (∑ β ∈ rd.posRoots, coeff β • β) + n • α =
        (coeff α + n) • α + ∑ β ∈ rd.posRoots.erase α, coeff β • β := by
      rw [← Finset.add_sum_erase rd.posRoots (fun β => coeff β • β) hα_mem]
      rw [add_nsmul]; abel
    rw [lhs_eq, ← rhs_eq]


theorem PositiveRootData.corootPairing_self_pos
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) :
    rd.corootPairing α α = 2 := rd.corootPairing_self α hα









theorem weightLE_antisymm
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a b : Δ.𝔥 →ₗ[R] R)
    (h1 : WeightLE rd a b)
    (h2 : WeightLE rd b a) : a = b := by

  unfold WeightLE at h1 h2
  have h2' : rd.IsInQPlus (-(b - a)) := by rwa [show -(b - a) = a - b from by abel]

  suffices h : b - a = 0 by rw [sub_eq_zero] at h; exact h.symm
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2'
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push Not at hall

    exact hμ (by rw [hc]; exact Finset.sum_eq_zero fun β hβ => by simp [hall β hβ])
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _; rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [Finset.ne_of_mem_erase hγ]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ; omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

theorem reflectionLT_ne
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α μ ν : Δ.𝔥 →ₗ[R] R)
    (h : ReflectionLT rd α μ ν) : μ ≠ ν := by
  obtain ⟨hα, n, hn, _, heq⟩ := h
  intro hμν

  have h_nsmul : (n : ℕ) • α = (0 : Δ.𝔥 →ₗ[R] R) := by
    have h1 : ν - n • α = ν := by rw [← heq]; exact hμν
    have : n • α = ν - ν := by
      calc n • α = ν - (ν - n • α) := by abel
        _ = ν - ν := by rw [h1]
    rwa [sub_self] at this


  have h_neg : (-(n : ℤ)) < 0 := by omega
  exact absurd ⟨fun _ => 0, by
    simp only [zero_nsmul, Finset.sum_const_zero]
    rw [show (-(n : ℤ)) • α = -(n • α) from by rw [neg_zsmul, natCast_zsmul]]
    rw [h_nsmul, neg_zero]⟩ (rd.posRoots_pointed_cone α hα (-(n : ℤ)) h_neg)

lemma reflectionLT_implies_weightLE
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α μ ν : Δ.𝔥 →ₗ[R] R)
    (h : ReflectionLT rd α μ ν) :
    WeightLE rd μ ν := by
  classical
  obtain ⟨hα, n, hn, _, heq⟩ := h

  unfold WeightLE
  rw [heq, show ν - (ν - n • α) = n • α from by abel]

  refine ⟨Function.update (fun _ => 0) α n, ?_⟩
  simp_rw [Function.update_apply]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', hα, ite_true]

lemma weightLE_trans
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a b c : Δ.𝔥 →ₗ[R] R)
    (h1 : WeightLE rd a b)
    (h2 : WeightLE rd b c) :
    WeightLE rd a c :=
  PositiveRootData.IsInQPlus_trans rd c b a h2 h1

lemma weightLE_refl
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a : Δ.𝔥 →ₗ[R] R) :
    WeightLE rd a a := by
  unfold WeightLE
  rw [show a - a = 0 from sub_self a]
  exact PositiveRootData.IsInQPlus_zero rd


theorem dominantLE_implies_dominantBruhat
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (h : IsDominantWeightLE rd wg lam) : IsDominantWeightBruhat rd wg lam := by
  intro w hw hBruhat


  have hle : WeightLE rd lam (wg.dualAction w lam) :=
    bruhatLE_implies_weightLE _ _ hBruhat
  exact h w hw hle


def NotNegIntCorootPairing
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, ¬ ∃ n : ℤ, n < 0 ∧ lam (rs.coroot α) = (n : R)

def IsIntegralDominantWeightBruhat
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → BruhatLE rd (wg.dualAction w lam) lam

def IsIntegralDominantWeightLE
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → WeightLE rd (wg.dualAction w lam) lam






theorem neg_zsmul_posRoot_not_in_QPlus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (α : Δ.𝔥 →ₗ[R] R)
    (hα : α ∈ rd.posRoots)
    (n : ℤ) (hn : n < 0) :
    ¬ rd.IsInQPlus (n • α) := by

  intro ⟨c, hc⟩
  exact rd.posRoots_pointed_cone α hα n hn ⟨c, hc⟩

theorem stabilizer_roots_form_root_system
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    IsRootSubsystem rd wg rs (rootsOfStabilizer rd wg rs x) :=
  Wx_roots_form_root_system rd wg rs x


theorem stabilizer_dual_root_subsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    ∀ h : Δ.𝔥,
      h ∈ corootsOf rs (rootsOfStabilizer rd wg rs x) ↔
        (h ∈ Submodule.span ℤ (corootsOf rs (rootsOfStabilizer rd wg rs x)) ∧
         h ∈ corootsOf rs (↑rs.allRoots : Set (Δ.𝔥 →ₗ[R] R))) :=
  Rx_dual_is_root_subsystem rd wg rs x


lemma pairing_integral_of_WeylStabilizerModQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R)
    (w : wg.W)
    (hw : w ∈ WeylStabilizerModQ rd wg lam)
    (α : Δ.𝔥 →ₗ[R] R)
    (hα_pos : α ∈ rd.posRoots)
    (hs : rs.reflection α ∈ WeylStabilizerModQ rd wg lam) :
    ∃ (n : ℤ), (wg.dualAction w lam) (rs.coroot α) = (n : R) := by

  have hα_all : α ∈ rs.allRoots := rs.posRoots_sub α hα_pos
  have hsw_mem : rs.reflection α * w ∈ WeylStabilizerModQ rd wg lam :=
    WeylStabilizerModQ_mul_closed rd wg rs lam hs hw

  obtain ⟨c₁, hc₁⟩ := hw
  obtain ⟨c₂, hc₂⟩ := hsw_mem

  have hmul : wg.dualAction (rs.reflection α * w) lam =
    wg.dualAction (rs.reflection α) (wg.dualAction w lam) :=
    rs.dualAction_mul (rs.reflection α) w lam

  set μ := wg.dualAction w lam
  have hrefl : wg.dualAction (rs.reflection α) μ = μ - μ (rs.coroot α) • α :=
    rs.reflection_formula α hα_all μ

  have h1 : (μ - μ (rs.coroot α) • α) - lam =
    ∑ γ ∈ rd.posRoots, c₂ γ • γ := by rw [← hrefl, ← hmul]; exact hc₂
  have h2 : μ - lam = ∑ γ ∈ rd.posRoots, c₁ γ • γ := hc₁
  have hsub_eq : -(μ (rs.coroot α)) • α =
    ∑ γ ∈ rd.posRoots, (c₂ γ - c₁ γ) • γ := by


    have key : (∑ γ ∈ rd.posRoots, c₂ γ • γ) - (∑ γ ∈ rd.posRoots, c₁ γ • γ) =
      -(μ (rs.coroot α)) • α := by
      have habelsub : (μ - μ (rs.coroot α) • α) - lam - (μ - lam) =
        -(μ (rs.coroot α) • α) := by abel
      rw [h1, h2] at habelsub
      rwa [← neg_smul] at habelsub
    rw [← key, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    exact (sub_smul (c₂ γ) (c₁ γ) γ).symm


  exact rs.pairing_integral α hα_all μ ⟨fun γ => c₂ γ - c₁ γ, hsub_eq⟩


lemma IsInQPlus_add
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (μ ν : Δ.𝔥 →ₗ[R] R)
    (hμ : rd.IsInQPlus μ) (hν : rd.IsInQPlus ν) :
    rd.IsInQPlus (μ + ν) := by
  obtain ⟨c₁, hc₁⟩ := hμ
  obtain ⟨c₂, hc₂⟩ := hν
  refine ⟨fun α => c₁ α + c₂ α, ?_⟩
  rw [hc₁, hc₂, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  exact (add_nsmul α (c₁ α) (c₂ α)).symm

lemma nsmul_posRoot_IsInQPlus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (β : Δ.𝔥 →ₗ[R] R) (hβ : β ∈ rd.posRoots) (n : ℕ) :
    rd.IsInQPlus (n • β) := by
  refine ⟨fun γ => if γ = β then n else 0, ?_⟩
  have : ∀ γ ∈ rd.posRoots,
      (if γ = β then n else 0) • γ = if γ = β then n • β else (0 : Δ.𝔥 →ₗ[R] R) := by
    intro γ _
    split_ifs with h
    · subst h; rfl
    · exact zero_nsmul γ
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' rd.posRoots β]
  simp [hβ]




def IsProjectiveInO {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (P : Type uCatO) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hP : IsCategoryO Δ rd P) : Prop :=
  ∀ (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_ : IsCategoryO Δ rd M),
  ∀ (N : Type uCatO) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (_ : IsCategoryO Δ rd N),
  ∀ (f : M →ₗ⁅R, 𝔤⁆ N) (_ : Function.Surjective f)
    (g : P →ₗ⁅R, 𝔤⁆ N),
    ∃ (h : P →ₗ⁅R, 𝔤⁆ M), ∀ p, f (h p) = g p

theorem weight_decomp_component_eq
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hMO : IsCategoryO Δ rd M)
    (μ : Δ.𝔥 →ₗ[R] R)
    (v : M)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), v⁆ = μ h • v)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (y : (Δ.𝔥 →ₗ[R] R) → M)
    (hy_wt : ∀ ν, ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), y ν⁆ = ν h • y ν)
    (hsum : v = ∑ ν ∈ S, y ν) :
    ∑ ν ∈ S.filter (· ≠ μ), y ν = 0 := by
  set w := ∑ ν ∈ S.filter (· ≠ μ), y ν with hw_def

  have hy_mem : ∀ ν, y ν ∈ WeightSpace Δ M ν := fun ν => hy_wt ν

  have hv_mem : v ∈ WeightSpace Δ M μ := hv_wt

  have hfilt : S.filter (· ≠ μ) = S.filter (fun x => ¬(x = μ)) := by
    ext x; simp [ne_eq]

  have hsplit : v = ∑ ν ∈ S.filter (· = μ), y ν + w := by
    rw [hsum, hw_def, hfilt]
    exact (Finset.sum_filter_add_sum_filter_not S (· = μ) y).symm

  have hmu_sum_mem : ∑ ν ∈ S.filter (· = μ), y ν ∈ WeightSpace Δ M μ := by
    apply Submodule.sum_mem
    intro ν hν
    rw [Finset.mem_filter] at hν
    rw [hν.2]; exact hy_mem μ

  have hw_in_mu : w ∈ WeightSpace Δ M μ := by
    have : w = v - ∑ ν ∈ S.filter (· = μ), y ν := by rw [hsplit]; abel
    rw [this]; exact (WeightSpace Δ M μ).sub_mem hv_mem hmu_sum_mem

  have hw_in_sup : w ∈ ⨆ (ν : Δ.𝔥 →ₗ[R] R) (_ : ν ≠ μ), WeightSpace Δ M ν := by
    rw [hw_def]
    apply Submodule.sum_mem _ (fun ν hν => ?_)
    rw [Finset.mem_filter] at hν
    exact Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hν.2 (hy_mem ν))

  have hindep := @weightSpace_iSupIndep R _ 𝔤 _ _ Δ M _ _ _ _
  have hdisjoint := hindep μ
  rw [Submodule.disjoint_def] at hdisjoint
  exact hdisjoint w hw_in_mu hw_in_sup

theorem weight_space_surjective_of_surjective
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    {Y : Type*} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (_hYO : IsCategoryO Δ rd Y)
    (f : X →ₗ⁅R, 𝔤⁆ Y)
    (_hf : Function.Surjective f)
    (μ : Δ.𝔥 →ₗ[R] R)
    (v : Y)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v) :
    ∃ (w : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) ∧
      f w = v := by

  obtain ⟨m, hm⟩ := _hf v

  obtain ⟨S, wv, hdecomp⟩ := _hXO.weight_decomp m

  have hfm : v = ∑ ν ∈ S, (f (wv ν : X)) := by
    rw [← hm, hdecomp, map_sum]

  have hf_wt : ∀ ν, ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), (f (↑(wv ν) : X))⁆ = ν h • f (↑(wv ν)) := by
    intro ν h
    have := (wv ν).property h
    rw [← LieModuleHom.map_lie, this, map_smul]

  have hvanish := weight_decomp_component_eq _hYO μ v hv_wt S
    (fun ν => f (wv ν : X)) hf_wt hfm

  by_cases hμS : μ ∈ S
  ·
    refine ⟨(wv μ : X), (wv μ).property, ?_⟩


    have hsplit := Finset.add_sum_erase S (fun ν => f (↑(wv ν) : X)) hμS


    have herase_eq : S.erase μ = S.filter (· ≠ μ) := by
      ext x; simp [Finset.mem_erase, Finset.mem_filter]; tauto
    rw [herase_eq] at hsplit


    simp only [] at hsplit


    rw [hvanish, add_zero] at hsplit

    rw [hfm, hsplit]
  ·

    have hfilt_eq : S.filter (· ≠ μ) = S := by
      ext x; simp [Finset.mem_filter]
      intro hx heq; exact hμS (heq ▸ hx)
    rw [hfilt_eq] at hvanish


    simp only [] at hvanish
    have hv0 : v = 0 := by rw [hfm, hvanish]
    exact ⟨0, fun h => by simp, by rw [hv0]; simp⟩
lemma root_vec_raises_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
    (μ : Δ.𝔥 →ₗ[R] R) (w : X)
    (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) :
    ∀ (h : Δ.𝔥), ⁅(h : 𝔤), (⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ : X)⁆ =
      (α + μ) h • ⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ := by
  intro h

  have hleibniz := leibniz_lie (h : 𝔤) (↑(rd.posRootVec α hα) : 𝔤) w

  have hroot := rd.posRootVec_weight α hα h

  have hwt := hw_wt h
  rw [hroot, hwt] at hleibniz

  rw [smul_lie, LieModule.lie_smul] at hleibniz

  rw [hleibniz]
  simp only [LinearMap.add_apply]
  rw [← add_smul]

theorem dominant_weight_vectors_are_singular
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (μ : Δ.𝔥 →ₗ[R] R)
    (w : X)
    (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w)
    (hμ_max : ∀ (ν : Δ.𝔥 →ₗ[R] R) (v : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v) →
      rd.IsInQPlus (ν - μ) → ν ≠ μ → v = 0) :
    ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), w⁆ = 0 := by
  intro e

  obtain ⟨c, hc⟩ := rd.npos_span e

  have hew : (⁅(e : 𝔤), w⁆ : X) =
      ∑ x ∈ rd.posRoots.attach, c x.1 x.2 • ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), w⁆ := by
    conv_lhs => rw [show (e : 𝔤) = ∑ x ∈ rd.posRoots.attach,
      c x.1 x.2 • (↑(rd.posRootVec x.1 x.2) : 𝔤) from hc]
    rw [sum_lie]
    congr 1
    ext x
    rw [smul_lie]

  have hzero : ∀ (x : { x // x ∈ rd.posRoots }),
      ⁅(↑(rd.posRootVec x.1 x.2) : 𝔤), w⁆ = (0 : X) := by
    intro ⟨α, hα⟩
    apply hμ_max (α + μ)
    · exact root_vec_raises_weight α hα μ w hw_wt
    ·
      show rd.IsInQPlus (α + μ - μ)
      rw [add_sub_cancel_right]
      exact ⟨fun β => if β = α then 1 else 0, by simp [Finset.sum_ite_eq', hα]⟩
    ·
      intro heq
      apply rd.posRoots_ne_zero α hα
      have : α + μ - μ = μ - μ := by rw [heq]
      simp [add_sub_cancel_right, sub_self] at this
      exact this

  rw [hew]
  simp only [hzero, smul_zero, Finset.sum_const_zero]

theorem singular_vector_lift_in_O
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    {Y : Type*} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y)
    (f : X →ₗ⁅R, 𝔤⁆ Y)
    (hf : Function.Surjective f)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hμ_max : ∀ (ν : Δ.𝔥 →ₗ[R] R) (v : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v) →
      rd.IsInQPlus (ν - μ) → ν ≠ μ → v = 0)
    (v : Y)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = μ h • v)
    (_hv_sing : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) :
    ∃ (w : X),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), w⁆ = 0) ∧
      f w = v := by

  obtain ⟨w, hw_wt, hw_eq⟩ := weight_space_surjective_of_surjective hXO hYO f hf μ v hv_wt

  have hw_sing := dominant_weight_vectors_are_singular μ w hw_wt hμ_max
  exact ⟨w, hw_wt, hw_sing, hw_eq⟩

lemma IsInQPlus_antisymm_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hpos : rd.IsInQPlus μ)
    (hneg : rd.IsInQPlus (-μ)) :
    μ = 0 := by
  obtain ⟨c, hc⟩ := hpos
  obtain ⟨d, hd⟩ := hneg
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hμ (by rw [hc]; exact Finset.sum_eq_zero fun β hβ => by simp [hall β hβ])
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _; rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [Finset.ne_of_mem_erase hγ]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ; omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

def IsInBlockO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (_wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  IsCategoryO Δ rd M ∧


  ∃ (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R),
    GeneralizedEigenspaceCenter M ueaAct chi = ⊤















structure LieModule.CompositionSeriesOf
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  length : ℕ
  series : Fin (length + 1) → LieSubmodule R 𝔤 M
  bot : series ⟨0, Nat.zero_lt_succ length⟩ = ⊥
  top : series ⟨length, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤
  strictly_increasing : ∀ i : Fin length, series i.castSucc < series i.succ
  quotients_irreducible : ∀ i : Fin length,
    LieModule.IsIrreducible R 𝔤
      (↥(series i.succ) ⧸ (series i.castSucc).comap (series i.succ).incl)



theorem lieModule_isIrreducible_of_covBy
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {A B : LieSubmodule R 𝔤 M} (hcov : A ⋖ B) :
    LieModule.IsIrreducible R 𝔤 (↥B ⧸ LieSubmodule.comap B.incl A) := by
  set K := LieSubmodule.comap B.incl A
  have hne_top : K ≠ ⊤ := by
    intro h; apply ne_of_lt hcov.lt
    exact le_antisymm hcov.lt.le (fun x hx => by
      have := (h ▸ LieSubmodule.mem_top (R := R) (L := 𝔤) (⟨x, hx⟩ : ↥B) : (⟨x, hx⟩ : ↥B) ∈ K)
      simp at this; exact this)
  haveI : Nontrivial (↥B ⧸ K) := by
    change Nontrivial ((↥B : Type _) ⧸ (K : Submodule R ↥B))
    exact Submodule.Quotient.nontrivial_iff.mpr
      (fun h => hne_top (LieSubmodule.toSubmodule_injective h))
  apply LieModule.IsIrreducible.mk
  intro N hN
  set N' := LieSubmodule.comap (LieSubmodule.Quotient.mk' K) N
  have hK_le_N' : K ≤ N' := by
    intro x hx; show (LieSubmodule.Quotient.mk' K) x ∈ N
    rw [(LieSubmodule.Quotient.mk_eq_zero (N := K)).mpr hx]; exact N.zero_mem
  have hA_le : A ≤ LieSubmodule.map B.incl N' := by
    intro x hx; rw [LieSubmodule.mem_map]
    refine ⟨⟨x, hcov.lt.le hx⟩, hK_le_N' ?_, rfl⟩
    show ⟨x, hcov.lt.le hx⟩ ∈ LieSubmodule.comap B.incl A
    rw [LieSubmodule.mem_comap]; simp [LieSubmodule.incl_apply]; exact hx
  have hle_B : LieSubmodule.map B.incl N' ≤ B := LieSubmodule.map_incl_le
  rcases hcov.eq_or_eq hA_le hle_B with hmapA | hmapB
  ·
    exfalso; apply hN
    have hN'_eq : N' = K := le_antisymm
      (fun x hx => by rw [LieSubmodule.mem_comap]; rw [← hmapA]
                      exact (LieSubmodule.mem_map _).mpr ⟨x, hx, rfl⟩)
      hK_le_N'
    rw [eq_bot_iff]; intro q hq
    obtain ⟨b, rfl⟩ := LieSubmodule.Quotient.surjective_mk' K q
    rw [(LieSubmodule.Quotient.mk_eq_zero (N := K)).mpr (hN'_eq ▸ (hq : b ∈ N'))]
    exact LieSubmodule.zero_mem ⊥
  ·
    have hN'_eq_top : N' = ⊤ := by
      rw [eq_top_iff]; intro ⟨x, hxB⟩ _
      have hx_in_map : x ∈ LieSubmodule.map B.incl N' := hmapB.symm ▸ hxB
      obtain ⟨y, hy, hyx⟩ := (LieSubmodule.mem_map _).mp hx_in_map
      have : y = ⟨x, hxB⟩ := by
        ext; change (y : M) = x; rw [LieSubmodule.incl_eq_val] at hyx; exact hyx
      exact this ▸ hy
    rw [eq_top_iff]; intro q _
    obtain ⟨b, rfl⟩ := LieSubmodule.Quotient.surjective_mk' K q
    show (LieSubmodule.Quotient.mk' K) b ∈ N
    have : b ∈ N' := hN'_eq_top ▸ LieSubmodule.mem_top b
    exact this


section ProdLieModule

variable {R' : Type*} [CommRing R']
  {L' : Type*} [LieRing L'] [LieAlgebra R' L']
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R' M₁]
    [LieRingModule L' M₁] [LieModule R' L' M₁]
    [AddCommGroup M₂] [Module R' M₂]
    [LieRingModule L' M₂] [LieModule R' L' M₂]

noncomputable instance prodLieRingModule : LieRingModule L' (M₁ × M₂) where
  bracket x m := (⁅x, m.1⁆, ⁅x, m.2⁆)
  add_lie x y m := by ext <;> exact add_lie ..
  lie_add x m n := by ext <;> exact lie_add ..
  leibniz_lie x y m := by ext <;> [exact leibniz_lie x y m.1; exact leibniz_lie x y m.2]

noncomputable instance prodLieModule : LieModule R' L' (M₁ × M₂) where
  smul_lie r x m := by ext <;> exact smul_lie ..
  lie_smul r x m := by ext <;> exact lie_smul ..

variable {N' : Type*} [AddCommGroup N'] [Module R' N']
    [LieRingModule L' N'] [LieModule R' L' N']

noncomputable def prodLieModuleHom
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') :
    M₁ × M₂ →ₗ⁅R', L'⁆ N' where
  toFun m := f₁ m.1 + f₂ m.2
  map_add' m n := by simp [map_add, add_add_add_comm]
  map_smul' r m := by simp [map_smul, smul_add]
  map_lie' {x m} := by
    show f₁ ⁅x, m.1⁆ + f₂ ⁅x, m.2⁆ = ⁅x, f₁ m.1 + f₂ m.2⁆
    rw [lie_add, f₁.map_lie, f₂.map_lie]

omit [LieAlgebra R' L'] [LieModule R' L' M₁] [LieModule R' L' M₂] [LieModule R' L' N'] in
@[simp] lemma prodLieModuleHom_apply
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') (m : M₁ × M₂) :
    prodLieModuleHom f₁ f₂ m = f₁ m.1 + f₂ m.2 := rfl

end ProdLieModule

theorem IsProjectiveInO_prod
    {R' : Type uCatO} [CommRing R']
    {𝔤' : Type uCatO} [LieRing 𝔤'] [LieAlgebra R' 𝔤']
    {Δ : TriangularDecomposition R' 𝔤'}
    {rd : PositiveRootData Δ}
    {P₁ : Type uCatO} [AddCommGroup P₁] [Module R' P₁]
    [LieRingModule 𝔤' P₁] [LieModule R' 𝔤' P₁]
    {P₂ : Type uCatO} [AddCommGroup P₂] [Module R' P₂]
    [LieRingModule 𝔤' P₂] [LieModule R' 𝔤' P₂]
    {hP₁O : IsCategoryO Δ rd P₁} {hP₂O : IsCategoryO Δ rd P₂}
    (hP₁ : IsProjectiveInO rd P₁ hP₁O)
    (hP₂ : IsProjectiveInO rd P₂ hP₂O)
    (hProdO : IsCategoryO Δ rd (P₁ × P₂)) :
    IsProjectiveInO rd (P₁ × P₂) hProdO := by

  intro A _ _ _ _ hAO B _ _ _ _ hBO f hf g

  let g₁ : P₁ →ₗ⁅R', 𝔤'⁆ B :=
    { toFun := fun m => g (m, 0)
      map_add' := fun a b => by
        rw [show (a + b, (0 : P₂)) = (a, 0) + (b, 0) from
          Prod.ext rfl (add_zero 0).symm]
        exact map_add g _ _
      map_smul' := fun r m => by
        rw [show (r • m, (0 : P₂)) = r • (m, 0) from
          Prod.ext rfl (smul_zero r).symm]
        exact map_smul g r _
      map_lie' := fun {x m} => by
        rw [show (⁅x, m⁆, (0 : P₂)) = ⁅x, (m, (0 : P₂))⁆ from
          Prod.ext rfl (lie_zero x).symm]
        exact g.map_lie x _ }
  let g₂ : P₂ →ₗ⁅R', 𝔤'⁆ B :=
    { toFun := fun m => g (0, m)
      map_add' := fun a b => by
        rw [show ((0 : P₁), a + b) = (0, a) + (0, b) from
          Prod.ext (add_zero 0).symm rfl]
        exact map_add g _ _
      map_smul' := fun r m => by
        rw [show ((0 : P₁), r • m) = r • (0, m) from
          Prod.ext (smul_zero r).symm rfl]
        exact map_smul g r _
      map_lie' := fun {x m} => by
        rw [show ((0 : P₁), ⁅x, m⁆) = ⁅x, ((0 : P₁), m)⁆ from
          Prod.ext (lie_zero x).symm rfl]
        exact g.map_lie x _ }

  obtain ⟨h₁, hh₁⟩ := hP₁ A hAO B hBO f hf g₁
  obtain ⟨h₂, hh₂⟩ := hP₂ A hAO B hBO f hf g₂

  refine ⟨prodLieModuleHom h₁ h₂, fun p => ?_⟩
  simp only [prodLieModuleHom_apply, map_add, hh₁, hh₂]

  show g (p.1, 0) + g (0, p.2) = g p
  rw [← map_add g]
  congr 1
  ext <;> simp

theorem IsCategoryO_prod
    {R' : Type*} [CommRing R']
    {𝔤' : Type*} [LieRing 𝔤'] [LieAlgebra R' 𝔤']
    {Δ : TriangularDecomposition R' 𝔤'}
    {rd : PositiveRootData Δ}
    {M₁ : Type*} [AddCommGroup M₁] [Module R' M₁]
    [LieRingModule 𝔤' M₁] [LieModule R' 𝔤' M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R' M₂]
    [LieRingModule 𝔤' M₂] [LieModule R' 𝔤' M₂]
    (_hM₁ : IsCategoryO Δ rd M₁) (_hM₂ : IsCategoryO Δ rd M₂) :
    IsCategoryO Δ rd (M₁ × M₂) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨S₁, hS₁⟩ := _hM₁.finitely_generated
    obtain ⟨S₂, hS₂⟩ := _hM₂.finitely_generated

    let inl : M₁ →ₗ⁅R', 𝔤'⁆ (M₁ × M₂) :=
      { toFun := fun m => (m, 0)
        map_add' := fun a b => by ext <;> simp
        map_smul' := fun r m => by ext <;> simp
        map_lie' := fun {x m} => by
          show (⁅x, m⁆, (0 : M₂)) = (⁅x, m⁆, ⁅x, (0 : M₂)⁆)
          congr 1; exact (lie_zero x).symm }
    let inr : M₂ →ₗ⁅R', 𝔤'⁆ (M₁ × M₂) :=
      { toFun := fun m => (0, m)
        map_add' := fun a b => by ext <;> simp
        map_smul' := fun r m => by ext <;> simp
        map_lie' := fun {x m} => by
          show ((0 : M₁), ⁅x, m⁆) = (⁅x, (0 : M₁)⁆, ⁅x, m⁆)
          congr 1; exact (lie_zero x).symm }
    let S := S₁.image inl ∪ S₂.image inr
    refine ⟨S, ?_⟩
    rw [eq_top_iff]
    intro ⟨m₁, m₂⟩ _
    have hdecomp : (m₁, m₂) = inl m₁ + inr m₂ := by ext <;> simp [inl, inr]
    rw [hdecomp]
    apply (LieSubmodule.lieSpan R' 𝔤' (↑S : Set (M₁ × M₂))).add_mem
    ·

      have h_comap : LieSubmodule.lieSpan R' 𝔤' (↑S₁ : Set M₁) ≤
          LieSubmodule.comap inl (LieSubmodule.lieSpan R' 𝔤' (↑S : Set (M₁ × M₂))) := by
        rw [LieSubmodule.lieSpan_le]
        intro s hs
        simp only [S]
        apply LieSubmodule.subset_lieSpan
        simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
        left
        exact ⟨s, hs, rfl⟩
      rw [hS₁] at h_comap
      exact h_comap (LieSubmodule.mem_top m₁)
    ·
      have h_comap : LieSubmodule.lieSpan R' 𝔤' (↑S₂ : Set M₂) ≤
          LieSubmodule.comap inr (LieSubmodule.lieSpan R' 𝔤' (↑S : Set (M₁ × M₂))) := by
        rw [LieSubmodule.lieSpan_le]
        intro s hs
        simp only [S]
        apply LieSubmodule.subset_lieSpan
        simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
        right
        exact ⟨s, hs, rfl⟩
      rw [hS₂] at h_comap
      exact h_comap (LieSubmodule.mem_top m₂)

  ·
    intro ⟨m₁, m₂⟩
    obtain ⟨S₁, v₁, hm₁⟩ := _hM₁.weight_decomp m₁
    obtain ⟨S₂, v₂, hm₂⟩ := _hM₂.weight_decomp m₂
    refine ⟨S₁ ∪ S₂, fun μ => ⟨(if μ ∈ S₁ then (v₁ μ : M₁) else 0, if μ ∈ S₂ then (v₂ μ : M₂) else 0), ?_⟩, ?_⟩
    · intro h
      ext
      · show ⁅(↑h : 𝔤'), if μ ∈ S₁ then (v₁ μ : M₁) else 0⁆ =
              μ h • (if μ ∈ S₁ then (v₁ μ : M₁) else 0)
        split_ifs with h1
        · exact (v₁ μ).prop h
        · simp [lie_zero]
      · show ⁅(↑h : 𝔤'), if μ ∈ S₂ then (v₂ μ : M₂) else 0⁆ =
              μ h • (if μ ∈ S₂ then (v₂ μ : M₂) else 0)
        split_ifs with h2
        · exact (v₂ μ).prop h
        · simp [lie_zero]
    · ext
      ·
        show m₁ = (∑ μ ∈ S₁ ∪ S₂, (if μ ∈ S₁ then (v₁ μ : M₁) else 0, if μ ∈ S₂ then (v₂ μ : M₂) else 0)).1
        simp only [Prod.fst_sum]
        rw [hm₁, ← Finset.sum_filter]
        congr 1
        ext x; simp (config := { contextual := true }) [Finset.mem_filter, Finset.mem_union]
      ·
        show m₂ = (∑ μ ∈ S₁ ∪ S₂, (if μ ∈ S₁ then (v₁ μ : M₁) else 0, if μ ∈ S₂ then (v₂ μ : M₂) else 0)).2
        simp only [Prod.snd_sum]
        rw [hm₂, ← Finset.sum_filter]
        congr 1
        ext x; simp (config := { contextual := true }) [Finset.mem_filter, Finset.mem_union]
  ·
    obtain ⟨bds₁, hbds₁⟩ := _hM₁.weight_bound
    obtain ⟨bds₂, hbds₂⟩ := _hM₂.weight_bound
    refine ⟨bds₁ ∪ bds₂, fun μ hμ => ?_⟩


    simp only [weights, Set.mem_setOf_eq] at hμ
    rw [Submodule.ne_bot_iff] at hμ
    obtain ⟨⟨m₁, m₂⟩, hm, hne⟩ := hμ


    have hm₁_wt : m₁ ∈ WeightSpace Δ M₁ μ := by
      intro h
      have := congr_arg Prod.fst (hm h)
      exact this
    have hm₂_wt : m₂ ∈ WeightSpace Δ M₂ μ := by
      intro h
      have := congr_arg Prod.snd (hm h)
      exact this
    have h_or : m₁ ≠ 0 ∨ m₂ ≠ 0 := by
      by_contra h_neg
      push Not at h_neg

      exact hne (Prod.ext h_neg.1 h_neg.2)
    cases h_or with
    | inl hm₁_ne =>
      have hμ₁ : μ ∈ weights Δ M₁ := by
        simp only [weights, Set.mem_setOf_eq]
        rw [Submodule.ne_bot_iff]
        exact ⟨m₁, hm₁_wt, hm₁_ne⟩
      obtain ⟨wt, hwt, hq⟩ := hbds₁ μ hμ₁
      exact ⟨wt, Finset.mem_union_left _ hwt, hq⟩
    | inr hm₂_ne =>
      have hμ₂ : μ ∈ weights Δ M₂ := by
        simp only [weights, Set.mem_setOf_eq]
        rw [Submodule.ne_bot_iff]
        exact ⟨m₂, hm₂_wt, hm₂_ne⟩
      obtain ⟨wt, hwt, hq⟩ := hbds₂ μ hμ₂
      exact ⟨wt, Finset.mem_union_right _ hwt, hq⟩



















def LieModule.CompositionSeriesOf.countFactorsIso
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs : LieModule.CompositionSeriesOf rd M)
    (L : Type*) [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] : ℕ :=
  Finset.card (Finset.univ.filter fun (i : Fin cs.length) =>
    Nonempty (L ≃ₗ⁅R, 𝔤⁆ (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl)))



noncomputable def quotTopBotLieModuleEquiv
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] :
    (↥(⊤ : LieSubmodule R 𝔤 L) ⧸
      ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl)) ≃ₗ⁅R,𝔤⁆ L := by
  have hbot_sub : ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule = ⊥ := by
    have h : (⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl = ⊥ := by
      rw [LieSubmodule.comap_incl_eq_bot]; simp
    simp [h]
  exact {
    ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule.quotEquivOfEqBot
      hbot_sub |>.trans (LinearEquiv.ofTop (⊤ : Submodule R L) rfl) with
    map_lie' := by
      intro x q
      induction q using Quotient.inductionOn'
      rfl
  }

lemma schur_lie_module_noniso_zero
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (_h1 : LieModule.IsIrreducible R 𝔤 M₁)
    (_h2 : LieModule.IsIrreducible R 𝔤 M₂)
    (_hne : ¬ Nonempty (M₁ ≃ₗ⁅R, 𝔤⁆ M₂)) :
    Module.finrank R (M₁ →ₗ⁅R, 𝔤⁆ M₂) = 0 := by

  have hall_zero : ∀ f : M₁ →ₗ⁅R, 𝔤⁆ M₂, f = 0 := by
    intro f
    by_contra hf
    apply _hne

    have hker : f.ker ≠ ⊤ := by
      intro h
      apply hf
      ext x
      have : x ∈ f.ker := by rw [h]; trivial
      rwa [LieModuleHom.mem_ker] at this

    have hker_bot : f.ker = ⊥ :=
      (_h1.eq_bot_or_eq_top f.ker).resolve_right hker

    have hinj : Function.Injective f := (LieModuleHom.ker_eq_bot f).mp hker_bot

    have hrange_ne_bot : f.range ≠ ⊥ := by
      intro h
      apply hf
      ext x
      have : f x ∈ f.range := ⟨x, rfl⟩
      rw [h] at this
      simp [LieSubmodule.mem_bot] at this
      simp [this]

    have hrange_top : f.range = ⊤ :=
      (_h2.eq_bot_or_eq_top f.range).resolve_left hrange_ne_bot

    have hsurj : Function.Surjective f := (LieModuleHom.range_eq_top f).mp hrange_top

    let e : M₁ ≃ₗ[R] M₂ := LinearEquiv.ofBijective (f : M₁ →ₗ[R] M₂) ⟨hinj, hsurj⟩
    exact ⟨{
      f with
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
    }⟩

  haveI : Subsingleton (M₁ →ₗ⁅R, 𝔤⁆ M₂) := ⟨fun a b => by
    rw [hall_zero a, hall_zero b]⟩
  exact Module.finrank_zero_of_subsingleton

lemma lie_endo_is_scalar
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hirr : LieModule.IsIrreducible R 𝔤 M)
    [FiniteDimensional R M]
    (f : M →ₗ⁅R, 𝔤⁆ M) : ∃ c : R, f = c • LieModuleHom.id := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible R 𝔤 M
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f : M →ₗ[R] M)
  use c
  set g : M →ₗ⁅R, 𝔤⁆ M := f - c • LieModuleHom.id
  suffices g = 0 by rwa [sub_eq_zero] at this
  have hker_ne_bot : g.ker ≠ ⊥ := by
    rw [Module.End.hasEigenvalue_iff] at hc
    intro h; apply hc; rw [eq_bot_iff]
    intro x hx; rw [Module.End.mem_eigenspace_iff] at hx
    have : x ∈ g.ker := by
      rw [LieModuleHom.mem_ker]
      have : g x = f x - c • x := by
        show (f - c • LieModuleHom.id).toFun x = f x - c • x
        simp [LieModuleHom.sub_apply, LieModuleHom.smul_apply, LieModuleHom.id_apply]
      rw [this]; exact sub_eq_zero.mpr hx
    rw [h] at this; exact this
  ext x
  have hx : x ∈ g.ker := by
    rw [(hirr.eq_bot_or_eq_top g.ker).resolve_left hker_ne_bot]
    exact LieSubmodule.mem_top x
  rwa [LieModuleHom.mem_ker] at hx

lemma schur_lie_module_iso_one
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (_h1 : LieModule.IsIrreducible R 𝔤 M₁)
    (_h2 : LieModule.IsIrreducible R 𝔤 M₂)
    (_hiso : Nonempty (M₁ ≃ₗ⁅R, 𝔤⁆ M₂))
    [FiniteDimensional R M₁] :
    Module.finrank R (M₁ →ₗ⁅R, 𝔤⁆ M₂) = 1 := by
  obtain ⟨σ⟩ := _hiso
  apply finrank_eq_one (σ.toLieModuleHom)
  ·
    intro h
    haveI : Nontrivial M₁ := LieModule.nontrivial_of_isIrreducible R 𝔤 M₁
    obtain ⟨x, hx⟩ := exists_ne (0 : M₁)
    apply hx; apply σ.injective
    have : σ.toLieModuleHom x = 0 := by rw [h]; simp
    rw [show σ x = σ.toLieModuleHom x from rfl, this, map_zero]
  ·
    intro f

    set g : M₁ →ₗ⁅R, 𝔤⁆ M₁ := LieModuleHom.comp σ.symm.toLieModuleHom f

    obtain ⟨c, hc⟩ := lie_endo_is_scalar _h1 g
    use c
    ext x

    have hgx : σ.symm (f x) = c • x := by
      have := congr_arg (· x) hc
      simp [LieModuleHom.smul_apply] at this
      exact this
    have hfx : f x = σ (c • x) := by
      rw [← hgx, LieModuleEquiv.apply_symm_apply]
    rw [LieModuleHom.smul_apply, hfx, map_smul]
    rfl

lemma radical_le_ker_of_hom_to_simple
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L]
    (hL_simple : LieModule.IsIrreducible R 𝔤 L)
    {J : LieSubmodule R 𝔤 P}
    (hJ_proper : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)
    (f : P →ₗ⁅R, 𝔤⁆ L) : J ≤ f.ker := by
  rcases hL_simple.eq_bot_or_eq_top f.range with hrange | hrange
  ·
    have hf0 : f = 0 := by
      ext x
      have hx : f x ∈ f.range := (LieModuleHom.mem_range f (f x)).mpr ⟨x, rfl⟩
      rw [hrange] at hx; simpa [LieSubmodule.mem_bot] using hx
    rw [hf0]; intro x _; simp [LieModuleHom.mem_ker]
  ·

    rcases hL_simple.eq_bot_or_eq_top (LieSubmodule.map f J) with hfJ | hfJ
    ·
      exact (LieModuleHom.le_ker_iff_map J).mpr hfJ
    ·
      exfalso; apply hJ_proper
      ext p; simp only [LieSubmodule.mem_top, iff_true]

      have hfp : f p ∈ LieSubmodule.map f J := hfJ ▸ LieSubmodule.mem_top _
      obtain ⟨j, hj, hjp⟩ := (LieSubmodule.mem_map (f p)).mp hfp

      have hker_ne_top : f.ker ≠ ⊤ := by
        intro hk
        have hf0 : f = 0 := by
          ext x; exact LieModuleHom.mem_ker.mp (hk ▸ LieSubmodule.mem_top x)
        have hrange0 : (0 : P →ₗ⁅R, 𝔤⁆ L).range = ⊥ := by
          ext y; constructor
          · intro hy; rw [LieModuleHom.mem_range] at hy; obtain ⟨a, ha⟩ := hy
            simp at ha; rw [LieSubmodule.mem_bot]; exact ha.symm
          · intro hy; rw [LieSubmodule.mem_bot] at hy; rw [hy]
            rw [LieModuleHom.mem_range]; exact ⟨0, by simp⟩
        rw [hf0, hrange0] at hrange; exact absurd hrange bot_ne_top

      have hker_le := hJ_max f.ker hker_ne_top

      have hpj_ker : p - j ∈ f.ker :=
        LieModuleHom.mem_ker.mpr (by rw [map_sub, hjp, sub_self])
      have : p = j + (p - j) := by abel
      rw [this]; exact J.add_mem hj (hker_le hpj_ker)

noncomputable def LieModuleHom.liftQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (f : P →ₗ⁅R, 𝔤⁆ L) (h : J ≤ f.ker) :
    (P ⧸ J) →ₗ⁅R, 𝔤⁆ L where
  toLinearMap := J.toSubmodule.liftQ f.toLinearMap (by
    intro x hx; exact LinearMap.mem_ker.mpr (LieModuleHom.mem_ker.mp (h hx)))
  map_lie' := by
    intro x m
    induction m using Quotient.inductionOn' with | h m =>
    show f ⁅x, m⁆ = ⁅x, f m⁆
    exact f.map_lie x m

noncomputable def homEquivThroughQuotient
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (hfact : ∀ (f : P →ₗ⁅R, 𝔤⁆ L), J ≤ f.ker) :
    ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) ≃ₗ[R] (P →ₗ⁅R, 𝔤⁆ L) :=
  LinearEquiv.ofBijective
    { toFun := fun g => g.comp (LieSubmodule.Quotient.mk' J)
      map_add' := fun g₁ g₂ => by ext; simp
      map_smul' := fun r g => by ext; simp }
    ⟨by

      intro g₁ g₂ h
      ext ⟨m⟩
      exact LieModuleHom.congr_fun h m
    , by

      intro f
      exact ⟨LieModuleHom.liftQ f (hfact f), by
        ext p; rfl⟩
    ⟩

theorem projective_hom_simple_kronecker_delta
    {R : Type*} [Field R] [IsAlgClosed R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {J : LieSubmodule R 𝔤 P}
    (hJ_proper : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)

    [FiniteDimensional R (P ⧸ J)]

    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    (hL_simple : LieModule.IsIrreducible R 𝔤 L) :

    (Nonempty (L ≃ₗ⁅R, 𝔤⁆ (P ⧸ J)) →
      Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) = 1) ∧
    (¬ Nonempty (L ≃ₗ⁅R, 𝔤⁆ (P ⧸ J)) →
      Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) = 0) := by

  have hfact : ∀ (f : P →ₗ⁅R, 𝔤⁆ L), J ≤ f.ker :=
    fun f => radical_le_ker_of_hom_to_simple hL_simple hJ_proper hJ_max f

  have hequiv : ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) ≃ₗ[R] (P →ₗ⁅R, 𝔤⁆ L) :=
    homEquivThroughQuotient hfact

  have hJcoatom : IsCoatom J :=
    ⟨hJ_proper, fun K hJK => by
      by_contra hK
      exact lt_irrefl J (lt_of_lt_of_le hJK (hJ_max K hK))⟩
  have hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J) := by
    haveI : Nontrivial (LieSubmodule R 𝔤 (P ⧸ J)) := by
      refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro h
      apply hJcoatom.1
      rw [eq_top_iff]
      intro p _
      have := (show LieSubmodule.Quotient.mk' J p ∈ (⊤ : LieSubmodule R 𝔤 (P ⧸ J))
        from LieSubmodule.mem_top _)
      rw [← h] at this
      simp [LieSubmodule.mem_bot] at this
      exact this
    exact {
      eq_bot_or_eq_top := by
        intro N
        set N' := LieSubmodule.comap (LieSubmodule.Quotient.mk' J) N
        have hJ_le_N' : J ≤ N' := by
          intro x hx
          show (LieSubmodule.Quotient.mk' J) x ∈ N
          rw [(LieSubmodule.Quotient.mk_eq_zero J).mpr hx]
          exact N.zero_mem
        rcases eq_or_lt_of_le hJ_le_N' with hJN | hJN
        · left
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨p, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
          simp only [LieSubmodule.mem_bot]
          rw [LieSubmodule.Quotient.mk_eq_zero]
          exact hJN ▸ (hx : p ∈ N')
        · right
          rw [eq_top_iff]
          intro x _
          obtain ⟨p, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
          exact (show p ∈ N' from by rw [hJcoatom.2 N' hJN]; exact LieSubmodule.mem_top _)
    }

  have hfinrank : Module.finrank R (P →ₗ⁅R, 𝔤⁆ L) =
      Module.finrank R ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) :=
    (hequiv.finrank_eq).symm

  constructor
  ·
    intro ⟨iso⟩
    rw [hfinrank]

    exact schur_lie_module_iso_one hPJ_irr hL_simple ⟨iso.symm⟩
  ·
    intro hne
    rw [hfinrank]

    have hne' : ¬ Nonempty ((P ⧸ J) ≃ₗ⁅R, 𝔤⁆ L) := by
      intro ⟨iso⟩; exact hne ⟨iso.symm⟩
    exact schur_lie_module_noniso_zero hPJ_irr hL_simple hne'










end
