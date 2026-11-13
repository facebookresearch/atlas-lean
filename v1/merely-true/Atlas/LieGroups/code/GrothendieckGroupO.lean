/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ProjectiveFunctors
import Atlas.LieGroups.code.HeckeKL

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure GrothendieckGroupData (Δ : TriangularDecomposition R 𝔤) where
  carrier : Type u
  instACG : AddCommGroup carrier
  instMod : @Module ℤ carrier _ instACG.toAddCommMonoid
  delta : (Δ.𝔥 →ₗ[R] R) → carrier
  pairing : carrier → carrier → ℤ
  pairing_orthonormal : ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
    pairing (delta lam) (delta mu) = if lam = mu then 1 else 0
  pairing_basis_determines :
    ∀ (h₁ h₂ : carrier → carrier → ℤ),
      (∀ lam mu : Δ.𝔥 →ₗ[R] R,
        h₁ (delta lam) (delta mu) = h₂ (delta lam) (delta mu)) →
      ∀ (x y : carrier), h₁ x y = h₂ x y

structure GrothendieckGroupData.InnerProductData
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) where
  pairing : KO.carrier → KO.carrier → ℤ
  orthonormal : ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
    pairing (KO.delta lam) (KO.delta mu) = if lam = mu then 1 else 0
  pairing_basis_determines :
    ∀ (h₁ h₂ : KO.carrier → KO.carrier → ℤ),
      (∀ lam mu : Δ.𝔥 →ₗ[R] R,
        h₁ (KO.delta lam) (KO.delta mu) = h₂ (KO.delta lam) (KO.delta mu)) →
      ∀ (x y : KO.carrier), h₁ x y = h₂ x y


structure WeylActionData
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ) where
  act : wg.W → KO.carrier → KO.carrier
  act_delta : ∀ (w : wg.W) (lam : Δ.𝔥 →ₗ[R] R),
    act w (KO.delta lam) = KO.delta (wg.dualAction w lam)


structure AdjointPairDataWeak where
  F : EndoFunctorData R 𝔤
  Fv : EndoFunctorData R 𝔤
  adjunction_fwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom (F.obj M) N → RepGfHom M (Fv.obj N)
  adjunction_bwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom M (Fv.obj N) → RepGfHom (F.obj M) N





def DominatesSet
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=
  ∀ mu ∈ S, rd.IsInQPlus (lam - mu)

structure WeightBilinForm {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ) where
  form : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  symm : ∀ (mu nu : Δ.𝔥 →ₗ[R] R), form mu nu = form nu mu
  bilin_left : ∀ (mu₁ mu₂ nu : Δ.𝔥 →ₗ[R] R),
    form (mu₁ + mu₂) nu = form mu₁ nu + form mu₂ nu
  weyl_normSq_invariant : ∀ (w : wg.W) (mu nu : Δ.𝔥 →ₗ[R] R),
    form (wg.dualAction w mu - wg.dualAction w nu)
         (wg.dualAction w mu - wg.dualAction w nu) = form (mu - nu) (mu - nu)
  pos_semidef : ∀ [LinearOrder R] [IsStrictOrderedRing R] (mu : Δ.𝔥 →ₗ[R] R),
    (0 : R) ≤ form mu mu
  form_corootPairing_compat :
    ∀ (rd : PositiveRootData Δ) (alpha mu : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rd.posRoots),
    2 • form alpha mu = rd.corootPairing mu alpha * form alpha alpha
  dominant_corootPairing_diff_nonneg :
    ∀ [LinearOrder R] [IsStrictOrderedRing R]
      (rd : PositiveRootData Δ)
      (lam phi alpha : Δ.𝔥 →ₗ[R] R)
      (_ : IsDominantWeightBruhat rd wg lam)
      (_ : BruhatLE rd phi lam)
      (_ : alpha ∈ rd.posRoots),
    (0 : R) ≤ rd.corootPairing (lam - phi) alpha
  form_coroot_compat :
    ∀ (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
      (alpha mu : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rs.allRoots),
    2 • form alpha mu = mu (rs.coroot alpha) * form alpha alpha
  form_posRoot_pos :
    ∀ [LinearOrder R] [IsStrictOrderedRing R]
      (rd : PositiveRootData Δ)
      (alpha : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rd.posRoots),
    (0 : R) < form alpha alpha

theorem WeightBilinForm.form_posRoot_nonneg
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (alpha : Δ.𝔥 →ₗ[R] R)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) ≤ B.form alpha alpha :=
  B.pos_semidef alpha

theorem WeightBilinForm.form_corootPairing_compat_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (alpha mu : Δ.𝔥 →ₗ[R] R)
    (halpha : alpha ∈ rd.posRoots) :
    2 • B.form alpha mu = rd.corootPairing mu alpha * B.form alpha alpha :=
  B.form_corootPairing_compat rd alpha mu halpha

theorem dominant_corootPairing_diff_nonneg_ax
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ) (B : WeightBilinForm wg)

    (lam phi alpha : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) ≤ rd.corootPairing (lam - phi) alpha :=
  B.dominant_corootPairing_diff_nonneg rd lam phi alpha hlam_dom hphi_le halpha_pos

theorem WeightBilinForm.form_posRoot_dominant_diff_nonneg
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) ≤ B.form alpha (lam - phi) := by

  have hcompat := B.form_corootPairing_compat_ax rd alpha (lam - phi) halpha_pos

  have hpair_nonneg := dominant_corootPairing_diff_nonneg_ax rd wg B lam phi alpha hlam_dom hphi_le halpha_pos

  have haa_nonneg := B.pos_semidef alpha

  have hprod_nonneg : (0 : R) ≤ rd.corootPairing (lam - phi) alpha * B.form alpha alpha :=
    mul_nonneg hpair_nonneg haa_nonneg
  have h2_nonneg : (0 : R) ≤ 2 • B.form alpha (lam - phi) := by rw [hcompat]; exact hprod_nonneg

  rw [two_nsmul] at h2_nonneg
  linarith

theorem WeightBilinForm.cross_terms_nonneg
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (_hn_pos : 0 < n) :
    (0 : R) ≤ n • B.form alpha (lam - phi) + n • B.form alpha (lam - phi) +
          n • (n • B.form alpha alpha) := by
  have h_cross := B.form_posRoot_dominant_diff_nonneg rd lam phi alpha hlam_dom hphi_le halpha_pos
  have h_sq := B.form_posRoot_nonneg rd alpha halpha_pos
  have h1 : (0 : R) ≤ n • B.form alpha (lam - phi) := nsmul_nonneg h_cross n
  have h2 : (0 : R) ≤ n • B.form alpha alpha := nsmul_nonneg h_sq n
  have h3 : (0 : R) ≤ n • (n • B.form alpha alpha) := nsmul_nonneg h2 n
  linarith

theorem WeightBilinForm.form_coroot_compat_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
    (alpha mu : Δ.𝔥 →ₗ[R] R)
    (halpha : alpha ∈ rs.allRoots) :
    2 • B.form alpha mu = mu (rs.coroot alpha) * B.form alpha alpha :=
  B.form_coroot_compat rd rs alpha mu halpha

theorem WeightBilinForm.form_posRoot_pos_ax
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (alpha : Δ.𝔥 →ₗ[R] R)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) < B.form alpha alpha :=
  B.form_posRoot_pos rd alpha halpha_pos

theorem WeightBilinForm.norm_diff_factor_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
    (v alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (halpha : alpha ∈ rs.allRoots) :
    B.form (v + n • alpha) (v + n • alpha) - B.form v v =
      (n : R) * v (rs.coroot alpha) * B.form alpha alpha +
      (n : R) * (n : R) * B.form alpha alpha := by

  have form_zero_left : ∀ (nu : Δ.𝔥 →ₗ[R] R), B.form 0 nu = 0 := by
    intro nu
    have h := B.bilin_left 0 0 nu
    rw [zero_add] at h

    have h2 : B.form 0 nu + 0 = B.form 0 nu + B.form 0 nu := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have form_nsmul_left : ∀ (m : ℕ) (mu nu : Δ.𝔥 →ₗ[R] R),
      B.form (m • mu) nu = m • B.form mu nu := by

    intro m mu nu
    induction m with
    | zero => simp [form_zero_left nu]
    | succ m ih => rw [succ_nsmul, B.bilin_left, ih, succ_nsmul]

  have e1 : B.form v (v + n • alpha) = B.form v v + B.form v (n • alpha) := by
    rw [B.symm v (v + n • alpha), B.bilin_left, B.symm v v, B.symm (n • alpha) v]
  have e2 : B.form (n • alpha) (v + n • alpha) =
      B.form (n • alpha) v + B.form (n • alpha) (n • alpha) := by
    rw [B.symm (n • alpha) (v + n • alpha), B.bilin_left,
        B.symm v (n • alpha), B.symm (n • alpha) (n • alpha)]
  have hexpand : B.form (v + n • alpha) (v + n • alpha) =
      B.form v v + (n • B.form alpha v + n • B.form alpha v +
        n • (n • B.form alpha alpha)) := by
    rw [B.bilin_left, e1, e2]
    rw [form_nsmul_left n alpha v]
    rw [B.symm v (n • alpha), form_nsmul_left n alpha v]
    rw [form_nsmul_left n alpha (n • alpha), B.symm alpha (n • alpha),
        form_nsmul_left n alpha alpha]
    ring

  simp only [nsmul_eq_mul] at hexpand

  have hcompat := B.form_coroot_compat_ax rd rs alpha v halpha
  simp only [nsmul_eq_mul] at hcompat

  push_cast at hcompat


  have hdiff : B.form (v + n • alpha) (v + n • alpha) - B.form v v =
      ↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha) := by
    have : B.form v v + (↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha)) - B.form v v =
        ↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha) := by ring
    rw [hexpand]; exact this

  have hcross : ↑n * B.form alpha v + ↑n * B.form alpha v = ↑n * (2 * B.form alpha v) := by ring
  rw [hdiff, hcross, hcompat]
  ring

theorem WeightBilinForm.norm_eq_coroot_zero
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
    (lam b alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hn_pos : 0 < n)
    (hpair : rd.corootPairing b alpha = (n : R))
    (h_eq : B.form (lam - b) (lam - b) = B.form (lam - b + n • alpha) (lam - b + n • alpha)) :
    lam (rs.coroot alpha) = 0 := by

  have hα_root : alpha ∈ rs.allRoots := rs.posRoots_sub alpha halpha_pos

  set v := lam - b with hv_def
  set aα := B.form alpha alpha with haα_def
  set c := lam (rs.coroot alpha) with hc_def

  have hdiff : B.form (v + n • alpha) (v + n • alpha) - B.form v v = 0 := by linarith

  have hfact := B.norm_diff_factor_ax rd rs v alpha n hα_root

  have hzero : (↑n : R) * v (rs.coroot alpha) * aα + (↑n : R) * (↑n : R) * aα = 0 := by
    linarith

  have hv_eval : v (rs.coroot alpha) = c - (↑n : R) := by
    simp only [hv_def, hc_def, LinearMap.sub_apply]
    rw [← rs.corootPairing_eq_eval alpha hα_root b]
    rw [hpair]

  rw [hv_eval] at hzero


  have hfactor : (↑n : R) * aα * c = 0 := by ring_nf; linarith

  have hn_pos_R : (0 : R) < (↑n : R) := Nat.cast_pos.mpr hn_pos
  have haα_pos : (0 : R) < aα := B.form_posRoot_pos_ax rd alpha halpha_pos

  have hna_pos : (0 : R) < (↑n : R) * aα := mul_pos hn_pos_R haα_pos
  have hna_ne : (↑n : R) * aα ≠ 0 := ne_of_gt hna_pos

  have hfactor' : (↑n : R) * aα * c = (↑n : R) * aα * 0 := by rw [mul_zero]; exact hfactor
  exact mul_left_cancel₀ hna_ne hfactor'

theorem WeightBilinForm.dominant_posRoot_cross_le
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hn_pos : 0 < n) :
    B.form (lam - phi) (lam - phi) ≤
      B.form (lam - phi) (lam - phi) +
        (n • B.form alpha (lam - phi) + n • B.form alpha (lam - phi) +
          n • (n • B.form alpha alpha)) :=
  le_add_of_nonneg_right (B.cross_terms_nonneg rd lam phi alpha n hlam_dom hphi_le halpha_pos hn_pos)

def WeightBilinForm.normSq {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg) (mu : Δ.𝔥 →ₗ[R] R) : R :=
  B.form mu mu

structure GrothendieckGroupBlock
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) where
  carrier : Type u
  instACG : AddCommGroup carrier
  instMod : @Module ℤ carrier _ instACG.toAddCommMonoid
  delta_w : wg.W → carrier
  basis_injective : Function.Injective delta_w
  basis_linearIndep :
    letI := instACG; letI := instMod
    ∀ (c : wg.W → ℤ),
      (Finset.univ.sum (fun w => (c w) • (delta_w w)) = (0 : carrier)) →
      ∀ w, c w = 0

section Theorems

variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)























def grothendieck_group_has_inner_product
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) :
    KO.InnerProductData :=
  { pairing := KO.pairing
    orthonormal := KO.pairing_orthonormal
    pairing_basis_determines := KO.pairing_basis_determines }

theorem inner_product_nondegen
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (a b : KO.carrier)
    (h : ∀ mu : Δ.𝔥 →ₗ[R] R, ip.pairing (KO.delta mu) a = ip.pairing (KO.delta mu) b) :
    a = b := by


  have delta_surj : ∀ (c : KO.carrier), ∃ lam, KO.delta lam = c := by
    intro c
    by_contra hc
    push Not at hc
    have key := ip.pairing_basis_determines
      (fun x _ => if x = c then (1 : ℤ) else 0)
      (fun _ _ => (0 : ℤ))
      (fun lam _ => by simp [if_neg (hc lam)])
    have := key c c
    simp at this

  obtain ⟨la, hla⟩ := delta_surj a
  obtain ⟨lb, hlb⟩ := delta_surj b


  have h_la := h la
  rw [← hla, ← hlb] at h_la
  rw [ip.orthonormal la la, ip.orthonormal la lb] at h_la
  simp at h_la
  rw [← hla, ← hlb, h_la]






theorem direct_summand_preserves_exact
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F G : EndoFunctorData R 𝔤)
    (h_summand : IsDirectSummand F G)
    (hG_exact : ∀ {M₁ M₂ M₃ : RepGfObj R 𝔤}
      (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
      (_hex : IsExactSequence f g),
      IsExactSequence (G.mapHom f) (G.mapHom g))
    {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (hex : IsExactSequence f g) :
    IsExactSequence (F.mapHom f) (F.mapHom g) := by
  obtain ⟨i, p, hpi⟩ := h_summand
  have hG := hG_exact f g hex
  intro m
  constructor
  ·
    intro hm


    have hi_nat_g := i.naturality g m

    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_g

    have hi_zero : (i.app M₃).toFun ((F.mapHom g).toFun m) = 0 := by
      rw [hm, map_zero]
    rw [hi_nat_g] at hi_zero

    have ⟨y, hy⟩ := (hG ((i.app M₂).toFun m)).mp hi_zero

    use (p.app M₁).toFun y


    have hp_nat_f := p.naturality f y
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hp_nat_f

    rw [← hp_nat_f, hy]

    have hpi_M₂ := hpi M₂ m
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp,
               Function.comp_apply, NatTransData.id, RepGfHom.id,
               LieModuleHom.coe_id, id_eq] at hpi_M₂
    exact hpi_M₂
  ·
    rintro ⟨x, hx⟩
    rw [← hx]


    have hi_nat_f := i.naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_f

    have hi_nat_g := i.naturality g ((F.mapHom f).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_g

    rw [hi_nat_f] at hi_nat_g

    have hker : (G.mapHom g).toFun ((G.mapHom f).toFun ((i.app M₁).toFun x)) = 0 := by
      exact (hG ((G.mapHom f).toFun ((i.app M₁).toFun x))).mpr ⟨(i.app M₁).toFun x, rfl⟩

    rw [hker] at hi_nat_g

    have hpi_M₃ := hpi M₃ ((F.mapHom g).toFun ((F.mapHom f).toFun x))
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp,
               Function.comp_apply, NatTransData.id, RepGfHom.id,
               LieModuleHom.coe_id, id_eq] at hpi_M₃
    rw [← hpi_M₃, hi_nat_g, map_zero]






theorem InnerProductData.pairing_symm
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {KO : GrothendieckGroupData Δ}
    (ip : KO.InnerProductData)
    (x y : KO.carrier) : ip.pairing x y = ip.pairing y x := by
  apply ip.pairing_basis_determines (fun a b => ip.pairing a b) (fun a b => ip.pairing b a)
  intro lam mu
  rw [ip.orthonormal, ip.orthonormal]
  simp [eq_comm]













theorem dominatesSet_implies_isDominantWeightLE
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S)
    (h_orbit : ∀ w ∈ WeylStabilizerModQ rd wg lam, wg.dualAction w lam ∈ S) :
    IsDominantWeightLE rd wg lam := by
  intro w hw hle


  have h_wle : WeightLE rd (wg.dualAction w lam) lam := hdom (wg.dualAction w lam) (h_orbit w hw)
  exact weightLE_antisymm rd _ _ hle h_wle


theorem IsInQPlus_antisymm
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
    apply hμ
    rw [hc]
    apply Finset.sum_eq_zero
    intro β hβ
    simp [hall β hβ]
  obtain ⟨β, hβ, hcβ⟩ := hne

  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _
    rw [add_nsmul]

  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract


  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ

  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hne : γ ≠ β := Finset.ne_of_mem_erase hγ
    simp [hne]


  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]

  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ
    omega

  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩







lemma WeightBilinForm.form_zero_left {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} (B : WeightBilinForm wg) (nu : Δ.𝔥 →ₗ[R] R) :
    B.form 0 nu = 0 := by
  have h := B.bilin_left 0 0 nu
  rw [zero_add] at h
  have : B.form 0 nu + B.form 0 nu - B.form 0 nu = B.form 0 nu - B.form 0 nu := by
    rw [← h]
  simp [add_sub_cancel_right] at this
  exact this

lemma WeightBilinForm.form_nsmul_left {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} (B : WeightBilinForm wg) (n : ℕ)
    (mu nu : Δ.𝔥 →ₗ[R] R) :
    B.form (n • mu) nu = n • B.form mu nu := by
  induction n with
  | zero => simp [B.form_zero_left nu]
  | succ n ih =>
    rw [succ_nsmul, B.bilin_left, ih, succ_nsmul]

lemma WeightBilinForm.form_expand {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} (B : WeightBilinForm wg)
    (v alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ) :
    B.form (v + n • alpha) (v + n • alpha) =
    B.form v v + (n • B.form alpha v + n • B.form alpha v +
      n • (n • B.form alpha alpha)) := by
  rw [B.bilin_left]
  have e1 : B.form v (v + n • alpha) = B.form v v + B.form v (n • alpha) := by
    rw [B.symm v (v + n • alpha), B.bilin_left, B.symm v v, B.symm (n • alpha) v]
  have e2 : B.form (n • alpha) (v + n • alpha) =
      B.form (n • alpha) v + B.form (n • alpha) (n • alpha) := by
    rw [B.symm (n • alpha) (v + n • alpha), B.bilin_left,
        B.symm v (n • alpha), B.symm (n • alpha) (n • alpha)]
  rw [e1, e2]
  rw [B.form_nsmul_left n alpha v]
  rw [B.symm v (n • alpha), B.form_nsmul_left n alpha v]
  rw [B.form_nsmul_left n alpha (n • alpha), B.symm alpha (n • alpha),
      B.form_nsmul_left n alpha alpha]
  ring

theorem norm_sq_dominant_reflection_nonneg_diff
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hn_pos : 0 < n) :
    B.normSq (lam - phi) ≤ B.normSq (lam - phi + n • alpha) := by

  unfold WeightBilinForm.normSq

  have hexpand := B.form_expand (lam - phi) alpha n


  have hle := B.dominant_posRoot_cross_le rd lam phi alpha n hlam_dom hphi_le halpha_pos hn_pos

  rw [hexpand]
  exact hle

theorem norm_sq_single_step_le
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (lam a b : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hb_le : BruhatLE rd b lam)
    (hstep : ∃ α, ReflectionLT rd α a b) :
    B.normSq (lam - b) ≤ B.normSq (lam - a) := by
  obtain ⟨α, hα_pos, n, hn_pos, _hpair, hab⟩ := hstep

  have hkey : lam - a = lam - b + n • α := by
    rw [hab]; abel
  rw [hkey]
  exact norm_sq_dominant_reflection_nonneg_diff rd wg B lam b α n hlam_dom hb_le hα_pos hn_pos

theorem corootPairing_eq_coroot_eval_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (μ α : Δ.𝔥 →ₗ[R] R)
    (hα : α ∈ rs.allRoots) :
    rd.corootPairing μ α = μ (rs.coroot α) :=
  rs.corootPairing_eq_eval α hα μ

theorem norm_sq_equality_implies_lam_coroot_zero_ax
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam b α : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hα_pos : α ∈ rd.posRoots)
    (hn_pos : 0 < n)
    (hpair : rd.corootPairing b α = (n : R))
    (h_eq : B.normSq (lam - b) = B.normSq (lam - b + n • α)) :
    lam (rs.coroot α) = 0 :=
  B.norm_eq_coroot_zero rd rs lam b α n hlam_dom hα_pos hn_pos hpair h_eq

theorem norm_sq_reflection_equality_weyl_element
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam b α : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hα_pos : α ∈ rd.posRoots)
    (hn_pos : 0 < n)
    (hpair : rd.corootPairing b α = (n : R))
    (h_eq : B.normSq (lam - b) = B.normSq (lam - b + n • α)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧
      wg.dualAction w b = b - n • α := by

  have hα_root : α ∈ rs.allRoots := rs.posRoots_sub α hα_pos

  have hlam_zero : lam (rs.coroot α) = 0 :=
    norm_sq_equality_implies_lam_coroot_zero_ax rd wg rs B lam b α n
      hlam_dom hα_pos hn_pos hpair h_eq

  have hrefl_lam : wg.dualAction (rs.reflection α) lam = lam := by
    rw [rs.reflection_formula α hα_root lam, hlam_zero, zero_smul, sub_zero]

  have hcompat : b (rs.coroot α) = (n : R) := by
    rw [← corootPairing_eq_coroot_eval_ax rd wg rs b α hα_root]
    exact hpair
  have hrefl_b : wg.dualAction (rs.reflection α) b = b - n • α := by
    rw [rs.reflection_formula α hα_root b, hcompat]


    congr 1
    exact Nat.cast_smul_eq_nsmul R n α

  have hs_stab : rs.reflection α ∈ WeylStabilizer rd wg lam := hrefl_lam

  exact ⟨rs.reflection α, hs_stab, hrefl_b⟩

theorem norm_sq_single_step_eq
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam a b : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hstep : ∃ α, ReflectionLT rd α a b)
    (h_eq : B.normSq (lam - b) = B.normSq (lam - a)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧
      wg.dualAction w b = a := by

  obtain ⟨α, hα_pos, n, hn_pos, hpair, hab⟩ := hstep

  have hkey : lam - a = lam - b + n • α := by
    rw [hab]; abel
  rw [hkey] at h_eq

  obtain ⟨w, hw_stab, hw_act⟩ :=
    norm_sq_reflection_equality_weyl_element rd wg rs B lam b α n hlam_dom hα_pos hn_pos hpair h_eq
  exact ⟨w, hw_stab, hw_act.trans hab.symm⟩

lemma lemma_23_4_i [LinearOrder R] [IsStrictOrderedRing R]
    (B : WeightBilinForm wg)
    (lam phi psi : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hBruhat : BruhatLE rd psi phi)
    (hphi_le_lam : BruhatLE rd phi lam) :
    B.normSq (lam - phi) ≤ B.normSq (lam - psi) := by


  induction hBruhat with
  | refl => exact le_rfl
  | @tail b c _hab hbc ih =>


    have hb_le_c : BruhatLE rd b c := Relation.ReflTransGen.single hbc
    have hb_le_lam : BruhatLE rd b lam := hb_le_c.trans hphi_le_lam
    exact le_trans (norm_sq_single_step_le rd wg B lam b c hlam_dom hphi_le_lam hbc)
      (ih hb_le_lam)

lemma lemma_23_4_ii [LinearOrder R] [IsStrictOrderedRing R]
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam phi psi : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hBruhat : BruhatLE rd psi phi)
    (hphi_le_lam : BruhatLE rd phi lam)
    (h_eq : B.normSq (lam - phi) = B.normSq (lam - psi)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧
      wg.dualAction w phi = psi := by

  induction hBruhat with
  | refl =>

    exact ⟨1, wg.dualAction_one lam, wg.dualAction_one psi⟩
  | @tail b c hab hbc ih =>


    have hb_le_c : BruhatLE rd b c := Relation.ReflTransGen.single hbc
    have hb_le_lam : BruhatLE rd b lam := hb_le_c.trans hphi_le_lam

    have hstep_le := norm_sq_single_step_le rd wg B lam b c hlam_dom hphi_le_lam hbc

    have hchain_le := lemma_23_4_i rd wg B lam b psi hlam_dom hab hb_le_lam


    have h_eq_step : B.normSq (lam - c) = B.normSq (lam - b) :=
      le_antisymm hstep_le (h_eq ▸ hchain_le)
    have h_eq_chain : B.normSq (lam - b) = B.normSq (lam - psi) :=
      le_antisymm hchain_le (h_eq_step ▸ h_eq ▸ le_rfl)

    obtain ⟨w₁, hw₁_stab, hw₁_act⟩ := norm_sq_single_step_eq rd wg rs B lam b c hlam_dom hbc h_eq_step

    obtain ⟨w₂, hw₂_stab, hw₂_act⟩ := ih hb_le_lam h_eq_chain

    exact ⟨w₂ * w₁,
      WeylStabilizer_mul_closed rd wg lam hw₂_stab hw₁_stab,
      by rw [wg.dualAction_mul, hw₁_act, hw₂_act]⟩

def IsInXi0
    (rd : PositiveRootData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ), lam - mu = ∑ α ∈ rd.posRoots, (c α) • α

def IsProperRep
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  IsDominantWeightBruhat rd wg lam ∧
  IsInXi0 rd mu lam ∧
  ∀ (w : wg.W), w ∈ WeylStabilizer rd wg lam →
    BruhatLE rd mu (wg.dualAction w mu)




def WeylOrbitPair
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | ∃ w : wg.W, p = (wg.dualAction w mu, wg.dualAction w lam)}












theorem bilinForm_weyl_normSq_invariant
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (w : wg.W)
    (mu nu : Δ.𝔥 →ₗ[R] R) :
    B.normSq (wg.dualAction w mu - wg.dualAction w nu) = B.normSq (mu - nu) := by
  exact B.weyl_normSq_invariant w mu nu










lemma normSq_weyl_invariant [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (a b : Δ.𝔥 →ₗ[R] R)
    (w : wg.W) :
    B.normSq (wg.dualAction w a - wg.dualAction w b) = B.normSq (a - b) := by
  exact bilinForm_weyl_normSq_invariant wg B w a b


lemma weylStabilizer_fixes_dominant_lam [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hlam_dom : IsDominantWeightBruhat rd wg lam)
    (w : wg.W)
    (hw_stab : w ∈ WeylStabilizer rd wg lam) :
    wg.dualAction w lam = lam :=
  hw_stab




def SameInfChar
    (wg : WeylGroupData Δ)
    (nu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (w : wg.W), nu = wg.dualAction w lam

def IsZeroRepGfObj (M : RepGfObj R 𝔤) : Prop :=
  Subsingleton M.carrier






















theorem multiplicity_free_wall_crossing
    (C : CoxeterGroupData)
    (KOB : GrothendieckGroupBlock Δ wg)
    (s : C.W) (_hs : s ∈ C.simpleReflections)
    (fF_mapKO : KOB.carrier → KOB.carrier)

    (compat : CoxeterWeylCompatibility C rd wg)

    (wact : wg.W → KOB.carrier → KOB.carrier)

    (fF_equivariant : ∀ (w_act : wg.W) (x : KOB.carrier),
      wact w_act (fF_mapKO x) = fF_mapKO (wact w_act x))

    (wact_basis : ∀ (w_act v : wg.W),
      wact w_act (KOB.delta_w v) = KOB.delta_w (w_act * v))

    (wact_add : ∀ (w_act : wg.W) (x y : KOB.carrier),
      letI := KOB.instACG
      wact w_act (x + y) = wact w_act x + wact w_act y)


    (fF_base : letI := KOB.instACG;
      fF_mapKO (KOB.delta_w 1) =
        KOB.delta_w 1 + KOB.delta_w (compat.ι s)) :

    ∀ (w : C.W),
      letI := KOB.instACG
      fF_mapKO (KOB.delta_w (compat.ι w)) =
        KOB.delta_w (compat.ι w) +
        KOB.delta_w (compat.ι w * compat.ι s) := by
  intro w

  have h1 := fF_equivariant (compat.ι w) (KOB.delta_w 1)

  rw [wact_basis (compat.ι w) 1, mul_one] at h1

  rw [← h1]

  rw [fF_base]
  rw [wact_add]
  rw [wact_basis, wact_basis]
  rw [mul_one]


end Theorems

end
