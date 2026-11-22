/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HarishChandraIsomorphism
import Atlas.LieGroups.code.CategoryO
import Atlas.LieGroups.code.KostantTheorem
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Opposite

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

structure LieBimodule (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] where
  carrier : Type*
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  leftAction : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R carrier
  rightAction : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ →ₐ[R] Module.End R carrier
  actions_commute : ∀ (u : UniversalEnvelopingAlgebra R 𝔤)
    (v : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : carrier),
    leftAction u (rightAction v m) = rightAction v (leftAction u m)

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

def LieBimodule.adjointAction (M : LieBimodule R 𝔤) (x : 𝔤) :
    Module.End R M.carrier :=
  M.leftAction (UniversalEnvelopingAlgebra.ι R x) -
  M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R x))

def LieBimodule.IsSubBimodule (M : LieBimodule R 𝔤) (S : Submodule R M.carrier) : Prop :=
  (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (s : M.carrier), s ∈ S → M.leftAction u s ∈ S) ∧
  (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (s : M.carrier), s ∈ S → M.rightAction u s ∈ S)

def LieBimodule.IsIrreducible (M : LieBimodule R 𝔤) : Prop :=
  (∃ m : M.carrier, m ≠ 0) ∧
  ∀ (S : Submodule R M.carrier), M.IsSubBimodule S → S = ⊥ ∨ S = ⊤

structure IsHarishChandraBimodule (M : LieBimodule R 𝔤) : Prop where
  locally_finite : ∀ (m : M.carrier), ∃ (S : Submodule R M.carrier),
    Module.Finite R S ∧ m ∈ S ∧
    ∀ (x : 𝔤), ∀ (s : M.carrier), s ∈ S → M.adjointAction x s ∈ S

structure LieBimodule.HasInfinitesimalCharacterPair (M : LieBimodule R 𝔤)
    (θ χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) : Prop where
  left_char : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.leftAction (z : UniversalEnvelopingAlgebra R 𝔤) m = θ z • m
  right_char : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) m = χ z • m

def HomAdEquivariant
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : LieBimodule R 𝔤) : Submodule R (V →ₗ[R] M.carrier) where
  carrier := { f | ∀ (x : 𝔤) (v : V), f ⁅x, v⁆ = M.adjointAction x (f v) }
  add_mem' := fun {f g} hf hg x v => by
    simp [LinearMap.add_apply, hf x v, hg x v, map_add]
  zero_mem' := fun x v => by simp
  smul_mem' := fun c {f} hf x v => by
    simp [LinearMap.smul_apply, hf x v, map_smul]

structure IsAdmissibleBimodule (M : LieBimodule R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  admissible : ∀ (V : Type 0) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [LieModule.IsIrreducible R 𝔤 V],
    Module.Finite R (HomAdEquivariant V M)

def maximalQuotientIdeal
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    TwoSidedIdeal (UniversalEnvelopingAlgebra R 𝔤) :=
  TwoSidedIdeal.span
    { x | ∃ (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      x = (z : UniversalEnvelopingAlgebra R 𝔤) - algebraMap R _ (χ z) }

abbrev MaximalQuotient
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  (maximalQuotientIdeal χ).ringCon.Quotient

def MaximalQuotient.proj
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] MaximalQuotient χ :=
  { (maximalQuotientIdeal χ).ringCon.mk' with
    commutes' := fun r => by
      simp [RingCon.mk', Algebra.algebraMap_eq_smul_one] }

def negOpLieHom : 𝔤 →ₗ⁅R⁆ (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ where
  toFun x := MulOpposite.op (-(UniversalEnvelopingAlgebra.ι R x))
  map_add' x y := by
    simp only [map_add, neg_add_rev, MulOpposite.op_add]; abel
  map_smul' c x := by
    simp only [map_smul, smul_neg, RingHom.id_apply, MulOpposite.op_neg, MulOpposite.op_smul]
  map_lie' {x y} := by
    simp only [LieRing.of_associative_ring_bracket, LieHom.map_lie]
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, ← MulOpposite.op_sub]
    congr 1; simp only [neg_mul, mul_neg, neg_neg, neg_sub]

def ueaPrincipalAntiAut :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift R negOpLieHom

def rmulAlgHom (A : Type*) [Ring A] [Algebra R A] :
    Aᵐᵒᵖ →ₐ[R] Module.End R A where
  toFun a :=
    { toFun := fun x => x * a.unop
      map_add' := fun x y => add_mul x y _
      map_smul' := fun c x => Algebra.smul_mul_assoc c x _ }
  map_one' := by ext; simp
  map_mul' a b := by ext x; simp [MulOpposite.unop_mul, mul_assoc]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [mul_add]
  commutes' r := by
    ext x; simp [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm]


def MaximalQuotient.bimodule
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    LieBimodule R 𝔤 where
  carrier := MaximalQuotient χ
  leftAction := (Algebra.lmul R (MaximalQuotient χ)).comp (MaximalQuotient.proj χ)
  rightAction := (rmulAlgHom (MaximalQuotient χ)).comp (AlgHom.op (MaximalQuotient.proj χ))
  actions_commute := fun _ _ _ => (mul_assoc _ _ _).symm


theorem MaximalQuotient.factors_through
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hic : HasInfinitesimalCharacter M χ) :
    ∃ (act : MaximalQuotient χ →ₐ[R] Module.End R M),
      ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M),
        hic.ueaAction u m = act (MaximalQuotient.proj χ u) m := by

  have hideal : maximalQuotientIdeal χ ≤
      TwoSidedIdeal.ker hic.ueaAction.toRingHom := by
    rw [maximalQuotientIdeal, TwoSidedIdeal.span_le]
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    show _ ∈ TwoSidedIdeal.ker hic.ueaAction.toRingHom
    rw [TwoSidedIdeal.mem_ker]

    ext m
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.zero_apply]
    rw [hic.center_acts_by_scalar z m]
    simp [Algebra.algebraMap_eq_smul_one]

  have hker : (maximalQuotientIdeal χ).ringCon ≤
      RingCon.ker hic.ueaAction.toRingHom := by
    intro x y hxy
    rw [RingCon.ker_apply]
    have hmem := (TwoSidedIdeal.rel_iff _ x y).mp hxy
    have h1 : x - y ∈ TwoSidedIdeal.ker hic.ueaAction.toRingHom := hideal hmem
    rw [TwoSidedIdeal.mem_ker] at h1

    have h2 := h1
    simp only [map_sub] at h2
    exact sub_eq_zero.mp h2

  exact ⟨(maximalQuotientIdeal χ).ringCon.liftₐ hic.ueaAction hker,
    fun u _ => by
      show (hic.ueaAction u) _ = ((maximalQuotientIdeal χ).ringCon.liftₐ hic.ueaAction hker ((maximalQuotientIdeal χ).ringCon.mk' u)) _
      simp [RingCon.liftₐ_mk]⟩

lemma UniversalEnvelopingAlgebra.lift_centralizes
    {A : Type*} [Ring A] [Algebra R A]
    (f : 𝔤 →ₗ⁅R⁆ A) (E : A) (hf : ∀ x, f x * E = E * f x) :
    ∀ u, UniversalEnvelopingAlgebra.lift R f u * E =
      E * UniversalEnvelopingAlgebra.lift R f u := by
  let C := Subalgebra.centralizer R ({E} : Set A)
  have hfC : ∀ x, f x ∈ C := by
    intro x; rw [Subalgebra.mem_centralizer_iff]
    intro g hg; rw [Set.mem_singleton_iff.mp hg]; exact (hf x).symm
  let f' : 𝔤 →ₗ⁅R⁆ C :=
  { toFun := fun x => ⟨f x, hfC x⟩
    map_add' := fun x y => by ext; simp [map_add]
    map_smul' := fun c x => by ext; simp [map_smul]
    map_lie' := fun {x y} => by
      ext; simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket]; rfl }
  let F' := UniversalEnvelopingAlgebra.lift R f'
  have key : C.val.comp F' = UniversalEnvelopingAlgebra.lift R f := by
    apply UniversalEnvelopingAlgebra.hom_ext R; ext x; simp [f', F']
  intro u
  have hu : UniversalEnvelopingAlgebra.lift R f u ∈ C := by rw [← key]; exact (F' u).2
  rw [Subalgebra.mem_centralizer_iff] at hu
  exact (hu E (Set.mem_singleton E)).symm


def tensorBimodule
    (V : LieBimodule R 𝔤)
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    LieBimodule R 𝔤 := by
  let bimodM := MaximalQuotient.bimodule χ
  let rTA := Module.End.rTensorAlgHom R V.carrier bimodM.carrier
  let lTA := Module.End.lTensorAlgHom R bimodM.carrier V.carrier

  have h_cross : ∀ (f : Module.End R V.carrier) (g : Module.End R bimodM.carrier),
      rTA f * lTA g = lTA g * rTA f := by
    intro f g; apply LinearMap.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v m =>
      change (rTA f) ((lTA g) (v ⊗ₜ[R] m)) = (lTA g) ((rTA f) (v ⊗ₜ[R] m))
      dsimp only [rTA, lTA]
      simp only [Module.End.rTensorAlgHom_apply_apply, Module.End.lTensorAlgHom_apply_apply]
      simp [TensorProduct.liftAux_tmul, LinearMap.compl₂_apply, TensorProduct.mk_apply]
    | add x y hx hy => simp [map_add, hx, hy]

  let diagLieHom : 𝔤 →ₗ⁅R⁆ Module.End R (TensorProduct R V.carrier bimodM.carrier) :=
  { toFun := fun x =>
      rTA (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) +
      lTA (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x))
    map_add' := fun x y => by simp only [map_add]; abel
    map_smul' := fun c x => by
      simp only [map_smul, RingHom.id_apply, smul_add]
    map_lie' := fun {x y} => by
      simp only [LieRing.of_associative_ring_bracket]


      rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      simp only [map_sub, map_mul]


      have hc1 := h_cross (V.leftAction (UniversalEnvelopingAlgebra.ι R x))
        (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R y))
      have hc2 := h_cross (V.leftAction (UniversalEnvelopingAlgebra.ι R y))
        (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x))

      simp only [add_mul, mul_add]

      rw [hc1, hc2]
      abel }

  let leftAction' := UniversalEnvelopingAlgebra.lift R diagLieHom
  let rightAction' := lTA.comp bimodM.rightAction
  exact
  { carrier := TensorProduct R V.carrier bimodM.carrier
    leftAction := leftAction'
    rightAction := rightAction'
    actions_commute := fun u v m => by


      let E_v := rightAction' v

      have h_gen : ∀ x, diagLieHom x * E_v = E_v * diagLieHom x := by
        intro x
        show (rTA (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) +
              lTA (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x))) *
              (lTA (bimodM.rightAction v)) =
            (lTA (bimodM.rightAction v)) *
              (rTA (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) +
              lTA (bimodM.leftAction (UniversalEnvelopingAlgebra.ι R x)))
        simp only [add_mul, mul_add]
        rw [h_cross (V.leftAction (UniversalEnvelopingAlgebra.ι R x)) (bimodM.rightAction v)]
        congr 1


        rw [← map_mul, ← map_mul]
        congr 1

        ext m'
        exact bimodM.actions_commute (UniversalEnvelopingAlgebra.ι R x) v m'

      have h_all := UniversalEnvelopingAlgebra.lift_centralizes diagLieHom E_v h_gen u


      exact congr_fun (congr_arg DFunLike.coe h_all) m }

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]














lemma uea_ad_stable_mul
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Sa Sb : Submodule R (UniversalEnvelopingAlgebra R 𝔤))
    (hSa : ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ Sa →
      (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ Sa)
    (hSb : ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ Sb →
      (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ Sb) :
    ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ Sa * Sb →
      (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ Sa * Sb := by
  intro x s hs
  refine Submodule.mul_induction_on hs (fun a ha b hb => ?_) (fun u v hu hv => ?_)
  · have leibniz : UniversalEnvelopingAlgebra.ι R x * (a * b) - a * b * UniversalEnvelopingAlgebra.ι R x =
        (UniversalEnvelopingAlgebra.ι R x * a - a * UniversalEnvelopingAlgebra.ι R x) * b +
        a * (UniversalEnvelopingAlgebra.ι R x * b - b * UniversalEnvelopingAlgebra.ι R x) := by
      simp only [sub_mul, mul_sub, mul_assoc]; abel
    rw [leibniz]
    exact Submodule.add_mem _
      (Submodule.mul_mem_mul (hSa x a ha) hb)
      (Submodule.mul_mem_mul ha (hSb x b hb))
  · have : UniversalEnvelopingAlgebra.ι R x * (u + v) - (u + v) * UniversalEnvelopingAlgebra.ι R x =
        (UniversalEnvelopingAlgebra.ι R x * u - u * UniversalEnvelopingAlgebra.ι R x) +
        (UniversalEnvelopingAlgebra.ι R x * v - v * UniversalEnvelopingAlgebra.ι R x) := by
      simp only [mul_add, add_mul]; abel
    rw [this]
    exact Submodule.add_mem _ hu hv

theorem uea_adjoint_locally_finite
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] [Module.Finite R 𝔤] :
    ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
      ∃ (S : Submodule R (UniversalEnvelopingAlgebra R 𝔤)),
        Module.Finite R S ∧ u ∈ S ∧
        ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ S →
          (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ S := by
  intro u
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R (UniversalEnvelopingAlgebra.Rel R 𝔤) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    refine ⟨LinearMap.range (Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤)),
            Module.Finite.range _, ?_, fun x s hs => ?_⟩
    · rw [AlgHom.commutes]; exact ⟨r, rfl⟩
    · obtain ⟨r', rfl⟩ := hs
      simp only [Algebra.linearMap_apply]
      rw [Algebra.commutes r' (UniversalEnvelopingAlgebra.ι R x), sub_self]
      exact zero_mem _
  | ι x₀ =>
    refine ⟨Submodule.map (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap ⊤,
            Module.Finite.map _ _, ?_, fun x s hs => ?_⟩
    · exact Submodule.mem_map.mpr ⟨x₀, trivial, rfl⟩
    · obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hs
      simp only [LieHom.coe_toLinearMap]
      have h := (UniversalEnvelopingAlgebra.ι R (L := 𝔤)).map_lie x y
      simp only [LieRing.of_associative_ring_bracket] at h
      rw [h.symm]
      exact Submodule.mem_map.mpr ⟨⁅x, y⁆, trivial, rfl⟩
  | mul a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stable⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stable⟩ := ihb
    refine ⟨Sa * Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).mul (Module.Finite.iff_fg.mp hSb_fin)
    · rw [map_mul]; exact Submodule.mul_mem_mul ha_mem hb_mem
    · exact uea_ad_stable_mul R 𝔤 Sa Sb hSa_stable hSb_stable
  | add a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stable⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stable⟩ := ihb
    refine ⟨Sa ⊔ Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).sup (Module.Finite.iff_fg.mp hSb_fin)
    · rw [map_add]; exact Submodule.mem_sup.mpr ⟨_, ha_mem, _, hb_mem, rfl⟩
    · intro x s hs
      rcases Submodule.mem_sup.mp hs with ⟨sa, hsa, sb, hsb, rfl⟩
      have : UniversalEnvelopingAlgebra.ι R x * (sa + sb) - (sa + sb) * UniversalEnvelopingAlgebra.ι R x =
          (UniversalEnvelopingAlgebra.ι R x * sa - sa * UniversalEnvelopingAlgebra.ι R x) +
          (UniversalEnvelopingAlgebra.ι R x * sb - sb * UniversalEnvelopingAlgebra.ι R x) := by
        simp only [mul_add, add_mul]; abel
      rw [this]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (hSa_stable x sa hsa))
        (Submodule.mem_sup_right (hSb_stable x sb hsb))


theorem corollary_14_3_HC
    [LieAlgebra.IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤]
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ) :
    IsHarishChandraBimodule (MaximalQuotient.bimodule χ) := by
  constructor
  intro m

  have hsurj : Function.Surjective (MaximalQuotient.proj χ) :=
    RingCon.mk'_surjective _
  obtain ⟨u, hu⟩ := hsurj m

  obtain ⟨S, hS_fin, hu_mem, hS_stable⟩ := uea_adjoint_locally_finite ℂ 𝔤 u

  let projLin : UniversalEnvelopingAlgebra ℂ 𝔤 →ₗ[ℂ] MaximalQuotient χ :=
    (MaximalQuotient.proj χ).toLinearMap
  refine ⟨Submodule.map projLin S, Module.Finite.map S projLin, ?_, ?_⟩

  · exact Submodule.mem_map.mpr ⟨u, hu_mem, hu⟩

  · intro x s' hs'

    obtain ⟨s, hs_mem, rfl⟩ := Submodule.mem_map.mp hs'


    suffices h : projLin (UniversalEnvelopingAlgebra.ι ℂ x * s - s * UniversalEnvelopingAlgebra.ι ℂ x) ∈
        Submodule.map projLin S by
      have had : (MaximalQuotient.bimodule χ).adjointAction x (projLin s) =
          projLin (UniversalEnvelopingAlgebra.ι ℂ x * s - s * UniversalEnvelopingAlgebra.ι ℂ x) := by
        simp only [LieBimodule.adjointAction, MaximalQuotient.bimodule, map_sub]

        rfl
      exact had ▸ h
    exact Submodule.mem_map.mpr ⟨_, hS_stable x s hs_mem, rfl⟩





theorem algebraic_end_has_eigenvalue
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K) (hp : p ≠ 0) (hpT : Polynomial.aeval T p = 0)
    (hV : ∃ v : V, v ≠ 0) :
    ∃ (c : K) (v : V), v ≠ 0 ∧ T v = c • v := by

  have hdeg : p.natDegree ≠ 0 := by
    intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h] at hpT
    simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at hpT
    obtain ⟨m, hm⟩ := hV
    apply hp
    rw [Polynomial.eq_C_of_natDegree_eq_zero h]
    suffices p.coeff 0 = 0 by simp [this]
    by_contra hc
    apply hm
    have h1 : (p.coeff 0 • (1 : Module.End K V)) m = (0 : Module.End K V) m := by rw [hpT]
    simp at h1
    exact h1.resolve_left hc

  have hpdeg' : p.degree ≠ 0 := by intro h'; apply hdeg; simp [Polynomial.natDegree, h']
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hpdeg'

  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hr

  have hcomp : (Polynomial.aeval T (Polynomial.X - Polynomial.C r)) *
      (Polynomial.aeval T q) = 0 := by
    rw [← map_mul, ← hq, hpT]

  by_cases hqT : Polynomial.aeval T q = 0
  · have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hq; exact hp hq
    exact algebraic_end_has_eigenvalue T q hq_ne hqT hV
  ·
    have : ¬∀ x, Polynomial.aeval T q x = 0 := by
      intro h; apply hqT; ext; exact h _
    push Not at this

    obtain ⟨w, hw⟩ := this

    refine ⟨r, Polynomial.aeval T q w, hw, ?_⟩
    have hzero : Polynomial.aeval T (Polynomial.X - Polynomial.C r)
        (Polynomial.aeval T q w) = 0 := by
      change (Polynomial.aeval T (Polynomial.X - Polynomial.C r) *
        Polynomial.aeval T q) w = 0
      rw [hcomp]; simp
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply, LinearMap.smul_apply] at hzero
    simp at hzero
    exact sub_eq_zero.mp hzero
termination_by p.natDegree
decreasing_by
  rw [hq]
  have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hq; exact hp hq
  rw [Polynomial.natDegree_mul (by simp [Polynomial.X_sub_C_ne_zero]) hq_ne,
    Polynomial.natDegree_X_sub_C]
  omega




@[reducible]
def LieBimodule.toLieRingModule' {R' : Type*} [CommRing R'] {𝔤' : Type*} [LieRing 𝔤']
    [LieAlgebra R' 𝔤'] (M : LieBimodule R' 𝔤') :
    LieRingModule 𝔤' M.carrier where
  bracket x m := M.adjointAction x m
  add_lie x y m := by
    simp only [LieBimodule.adjointAction]
    simp only [map_add, MulOpposite.op_add, LinearMap.add_apply, LinearMap.sub_apply]
    abel
  lie_add x m n := by
    simp only [LieBimodule.adjointAction]
    simp only [map_add]
  leibniz_lie x y m := by
    simp only [LieBimodule.adjointAction]
    have hcomm_xy : M.leftAction (UniversalEnvelopingAlgebra.ι R' x)
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y)) m) =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y))
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' x) m) :=
      M.actions_commute _ _ _
    have hcomm_yx : M.leftAction (UniversalEnvelopingAlgebra.ι R' y)
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x)) m) =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x))
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' y) m) :=
      M.actions_commute _ _ _
    have hLmul : M.leftAction (UniversalEnvelopingAlgebra.ι R' x *
        UniversalEnvelopingAlgebra.ι R' y) m =
      M.leftAction (UniversalEnvelopingAlgebra.ι R' x)
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' y) m) := by
      rw [map_mul]; rfl
    have hLmul' : M.leftAction (UniversalEnvelopingAlgebra.ι R' y *
        UniversalEnvelopingAlgebra.ι R' x) m =
      M.leftAction (UniversalEnvelopingAlgebra.ι R' y)
        (M.leftAction (UniversalEnvelopingAlgebra.ι R' x) m) := by
      rw [map_mul]; rfl
    have hRmul : M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y *
        UniversalEnvelopingAlgebra.ι R' x)) m =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x))
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y)) m) := by
      rw [MulOpposite.op_mul, map_mul]; rfl
    have hRmul' : M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x *
        UniversalEnvelopingAlgebra.ι R' y)) m =
      M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' y))
        (M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R' x)) m) := by
      rw [MulOpposite.op_mul, map_mul]; rfl
    have hι_lie : UniversalEnvelopingAlgebra.ι R' ⁅x, y⁆ =
      UniversalEnvelopingAlgebra.ι R' x * UniversalEnvelopingAlgebra.ι R' y -
      UniversalEnvelopingAlgebra.ι R' y * UniversalEnvelopingAlgebra.ι R' x := by
      rw [(UniversalEnvelopingAlgebra.ι R').map_lie, LieRing.of_associative_ring_bracket]
    simp only [LinearMap.sub_apply]
    rw [hι_lie]
    simp only [map_sub, MulOpposite.op_sub, LinearMap.sub_apply]
    rw [hLmul, hLmul', hRmul, hRmul']
    rw [hcomm_xy, hcomm_yx]
    abel

@[reducible]
def LieBimodule.toLieModule' {R' : Type*} [CommRing R'] {𝔤' : Type*} [LieRing 𝔤']
    [LieAlgebra R' 𝔤'] (M : LieBimodule R' 𝔤') :
    @LieModule R' 𝔤' M.carrier _ _ _ M.instAddCommGroup M.instModule M.toLieRingModule' :=
  @LieModule.mk R' 𝔤' M.carrier _ _ _ M.instAddCommGroup M.instModule M.toLieRingModule'
    (fun t x m => by
      show M.adjointAction (t • x) m = t • M.adjointAction x m
      simp only [LieBimodule.adjointAction]
      simp only [map_smul, MulOpposite.op_smul, LinearMap.smul_apply, LinearMap.sub_apply]
      rw [smul_sub])
    (fun t x m => by
      show M.adjointAction x (t • m) = t • M.adjointAction x m
      simp only [LieBimodule.adjointAction, LinearMap.sub_apply, map_smul])

lemma isIrreducible_of_isAtom_lieSubmodule
    {𝔤' : Type*} [LieRing 𝔤']
    {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule 𝔤' V]
    (N : LieSubmodule ℂ 𝔤' V) (hN : IsAtom N) :
    LieModule.IsIrreducible ℂ 𝔤' ↥N := by
  have hNne : N ≠ ⊥ := hN.1
  haveI : Nontrivial ↥N := by
    rw [LieSubmodule.nontrivial_iff_ne_bot]; exact hNne
  apply LieModule.IsIrreducible.mk
  intro P hP
  have h1 : P.map N.incl ≤ N := LieSubmodule.map_incl_le
  have h2 : P.map N.incl ≠ ⊥ := by
    intro heq; apply hP; rw [eq_bot_iff]
    intro x hx
    have hmem : N.incl x ∈ P.map N.incl := LieSubmodule.mem_map_of_mem hx
    rw [heq] at hmem; simp [LieSubmodule.mem_bot] at hmem; simp [hmem]
  have h3 : P.map N.incl = N := (hN.le_iff.mp h1).resolve_left h2
  by_contra h
  have hlt : P < ⊤ := lt_top_iff_ne_top.mpr h
  rw [← LieSubmodule.map_incl_lt_iff_lt_top] at hlt
  exact absurd h3 (ne_of_lt hlt)


universe u_bimod_carrier

theorem weyl_irred_submodule_of_ad_stable
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (M : LieBimodule.{_, _, u_bimod_carrier} ℂ 𝔤)
    (S : Submodule ℂ M.carrier)
    (hS_fin : Module.Finite ℂ S)
    (hS_ne : ∃ (s : M.carrier), s ∈ S ∧ s ≠ 0)
    (hS_stable : ∀ (x : 𝔤) (s : M.carrier), s ∈ S → M.adjointAction x s ∈ S) :
    ∃ (V : Type u_bimod_carrier) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule ℂ 𝔤 V)
      (_ : Module.Finite ℂ V)
      (_ : LieModule.IsIrreducible ℂ 𝔤 V)
      (ι : V →ₗ[ℂ] M.carrier),
      Function.Injective ι ∧
      (∀ (x : 𝔤) (v : V), ι (⁅x, v⁆) = M.adjointAction x (ι v)) := by


  letI : LieRingModule 𝔤 M.carrier := M.toLieRingModule'
  letI : LieModule ℂ 𝔤 M.carrier := M.toLieModule'


  let S_lie : LieSubmodule ℂ 𝔤 M.carrier :=
    { toSubmodule := S
      lie_mem := fun {x} {m} hm => hS_stable x m hm }

  haveI : Module.Finite ℂ S_lie := hS_fin
  haveI : IsArtinian ℂ S_lie := inferInstance

  haveI : IsAtomic (LieSubmodule ℂ 𝔤 S_lie) := inferInstance

  have hS_ne_bot : S_lie ≠ ⊥ := by
    obtain ⟨s, hs_mem, hs_ne⟩ := hS_ne
    intro h
    have : s ∈ (⊥ : LieSubmodule ℂ 𝔤 M.carrier) := h ▸ hs_mem
    simp [LieSubmodule.mem_bot] at this
    exact hs_ne this
  haveI : Nontrivial S_lie := by
    rw [LieSubmodule.nontrivial_iff_ne_bot]; exact hS_ne_bot

  have htop_ne_bot : (⊤ : LieSubmodule ℂ 𝔤 S_lie) ≠ ⊥ :=
    top_ne_bot
  obtain ⟨A, hA_atom, _hA_le⟩ :=
    (IsAtomic.eq_bot_or_exists_atom_le (⊤ : LieSubmodule ℂ 𝔤 S_lie)).resolve_left htop_ne_bot

  have hA_irred : LieModule.IsIrreducible ℂ 𝔤 A :=
    isIrreducible_of_isAtom_lieSubmodule A hA_atom

  haveI : Module.Finite ℂ A := inferInstance

  let ι_comp : A →ₗ[ℂ] M.carrier := S_lie.incl.toLinearMap.comp A.incl.toLinearMap
  have hι_inj : Function.Injective ι_comp := by
    intro x y h
    have h1 : S_lie.incl (A.incl x) = S_lie.incl (A.incl y) := h
    have h2 : A.incl x = A.incl y := S_lie.injective_incl h1
    exact A.injective_incl h2


  have hι_lie : ∀ (x : 𝔤) (v : ↥A), ι_comp (⁅x, v⁆) = M.adjointAction x (ι_comp v) := by
    intro x v
    rfl
  exact ⟨↥A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hA_irred, ι_comp, hι_inj, hι_lie⟩

theorem adjoint_irred_submodule
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (M : LieBimodule.{_, _, u_bimod_carrier} ℂ 𝔤)
    (hirr : M.IsIrreducible)
    (hlocfin : IsHarishChandraBimodule M) :
    ∃ (V : Type u_bimod_carrier) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule ℂ 𝔤 V)
      (_ : Module.Finite ℂ V)
      (_ : LieModule.IsIrreducible ℂ 𝔤 V)
      (ι : V →ₗ[ℂ] M.carrier),
      Function.Injective ι ∧
      (∀ (x : 𝔤) (v : V), ι (⁅x, v⁆) = M.adjointAction x (ι v)) := by


  obtain ⟨m, hm⟩ := hirr.1

  obtain ⟨S, hS_fin, hm_mem, hS_stable⟩ := hlocfin.locally_finite m


  exact weyl_irred_submodule_of_ad_stable M S hS_fin ⟨m, hm_mem, hm⟩ hS_stable

def UniversalEnvelopingAlgebra.counit {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : 𝔤 →ₗ⁅R⁆ R)

def UniversalEnvelopingAlgebra.counitOp {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] :
    (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ →ₐ[R] R where
  toFun x := UniversalEnvelopingAlgebra.counit x.unop
  map_one' := by simp [map_one]
  map_mul' a b := by simp [MulOpposite.unop_mul, map_mul, mul_comm]
  map_zero' := by simp [map_zero]
  map_add' a b := by simp [map_add]
  commutes' r := by
    simp only [MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      UniversalEnvelopingAlgebra.counit, UniversalEnvelopingAlgebra.lift]
    simp [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

def LieBimodule.trivial {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] :
    LieBimodule R 𝔤 where
  carrier := V
  leftAction := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 V)
  rightAction := (Algebra.ofId R (Module.End R V)).comp
    UniversalEnvelopingAlgebra.counitOp
  actions_commute := by
    intro u v m
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
    exact LinearMap.map_smul _ _ _

instance LieBimodule.trivial_finiteDimensional {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] :
    Module.Finite R (LieBimodule.trivial V : LieBimodule R 𝔤).carrier :=
  ‹Module.Finite R V›



theorem canonical_element_image_is_subbimodule
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (M : LieBimodule ℂ 𝔤)
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ)
    (_hχ : ∀ (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤))
        (m : M.carrier),
        M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra ℂ 𝔤)) m = χ z • m)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    [Module.Finite ℂ V]
    (_ι : V →ₗ[ℂ] M.carrier) (_hι : Function.Injective _ι)
    (ξ : TensorProduct ℂ V (MaximalQuotient χ) →ₗ[ℂ] M.carrier)
    (_hξ_ne : ξ ≠ 0)
    (hξ_left : ∀ (u : UniversalEnvelopingAlgebra ℂ 𝔤)
      (t : TensorProduct ℂ V (MaximalQuotient χ)),
      ξ ((tensorBimodule (LieBimodule.trivial V) χ).leftAction u t) =
      M.leftAction u (ξ t))
    (hξ_right : ∀ (u : (UniversalEnvelopingAlgebra ℂ 𝔤)ᵐᵒᵖ)
      (t : TensorProduct ℂ V (MaximalQuotient χ)),
      ξ ((tensorBimodule (LieBimodule.trivial V) χ).rightAction u t) =
      M.rightAction u (ξ t)) :
    M.IsSubBimodule (LinearMap.range ξ) := by
  constructor
  ·
    intro u s hs
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hs
    rw [← hξ_left u t]
    exact LinearMap.mem_range.mpr ⟨_, rfl⟩
  ·
    intro u s hs
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hs
    rw [← hξ_right u t]
    exact LinearMap.mem_range.mpr ⟨_, rfl⟩







theorem hc_hom_finite
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (N : LieBimodule ℂ 𝔤)
    (hN : IsAdmissibleBimodule N)
    (W : Type 0) [AddCommGroup W] [Module ℂ W] [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    [Module.Finite ℂ W] (hirr : LieModule.IsIrreducible ℂ 𝔤 W) :
    Module.Finite ℂ (HomAdEquivariant W N) :=
  hN.admissible W



end
