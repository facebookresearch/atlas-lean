/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.MaximalQuotients
import Atlas.LieGroups.code.HighestWeightModules
import Atlas.LieGroups.code.HarishChandraCorollaries

noncomputable section

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]


def adjointActionOnHom
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : M →ₗ[R] N) : M →ₗ[R] N where
  toFun m := ⁅x, T m⁆ - T ⁅x, m⁆
  map_add' a b := by simp [lie_add, sub_add_sub_comm]
  map_smul' c m := by simp [lie_smul, smul_sub]

def IsFiniteTypeMap
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (T : M →ₗ[R] N) : Prop :=
  ∃ (S : Submodule R (M →ₗ[R] N)),
    Module.Finite R S ∧ T ∈ S ∧
    (∀ (x : 𝔤) (f : M →ₗ[R] N), f ∈ S → adjointActionOnHom M N x f ∈ S)

def HomFin
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    Submodule R (M →ₗ[R] N) where
  carrier := { T | IsFiniteTypeMap (𝔤 := 𝔤) M N T }
  add_mem' := by
    intro a b ha hb
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (a + b)
    obtain ⟨S₁, hfin₁, ha_mem, hstab₁⟩ := ha
    obtain ⟨S₂, hfin₂, hb_mem, hstab₂⟩ := hb
    refine ⟨S₁ ⊔ S₂, Submodule.finite_sup S₁ S₂, Submodule.add_mem_sup ha_mem hb_mem, ?_⟩
    intro x f hf
    rw [Submodule.mem_sup] at hf
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := hf
    have : adjointActionOnHom M N x (f₁ + f₂) = adjointActionOnHom M N x f₁ + adjointActionOnHom M N x f₂ := by
      ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
    rw [this]
    exact Submodule.add_mem_sup (hstab₁ x f₁ hf₁) (hstab₂ x f₂ hf₂)
  zero_mem' := by
    show IsFiniteTypeMap (𝔤 := 𝔤) M N 0
    exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun x f hf => by
      rw [Submodule.mem_bot] at hf ⊢
      subst hf
      ext m
      simp [adjointActionOnHom]⟩
  smul_mem' := by
    intro c f hf
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (c • f)
    obtain ⟨S, hfin, hf_mem, hstab⟩ := hf
    exact ⟨S, hfin, S.smul_mem c hf_mem, hstab⟩

def homLeftComp (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    Module.End R N →ₐ[R] Module.End R (M →ₗ[R] N) where
  toFun f := { toFun := fun T => f.comp T
               map_add' := fun T₁ T₂ => by ext; simp
               map_smul' := fun r T => by ext; simp }
  map_one' := by ext T m; simp
  map_mul' := fun f g => by ext T m; simp [Module.End.mul_apply]
  map_zero' := by ext T m; simp
  map_add' := fun f g => by ext T m; simp [LinearMap.add_apply]
  commutes' := fun r => by ext T m; simp [Module.algebraMap_end_apply]

def homRightComp (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (Module.End R M)ᵐᵒᵖ →ₐ[R] Module.End R (M →ₗ[R] N) where
  toFun gop := { toFun := fun T => T.comp (MulOpposite.unop gop)
                 map_add' := fun T₁ T₂ => by ext; simp
                 map_smul' := fun r T => by ext; simp }
  map_one' := by ext T m; simp
  map_mul' := fun a b => by
    ext T m
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl
  map_zero' := by ext T m; simp
  map_add' := fun a b => by ext T m; simp [MulOpposite.unop_add, LinearMap.add_apply]
  commutes' := fun r => by
    ext T m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Module.algebraMap_end_apply]
    simp [map_smul]

def HomBimodule
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    LieBimodule R 𝔤 where
  carrier := M →ₗ[R] N
  leftAction :=
    (homLeftComp M N).comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N))
  rightAction :=
    (homRightComp M N).comp
      (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)))
  actions_commute := fun u v T => by


    show (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp
        (T.comp (MulOpposite.unop (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)) v))) =
      ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T).comp
        (MulOpposite.unop (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)) v))
    ext m
    simp [LinearMap.comp_apply]

@[elab_as_elim]
theorem UniversalEnvelopingAlgebra.induction
    {motive : UniversalEnvelopingAlgebra R 𝔤 → Prop}
    (halg : ∀ r, motive (algebraMap R (UniversalEnvelopingAlgebra R 𝔤) r))
    (hι : ∀ x, motive (UniversalEnvelopingAlgebra.ι R x))
    (hmul : ∀ a b, motive a → motive b → motive (a * b))
    (hadd : ∀ a b, motive a → motive b → motive (a + b))
    (u : UniversalEnvelopingAlgebra R 𝔤) : motive u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R (UniversalEnvelopingAlgebra.Rel R 𝔤) u
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

lemma uea_ad_leibniz (x : 𝔤) (a b : UniversalEnvelopingAlgebra R 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * (a * b) - (a * b) * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * a - a * UniversalEnvelopingAlgebra.ι R x) * b +
    a * (UniversalEnvelopingAlgebra.ι R x * b - b * UniversalEnvelopingAlgebra.ι R x) := by
  simp only [mul_sub, sub_mul, mul_assoc]; abel

lemma uea_ad_add (x : 𝔤) (v₁ v₂ : UniversalEnvelopingAlgebra R 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * (v₁ + v₂) - (v₁ + v₂) * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * v₁ - v₁ * UniversalEnvelopingAlgebra.ι R x) +
    (UniversalEnvelopingAlgebra.ι R x * v₂ - v₂ * UniversalEnvelopingAlgebra.ι R x) := by
  simp only [mul_add, add_mul]; abel

lemma uea_comm_rel (x y : 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
    UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R) ⁅x, y⁆ := by
  have h := (UniversalEnvelopingAlgebra.ι R (L := 𝔤)).map_lie (x := x) (y := y)
  simp only [LieRing.of_associative_ring_bracket] at h
  exact h.symm

def ueaIotaRange : Submodule R (UniversalEnvelopingAlgebra R 𝔤) :=
  LinearMap.range (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ UniversalEnvelopingAlgebra R 𝔤).toLinearMap

def ueaScalarsSubmodule : Submodule R (UniversalEnvelopingAlgebra R 𝔤) :=
  LinearMap.range (Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤))

lemma ueaScalarsSubmodule_fg : (ueaScalarsSubmodule (R := R) (𝔤 := 𝔤)).FG := by
  rw [ueaScalarsSubmodule, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

lemma ueaIotaRange_fg [Module.Finite R 𝔤] : (ueaIotaRange (R := R) (𝔤 := 𝔤)).FG := by
  rw [ueaIotaRange, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

theorem ueaAdLocallyFinite [Module.Finite R 𝔤]
    (u : UniversalEnvelopingAlgebra R 𝔤) :
    ∃ (S : Submodule R (UniversalEnvelopingAlgebra R 𝔤)),
      Module.Finite R S ∧ u ∈ S ∧
      (∀ (x : 𝔤) (v : UniversalEnvelopingAlgebra R 𝔤), v ∈ S →
        (UniversalEnvelopingAlgebra.ι R x * v - v * UniversalEnvelopingAlgebra.ι R x) ∈ S) := by
  induction u using UniversalEnvelopingAlgebra.induction with
  | halg r =>
    refine ⟨ueaScalarsSubmodule, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact ueaScalarsSubmodule_fg
    · exact ⟨r, rfl⟩
    · intro x v hv
      obtain ⟨c, rfl⟩ := hv
      have : UniversalEnvelopingAlgebra.ι R x * Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c -
             Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c * UniversalEnvelopingAlgebra.ι R x = 0 := by
        simp [Algebra.linearMap_apply, Algebra.commutes]
      rw [this]
      exact ⟨0, map_zero _⟩
  | hι y =>
    refine ⟨ueaIotaRange ⊔ ueaScalarsSubmodule, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact ueaIotaRange_fg.sup ueaScalarsSubmodule_fg
    · exact Submodule.mem_sup_left (LinearMap.mem_range_self _ y)
    · intro x v hv
      rw [Submodule.mem_sup] at hv
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hv
      rw [uea_ad_add]
      apply Submodule.add_mem
      · obtain ⟨z, rfl⟩ := hv₁
        show UniversalEnvelopingAlgebra.ι R x *
          (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap z -
          (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap z *
          UniversalEnvelopingAlgebra.ι R x ∈ _
        simp only [LieHom.coe_toLinearMap]
        rw [uea_comm_rel]
        exact Submodule.mem_sup_left (LinearMap.mem_range_self _ ⁅x, z⁆)
      · obtain ⟨c, rfl⟩ := hv₂
        have : UniversalEnvelopingAlgebra.ι R x * Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c -
               Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c * UniversalEnvelopingAlgebra.ι R x = 0 := by
          simp [Algebra.linearMap_apply, Algebra.commutes]
        rw [this]
        exact Submodule.zero_mem _
  | hadd a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stab⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stab⟩ := ihb
    refine ⟨Sa ⊔ Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).sup (Module.Finite.iff_fg.mp hSb_fin)
    · exact Submodule.add_mem _ (Submodule.mem_sup_left ha_mem) (Submodule.mem_sup_right hb_mem)
    · intro x v hv
      rw [Submodule.mem_sup] at hv
      obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
      rw [uea_ad_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hSa_stab x va hva))
        (Submodule.mem_sup_right (hSb_stab x vb hvb))
  | hmul a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stab⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stab⟩ := ihb
    refine ⟨Sa * Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).mul (Module.Finite.iff_fg.mp hSb_fin)
    · exact Submodule.mul_mem_mul ha_mem hb_mem
    · intro x v hv
      refine Submodule.mul_induction_on hv ?_ ?_
      · intro sa hsa sb hsb
        rw [uea_ad_leibniz]
        exact Submodule.add_mem _ (Submodule.mul_mem_mul (hSa_stab x sa hsa) hsb)
          (Submodule.mul_mem_mul hsa (hSb_stab x sb hsb))
      · intro v₁ v₂ hv₁ hv₂
        rw [uea_ad_add]
        exact Submodule.add_mem _ hv₁ hv₂

lemma ueaAction_adjoint_intertwine
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (x : 𝔤) (u : UniversalEnvelopingAlgebra R 𝔤) :
    adjointActionOnHom M M x (act u) =
    act (UniversalEnvelopingAlgebra.ι R x * u - u * UniversalEnvelopingAlgebra.ι R x) := by
  ext m
  simp only [adjointActionOnHom, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_mul,
    LinearMap.sub_apply]
  change ⁅x, (act u) m⁆ - (act u) ⁅x, m⁆ =
    act (UniversalEnvelopingAlgebra.ι R x) ((act u) m) - (act u) (act (UniversalEnvelopingAlgebra.ι R x) m)
  rw [hcompat x ((act u) m), hcompat x m]

lemma adjointActionOnHom_left_comp
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (f : N →ₗ[R] N) (T : M →ₗ[R] N) :
    adjointActionOnHom M N x (f.comp T) =
    (adjointActionOnHom N N x f).comp T + f.comp (adjointActionOnHom M N x T) := by
  ext m
  simp [adjointActionOnHom, LinearMap.comp_apply, LinearMap.add_apply]

lemma adjointActionOnHom_right_comp
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : M →ₗ[R] N) (g : M →ₗ[R] M) :
    adjointActionOnHom M N x (T.comp g) =
    (adjointActionOnHom M N x T).comp g + T.comp (adjointActionOnHom M M x g) := by
  ext m
  simp [adjointActionOnHom, LinearMap.comp_apply, LinearMap.add_apply]

theorem ueaAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈
      HomFin (R := R) (𝔤 := 𝔤) M N ∧
    T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈
      HomFin (R := R) (𝔤 := 𝔤) M N := by
  obtain ⟨S_T, hfin_T, hT_mem, hT_stab⟩ := hT
  obtain ⟨S_u, hfin_u, hu_mem, hu_stab⟩ := ueaAdLocallyFinite (R := R) (𝔤 := 𝔤) u
  let actN := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N)
  let actM := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)
  have hcompatN : ∀ (y : 𝔤) (n : N), actN (UniversalEnvelopingAlgebra.ι R y) n = ⁅y, n⁆ := by
    intro y n; simp [actN, LieModule.toEnd_apply_apply]
  have hcompatM : ∀ (y : 𝔤) (m : M), actM (UniversalEnvelopingAlgebra.ι R y) m = ⁅y, m⁆ := by
    intro y m; simp [actM, LieModule.toEnd_apply_apply]

  let compBilinL : (N →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) :=
    LinearMap.llcomp R M N N
  let compBilinR : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] M) →ₗ[R] (M →ₗ[R] N) :=
    { toFun := fun T' => {
        toFun := fun g => T'.comp g
        map_add' := fun g₁ g₂ => by ext; simp [LinearMap.comp_apply, LinearMap.add_apply]
        map_smul' := fun r g => by ext; simp [LinearMap.comp_apply, LinearMap.smul_apply] }
      map_add' := fun T₁ T₂ => by ext g m; simp [LinearMap.add_apply]
      map_smul' := fun r T₁ => by ext g m; simp [LinearMap.smul_apply] }
  let imgS_uN := S_u.map actN.toLinearMap
  let imgS_uM := S_u.map actM.toLinearMap
  let W_left := Submodule.map₂ compBilinL imgS_uN S_T
  let W_right := Submodule.map₂ compBilinR S_T imgS_uM

  have hfin_imgN : imgS_uN.FG := (Module.Finite.iff_fg.mp (Module.Finite.map S_u actN.toLinearMap))
  have hfin_imgM : imgS_uM.FG := (Module.Finite.iff_fg.mp (Module.Finite.map S_u actM.toLinearMap))
  have hfin_ST : S_T.FG := Module.Finite.iff_fg.mp hfin_T

  have imgN_stab : ∀ (x : 𝔤) (f : N →ₗ[R] N), f ∈ imgS_uN →
      adjointActionOnHom N N x f ∈ imgS_uN := by
    intro x f hf
    obtain ⟨v, hv_mem, rfl⟩ := Submodule.mem_map.mp hf
    simp only [AlgHom.toLinearMap_apply]
    rw [ueaAction_adjoint_intertwine N actN hcompatN x v]
    exact Submodule.mem_map_of_mem (hu_stab x v hv_mem)

  have imgM_stab : ∀ (x : 𝔤) (g : M →ₗ[R] M), g ∈ imgS_uM →
      adjointActionOnHom M M x g ∈ imgS_uM := by
    intro x g hg
    obtain ⟨v, hv_mem, rfl⟩ := Submodule.mem_map.mp hg
    simp only [AlgHom.toLinearMap_apply]
    rw [ueaAction_adjoint_intertwine M actM hcompatM x v]
    exact Submodule.mem_map_of_mem (hu_stab x v hv_mem)
  constructor
  ·
    show IsFiniteTypeMap (𝔤 := 𝔤) M N ((actN u).comp T)
    refine ⟨W_left, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact hfin_imgN.map₂ compBilinL hfin_ST
    · exact Submodule.apply_mem_map₂ compBilinL (Submodule.mem_map_of_mem hu_mem) hT_mem
    ·
      intro x w hw


      have hW_left_le : W_left ≤ W_left.comap
          ({ toFun := adjointActionOnHom M N x
             map_add' := fun f g => by ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
             map_smul' := fun c f => by ext m; simp [adjointActionOnHom, lie_smul, smul_sub]
           } : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N)) := by
        rw [Submodule.map₂_le]
        intro f hf T' hT'

        show adjointActionOnHom M N x (compBilinL f T') ∈ W_left
        change adjointActionOnHom M N x (f.comp T') ∈ W_left
        rw [adjointActionOnHom_left_comp M N x f T']


        apply W_left.add_mem
        · exact Submodule.apply_mem_map₂ compBilinL (imgN_stab x f hf) hT'
        · exact Submodule.apply_mem_map₂ compBilinL hf (hT_stab x T' hT')
      exact hW_left_le hw
  ·
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (T.comp (actM u))
    refine ⟨W_right, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact hfin_ST.map₂ compBilinR hfin_imgM
    · exact Submodule.apply_mem_map₂ compBilinR hT_mem (Submodule.mem_map_of_mem hu_mem)
    · intro x w hw
      have hW_right_le : W_right ≤ W_right.comap
          ({ toFun := adjointActionOnHom M N x
             map_add' := fun f g => by ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
             map_smul' := fun c f => by ext m; simp [adjointActionOnHom, lie_smul, smul_sub]
           } : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N)) := by
        rw [Submodule.map₂_le]
        intro T' hT' g hg
        show adjointActionOnHom M N x (compBilinR T' g) ∈ W_right
        change adjointActionOnHom M N x (T'.comp g) ∈ W_right
        rw [adjointActionOnHom_right_comp M N x T' g]
        apply W_right.add_mem
        · exact Submodule.apply_mem_map₂ compBilinR (hT_stab x T' hT') hg
        · exact Submodule.apply_mem_map₂ compBilinR hT' (imgM_stab x g hg)
      exact hW_right_le hw

theorem leftAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈
      HomFin (R := R) (𝔤 := 𝔤) M N :=
  (ueaAction_preserves_HomFin M N u T hT).1

theorem rightAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈
      HomFin (R := R) (𝔤 := 𝔤) M N :=
  (ueaAction_preserves_HomFin M N u T hT).2

def HomFinBimodule [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    LieBimodule R 𝔤 where
  carrier := ↥(HomFin (R := R) (𝔤 := 𝔤) M N)
  leftAction := {
    toFun := fun u => {
      toFun := fun ⟨T, hT⟩ => ⟨(UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T,
        leftAction_preserves_HomFin M N u T hT⟩
      map_add' := fun ⟨T₁, _⟩ ⟨T₂, _⟩ => by
        ext m; simp [LinearMap.comp_apply, map_add]
      map_smul' := fun r ⟨T₁, _⟩ => by
        ext m; simp [LinearMap.comp_apply, map_smul]
    }
    map_one' := by ext ⟨T, _⟩ m; simp
    map_mul' := fun u₁ u₂ => by
      ext ⟨T, _⟩ m; simp [Module.End.mul_apply, LinearMap.comp_apply]
    map_zero' := by ext ⟨T, _⟩ m; simp
    map_add' := fun u₁ u₂ => by
      ext ⟨T, _⟩ m; simp [LinearMap.add_apply, LinearMap.comp_apply]
    commutes' := fun r => by
      ext ⟨T, _⟩ m; simp [Module.algebraMap_end_apply]
  }
  rightAction := {
    toFun := fun vop => {
      toFun := fun ⟨T, hT⟩ => ⟨T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) (MulOpposite.unop vop)),
        rightAction_preserves_HomFin M N (MulOpposite.unop vop) T hT⟩
      map_add' := fun ⟨T₁, _⟩ ⟨T₂, _⟩ => by
        ext m; simp [LinearMap.comp_apply]
      map_smul' := fun r ⟨T₁, _⟩ => by
        ext m; simp [LinearMap.comp_apply]
    }
    map_one' := by ext ⟨T, _⟩ m; simp
    map_mul' := fun a b => by
      ext ⟨T, _⟩ m
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        MulOpposite.unop_mul, map_mul]
    map_zero' := by ext ⟨T, _⟩ m; simp
    map_add' := fun a b => by
      ext ⟨T, _⟩ m; simp [MulOpposite.unop_add, LinearMap.add_apply, LinearMap.comp_apply]
    commutes' := fun r => by
      ext ⟨T, _⟩ m
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        Module.algebraMap_end_apply]
      simp [map_smul]
  }
  actions_commute := fun u v ⟨T, hT⟩ => by
    ext m
    simp [LinearMap.comp_apply]








theorem HomAdEquivariant.finite_of_injection
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {M N : LieBimodule R 𝔤}
    (ι : M.carrier →ₗ[R] N.carrier)
    (hι_inj : Function.Injective ι)
    (hι_left : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M.carrier),
      ι (M.leftAction u m) = N.leftAction u (ι m))
    (hι_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M.carrier),
      ι (M.rightAction u m) = N.rightAction u (ι m))
    (hN_fin : Module.Finite R (HomAdEquivariant V N)) :
    Module.Finite R (HomAdEquivariant V M) := by

  let pc := HomAdEquivariant.postcomp (R := R) (𝔤 := 𝔤) (V := V) ι hι_left hι_right

  have hpc_inj : Function.Injective pc := by
    intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ heq
    simp only [pc, HomAdEquivariant.postcomp, LinearMap.coe_mk, AddHom.coe_mk] at heq
    apply Subtype.ext
    ext v
    have : ι (f₁ v) = ι (f₂ v) := by
      have := congr_arg (fun x => (x : V →ₗ[R] N.carrier) v) (Subtype.mk.inj heq)
      simpa [LinearMap.comp_apply] using this
    exact hι_inj this
  exact Module.Finite.of_injective pc hpc_inj


lemma homFinBimodule_adjointAction_val [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)) :
    ((HomFinBimodule (R := R) (𝔤 := 𝔤) M N).adjointAction x T).val =
    adjointActionOnHom (R := R) (𝔤 := 𝔤) M N x T.val := by
  unfold HomFinBimodule LieBimodule.adjointAction adjointActionOnHom
  ext m
  simp [LinearMap.sub_apply, LinearMap.comp_apply]







def HomEquivariant
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (N : Type*) [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    Submodule R (M →ₗ[R] N) where
  carrier := { f | ∀ (x : 𝔤) (m : M), f ⁅x, m⁆ = ⁅x, f m⁆ }
  add_mem' := fun {f g} hf hg x m => by
    simp only [LinearMap.add_apply]; rw [hf x m, hg x m, lie_add]
  zero_mem' := fun x m => by simp
  smul_mem' := fun c {f} hf x m => by
    simp only [LinearMap.smul_apply]; rw [hf x m, lie_smul]













def ueaActionFromLieModule
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)

theorem ueaActionFromLieModule_compat
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (x : 𝔤) (m : M) :
    ueaActionFromLieModule M (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
  simp [ueaActionFromLieModule, LieModule.toEnd_apply_apply]







def ueaIncl_neg (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔫_neg.incl : Δ.𝔫_neg →ₗ⁅R⁆ 𝔤))

def ueaIncl_pos (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔫_pos.incl : Δ.𝔫_pos →ₗ⁅R⁆ 𝔤))


noncomputable def multMap_ug
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) →ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => ueaIncl_neg Δ a * ueaIncl_pos Δ b
          map_add' := fun b₁ b₂ => by simp [mul_add]
          map_smul' := fun r b => by simp }
      map_add' := fun a₁ a₂ => by ext b; simp [add_mul]
      map_smul' := fun r a => by ext b; simp }





def ueaIncl_h (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔥 →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔥.incl : Δ.𝔥 →ₗ⁅R⁆ 𝔤))




















lemma isFiniteTypeMap_comp_mk_tensor
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (v : V) (T : M →ₗ[R] N) (hT : IsFiniteTypeMap (𝔤 := 𝔤) M N T) :
    IsFiniteTypeMap (𝔤 := 𝔤) M (TensorProduct R V N)
      ((TensorProduct.mk R V N v).comp T) := by

  obtain ⟨S, hfin, hT_mem, hstab⟩ := hT

  let Φ : TensorProduct R V S →ₗ[R] (M →ₗ[R] TensorProduct R V N) :=
    TensorProduct.lift
      { toFun := fun w =>
          { toFun := fun g => (TensorProduct.mk R V N w).comp (g : M →ₗ[R] N)
            map_add' := fun g₁ g₂ => by ext m; simp [LinearMap.comp_apply, map_add]
            map_smul' := fun r g => by ext m; simp [LinearMap.comp_apply, map_smul] }
        map_add' := fun w₁ w₂ => by
          ext g : 1; ext m; simp [TensorProduct.mk]
        map_smul' := fun r w => by
          ext g : 1; ext m; simp [TensorProduct.mk, TensorProduct.smul_tmul'] }

  have hΦ_tmul : ∀ (w : V) (g : S), Φ (w ⊗ₜ[R] g) = (TensorProduct.mk R V N w).comp (g : M →ₗ[R] N) := by
    intro w g; simp [Φ, TensorProduct.lift.tmul]

  let S' : Submodule R (M →ₗ[R] TensorProduct R V N) := LinearMap.range Φ

  haveI : Module.Finite R (TensorProduct R V S) := Module.Finite.tensorProduct R V S
  haveI : Module.Finite R S' := Module.Finite.range Φ
  refine ⟨S', inferInstance, ?_, ?_⟩
  ·
    exact ⟨v ⊗ₜ[R] ⟨T, hT_mem⟩, hΦ_tmul v ⟨T, hT_mem⟩⟩
  ·
    intro x f hf

    obtain ⟨z, rfl⟩ := hf

    induction z using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      have : adjointActionOnHom (R := R) (𝔤 := 𝔤) M (TensorProduct R V N) x 0 = 0 := by
        ext m; simp [adjointActionOnHom]
      rw [this]; exact zero_mem _
    | tmul w g =>


      have key : adjointActionOnHom M (TensorProduct R V N) x
            ((TensorProduct.mk R V N w).comp (g : M →ₗ[R] N)) =
          (TensorProduct.mk R V N ⁅x, w⁆).comp (g : M →ₗ[R] N) +
          (TensorProduct.mk R V N w).comp (adjointActionOnHom M N x (g : M →ₗ[R] N)) := by
        ext m
        simp only [adjointActionOnHom, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
          TensorProduct.mk_apply, LinearMap.add_apply]
        rw [TensorProduct.LieModule.lie_tmul_right]
        rw [add_sub_assoc]
        congr 1
        rw [← TensorProduct.tmul_sub]
      rw [hΦ_tmul, key]
      have hg_stab : adjointActionOnHom M N x (g : M →ₗ[R] N) ∈ S :=
        hstab x g g.property
      exact ⟨⁅x, w⁆ ⊗ₜ[R] g + w ⊗ₜ[R] ⟨adjointActionOnHom M N x (g : M →ₗ[R] N), hg_stab⟩, by
        rw [map_add, hΦ_tmul, hΦ_tmul]⟩
    | add z₁ z₂ ih₁ ih₂ =>

      have hadj_add : adjointActionOnHom M (TensorProduct R V N) x (Φ (z₁ + z₂)) =
          adjointActionOnHom M (TensorProduct R V N) x (Φ z₁) +
          adjointActionOnHom M (TensorProduct R V N) x (Φ z₂) := by
        simp only [map_add]
        ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
      rw [hadj_add]
      exact Submodule.add_mem S' ih₁ ih₂


def tensorHomMap
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    TensorProduct R V (HomFin (R := R) (𝔤 := 𝔤) M M) →ₗ[R]
      HomFin (R := R) (𝔤 := 𝔤) M (TensorProduct R V M) :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun f =>
            ⟨(TensorProduct.mk R V M v).comp (f : M →ₗ[R] M),
             isFiniteTypeMap_comp_mk_tensor V v (f : M →ₗ[R] M) f.property⟩
          map_add' := fun f₁ f₂ => by
            apply Subtype.ext; ext m; simp [map_add]
          map_smul' := fun r f => by
            apply Subtype.ext; simp only [SetLike.val_smul]; ext m; simp [map_smul] }
      map_add' := fun v₁ v₂ => by
        ext f : 1; exact Subtype.ext (by ext m; simp [TensorProduct.mk])
      map_smul' := fun r v => by
        ext f : 1
        exact Subtype.ext (by ext m; simp [TensorProduct.mk, TensorProduct.smul_tmul']) }





def leftInfChars
    (M : LieBimodule R 𝔤) :
    Set (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  { θ | ∃ (m : M.carrier), m ≠ 0 ∧
    ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
      M.leftAction (z : UniversalEnvelopingAlgebra R 𝔤) m = θ z • m }





def infCharsOfModule
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    Set (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  { χ | ∃ (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M),
    (∀ (x : 𝔤) (m : M), act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) ∧
    ∃ (m : M), m ≠ 0 ∧
      ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        act (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m }







theorem weights_in_weightLattice
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (chev : ChevalleyData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [IsNoetherian R V] [Module.IsTorsionFree R V]
    (ν : Δ.𝔥 →ₗ[R] R)
    (hν : ν ∈ weights Δ V) :
    chev.IsInWeightLattice ν := by

  intro i

  have hν' : WeightSpace Δ V ν ≠ ⊥ := hν
  rw [Submodule.ne_bot_iff] at hν'
  obtain ⟨v, hv_mem, hv_ne⟩ := hν'

  have hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v := hv_mem

  have hh : ⁅(chev.simpleCoroot i : 𝔤), v⁆ = ν (chev.simpleCoroot i) • v := hv_wt _

  by_cases hhz : (chev.simpleCoroot i : 𝔤) = 0
  · have hμv : ν (chev.simpleCoroot i) • v = 0 := by rw [← hh, hhz, zero_lie]
    have hμ0 : ν (chev.simpleCoroot i) = 0 := by
      by_contra hμ
      have hreg : IsRegular (ν (chev.simpleCoroot i)) :=
        ⟨fun a b hab => mul_left_cancel₀ hμ hab,
         fun a b hab => mul_right_cancel₀ hμ hab⟩
      have hsmul : IsSMulRegular V (ν (chev.simpleCoroot i)) :=
        Module.IsTorsionFree.isSMulRegular (M := V) hreg
      exact hv_ne (hsmul (show ν (chev.simpleCoroot i) • v = ν (chev.simpleCoroot i) • 0 by
        simp [hμv]))
    exact ⟨0, by simp [hμ0]⟩
  ·

    have t : IsSl2Triple (chev.simpleCoroot i : 𝔤) (chev.posGen i) (chev.negGen i) :=
      IsSl2Triple.mk hhz
        (chev.bracket_ef i)
        (by rw [two_nsmul]; exact chev.bracket_he i)
        (by rw [two_nsmul]; exact chev.bracket_hf i)
    set μ := ν (chev.simpleCoroot i)
    set e_i := chev.posGen i
    set h_i := (chev.simpleCoroot i : 𝔤)

    set ψ : ℕ → V := fun k => ((LieModule.toEnd R 𝔤 V e_i) ^ k) v

    have hψ_eig : ∀ k : ℕ, ⁅h_i, ψ k⁆ = (μ + 2 * (k : R)) • ψ k := by
      intro k
      induction k with
      | zero => simp [ψ, hh]
      | succ n ih =>
        simp only [ψ, pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]
        rw [leibniz_lie]
        rw [t.lie_h_e_smul R]
        simp only [ψ] at ih
        rw [ih]
        simp only [lie_smul, smul_lie]
        rw [← add_smul]
        congr 1
        push_cast
        ring

    have hψ_zero : ∃ k : ℕ, ψ k = 0 := by
      by_contra! hall

      have hs : (Set.range (fun (n : ℕ) => μ + 2 * (n : R))).Infinite := by
        rw [Set.infinite_range_iff]
        · infer_instance
        · intro a b hab
          simp only at hab
          exact_mod_cast mul_left_cancel₀ (two_ne_zero (α := R)) (add_left_cancel hab)


      exact hs ((LieModule.toEnd R 𝔤 V h_i).eigenvectors_linearIndependent
        (Set.range (fun (n : ℕ) => μ + 2 * (n : R)))
        (fun ⟨_, hs⟩ => ψ (Classical.choose hs))
        (fun ⟨_, hs⟩ => by
          simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
          have hk := Classical.choose_spec hs
          simp only at hk
          refine ⟨?_, hall _⟩
          rw [LieModule.toEnd_apply_apply, hψ_eig, hk])).finite


    obtain ⟨k₀, hk₀_ne, hk₀_zero⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
      (show ¬(ψ 0 = 0) from by simp [ψ, hv_ne]) hψ_zero

    have he_kill : ⁅e_i, ψ k₀⁆ = 0 := by
      show (LieModule.toEnd R 𝔤 V e_i) (((LieModule.toEnd R 𝔤 V e_i) ^ k₀) v) = 0
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hk₀_zero

    have hprim : t.HasPrimitiveVectorWith (ψ k₀) (μ + 2 * (k₀ : R)) :=
      IsSl2Triple.HasPrimitiveVectorWith.mk hk₀_ne (hψ_eig k₀) he_kill

    obtain ⟨n, hn⟩ := hprim.exists_nat

    exact ⟨(n : ℤ) - 2 * (k₀ : ℤ), by push_cast; linear_combination hn⟩





def IsDominantIntegralWeight (Δ : TriangularDecomposition R 𝔤)
    (_rd : PositiveRootData Δ) (chev : ChevalleyData Δ) (γ : Δ.𝔥 →ₗ[R] R) : Prop :=
  chev.IsDominantIntegral γ

abbrev CentralCharacter (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] :=
  ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R

def DominantWeights (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ) (chev : ChevalleyData Δ) : Set (Δ.𝔥 →ₗ[R] R) :=
  { γ | IsDominantIntegralWeight Δ rd chev γ }

structure IsInHCBimod
    (M : LieBimodule R 𝔤)
    (θ χ : CentralCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  charPair : M.HasInfinitesimalCharacterPair θ χ







def stabilizerOfWeight (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) (γ : Δ.𝔥 →ₗ[R] R) : Subgroup wg.W where
  carrier := { w | wg.dualAction w γ = γ }
  one_mem' := by
    show wg.dualAction 1 γ = γ
    exact wg.dualAction_one γ
  mul_mem' := by
    intro a b ha hb
    show wg.dualAction (a * b) γ = γ
    rw [wg.dualAction_mul, hb, ha]
  inv_mem' := by
    intro a ha
    show wg.dualAction a⁻¹ γ = γ
    have h := wg.dualAction_mul a⁻¹ a γ
    rw [inv_mul_cancel, wg.dualAction_one, ha] at h
    exact h.symm

def equivModStab (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (γ : Δ.𝔥 →ₗ[R] R) (lam₁ lam₂ : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ w ∈ stabilizerOfWeight Δ wg γ, wg.dualAction w lam₁ = lam₂








end
