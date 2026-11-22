/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def Subalgebra.invariants {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
    (G : Type*) [Group G] (act : G →* A ≃ₐ[R] A) : Subalgebra R A where
  carrier := { a : A | ∀ g : G, (act g) a = a }
  mul_mem' := fun {a b} ha hb g => by simp [map_mul, ha g, hb g]
  one_mem' := fun g => by simp
  add_mem' := fun {a b} ha hb g => by simp [map_add, ha g, hb g]
  zero_mem' := fun g => by simp
  algebraMap_mem' := fun r g => by simp [AlgEquiv.commutes]

theorem cartan_isLieAbelian (Δ : TriangularDecomposition R 𝔤) : IsLieAbelian Δ.𝔥 :=
  Δ.h_abelian

def weightToLieHom
    {L : Type*} [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    (wt : L →ₗ[R] R) : L →ₗ⁅R⁆ R where
  toLinearMap := wt
  map_lie' {x y} := by
    simp [LieRing.of_associative_ring_bracket, mul_comm]

def evalWeight (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    UniversalEnvelopingAlgebra R Δ.𝔥 →ₐ[R] R :=
  have : IsLieAbelian Δ.𝔥 := cartan_isLieAbelian Δ
  UniversalEnvelopingAlgebra.lift R (weightToLieHom wt)

structure WeylGroupData (Δ : TriangularDecomposition R 𝔤) where
  W : Type*
  [instGroup : Group W]
  [instFintype : Fintype W]
  algAction : W →* (UniversalEnvelopingAlgebra R Δ.𝔥) ≃ₐ[R]
    (UniversalEnvelopingAlgebra R Δ.𝔥)
  ρ : Δ.𝔥 →ₗ[R] R

  dualAction : W → (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R)
  dualAction_one : ∀ (μ : Δ.𝔥 →ₗ[R] R), dualAction 1 μ = μ
  dualAction_mul : ∀ (w₁ w₂ : W) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction (w₁ * w₂) μ = dualAction w₁ (dualAction w₂ μ)
  dualAction_add : ∀ (w : W) (μ ν : Δ.𝔥 →ₗ[R] R),
    dualAction w (μ + ν) = dualAction w μ + dualAction w ν
  dualAction_smul : ∀ (w : W) (c : R) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction w (c • μ) = c • dualAction w μ
  algDualCompat : ∀ (g : W) (wt : Δ.𝔥 →ₗ[R] R) (p : UniversalEnvelopingAlgebra R Δ.𝔥),
    evalWeight Δ wt ((algAction g) p) = evalWeight Δ (dualAction g⁻¹ wt) p
  orbitSeparation : ∀ (mu nu : Δ.𝔥 →ₗ[R] R),
    (∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥),
      (∀ g : W, (algAction g) p = p) →
      evalWeight Δ mu p = evalWeight Δ nu p) →
    ∃ w : W, nu = dualAction w mu

attribute [instance] WeylGroupData.instGroup WeylGroupData.instFintype

def WeylGroupData.invariantSubalgebra {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) :
    Subalgebra R (UniversalEnvelopingAlgebra R Δ.𝔥) :=
  Subalgebra.invariants wg.W wg.algAction

def WeylGroupData.shiftedAction {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) (w : wg.W) (mu : Δ.𝔥 →ₗ[R] R) : Δ.𝔥 →ₗ[R] R :=
  wg.dualAction w (mu + wg.ρ) - wg.ρ

def PositiveRootData.sumPosRoots {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (rd : PositiveRootData Δ) : Δ.𝔥 →ₗ[R] R :=
  ∑ α ∈ rd.posRoots, α

def augmentation (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

set_option maxHeartbeats 400000 in
def betaMap (Δ : TriangularDecomposition R 𝔤) :
    TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos)) →ₗ[R]
    UniversalEnvelopingAlgebra R Δ.𝔥 := by
  apply TensorProduct.lift

  let inner : TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
      (UniversalEnvelopingAlgebra R Δ.𝔫_pos) →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔥 :=
    TensorProduct.lift
      (((LinearMap.lsmul R (UniversalEnvelopingAlgebra R Δ.𝔥)).comp
        (augmentation R Δ.𝔫_pos).toLinearMap).flip)

  exact ((LinearMap.lsmul R _).comp (augmentation R Δ.𝔫_neg).toLinearMap).flip inner

lemma LinearMap.exists_factor_of_surjective_ker_le
    {R' : Type*} [CommRing R']
    {A B C : Type*} [AddCommGroup A] [Module R' A]
    [AddCommGroup B] [Module R' B] [AddCommGroup C] [Module R' C]
    (p : A →ₗ[R'] B) (f : A →ₗ[R'] C)
    (hsurj : Function.Surjective p)
    (hker : LinearMap.ker p ≤ LinearMap.ker f) :
    ∃ (ℓ : B →ₗ[R'] C), ∀ a, ℓ (p a) = f a := by
  choose g hg using hsurj
  have well_def : ∀ (u₁ u₂ : A), p u₁ = p u₂ → f u₁ = f u₂ := by
    intro u₁ u₂ h
    have hmem : u₁ - u₂ ∈ LinearMap.ker p :=
      LinearMap.mem_ker.mpr (by rw [map_sub, h, sub_self])
    have := hker hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
  exact ⟨{
    toFun := fun b => f (g b)
    map_add' := fun b₁ b₂ => by
      have h := well_def (g (b₁ + b₂)) (g b₁ + g b₂) (by rw [hg, map_add, hg, hg])
      rw [h, map_add]
    map_smul' := fun r b => by
      simp only [RingHom.id_apply]
      have h := well_def (g (r • b)) (r • g b) (by rw [hg, map_smul, hg])
      rw [h, map_smul]
  }, fun a => well_def (g (p a)) a (by rw [hg])⟩

theorem pbw_ueaAct_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    Function.Surjective (fun u => ueaAct u hM.highestWeightVec) := by
  intro m
  have hm_top : m ∈ (⊤ : LieSubmodule R 𝔤 M) := LieSubmodule.mem_top m
  rw [← hM.generates] at hm_top
  exact LieSubmodule.lieSpan_induction (R := R) (L := 𝔤)
    (p := fun x _ => ∃ a, (ueaAct a) hM.highestWeightVec = x)
    (fun x hx => by
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨1, by simp [map_one, Module.End.one_apply]⟩)
    (⟨0, by simp [map_zero, LinearMap.zero_apply]⟩)
    (fun x y _ _ ⟨a, ha⟩ ⟨b, hb⟩ =>
      ⟨a + b, by simp only [map_add, LinearMap.add_apply, ha, hb]⟩)
    (fun r x _ ⟨a, ha⟩ =>
      ⟨r • a, by rw [map_smul, LinearMap.smul_apply, ha]⟩)
    (fun x y _ ⟨a, ha⟩ =>
      ⟨UniversalEnvelopingAlgebra.ι R x * a, by
        rw [map_mul, Module.End.mul_apply, ha, hcompat]⟩)
    hm_top

theorem evalWeight_algAction_eq (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R) (p : UniversalEnvelopingAlgebra R Δ.𝔥) :
    evalWeight Δ wt ((wg.algAction g) p) = evalWeight Δ (wg.dualAction g⁻¹ wt) p :=
  wg.algDualCompat g wt p

theorem WeylGroupData.dualAction_inv_cancel_left {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R) :
    wg.dualAction g⁻¹ (wg.dualAction g wt) = wt := by
  rw [← wg.dualAction_mul g⁻¹ g wt, inv_mul_cancel, wg.dualAction_one]

structure HasInfinitesimalCharacter
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) where
  ueaAction : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M
  compat : ∀ (x : 𝔤) (m : M),
    ueaAction (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆
  center_acts_by_scalar : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M), ueaAction (z : UniversalEnvelopingAlgebra R 𝔤) m = chi z • m

theorem schur_lie_module_scalar
    {k : Type*} [Field k] [IsAlgClosed k]
    {𝔤' : Type*} [LieRing 𝔤'] [LieAlgebra k 𝔤']
    {M : Type*} [AddCommGroup M] [Module k M]
    [LieRingModule 𝔤' M] [LieModule k 𝔤' M]
    [Module.Finite k M]
    (hirr : LieModule.IsIrreducible k 𝔤' M)
    (T : Module.End k M)
    (hT : ∀ (x : 𝔤') (m : M), T ⁅x, m⁆ = ⁅x, T m⁆) :
    ∃ c : k, ∀ m : M, T m = c • m := by

  have hM : Nontrivial M := by
    have hne : (⊥ : LieSubmodule k 𝔤' M) ≠ ⊤ := IsSimpleOrder.bot_ne_top
    by_contra h; rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)

  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T

  set S : Module.End k M := T - c • (1 : Module.End k M) with hS_def

  have hS_comm : ∀ (x : 𝔤') (m : M), S ⁅x, m⁆ = ⁅x, S m⁆ := by
    intro x m
    simp only [hS_def, LinearMap.sub_apply, LinearMap.smul_apply]
    change T ⁅x, m⁆ - c • (⁅x, m⁆) = ⁅x, T m - c • m⁆
    rw [hT, lie_sub, lie_smul]

  let kerS : LieSubmodule k 𝔤' M :=
    { LinearMap.ker S with
      lie_mem := by
        intro x m hm
        show S ⁅x, m⁆ = 0
        rw [hS_comm x m]
        have : S m = 0 := hm
        rw [this, lie_zero] }

  have hker_ne_bot : kerS ≠ ⊥ := by
    intro h
    have hker_bot : (kerS : Submodule k M) = ⊥ :=
      (LieSubmodule.toSubmodule_eq_bot kerS).mpr h
    have : T.eigenspace c = ⊥ := by
      rw [Module.End.eigenspace_def]
      exact hker_bot
    exact (Module.End.hasEigenvalue_iff.mp hc) this

  have hker_top : kerS = ⊤ := by
    cases eq_bot_or_eq_top kerS with
    | inl h => exact absurd h hker_ne_bot
    | inr h => exact h

  have hker_sub_top : LinearMap.ker S = ⊤ :=
    (LieSubmodule.toSubmodule_eq_top kerS).mpr hker_top
  have hS_zero : S = 0 := LinearMap.ker_eq_top.mp hker_sub_top

  use c
  intro m
  have hSm : S m = 0 := by simp [hS_zero]
  change T m - c • m = 0 at hSm
  exact sub_eq_zero.mp hSm

set_option maxHeartbeats 800000 in

theorem weyl_orbit_separation (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (mu nu : Δ.𝔥 →ₗ[R] R)
    (h : ∀ p : wg.invariantSubalgebra,
      evalWeight Δ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥) =
      evalWeight Δ nu (p : UniversalEnvelopingAlgebra R Δ.𝔥)) :
    ∃ w : wg.W, nu = wg.dualAction w mu := by

  apply wg.orbitSeparation mu nu
  intro p hp
  exact h ⟨p, hp⟩

theorem evalWeight_weyl_invariant (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (w : wg.W) (mu : Δ.𝔥 →ₗ[R] R)
    (p : wg.invariantSubalgebra) :
    evalWeight Δ (wg.dualAction w mu) (p : UniversalEnvelopingAlgebra R Δ.𝔥) =
    evalWeight Δ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥) := by

  have key := evalWeight_algAction_eq Δ wg w⁻¹ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥)
  rw [p.prop w⁻¹] at key
  rw [inv_inv] at key
  exact key.symm

end
