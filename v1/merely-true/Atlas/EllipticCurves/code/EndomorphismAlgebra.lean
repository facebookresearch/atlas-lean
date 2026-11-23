/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Algebra.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Atlas.EllipticCurves.code.TorsionEndomorphism
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.GroupTheory.Archimedean
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-- A subring `O` of a `ℚ`-algebra `A` is an order if it is finitely generated as a
`ℤ`-module and its `ℚ`-span fills `A` (cf. Definition 12.22 of "Elliptic Curves"). -/
structure IsOrder (A : Type*) [Ring A] [Algebra ℚ A] (O : Subring A) : Prop where
  fg_zmul : (O.toAddSubgroup.toIntSubmodule).FG
  span_eq_top : Submodule.span ℚ (O : Set A) = ⊤

open NumberField

/-- The ring of integers `𝓞_K` of a number field `K` is an order in `K`
(Definition 12.22 / Theorem about `𝓞_K` being a free `ℤ`-module of rank `[K:ℚ]`). -/
theorem ringOfIntegers_isOrder (K : Type*) [Field K] [NumberField K] :
    IsOrder K (integralClosure ℤ K).toSubring where
  fg_zmul := by
    rw [show (integralClosure ℤ K).toSubring.toAddSubgroup.toIntSubmodule =
        Subalgebra.toSubmodule (integralClosure ℤ K) from by
      ext x; simp [AddSubgroup.toIntSubmodule]]
    have hfg := Submodule.fg_range (IsScalarTower.toAlgHom ℤ (𝓞 K) K).toLinearMap
    convert hfg using 1
    ext x
    constructor
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨y, hy⟩, rfl⟩; exact hy
  span_eq_top := by
    rw [eq_top_iff]
    intro x _
    have hbasis := (integralBasis K).mem_span x
    apply Submodule.span_mono _ hbasis
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    rw [integralBasis_apply]
    exact (RingOfIntegers.basis K i).2

universe u

namespace ConductorOrder

variable {d : ℤ}

/-- The order of conductor `f` in `ℤ[√d]`: the subring consisting of all elements
whose imaginary part is divisible by `f`. -/
def conductorOrder (d : ℤ) (f : ℕ) : Subring (ℤ√d) where
  carrier := { z | (f : ℤ) ∣ z.im }
  zero_mem' := dvd_zero _
  one_mem' := dvd_zero _
  add_mem' ha hb := dvd_add ha hb
  mul_mem' ha hb := by
    show (f : ℤ) ∣ _
    exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_left ha _)
  neg_mem' ha := dvd_neg.mpr ha

/-- Membership criterion for the conductor order: `z ∈ conductorOrder d f` iff
`f` divides `z.im`. -/
@[simp]
theorem mem_conductorOrder_iff {f : ℕ} {z : ℤ√d} :
    z ∈ conductorOrder d f ↔ (f : ℤ) ∣ z.im := Iff.rfl

/-- Divisibility of conductors gives a reverse inclusion of orders: if `f₂ ∣ f₁` then
`conductorOrder d f₁ ≤ conductorOrder d f₂`. -/
theorem conductorOrder_le_of_dvd {f₁ f₂ : ℕ} (h : f₂ ∣ f₁) :
    conductorOrder d f₁ ≤ conductorOrder d f₂ := by
  intro z hz
  simp only [mem_conductorOrder_iff] at *
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hz

/-- The conductor order is finitely generated as a `ℤ`-module, with basis `{1, f·√d}`. -/
theorem conductorOrder_fg (f : ℕ) :
    (conductorOrder d f).toAddSubgroup.toIntSubmodule.FG := by
  refine ⟨{(1 : ℤ√d), ⟨0, ↑f⟩}, ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · show (↑f : ℤ) ∣ (1 : ℤ√d).im; simp
    · show (↑f : ℤ) ∣ (⟨0, ↑f⟩ : ℤ√d).im; simp
  · intro z hz
    change (↑f : ℤ) ∣ z.im at hz
    obtain ⟨k, hk⟩ := hz
    have : z = z.re • (1 : ℤ√d) + k • (⟨0, ↑f⟩ : ℤ√d) := by
      ext <;> simp [hk, mul_comm]
    rw [this]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The "imaginary part" homomorphism `ℤ[√d] →+ ℤ` sending `a + b√d ↦ b`. -/
def imAddHom (d : ℤ) : ℤ√d →+ ℤ where
  toFun z := z.im
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Every integer cast `n : ℤ → ℤ[√d]` lies inside any subring `S` of `ℤ[√d]`. -/
lemma intCast_mem_subring (S : Subring (ℤ√d)) (n : ℤ) : (n : ℤ√d) ∈ S := by
  have : (n : ℤ√d) = n • (1 : ℤ√d) := by simp
  rw [this]; exact S.zsmul_mem S.one_mem n

/-- If a subring `S` contains the pure-imaginary element `(0, a)` and `a` divides the
imaginary part of `z`, then `z ∈ S`. -/
lemma mem_subring_of_dvd_im (S : Subring (ℤ√d))
    {a : ℤ} (ha : (⟨0, a⟩ : ℤ√d) ∈ S)
    {z : ℤ√d} (hdvd : a ∣ z.im) : z ∈ S := by
  obtain ⟨k, hk⟩ := hdvd
  have h1 : z = (z.re : ℤ√d) + k • (⟨0, a⟩ : ℤ√d) := by
    ext <;> simp [hk, mul_comm]
  rw [h1]
  exact S.add_mem (intCast_mem_subring S z.re) (S.zsmul_mem ha k)

/-- The conductor order with positive conductor `f` satisfies the two structural
conditions to be an order: finite generation as a `ℤ`-module, and containing an
element with nonzero imaginary part. -/
theorem conductorOrder_isOrder {f : ℕ} (hf : 0 < f) :
    (conductorOrder d f).toAddSubgroup.toIntSubmodule.FG ∧
    (∃ z ∈ conductorOrder d f, z.im ≠ 0) :=
  ⟨conductorOrder_fg f, ⟨⟨0, f⟩, dvd_refl _, by positivity⟩⟩

/-- Conversely, any subring `S` of `ℤ[√d]` that contains some element with nonzero
imaginary part is itself a conductor order for a unique positive integer `f`. -/
theorem exists_conductor_of_subring (S : Subring (ℤ√d))
    (hS : ∃ z ∈ S, z.im ≠ 0) :
    ∃ f : ℕ, 0 < f ∧ S = conductorOrder d f := by

  let H := S.toAddSubgroup.map (imAddHom d)

  obtain ⟨a, ha⟩ := Int.subgroup_cyclic H

  have ha_ne : a ≠ 0 := by
    intro ha0
    obtain ⟨z, hzS, hzim⟩ := hS
    have : z.im ∈ H := ⟨z, hzS, rfl⟩
    rw [ha, ha0, AddSubgroup.closure_singleton_zero] at this
    exact hzim (AddSubgroup.mem_bot.mp this)

  refine ⟨a.natAbs, Int.natAbs_pos.mpr ha_ne, ?_⟩

  ext z
  simp only [mem_conductorOrder_iff]
  constructor
  ·
    intro hz
    have : z.im ∈ H := ⟨z, hz, rfl⟩
    rw [ha, ← AddSubgroup.zmultiples_eq_closure, Int.mem_zmultiples_iff] at this
    rwa [Int.natAbs_dvd]
  ·
    intro hdvd

    have : a ∈ H := by
      rw [ha, ← AddSubgroup.zmultiples_eq_closure]
      exact AddSubgroup.mem_zmultiples a
    obtain ⟨w, hwS, hwim⟩ := this
    have him : w.im = a := hwim

    have h0a : (⟨0, a⟩ : ℤ√d) ∈ S := by
      have hw_eq : w - (w.re : ℤ√d) = ⟨0, w.im⟩ := by ext <;> simp
      have : (⟨0, w.im⟩ : ℤ√d) ∈ S :=
        hw_eq ▸ S.sub_mem hwS (intCast_mem_subring S w.re)
      rwa [him] at this

    exact mem_subring_of_dvd_im S h0a (Int.natAbs_dvd.mp hdvd)

/-- Classification of orders in `ℤ[√d]`: a subring `S` is an order (finitely generated
with at least one element having nonzero imaginary part) iff it equals
`conductorOrder d f` for some positive conductor `f`. -/
theorem orders_eq_conductorOrders :
    ∀ S : Subring (ℤ√d),
      (S.toAddSubgroup.toIntSubmodule.FG ∧ ∃ z ∈ S, z.im ≠ 0) ↔
      ∃ f : ℕ, 0 < f ∧ S = conductorOrder d f := by
  intro S
  constructor
  · exact fun ⟨_, h⟩ => exists_conductor_of_subring S h
  · rintro ⟨f, hf, rfl⟩
    exact conductorOrder_isOrder hf

/-- The discriminant of the conductor `f` order in `ℤ[√d]`, defined as `4 · f² · d`. -/
def orderDiscriminant (d : ℤ) (f : ℕ) : ℤ := 4 * (f : ℤ) ^ 2 * d

/-- The discriminant of the maximal order in `ℤ[√d]` (conductor `1`), which is `4d`. -/
def maximalDiscriminant (d : ℤ) : ℤ := 4 * d

end ConductorOrder

open scoped Quaternion
open Module

section QuaternionAlg

/-- A `k`-algebra `H` is a quaternion algebra (Definition 12.12) if it has a basis of
the form `{1, α, β, αβ}` with `α², β² ∈ k×` and `αβ = -βα`, equivalently encoded here
via the existence of anticommuting elements with nonzero scalar squares and
`finrank k H = 4`. -/
def IsQuaternionAlgebra (k : Type*) [Field k] (H : Type*)
    [Ring H] [Algebra k H] : Prop :=
  ∃ (α β : H),
    (∃ a : k, a ≠ 0 ∧ α * α = algebraMap k H a) ∧
    (∃ b : k, b ≠ 0 ∧ β * β = algebraMap k H b) ∧
    α * β = -(β * α) ∧
    Module.finrank k H = 4

/-- Convenient abbreviation for the quaternion algebra `ℍ[k, a, b]` with both
nonvanishing parameters `a, b ∈ k×`. -/
abbrev QAlgebra (k : Type*) [Field k] (a b : k) (_ : a ≠ 0) (_ : b ≠ 0) := ℍ[k, a, b]

variable {k : Type*} [Field k] (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)

/-- The standard basis element `i` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qI : ℍ[k, a, b] := ⟨0, 1, 0, 0⟩

/-- The standard basis element `j` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qJ : ℍ[k, a, b] := ⟨0, 0, 1, 0⟩

/-- The standard basis element `k = i·j` of the quaternion algebra `ℍ[k, a, b]`. -/
abbrev qK : ℍ[k, a, b] := ⟨0, 0, 0, 1⟩

/-- In `ℍ[k, a, b]`, `i² = a`. -/
theorem qI_mul_qI : qI a b * qI a b = (a : ℍ[k, a, b]) := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In `ℍ[k, a, b]`, `j² = b`. -/
theorem qJ_mul_qJ : qJ a b * qJ a b = (b : ℍ[k, a, b]) := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In `ℍ[k, a, b]`, `i · j = k`. -/
theorem qI_mul_qJ : qI a b * qJ a b = qK a b := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In `ℍ[k, a, b]`, `j · i = -k`. -/
theorem qJ_mul_qI : qJ a b * qI a b = -(qK a b) := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- The defining anticommutation relation `i · j = -(j · i)` in `ℍ[k, a, b]`. -/
theorem qI_mul_qJ_eq_neg_qJ_mul_qI :
    qI a b * qJ a b = -(qJ a b * qI a b) := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- Synonym: `ℍ[k, a, b]` is a ring (recorded for use later). -/
instance : Ring ℍ[k, a, b] := inferInstance

/-- Synonym: `ℍ[k, a, b]` is a `k`-algebra. -/
instance : Algebra k ℍ[k, a, b] := inferInstance

/-- A quaternion algebra has `k`-dimension exactly `4` (cf. Definition 12.12). -/
theorem finrank_eq_four : finrank k ℍ[k, a, b] = 4 :=
  QuaternionAlgebra.finrank_eq_four a 0 b

/-- The reduced trace `T γ = 2 · Re γ` on the quaternion algebra `ℍ[k, a, b]`
(Definition 12.6). -/
def reducedTrace {k : Type*} [Field k] (a b : k) (γ : ℍ[k, a, b]) : k :=
  2 * γ.re

/-- The reduced trace of a quaternion `⟨r, x, y, z⟩` equals `2r`. -/
theorem reducedTrace_mk {k : Type*} [Field k] (a b : k) (r x y z : k) :
    reducedTrace a b ⟨r, x, y, z⟩ = 2 * r := rfl

/-- The reduced trace of a scalar `c : k`, viewed in `ℍ[k, a, b]`, equals `2c`. -/
theorem reducedTrace_coe (c : k) : reducedTrace a b (c : ℍ[k, a, b]) = 2 * c := rfl

/-- The standard `k`-basis `{1, i, j, k}` of the quaternion algebra `ℍ[k, a, b]`. -/
noncomputable def basis : Basis (Fin 4) k ℍ[k, a, b] :=
  QuaternionAlgebra.basisOneIJK a 0 b

/-- The packaged `QuaternionAlgebra.Basis` structure for `ℍ[k, a, b]` itself. -/
def quatBasis : QuaternionAlgebra.Basis ℍ[k, a, b] a 0 b :=
  QuaternionAlgebra.Basis.self k

/-- Basis identity: `i² = a·1 + 0·i` in `ℍ[k, a, b]`. -/
theorem basis_i_mul_i :
    (quatBasis a b).i * (quatBasis a b).i =
      a • (1 : ℍ[k, a, b]) + (0 : k) • (quatBasis a b).i :=
  (quatBasis a b).i_mul_i

/-- Basis identity: `j² = b·1` in `ℍ[k, a, b]`. -/
theorem basis_j_mul_j :
    (quatBasis a b).j * (quatBasis a b).j = b • (1 : ℍ[k, a, b]) :=
  (quatBasis a b).j_mul_j

/-- Basis identity: `i · j = k` in `ℍ[k, a, b]`. -/
theorem basis_i_mul_j :
    (quatBasis a b).i * (quatBasis a b).j = (quatBasis a b).k :=
  (quatBasis a b).i_mul_j

/-- Basis identity: `j · i = 0·j - k = -k` in `ℍ[k, a, b]`. -/
theorem basis_j_mul_i :
    (quatBasis a b).j * (quatBasis a b).i =
      (0 : k) • (quatBasis a b).j - (quatBasis a b).k :=
  (quatBasis a b).j_mul_i

/-- The classical Hamilton quaternions `ℍ` are defeq to `ℍ[ℝ, -1, -1]`. -/
theorem hamilton_eq : Quaternion ℝ = ℍ[ℝ, -1, -1] := rfl

/-- In Hamilton's quaternions, `i² = -1`. -/
theorem hamilton_i_sq : qI (-1 : ℝ) (-1) * qI (-1 : ℝ) (-1) = (-1 : ℍ[ℝ, -1, -1]) := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In Hamilton's quaternions, `j² = -1`. -/
theorem hamilton_j_sq : qJ (-1 : ℝ) (-1) * qJ (-1 : ℝ) (-1) = (-1 : ℍ[ℝ, -1, -1]) := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- In Hamilton's quaternions, `i · j = -(j · i)`. -/
theorem hamilton_ij_eq_neg_ji :
    qI (-1 : ℝ) (-1) * qJ (-1 : ℝ) (-1) =
      -(qJ (-1 : ℝ) (-1) * qI (-1 : ℝ) (-1)) := by
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- Hamilton's quaternions have `ℝ`-dimension `4`. -/
theorem hamilton_finrank : finrank ℝ (Quaternion ℝ) = 4 :=
  Quaternion.finrank_eq_four

/-- Hamilton's quaternions are not commutative: `i · j ≠ j · i`. -/
theorem hamilton_not_commutative : ¬ ∀ (a b : Quaternion ℝ), a * b = b * a := by
  intro h
  have h1 := h ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩
  exact absurd (congr_arg QuaternionAlgebra.imK h1) (by norm_num)

/-- The reduced norm `N γ = (γ · γ̄).re` on the quaternion algebra `ℍ[k, a, b]`
(Definition 12.6). -/
def reducedNorm {k : Type*} [Field k] (a b : k) (γ : ℍ[k, a, b]) : k :=
  (γ * star γ).re

/-- Explicit formula: `N ⟨r, x, y, z⟩ = r² - a x² - b y² + a b z²`. -/
theorem reducedNorm_mk {k : Type*} [Field k] (a b : k) (r x y z : k) :
    reducedNorm a b ⟨r, x, y, z⟩ =
      r * r - a * (x * x) - b * (y * y) + a * b * (z * z) := by
  simp [reducedNorm, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk]; ring

/-- The product `γ · γ̄` equals the scalar `(N γ)` viewed in `ℍ[k, a, b]`. -/
theorem mul_star_eq_algebraMap_reducedNorm {k : Type*} [Field k] (a b : k)
    (γ : ℍ[k, a, b]) :
    γ * star γ = algebraMap k _ (reducedNorm a b γ) := by
  cases γ with | mk r i j kk =>
  ext <;> simp [reducedNorm, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk] <;> ring

/-- The product `γ̄ · γ` also equals the scalar `(N γ)`. -/
theorem star_mul_eq_algebraMap_reducedNorm {k : Type*} [Field k] (a b : k)
    (γ : ℍ[k, a, b]) :
    star γ * γ = algebraMap k _ (reducedNorm a b γ) := by
  cases γ with | mk r i j kk =>
  ext <;> simp [reducedNorm, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk] <;> ring

/-- Every quaternion algebra `ℍ[k, a, b]` is nontrivial. -/
instance quatAlg_nontrivial {k : Type*} [Field k] (a b : k) :
    Nontrivial ℍ[k, a, b] :=
  ⟨⟨0, 1, by simp⟩⟩

/-- Lemma 12.13: a quaternion algebra is a division ring iff its reduced norm is
anisotropic, i.e. `N γ = 0 ⇒ γ = 0`. -/
theorem isDivisionRing_iff_norm_anisotropic {k : Type*} [Field k] (a b : k) :
    (∀ γ : ℍ[k, a, b], reducedNorm a b γ = 0 → γ = 0) ↔
      (∀ γ : ℍ[k, a, b], γ ≠ 0 → IsUnit γ) := by
  constructor
  ·
    intro h γ hγ
    have hN : reducedNorm a b γ ≠ 0 := fun hN => hγ (h γ hN)
    exact ⟨⟨γ, (reducedNorm a b γ)⁻¹ • star γ,
      by rw [Algebra.mul_smul_comm, mul_star_eq_algebraMap_reducedNorm]
         simp [Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hN],
      by rw [Algebra.smul_mul_assoc, star_mul_eq_algebraMap_reducedNorm]
         simp [Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hN]⟩, rfl⟩
  ·
    intro h γ hN
    by_contra hγ
    obtain ⟨u, hu⟩ := h γ hγ

    have h1 : γ * star γ = 0 := by
      rw [mul_star_eq_algebraMap_reducedNorm, hN, map_zero]

    have h2 : star γ = 0 := by
      have key : ↑u * star γ = 0 := by rwa [hu]
      calc star γ = ↑u⁻¹ * (↑u * star γ) := by rw [Units.inv_mul_cancel_left]
        _ = ↑u⁻¹ * 0 := by rw [key]
        _ = 0 := mul_zero _

    have h3 : γ = 0 := by
      have := congr_arg star h2
      rwa [star_star, star_zero] at this
    exact hγ h3

/-- Promote a quaternion algebra `ℍ[k, a, b]` with anisotropic reduced norm to a
`DivisionRing`, by inverting nonzero elements via the conjugate. -/
@[reducible] noncomputable def toDivisionRing {k : Type*} [Field k] (a b : k)

    (h : ∀ γ : ℍ[k, a, b], reducedNorm a b γ = 0 → γ = 0) :
    DivisionRing ℍ[k, a, b] :=
  DivisionRing.ofIsUnitOrEqZero (fun γ => by
    by_cases hγ : γ = 0
    · right; exact hγ
    · left; exact (isDivisionRing_iff_norm_anisotropic a b).mp h γ hγ)

end QuaternionAlg

section Lemma125

open TensorProduct

/-- Algebra-map multiplication coincides with scalar action: `(algebraMap R K) r * k = r • k`. -/
lemma algebraMap_mul_eq_smul {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (r : R) (k : K) : (algebraMap R K) r * k = r • k := by
  rw [Algebra.smul_def]

/-- A key step in Lemma 12.5: every element of `A ⊗_R K`, where `K = Frac R`, can be
written as `a ⊗ ((algebraMap R K) s)⁻¹` for some `a ∈ A` and `s ∈ R⁰`. -/
theorem TensorProduct.exists_tmul_inv_algebraMap
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [AddCommGroup A] [Module R A]
    (x : A ⊗[R] K) :
    ∃ (a : A) (s : nonZeroDivisors R), x = a ⊗ₜ[R] ((algebraMap R K) s)⁻¹ := by
  induction x with
  | zero =>
    exact ⟨0, ⟨1, Submonoid.one_mem _⟩, by simp [TensorProduct.zero_tmul]⟩
  | tmul m n =>

    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) n
    dsimp at hs
    have hsne : (algebraMap R K) ↑s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [show n = (algebraMap R K) r * ((algebraMap R K) ↑s)⁻¹ from by
          rw [← mul_inv_cancel_right₀ hsne n, hs],
        algebraMap_mul_eq_smul, ← smul_tmul]
    exact ⟨r • m, s, rfl⟩
  | add x y hx hy =>

    obtain ⟨a₁, s₁, rfl⟩ := hx
    obtain ⟨a₂, s₂, rfl⟩ := hy
    have hs₁ := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₁.2 (K := K)
    have hs₂ := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s₂.2 (K := K)

    rw [show ((algebraMap R K) ↑s₁)⁻¹ =
          (algebraMap R K) ↑s₂ * ((algebraMap R K) (↑s₁ * ↑s₂))⁻¹ from by
            rw [map_mul, mul_inv, mul_comm ((algebraMap R K) ↑s₁)⁻¹,
                ← mul_assoc, mul_inv_cancel₀ hs₂, one_mul],
        show ((algebraMap R K) ↑s₂)⁻¹ =
          (algebraMap R K) ↑s₁ * ((algebraMap R K) (↑s₁ * ↑s₂))⁻¹ from by
            rw [map_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs₁, one_mul],
        algebraMap_mul_eq_smul, algebraMap_mul_eq_smul,
        ← smul_tmul, ← smul_tmul, ← add_tmul]
    exact ⟨(↑s₂ : R) • a₁ + (↑s₁ : R) • a₂,
           ⟨↑s₁ * ↑s₂, (nonZeroDivisors R).mul_mem s₁.2 s₂.2⟩, rfl⟩

/-- Lemma 12.5: every element of `A ⊗_R K` (where `K = Frac R`) can be written as a
single pure tensor `a ⊗ b`. -/
theorem TensorProduct.exists_pure_tensor_fractionRing
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [AddCommGroup A] [Module R A]
    (x : A ⊗[R] K) : ∃ a : A, ∃ b : K, x = a ⊗ₜ[R] b :=
  let ⟨a, s, h⟩ := TensorProduct.exists_tmul_inv_algebraMap x
  ⟨a, ((algebraMap R K) s)⁻¹, h⟩

/-- Specialization of Lemma 12.5 to `R = ℤ`, `K = ℚ`: every element of `M ⊗_ℤ ℚ` is a
pure tensor `m ⊗ n⁻¹` with `n ∈ ℤ \ {0}`. -/
theorem TensorProduct.exists_pure_tensor_int_rat
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (x : M ⊗[ℤ] ℚ) : ∃ m : M, ∃ n : ℤ, n ≠ 0 ∧ x = m ⊗ₜ[ℤ] (n⁻¹ : ℚ) := by
  obtain ⟨a, s, hs⟩ := TensorProduct.exists_tmul_inv_algebraMap x
  exact ⟨a, ↑s, nonZeroDivisors.ne_zero s.2, by rw [hs]; congr 1⟩

end Lemma125

section Corollary1220

open WeierstrassCurve.Affine

universe v

variable {F : Type v} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)







end Corollary1220

section Definition1221

open WeierstrassCurve.Affine

universe w

variable {F : Type w} [Field F] [DecidableEq F]


end Definition1221
