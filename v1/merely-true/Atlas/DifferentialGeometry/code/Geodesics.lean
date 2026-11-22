/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Atlas.DifferentialGeometry.code.Manifolds
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Atlas.DifferentialGeometry.code.Intrinsic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Atlas.DifferentialGeometry.code.GaussMap

open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators

noncomputable section

namespace Geodesics

def IsGeodesic {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) : Prop :=
  ContDiff ℝ ⊤ γ ∧
  (∀ t, γ t ∈ M) ∧
  (∀ t, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    IsLocalDefiningFunction ψ M (γ t) →
    ∀ v ∈ Hypersurface.tangentSpace ψ (γ t), ⟪deriv (deriv γ) t, v⟫_ℝ = 0)

lemma deriv_mem_tangentSpace {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hsmooth : ContDiff ℝ ⊤ γ) (hM : ∀ t, γ t ∈ M)
    {t : ℝ} (hψ : IsLocalDefiningFunction ψ M (γ t)) :
    deriv γ t ∈ Hypersurface.tangentSpace ψ (γ t) := by
  rw [mem_tangentSpace_iff]
  obtain ⟨U, hUo, hγtU, _, hψM⟩ := hψ.exists_open_nhd
  have hγcont : Continuous γ := hsmooth.continuous
  have hPreOpen : IsOpen (γ ⁻¹' U) := hγcont.isOpen_preimage U hUo
  have htInPre : t ∈ γ ⁻¹' U := hγtU

  have hconst : ∀ᶠ s in nhds t, ψ (γ s) = 0 :=
    hPreOpen.eventually_mem htInPre |>.mono fun s hs => (hψM (γ s) hs).mp (hM s)

  have hderivComp : deriv (fun s => ψ (γ s)) t = 0 := by
    have : (fun s => ψ (γ s)) =ᶠ[nhds t] (fun _ => (0 : ℝ)) :=
      hconst.mono (fun s hs => by simp [hs])
    rw [Filter.EventuallyEq.deriv_eq this]
    simp

  have hγDiff : DifferentiableAt ℝ γ t :=
    (hsmooth.differentiable (by simp)).differentiableAt
  have hψDiff : DifferentiableAt ℝ ψ (γ t) := hψ.differentiableAt
  have hchain : HasDerivAt (fun s => ψ (γ s)) (fderiv ℝ ψ (γ t) (deriv γ t)) t :=
    (hψDiff.hasFDerivAt).comp_hasDerivAt t (hγDiff.hasDerivAt)
  linarith [hchain.deriv]

theorem geodesic_constant_speed {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hHyp : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (hγ : IsGeodesic M hHyp γ) :
    ∃ c : ℝ, ∀ t, ‖deriv γ t‖ = c := by
  obtain ⟨hsmooth, hM, hperp⟩ := hγ

  have h_inner_zero : ∀ t, ⟪deriv (deriv γ) t, deriv γ t⟫_ℝ = 0 := by
    intro t

    obtain ⟨ψ, hψ⟩ := hHyp (γ t) (hM t)
    exact hperp t ψ hψ (deriv γ t) (deriv_mem_tangentSpace hsmooth hM hψ)

  have hγ2 : ContDiff ℝ 2 γ := hsmooth.of_le le_top
  have hderiv_diff : Differentiable ℝ (deriv γ) := hγ2.differentiable_deriv_two
  have hderiv_diffAt : ∀ t, DifferentiableAt ℝ (deriv γ) t :=
    fun t => hderiv_diff.differentiableAt

  have h_norm_sq_deriv : ∀ t, deriv (fun t => ⟪deriv γ t, deriv γ t⟫_ℝ) t = 0 := by
    intro t
    rw [deriv_inner_apply ℝ (hderiv_diffAt t) (hderiv_diffAt t)]

    have h1 := real_inner_comm (deriv γ t) (deriv (deriv γ) t)
    linarith [h_inner_zero t]

  have h_norm_sq_diff : Differentiable ℝ (fun t => ⟪deriv γ t, deriv γ t⟫_ℝ) :=
    fun t => (hderiv_diffAt t).inner ℝ (hderiv_diffAt t)

  have h_norm_sq_const : ∀ s t, ⟪deriv γ s, deriv γ s⟫_ℝ = ⟪deriv γ t, deriv γ t⟫_ℝ :=
    is_const_of_deriv_eq_zero h_norm_sq_diff h_norm_sq_deriv

  have h_norm_const : ∀ s t, ‖deriv γ s‖ = ‖deriv γ t‖ := by
    intro s t
    have hsq : ‖deriv γ s‖ ^ 2 = ‖deriv γ t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact h_norm_sq_const s t
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  exact ⟨‖deriv γ 0‖, fun t => h_norm_const t 0⟩

def energy {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖ ^ 2

structure SmoothVariation {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) where
  Γ : ℝ → ℝ → EuclideanSpace ℝ (Fin (n + 1))
  smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Γ p.1 p.2)
  base : ∀ t, Γ 0 t = γ t
  left_fixed : ∀ s, Γ s a = γ a
  right_fixed : ∀ s, Γ s b = γ b
  maps_to : ∀ s t, Γ s t ∈ M

def firstVariationEnergy {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) : ℝ :=
  deriv (fun s => energy (V.Γ s) a b) 0

def variationField {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  deriv (fun s => V.Γ s t) 0

lemma variationField_mem_tangentSpace {n : ℕ}
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {t : ℝ} (hψ : IsLocalDefiningFunction ψ M (γ t)) :
    variationField V t ∈ Hypersurface.tangentSpace ψ (γ t) := by
  rw [mem_tangentSpace_iff]

  obtain ⟨U, hUo, hγtU, _, hψM⟩ := hψ.exists_open_nhd

  have hΓcont : Continuous (fun s => V.Γ s t) := by
    have : (fun s => V.Γ s t) = (fun p : ℝ × ℝ => V.Γ p.1 p.2) ∘ (fun s => (s, t)) := by
      ext s; simp
    rw [this]
    exact V.smooth.continuous.comp (Continuous.prodMk_left t)


  have hbase : V.Γ 0 t ∈ U := by rw [V.base t]; exact hγtU
  have hPreOpen : IsOpen ((fun s => V.Γ s t) ⁻¹' U) := hΓcont.isOpen_preimage U hUo
  have h0InPre : (0 : ℝ) ∈ (fun s => V.Γ s t) ⁻¹' U := hbase

  have hconst : ∀ᶠ s in nhds (0 : ℝ), ψ (V.Γ s t) = 0 :=
    hPreOpen.eventually_mem h0InPre |>.mono fun s hs => (hψM (V.Γ s t) hs).mp (V.maps_to s t)

  have hderivComp : deriv (fun s => ψ (V.Γ s t)) 0 = 0 := by
    have : (fun s => ψ (V.Γ s t)) =ᶠ[nhds 0] (fun _ => (0 : ℝ)) :=
      hconst.mono (fun s hs => by simp [hs])
    rw [Filter.EventuallyEq.deriv_eq this]
    simp

  have hΓDiff : DifferentiableAt ℝ (fun s => V.Γ s t) 0 := by
    have : (fun s => V.Γ s t) = (fun p : ℝ × ℝ => V.Γ p.1 p.2) ∘ (fun s => (s, t)) := by
      ext s; simp
    rw [this]
    exact (V.smooth.differentiable (by simp)).differentiableAt.comp _
      (Differentiable.prodMk differentiable_id (differentiable_const t)).differentiableAt

  have hψDiff : DifferentiableAt ℝ ψ (V.Γ 0 t) := by
    rw [V.base t]; exact hψ.differentiableAt
  have hchain : HasDerivAt (fun s => ψ (V.Γ s t))
      (fderiv ℝ ψ (V.Γ 0 t) (deriv (fun s => V.Γ s t) 0)) 0 :=
    (hψDiff.hasFDerivAt).comp_hasDerivAt 0 (hΓDiff.hasDerivAt)
  have := hchain.deriv
  rw [V.base t] at this
  change fderiv ℝ ψ (γ t) (variationField V t) = 0
  change deriv (fun s => ψ (V.Γ s t)) 0 = (fderiv ℝ ψ (γ t)) (variationField V t) at this
  linarith [hderivComp, this]




def IsEnergyMinimizer {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : Prop :=
  ∀ V : SmoothVariation M γ a b, ∀ s : ℝ, energy γ a b ≤ energy (V.Γ s) a b



def IsGeodesicOn {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (I : Set ℝ) : Prop :=
  ContDiff ℝ ⊤ γ ∧
  (∀ t ∈ I, γ t ∈ M) ∧
  (∀ t ∈ I, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    IsLocalDefiningFunction ψ M (γ t) →
    ∀ v ∈ Hypersurface.tangentSpace ψ (γ t), ⟪deriv (deriv γ) t, v⟫_ℝ = 0)





def SatisfiesGeodesicEquation {n : ℕ} (patch : HypersurfacePatch n)
    (c : ℝ → Fin n → ℝ) : Prop :=
  ContDiff ℝ ⊤ c ∧
  (∀ t, c t ∈ patch.domain) ∧
  (∀ t, ∀ k : Fin n,
    (deriv (deriv c) t) k +
      ∑ i : Fin n, ∑ j : Fin n,
        ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
          (deriv c t i) * (deriv c t j) = 0)


lemma metric_christoffel_identity {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j s : Fin n) :
    ∑ k : Fin n, firstFundamentalForm patch x s k *
      ChristoffelSymbols.christoffelSymbol patch x i j k =
    (ChristoffelSymbols.secondPartialDeriv patch x i j) ⬝ᵥ
      (patch.partialDeriv x s) := by

  have hG := firstFundamentalForm_posDef patch x hx
  have hdet : IsUnit (firstFundamentalForm patch x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit

  let v : Fin n → ℝ := fun l =>
    (ChristoffelSymbols.secondPartialDeriv patch x i j) ⬝ᵥ (patch.partialDeriv x l)
  have hcancel : (firstFundamentalForm patch x).mulVec
      ((firstFundamentalForm patch x)⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]


  simp only [ChristoffelSymbols.christoffelSymbol, Matrix.mulVec, dotProduct]
  change (∑ x_1, firstFundamentalForm patch x s x_1 *
    ∑ x_2, (firstFundamentalForm patch x)⁻¹ x_1 x_2 * v x_2) = v s
  have := congr_fun hcancel s
  simp only [Matrix.mulVec, dotProduct] at this
  exact this








section GeodesicDistance

variable {n : ℕ}

structure SmoothPathIn (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) where
  toFun : ℝ → EuclideanSpace ℝ (Fin (n + 1))
  smooth : ∀ (m : ℕ∞), ContDiff ℝ m toFun
  source : toFun 0 = p
  target : toFun 1 = q
  maps_to : ∀ t, toFun t ∈ M

def pathLength {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖

def reversePath {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) :
    SmoothPathIn M q p where
  toFun := fun t => γ.toFun (1 - t)
  smooth := fun m => (γ.smooth m).comp (by fun_prop)
  source := by simp [γ.target]
  target := by simp [γ.source]
  maps_to := fun t => γ.maps_to _

theorem pathLength_reverse {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) :
    pathLength (reversePath γ) = pathLength γ := by
  simp only [pathLength, reversePath]
  have hd : ∀ t, deriv (fun t => γ.toFun (1 - t)) t = -(deriv γ.toFun (1 - t)) := by
    intro t
    have hda : DifferentiableAt ℝ γ.toFun (1 - t) :=
      ((γ.smooth 1).differentiable (by simp)).differentiableAt
    have hd1 : HasDerivAt (fun t => (1 : ℝ) - t) (-1) t := by
      have := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      simp at this
      exact this
    have hcomp := hda.hasDerivAt.scomp t hd1
    have heq : (fun t => γ.toFun (1 - t)) = γ.toFun ∘ HSub.hSub 1 := rfl
    rw [heq, hcomp.deriv]
    simp
  simp_rw [hd, norm_neg]
  rw [intervalIntegral.integral_comp_sub_left (fun t => ‖deriv γ.toFun t‖) 1]
  simp

def geodesicDist (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  sInf {l | ∃ γ : SmoothPathIn M p q, pathLength γ = l}

def IsSmoothOnHypersurface {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Set E) (f : ↥M → ℝ) : Prop :=
  ∀ (y : E) (hy : y ∈ M), ∃ (V : Set E) (hV : IsOpen V) (hyV : y ∈ V)
    (f_ext : E → ℝ), ContDiffOn ℝ ⊤ f_ext V ∧
    ∀ z (hzM : z ∈ M) (_ : z ∈ V), f_ext z = f ⟨z, hzM⟩

structure ConnectedHypersurface (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin (n + 1)))
  isHypersurface : IsHypersurface carrier
  connected : ∀ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
    (∀ y ∈ carrier, ContDiffAt ℝ ⊤ φ y) →
    (∀ y ∈ carrier, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      IsLocalDefiningFunction ψ carrier y →
      ∀ v ∈ tangentSpace ψ y, fderiv ℝ φ y v = 0) →
    (∀ y₁ ∈ carrier, ∀ y₂ ∈ carrier, φ y₁ = φ y₂)

structure ConnectedHypersurfaceWithPaths (n : ℕ) extends ConnectedHypersurface n where
  pathConnected : ∀ p q : EuclideanSpace ℝ (Fin (n + 1)),
    p ∈ carrier → q ∈ carrier → Nonempty (SmoothPathIn carrier p q)

end GeodesicDistance



section GeodesicDistance
variable {n : ℕ}

theorem geodesicDist_self (M : ConnectedHypersurfaceWithPaths n)
    (p : EuclideanSpace ℝ (Fin (n + 1))) (hp : p ∈ M.carrier) :
    geodesicDist M.carrier p p = 0 := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun l ⟨γ, hγ⟩ => hγ ▸
        intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)⟩
    · exact ⟨⟨fun _ => p, fun _ => contDiff_const, rfl, rfl, fun _ => hp⟩, by
        simp [pathLength, deriv_const]⟩
  · apply le_csInf
    · exact ⟨_, ⟨fun _ => p, fun _ => contDiff_const, rfl, rfl, fun _ => hp⟩, rfl⟩
    · intro l ⟨γ, hγ⟩
      rw [← hγ]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)

theorem geodesicDist_comm (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) :
    geodesicDist M p q = geodesicDist M q p := by
  simp only [geodesicDist]
  congr 1
  ext l
  simp only [Set.mem_setOf_eq]
  exact ⟨fun ⟨γ, hγ⟩ => ⟨reversePath γ, by rw [pathLength_reverse, hγ]⟩,
         fun ⟨γ, hγ⟩ => ⟨reversePath γ, by rw [pathLength_reverse, hγ]⟩⟩


theorem geodesicDist_eq_zero_iff (M : ConnectedHypersurfaceWithPaths n)
    (p q : EuclideanSpace ℝ (Fin (n + 1))) (hp : p ∈ M.carrier) (hq : q ∈ M.carrier)
    (heq : geodesicDist M.carrier p q = 0) : p = q := by
  by_contra hne
  have hpos : 0 < ‖q - p‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hle : ‖q - p‖ ≤ geodesicDist M.carrier p q := by
    apply le_csInf
    · exact ⟨pathLength (M.pathConnected p q hp hq).some, (M.pathConnected p q hp hq).some, rfl⟩
    · intro l ⟨γ, hγ⟩
      rw [← hγ]
      have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ γ.toFun x :=
        fun x _ => ((γ.smooth 1).differentiable (by simp)).differentiableAt
      have hint : IntervalIntegrable (deriv γ.toFun) volume 0 1 :=
        ((γ.smooth 1).continuous_deriv (by simp)).continuousOn.intervalIntegrable
      have hftc : ∫ t in (0 : ℝ)..1, deriv γ.toFun t = γ.toFun 1 - γ.toFun 0 :=
        integral_deriv_eq_sub hdiff hint
      calc ‖q - p‖ = ‖γ.toFun 1 - γ.toFun 0‖ := by rw [γ.target, γ.source]
        _ = ‖∫ t in (0 : ℝ)..1, deriv γ.toFun t‖ := by rw [hftc]
        _ ≤ ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖ := norm_integral_le_integral_norm (by norm_num)
  linarith


end GeodesicDistance



def lengthAB {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖


section EnergyLengthEquivalence

variable {n : ℕ}

def pathEnergy {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖ ^ 2

def IsConstantSpeed {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∃ c : ℝ, ∀ t, ‖deriv γ.toFun t‖ = c

def IsAbsoluteLengthMinimizer {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∀ σ : SmoothPathIn M p q, pathLength γ ≤ pathLength σ

def IsAbsoluteEnergyMinimizer {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∀ σ : SmoothPathIn M p q, pathEnergy γ ≤ pathEnergy σ







end EnergyLengthEquivalence

def IsMetricGeodesic {X : Type*} [MetricSpace X] (γ : ℝ → X) (a b : ℝ) : Prop :=
  Continuous γ ∧ ∀ s t, s ∈ Set.Icc a b → t ∈ Set.Icc a b → dist (γ s) (γ t) = |s - t|

def IsGlobalMetricGeodesic {X : Type*} [MetricSpace X] (γ : ℝ → X) : Prop :=
  ∀ s t : ℝ, dist (γ s) (γ t) = |s - t|

section Hadamard

variable {n : ℕ}

structure CompactPositiveGaussCurvature (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin (n + 1)))
  isHypersurface : IsHypersurface carrier
  isCompact : IsCompact carrier
  isConnected : IsConnected carrier
  gaussCurvaturePos : ∀ (patch : HypersurfacePatch n) (x : Fin n → ℝ),
    x ∈ patch.domain →
    (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ carrier →
    0 < gaussCurvature patch x




end Hadamard

section HopfRinow

variable {n : ℕ}

def IsRiemannianGeodesicallyComplete (M : ConnectedHypersurface n) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ M.carrier)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hψ : IsLocalDefiningFunction ψ M.carrier y)
    (Y : EuclideanSpace ℝ (Fin (n + 1))) (hY : Y ∈ Hypersurface.tangentSpace ψ y),
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      IsGeodesic M.carrier M.isHypersurface γ ∧ γ 0 = y ∧ deriv γ 0 = Y

def IsMetricallyComplete (M : ConnectedHypersurface n) : Prop :=
  ∀ (x : ℕ → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ i, x i ∈ M.carrier) →
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ k ≥ N, geodesicDist M.carrier (x m) (x k) < ε) →
    ∃ p ∈ M.carrier, ∀ ε > 0, ∃ N, ∀ m ≥ N, geodesicDist M.carrier (x m) p < ε

def IsMinimizingGeodesic (M : ConnectedHypersurface n)
    (p q : EuclideanSpace ℝ (Fin (n + 1)))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)))
    (a b : ℝ) : Prop :=
  IsGeodesic M.carrier M.isHypersurface γ ∧
  γ a = p ∧ γ b = q ∧
    ∀ σ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      ContDiff ℝ ⊤ σ → (∀ t, σ t ∈ M.carrier) → σ a = p → σ b = q →
      energy γ a b ≤ energy σ a b


end HopfRinow

def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ (p q : X), ∃ (γ : ℝ → X),
    IsMetricGeodesic γ 0 (dist p q) ∧ γ 0 = p ∧ γ (dist p q) = q

def IsCATZeroSpace (X : Type*) [MetricSpace X] : Prop :=
  IsGeodesicSpace X ∧
  ∀ (p₁ p₂ p₃ : X)
    (γ₁₂ γ₁₃ γ₂₃ : ℝ → X),

    IsMetricGeodesic γ₁₂ 0 (dist p₁ p₂) →
    γ₁₂ 0 = p₁ → γ₁₂ (dist p₁ p₂) = p₂ →
    IsMetricGeodesic γ₁₃ 0 (dist p₁ p₃) →
    γ₁₃ 0 = p₁ → γ₁₃ (dist p₁ p₃) = p₃ →
    IsMetricGeodesic γ₂₃ 0 (dist p₂ p₃) →
    γ₂₃ 0 = p₂ → γ₂₃ (dist p₂ p₃) = p₃ →

    ∀ (q₁ q₂ q₃ : EuclideanSpace ℝ (Fin 2)),
    dist q₁ q₂ = dist p₁ p₂ →
    dist q₁ q₃ = dist p₁ p₃ →
    dist q₂ q₃ = dist p₂ p₃ →

    ∀ (t : ℝ) (s : ℝ),
    t ∈ Set.Icc 0 (dist p₁ p₂) →
    s ∈ Set.Icc 0 (dist p₁ p₃) →

    dist (γ₁₂ t) (γ₁₃ s) ≤
      dist ((1 - t / dist p₁ p₂) • q₁ + (t / dist p₁ p₂) • q₂)
           ((1 - s / dist p₁ p₃) • q₁ + (s / dist p₁ p₃) • q₃)

class IsBusemannSpace (X : Type*) [MetricSpace X] : Prop where
  isGeodesicSpace : IsGeodesicSpace X
  busemann_inequality : ∀ (l : ℝ) (hl : 0 < l)
    (γ₁ γ₂ : ℝ → X)
    (hγ₁ : IsMetricGeodesic γ₁ 0 l) (hγ₂ : IsMetricGeodesic γ₂ 0 l)
    (h_start : γ₁ 0 = γ₂ 0)
    (t : ℝ) (ht : t ∈ Set.Icc 0 l),
    dist (γ₁ t) (γ₂ t) ≤ (t / l) * dist (γ₁ l) (γ₂ l)

theorem busemann_unique_geodesic
    {X : Type*} [MetricSpace X] [IsBusemannSpace X]
    (p q : X) :
    (∃ γ : ℝ → X, IsMetricGeodesic γ 0 (dist p q) ∧ γ 0 = p ∧ γ (dist p q) = q) ∧
    (∀ γ₁ γ₂ : ℝ → X,
      IsMetricGeodesic γ₁ 0 (dist p q) → γ₁ 0 = p → γ₁ (dist p q) = q →
      IsMetricGeodesic γ₂ 0 (dist p q) → γ₂ 0 = p → γ₂ (dist p q) = q →
      ∀ t ∈ Set.Icc 0 (dist p q), γ₁ t = γ₂ t) := by
  constructor
  ·
    exact IsBusemannSpace.isGeodesicSpace p q
  ·
    intro γ₁ γ₂ hγ₁ hγ₁p hγ₁q hγ₂ hγ₂p hγ₂q t ht
    by_cases hpq : dist p q = 0
    ·
      have ht0 : t = 0 := le_antisymm (by linarith [ht.2, hpq.symm ▸ ht.2]) ht.1
      rw [ht0, hγ₁p, hγ₂p]
    ·
      have hd_pos : 0 < dist p q := by positivity
      have h_bus := IsBusemannSpace.busemann_inequality (dist p q) hd_pos
        γ₁ γ₂ hγ₁ hγ₂ (by rw [hγ₁p, hγ₂p]) t ht
      rw [hγ₁q, hγ₂q, dist_self, mul_zero] at h_bus
      exact dist_le_zero.mp h_bus




end Geodesics
