/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.FermatsLastTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Analytic.Order
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold

noncomputable section

section WeakModularForms

/-- A weak modular form of weight `k` for a subgroup `Γ ≤ GL(2, ℝ)`: a slash-invariant
function on the upper half plane that is holomorphic (`MDiff`), but without any
condition on growth at the cusps. -/
structure WeakModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) extends
    SlashInvariantForm Γ k where
  holo' : MDiff (⇑toSlashInvariantForm)

end WeakModularForms

section ModularForms

/-- Modular forms of weight `k` for the full modular group `SL(2, ℤ) = Γ(1)`. -/
abbrev ModularFormForSL2Z (k : ℤ) := ModularForm (Γ(1) : Subgroup SL(2, ℤ)) k

/-- Forgetful map: every modular form for `SL(2, ℤ)` is in particular a weak modular
form (we drop the boundedness-at-cusps condition). -/
def ModularFormForSL2Z.toWeakModularForm {k : ℤ} (f : ModularFormForSL2Z k) :
    WeakModularForm (Γ(1) : Subgroup SL(2, ℤ)) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'

end ModularForms

section CongruenceSubgroups

/-- Modular forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev ModularFormGamma0 (N : ℕ) (k : ℤ) :=
  ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- Weak modular forms of weight `k` for `Γ₀(N)` (holomorphic and slash-invariant,
without cuspidal growth condition). -/
abbrev WeakModularFormGamma0 (N : ℕ) (k : ℤ) :=
  WeakModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

end CongruenceSubgroups

section CuspForms

/-- Cusp forms of weight `k` for the full modular group `SL(2, ℤ) = Γ(1)` (modular
forms vanishing at every cusp). -/
abbrev CuspFormForSL2Z (k : ℤ) := CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k

/-- Cusp forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev CuspFormGamma0 (N : ℕ) (k : ℤ) :=
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- A cusp form for `SL(2, ℤ)` is in particular a modular form (vanishing at cusps
implies boundedness at cusps). -/
def CuspFormForSL2Z.toModularFormForSL2Z {k : ℤ} (f : CuspFormForSL2Z k) :
    ModularFormForSL2Z k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f hc

/-- A cusp form for `SL(2, ℤ)` is in particular a weak modular form (drop both the
boundedness and vanishing conditions at cusps). -/
def CuspFormForSL2Z.toWeakModularForm {k : ℤ} (f : CuspFormForSL2Z k) :
    WeakModularForm (Γ(1) : Subgroup SL(2, ℤ)) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'

end CuspForms

namespace FLT




end FLT

namespace MinimalModel

/-- Predicate stating that an integral Weierstrass model `W` is a model for the
rational Weierstrass curve `E`, i.e. there is a `ℚ`-rational change of variables
taking `W` (viewed over `ℚ`) to `E`. -/
def IsModelFor (E : WeierstrassCurve.Affine ℚ) (W : WeierstrassCurve.Affine ℤ) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange ℚ,
    C • (W.map (Int.castRingHom ℚ)) = E

/-- Structure encoding that `W` is a minimal integral model for `E`: it is a model
for `E` and its discriminant divides that of every other integral model of `E`. -/
structure IsMinimalModel (E : WeierstrassCurve.Affine ℚ)
    (W : WeierstrassCurve.Affine ℤ) : Prop where
  is_model_for : IsModelFor E W
  discriminant_dvd : ∀ W' : WeierstrassCurve.Affine ℤ, IsModelFor E W' → W.Δ ∣ W'.Δ





end MinimalModel

namespace EllipticCurveReduction

open MinimalModel

/-- The four possible reduction types of an elliptic curve at a prime:
good reduction, split multiplicative reduction, nonsplit multiplicative reduction,
or additive reduction. -/
inductive ReductionType where
  | good : ReductionType
  | splitMultiplicative : ReductionType
  | nonsplitMultiplicative : ReductionType
  | additive : ReductionType
  deriving DecidableEq, Repr









end EllipticCurveReduction

namespace EllipticCurve






end EllipticCurve

namespace EllipticCurveLFunction

open Complex Polynomial EllipticCurveReduction















end EllipticCurveLFunction

namespace NewformQExpansion

open EllipticCurveLFunction EllipticCurveReduction

/-- An integral, normalized weight-2 newform: a level `N` together with integer
Fourier coefficients `a_n` with `a_0 = 0` and `a_1 = 1`. -/
structure IntegralWeight2Newform where
  level : ℕ+
  coeffs : ℕ → ℤ
  coeffs_zero : coeffs 0 = 0
  coeffs_one : coeffs 1 = 1





end NewformQExpansion

namespace ModularEllipticCurve

open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion



end ModularEllipticCurve

namespace ModularityTheorem

open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularEllipticCurve

/-- The L-function of a newform: the Dirichlet L-series with coefficients
`a_n ∈ ℂ`. -/
noncomputable def newformLFunction
    (f : IntegralWeight2Newform) (s : ℂ) : ℂ :=
  LSeries (fun n => (f.coeffs n : ℂ)) s








end ModularityTheorem


namespace FaltingsTate

open EllipticCurveLFunction EllipticCurveReduction



end FaltingsTate

namespace IsogenyLFunction

open EllipticCurveLFunction EllipticCurveReduction









end IsogenyLFunction


namespace HeckeOperatorProperties

open Complex

/-- A complex lattice `Λ ⊂ ℂ`: a pair of complex periods `ω₁, ω₂` that are
ℝ-linearly independent. -/
@[ext]
structure ComplexLattice where
  ω₁ : ℂ
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

/-- The free abelian group on the set of complex lattices, viewed as the divisor
group of lattices. -/
abbrev DivL := FreeAbelianGroup ComplexLattice

/-- Coercion of a positive natural number `n` to a nonzero complex unit. -/
noncomputable def pnatToComplexUnits (n : ℕ+) : ℂˣ :=
  Units.mk0 (n : ℂ) (by exact_mod_cast n.ne_zero)

/-- The action of a nonzero complex scalar `l` on a complex lattice, scaling
both periods. -/
noncomputable def scaleLattice (l : ℂˣ) (L : ComplexLattice) : ComplexLattice where
  ω₁ := (l : ℂ) * L.ω₁
  ω₂ := (l : ℂ) * L.ω₂
  indep := by
    have hl : (l : ℂ) ≠ 0 := Units.ne_zero l
    let f : ℂ →ₗ[ℝ] ℂ := {
      toFun := fun x => (l : ℂ) * x
      map_add' := fun a b => by ring
      map_smul' := fun r x => Algebra.mul_smul_comm r (l : ℂ) x
    }
    have hf_ker : f.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at hx
      exact (mul_eq_zero.mp hx).resolve_left hl
    have heq : ![(l : ℂ) * L.ω₁, (l : ℂ) * L.ω₂] = f ∘ ![L.ω₁, L.ω₂] := by
      ext i; fin_cases i <;> simp [f]
    rw [heq]
    exact L.indep.map' f hf_ker



/-- The homothety operator `R_l`: the ℤ-linear extension of the scaling action
on lattices by the scalar `l ∈ ℂˣ`. -/
noncomputable def homothetyR (l : ℂˣ) : Module.End ℤ DivL :=
  (FreeAbelianGroup.map (scaleLattice l)).toIntLinearMap

/-- Scalings compose by multiplication of scalars. -/
lemma scaleLattice_comp (l mu : ℂˣ) :
    scaleLattice l ∘ scaleLattice mu = scaleLattice (l * mu) := by
  funext L
  simp only [Function.comp, scaleLattice]
  ext <;> simp [Units.val_mul, mul_assoc]


/-- Homotheties multiply: `R_l ∘ R_μ = R_{lμ}`. -/
theorem homothety_mul (l mu : ℂˣ) :
    homothetyR l * homothetyR mu = homothetyR (l * mu) := by
  ext x
  show (FreeAbelianGroup.map (scaleLattice l)) ((FreeAbelianGroup.map (scaleLattice mu)) x) =
    (FreeAbelianGroup.map (scaleLattice (l * mu))) x
  rw [← FreeAbelianGroup.map_comp_apply, scaleLattice_comp]













end HeckeOperatorProperties

namespace HeckeMultiplicativity

open Complex








end HeckeMultiplicativity

namespace GaloisRepresentation

open EllipticCurveReduction EllipticCurveLFunction






/-- Reduction `GL₂(ℤ_ℓ) → GL₂(𝔽_ℓ)` modulo `ℓ`. -/
noncomputable def reductionModL (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    GL (Fin 2) ℤ_[ℓ] →* GL (Fin 2) (ZMod ℓ) :=
  Matrix.GeneralLinearGroup.map PadicInt.toZMod



end GaloisRepresentation

end

namespace NewformDefinition

open Complex Asymptotics Filter

/-- A formal Dirichlet series, wrapping a sequence of complex coefficients. -/
structure DirichletSeries where
  coeffs : ℕ → ℂ

/-- The value at `s` of a Dirichlet series, defined as the L-series of its
coefficient sequence. -/
noncomputable def DirichletSeries.eval (L : DirichletSeries) (s : ℂ) : ℂ :=
  LSeries L.coeffs s

/-- Summability of a Dirichlet series at `s`: the underlying L-series sum is
summable. -/
def DirichletSeries.summable (L : DirichletSeries) (s : ℂ) : Prop :=
  LSeriesSummable L.coeffs s

/-- Unfolding lemma: the `eval` of a Dirichlet series is definitionally the
L-series of its coefficients. -/
@[simp]
theorem DirichletSeries.eval_eq (L : DirichletSeries) (s : ℂ) :
    L.eval s = LSeries L.coeffs s := rfl

/-- The Dirichlet series summability predicate unfolds to L-series
summability. -/
theorem DirichletSeries.summable_iff (L : DirichletSeries) (s : ℂ) :
    L.summable s ↔ LSeriesSummable L.coeffs s := Iff.rfl

/-- If the coefficients are `O(n^σ)` at infinity, the Dirichlet series is
summable at every `s` with `Re(s) > σ + 1`. -/
theorem DirichletSeries.summable_of_isBigO_rpow (L : DirichletSeries) {σ : ℝ} {s : ℂ}
    (hs : σ + 1 < s.re)
    (hO : L.coeffs =O[atTop] fun n : ℕ => (n : ℝ) ^ σ) :
    L.summable s := by
  apply LSeriesSummable_of_isBigO_rpow (x := σ + 1) hs
  simp only [add_sub_cancel_right]
  exact hO

/-- Under the same `O(n^σ)` hypothesis on coefficients, the Dirichlet series is
differentiable on the half-plane `Re(s) > σ + 1`. -/
theorem DirichletSeries.differentiableOn_of_isBigO_rpow (L : DirichletSeries) {σ : ℝ}
    (hO : L.coeffs =O[atTop] fun n : ℕ => (n : ℝ) ^ σ) :
    DifferentiableOn ℂ L.eval {s | σ + 1 < s.re} := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have hab : LSeries.abscissaOfAbsConv L.coeffs ≤ σ + 1 :=
    LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hO
  have hlt : LSeries.abscissaOfAbsConv L.coeffs < ↑s.re := by
    exact lt_of_le_of_lt hab (by exact_mod_cast hs)
  exact (LSeries_hasDerivAt hlt).differentiableAt

end NewformDefinition

namespace WeakBSD

open EllipticCurveLFunction Complex

/-- The arithmetic rank of an elliptic curve over `ℚ`: the ℤ-rank of its
Mordell–Weil group modulo torsion. -/
noncomputable def arithmeticRank (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] : ℕ :=
  Module.finrank ℤ (E.Point ⧸ AddCommGroup.torsion E.Point)







end WeakBSD

namespace HeckeAnalyticContinuation

open Complex

/-- Data for a cusp form: weight, level, and complex Fourier coefficients with
`a_0 = 0`. -/
structure CuspFormData where
  weight : ℕ
  level : ℕ+
  coeffs : ℕ → ℂ
  coeffs_zero : coeffs 0 = 0

/-- The L-function attached to a cusp form's coefficient data: the Dirichlet
L-series of its coefficients. -/
noncomputable def CuspFormData.LFunction (f : CuspFormData) (s : ℂ) : ℂ :=
  LSeries f.coeffs s

/-- The completed L-function of a cusp form:
`Λ(f, s) = N^{s/2} (2π)^{-s} Γ(s) L(f, s)`. -/
noncomputable def CuspFormData.completedLFunction (f : CuspFormData) (s : ℂ) : ℂ :=
  (f.level : ℂ) ^ (s / 2) * (2 * ↑Real.pi : ℂ) ^ (-s) * Gamma s * f.LFunction s


end HeckeAnalyticContinuation

namespace EulerProductNewform

open Complex HeckeAnalyticContinuation

/-- Data for a normalized newform: cusp-form data together with the
normalization `a_1 = 1`. -/
structure NewformData extends CuspFormData where
  coeffs_one : toCuspFormData.coeffs 1 = 1

/-- The principal Dirichlet character of conductor `N` at the prime `p`: equals
`0` if `p | N` and `1` otherwise. -/
noncomputable def principalDirichletChar (N : ℕ+) (p : ℕ) : ℂ :=
  if p ∣ (N : ℕ) then 0 else 1

/-- The local Euler factor of a newform at the prime `p`:
`(1 - a_p p^{-s} + χ(p) p^{k-1} p^{-2s})^{-1}`. -/
noncomputable def localEulerFactor (f : NewformData) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - f.coeffs p * (p : ℂ) ^ (-s) +
    principalDirichletChar f.level p * (p : ℂ) ^ ((f.weight : ℤ) - 1) *
      (p : ℂ) ^ (-2 * s))⁻¹

/-- The Euler product of a newform: the (unordered) product over primes of the
local Euler factors. -/
noncomputable def eulerProduct (f : NewformData) (s : ℂ) : ℂ :=
  tprod (fun (p : Nat.Primes) => localEulerFactor f p.val s)

/-- The L-function of a newform, as a Dirichlet series in its Fourier
coefficients. -/
noncomputable def NewformData.LFunction (f : NewformData) (s : ℂ) : ℂ :=
  LSeries f.coeffs s


end EulerProductNewform

namespace ParityConjecture

open WeakBSD




end ParityConjecture

namespace PeterssonInnerProduct

open Complex MeasureTheory
open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- Cusp forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev CuspFormGamma0 (N : ℕ) (k : ℤ) :=
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k













end PeterssonInnerProduct

namespace SpectralTheorem

open LinearMap IsSymmetric Module.End

/-- Spectral theorem for a family of commuting symmetric operators: the family
admits a joint eigenspace decomposition, i.e. the joint eigenspaces give an
internal direct sum decomposition of the whole space. -/
theorem spectral_theorem_commuting_symmetric
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {ι : Type*} [DecidableEq (ι → 𝕜)] {T : ι → E →ₗ[𝕜] E}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Function.onFun Commute T)) :
    DirectSum.IsInternal (fun χ : ι → 𝕜 ↦ ⨅ j, eigenspace (T j) (χ j)) :=
  LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hC

/-- Spectral theorem (supremum version): the supremum of joint eigenspaces of a
commuting family of symmetric operators is the whole space. -/
theorem spectral_theorem_commuting_symmetric_iSup
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {ι : Type*} {T : ι → E →ₗ[𝕜] E}
    (hT : ∀ i, (T i).IsSymmetric) (hC : Pairwise (Function.onFun Commute T)) :
    ⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i) (χ i) = ⊤ :=
  iSup_iInf_eq_top_of_commute hT hC

/-- Spectral theorem for a commuting pair of symmetric operators: the joint
eigenspaces `Eig_A(α) ∩ Eig_B(β)` form an internal direct sum decomposition. -/
theorem directSum_isInternal_commuting_pair
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.IsInternal
      (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)) :=
  directSum_isInternal_of_commute hA hB hAB

end SpectralTheorem

namespace LFunctionAnalyticContinuation

open Complex EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularityTheorem HeckeAnalyticContinuation


/-- Convert an integral weight-2 newform to abstract cusp-form data (weight `2`,
same level, coefficients embedded in `ℂ`). -/
noncomputable def cuspFormDataOfNewform (f : IntegralWeight2Newform) : CuspFormData where
  weight := 2
  level := f.level
  coeffs := fun n => (f.coeffs n : ℂ)
  coeffs_zero := by simp [f.coeffs_zero]


end LFunctionAnalyticContinuation

namespace ModularForm

open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- Cusp forms of weight `k` for an arbitrary subgroup `Γ ≤ SL(2, ℤ)`. -/
abbrev CuspFormForSubgroup (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :=
  CuspForm Γ k

end ModularForm

namespace HeckeEigenformBasis

open Complex
open scoped CongruenceSubgroup MatrixGroups ModularForm

















end HeckeEigenformBasis

namespace HeckeEigenvalueTheorem

open scoped CongruenceSubgroup MatrixGroups ModularForm
open Complex









end HeckeEigenvalueTheorem

namespace HeckeCoeffRelation

open scoped CongruenceSubgroup MatrixGroups ModularForm
open Complex HeckeEigenvalueTheorem PeterssonInnerProduct









end HeckeCoeffRelation

namespace ModularFormDimension

open scoped CongruenceSubgroup MatrixGroups ModularForm














end ModularFormDimension

namespace HeckeNewformDecomposition

open Complex
open scoped CongruenceSubgroup MatrixGroups ModularForm



















end HeckeNewformDecomposition
