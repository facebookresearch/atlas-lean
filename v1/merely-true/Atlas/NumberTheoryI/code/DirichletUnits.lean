/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.ProductFormula

open scoped NumberField Classical Polynomial nonZeroDivisors NNReal
open NumberField NumberField.Units NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem Module
open NumberField.mixedEmbedding

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def logEmbedding_def : Additive ((𝓞 K)ˣ) →+ logSpace K :=
  NumberField.Units.logEmbedding K

theorem logEmbedding_ker_eq_torsion :
    (NumberField.Units.logEmbedding K).ker = (torsion K).toAddSubgroup :=
  logEmbedding_ker

def def_15_3_size (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : ℝ :=
  (∏ w : InfinitePlace K, f w ^ mult w) / (FractionalIdeal.absNorm I : ℝ)

def def_15_3_L (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set K :=
  {x : K | x ∈ (I : Submodule (𝓞 K) K) ∧ ∀ w : InfinitePlace K, w x ≤ f w}

theorem def_15_3_size_hom
    (I₁ I₂ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f₁ f₂ : InfinitePlace K → ℝ) :
    def_15_3_size K (I₁ * I₂) (f₁ * f₂) =
      def_15_3_size K I₁ f₁ * def_15_3_size K I₂ f₂ := by
  simp only [def_15_3_size, Pi.mul_apply, mul_pow, Finset.prod_mul_distrib, map_mul, Rat.cast_mul]
  ring

theorem def_15_3_kernel_contains_princ {x : K} (hx : x ≠ 0) :
    def_15_3_size K (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x)
      (fun w => w x) = 1 := by
  simp only [def_15_3_size]
  rw [InfinitePlace.prod_eq_abs_norm, FractionalIdeal.absNorm_span_singleton]
  exact div_self (Rat.cast_ne_zero.mpr (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hx)))

omit [NumberField K] in
theorem def_15_3_L_subset_I_c (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) :
    def_15_3_L K I f ⊆ (I : Set K) :=
  fun _ hx => hx.1

omit [NumberField K] in
def def_15_3_I_c_hom :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K × (InfinitePlace K → ℝ) →*
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  MonoidHom.fst _ _

theorem lem_15_7_unitLattice_spans_top :
    Submodule.span ℝ (unitLattice K : Set (logSpace K)) = ⊤ :=
  unitLattice_span_eq_top K

theorem lem_15_7_unitLattice_discrete :
    DiscreteTopology (unitLattice K) := inferInstance

theorem lem_15_7_unitLattice_inter_ball_finite (r : ℝ) :
    ((unitLattice K : Set (logSpace K)) ∩ Metric.closedBall 0 r).Finite :=
  unitLattice_inter_ball_finite K r

def arakelovL (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set K :=
  {x : K | x ∈ (I : Submodule (𝓞 K) K) ∧ ∀ w : InfinitePlace K, w x ≤ f w}

omit [NumberField K] in
theorem def_15_3_L_eq_arakelovL (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : def_15_3_L K I f = arakelovL K I f := rfl

theorem lem_15_7_arakelov_L_finite (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set.Finite (arakelovL K I f) := by
  obtain ⟨a, ha_mem, ha_int⟩ := I.isFractional
  have ha_ne : (a : K) ≠ 0 := by
    intro h; apply nonZeroDivisors.ne_zero ha_mem; exact Subtype.val_injective h
  let B := Finset.univ.sup' Finset.univ_nonempty (fun w : InfinitePlace K => w (a : K) * f w)
  apply Set.Finite.of_injOn (f := fun x => (a : K) * x)
    (t := {y : K | IsIntegral ℤ y ∧ ∀ φ : K →+* ℂ, ‖φ y‖ ≤ B})
  · intro x hx
    simp only [Set.mem_setOf_eq, arakelovL] at hx ⊢
    constructor
    · have h := ha_int x hx.1
      obtain ⟨c, hc⟩ := h
      rw [Algebra.smul_def] at hc
      rw [← hc]
      exact c.isIntegral_coe
    · intro φ
      rw [map_mul, norm_mul]
      calc ‖φ (a : K)‖ * ‖φ x‖
          = (InfinitePlace.mk φ) (a : K) * ‖φ x‖ := by rw [← InfinitePlace.apply φ]
        _ = (InfinitePlace.mk φ) (a : K) * (InfinitePlace.mk φ) x := by
            rw [← InfinitePlace.apply φ x]
        _ ≤ (InfinitePlace.mk φ) (a : K) * f (InfinitePlace.mk φ) := by
            gcongr; exact hx.2 _
        _ ≤ B := Finset.le_sup'_of_le _ (Finset.mem_univ _) le_rfl
  · intro x _ y _ h
    exact mul_left_cancel₀ ha_ne h
  · exact Embeddings.finite_of_norm_le K ℂ B

theorem cor_15_8_torsion_finite : Finite (torsion K) := inferInstance

theorem cor_15_8_kernel_characterization {x : (𝓞 K)ˣ} :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 :=
  mem_torsion K

theorem cor_15_8_logEmbedding_eq_zero_iff {x : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul x) = 0 ↔ x ∈ torsion K :=
  logEmbedding_eq_zero_iff

omit [NumberField K] in
theorem cor_15_8_torsion_subgroup :
    torsion K = CommGroup.torsion (𝓞 K)ˣ := rfl

theorem cor_15_8_torsion_cyclic : IsCyclic (torsion K) := inferInstance

theorem prop_15_9_unit_rank :
    finrank ℤ (↥(unitLattice K)) = rank K :=
  unitLattice_rank K

theorem rank_eq_card_sub_one : rank K = Fintype.card (InfinitePlace K) - 1 := rfl

theorem prop_15_9_L_contains_nonzero
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {f : InfinitePlace K → ℝ≥0}
    (h : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f)) :
    ∃ a ∈ arakelovL K (I : FractionalIdeal (𝓞 K)⁰ K) (fun w => (f w : ℝ)),
      a ≠ 0 := by
  obtain ⟨a, ha_mem, ha_ne, ha_bd⟩ := exists_ne_zero_mem_ideal_lt K I h
  exact ⟨a, ⟨ha_mem, fun w => le_of_lt (ha_bd w)⟩, ha_ne⟩

theorem prop_15_11_fundSystem_lattice_basis (i : Fin (rank K)) :
    (logEmbedding K) (Additive.ofMul (fundSystem K i)) =
      ↑((basisUnitLattice K) i) :=
  logEmbedding_fundSystem K i

def prop_15_11_basisUnitLattice : Basis (Fin (rank K)) ℤ (unitLattice K) :=
  basisUnitLattice K

theorem prop_15_11_closure_fundSystem_sup_torsion_eq_top :
    Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K = ⊤ :=
  closure_fundSystem_sup_torsion_eq_top K

theorem thm_15_12_dirichlet_unit_theorem (x : (𝓞 K)ˣ) :
    ∃! ζe : torsion K × (Fin (rank K) → ℤ),
      x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
  exist_unique_eq_mul_prod K x

theorem thm_15_12_units_fg : Monoid.FG (𝓞 K)ˣ := inferInstance

theorem thm_15_13_number_field_case (x : (𝓞 K)ˣ) :
    ∃! ζe : torsion K × (Fin (rank K) → ℤ),
      x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
  thm_15_12_dirichlet_unit_theorem K x

def placesAboveInfty (Fq F : Type*) [Field Fq] [Field F]
    [Algebra (RatFunc Fq) F] :
    Set (Valuation F (WithZero (Multiplicative ℤ))) :=
  {v | (v.comap (algebraMap (RatFunc Fq) F)).IsEquiv
         (FunctionField.inftyValuation Fq)}

def FunctionField.unitRank (Fq F : Type*) [Field Fq] [Field F]
    [Algebra (RatFunc Fq) F] : ℕ :=
  Nat.card (placesAboveInfty Fq F) - 1

def FunctionField.torsionUnits (Fq F : Type*) [Field Fq] [Field F]
    [Algebra Fq[X] F] : Subgroup (FunctionField.ringOfIntegers Fq F)ˣ :=
  CommGroup.torsion (FunctionField.ringOfIntegers Fq F)ˣ


def def_15_16_regulator : ℝ := regulator K

theorem def_15_16_regulator_pos : 0 < regulator K :=
  regulator_pos K

theorem def_15_16_regulator_ne_zero : regulator K ≠ 0 :=
  regulator_ne_zero K

def def_15_16_regOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ := regOfFamily u

theorem def_15_16_regulator_eq_det (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regulator K =
      |(Matrix.of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) *
        Real.log (w.val (fundSystem K (e i) : K))).det| :=
  regulator_eq_det K w' e

def arakelovDivisor_size (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : ℝ :=
  def_15_3_size K I f

def arakelovDivisor_L (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set K :=
  def_15_3_L K I f

theorem arakelovDivisor_size_mul
    (I₁ I₂ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f₁ f₂ : InfinitePlace K → ℝ) :
    def_15_3_size K (I₁ * I₂) (f₁ * f₂) =
      def_15_3_size K I₁ f₁ * def_15_3_size K I₂ f₂ :=
  def_15_3_size_hom K I₁ I₂ f₁ f₂

theorem arakelovDivisor_principal_size_eq_one {x : K} (hx : x ≠ 0) :
    def_15_3_size K (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x)
      (fun w => w x) = 1 :=
  def_15_3_kernel_contains_princ K hx

omit [NumberField K] in
theorem arakelovDivisor_L_subset (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) :
    def_15_3_L K I f ⊆ (I : Set K) :=
  def_15_3_L_subset_I_c K I f

omit [NumberField K] in
def arakelovDivisor_projection_hom :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K × (InfinitePlace K → ℝ) →*
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  def_15_3_I_c_hom K

theorem unitLattice_spans_top :
    Submodule.span ℝ (unitLattice K : Set (logSpace K)) = ⊤ :=
  lem_15_7_unitLattice_spans_top K

theorem unitLattice_discreteTopology :
    DiscreteTopology (unitLattice K) :=
  lem_15_7_unitLattice_discrete K

theorem arakelovL_finite (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set.Finite (arakelovL K I f) :=
  lem_15_7_arakelov_L_finite K I f

theorem torsion_finite : Finite (torsion K) :=
  cor_15_8_torsion_finite K

theorem mem_torsion_iff_forall_infinitePlace_eq_one {x : (𝓞 K)ˣ} :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 :=
  cor_15_8_kernel_characterization K

theorem logEmbedding_eq_zero_iff_mem_torsion {x : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul x) = 0 ↔ x ∈ torsion K :=
  cor_15_8_logEmbedding_eq_zero_iff K

omit [NumberField K] in
theorem torsion_eq_commGroup_torsion :
    torsion K = CommGroup.torsion (𝓞 K)ˣ :=
  cor_15_8_torsion_subgroup K

theorem torsion_isCyclic : IsCyclic (torsion K) :=
  cor_15_8_torsion_cyclic K

theorem rootsOfUnity_characterization :
    Finite (torsion K) ∧
    IsCyclic (torsion K) ∧
    (∀ x : (𝓞 K)ˣ, x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1) :=
  ⟨cor_15_8_torsion_finite K, cor_15_8_torsion_cyclic K,
   fun x => cor_15_8_kernel_characterization K⟩

theorem unitLattice_finrank_eq_rank :
    finrank ℤ (↑(unitLattice K)) = rank K :=
  prop_15_9_unit_rank K

theorem arakelovL_exists_ne_zero
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {f : InfinitePlace K → ℝ≥0}
    (h : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f)) :
    ∃ a ∈ arakelovL K (I : FractionalIdeal (𝓞 K)⁰ K) (fun w => (f w : ℝ)),
      a ≠ 0 :=
  prop_15_9_L_contains_nonzero K I h

theorem logEmbedding_fundSystem_eq_basisUnitLattice (i : Fin (rank K)) :
    (logEmbedding K) (Additive.ofMul (fundSystem K i)) =
      ↑((basisUnitLattice K) i) :=
  prop_15_11_fundSystem_lattice_basis K i

def basisOfUnitLattice : Basis (Fin (rank K)) ℤ (unitLattice K) :=
  prop_15_11_basisUnitLattice K

theorem closure_fundSystem_sup_torsion :
    Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K = ⊤ :=
  prop_15_11_closure_fundSystem_sup_torsion_eq_top K

theorem unit_eq_torsion_mul_fundSystem_pow (x : (𝓞 K)ˣ) :
    ∃! ζe : torsion K × (Fin (rank K) → ℤ),
      x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
  thm_15_12_dirichlet_unit_theorem K x

theorem units_fg : Monoid.FG (𝓞 K)ˣ :=
  thm_15_12_units_fg K

theorem numberField_unit_decomposition (x : (𝓞 K)ˣ) :
    ∃! ζe : torsion K × (Fin (rank K) → ℤ),
      x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) :=
  thm_15_13_number_field_case K x

def regulatorValue : ℝ := def_15_16_regulator K

theorem regulator_pos_of_numberField : 0 < regulator K :=
  def_15_16_regulator_pos K

theorem regulator_ne_zero_of_numberField : regulator K ≠ 0 :=
  def_15_16_regulator_ne_zero K

def regulatorOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ :=
  def_15_16_regOfFamily K u

theorem regulator_eq_det_of_fundSystem (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regulator K =
      |(Matrix.of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) *
        Real.log (w.val (fundSystem K (e i) : K))).det| :=
  def_15_16_regulator_eq_det K w' e

end
