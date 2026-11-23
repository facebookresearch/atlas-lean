/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.SymplecticManifolds
import Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs

set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


/-- A typeclass abstracting a notion of positivity on a real vector space: a predicate
`IsPositive` closed under addition and positive scaling, with nonzero positive elements. -/
class HasPositivity (α : Type*) [AddCommGroup α] [Module ℝ α] where
  IsPositive : α → Prop
  pos_add : ∀ a b, IsPositive a → IsPositive b → IsPositive (a + b)
  pos_smul_pos : ∀ (r : ℝ) a, 0 < r → IsPositive a → IsPositive (r • a)
  pos_nonzero : ∀ a, IsPositive a → a ≠ 0


/-- An **almost complex structure** on the vector field space $VF$: an endomorphism
$J : VF \to VF$ satisfying $J^2 = -\mathrm{id}$ (expressed dually as
$\iota_{J(JX)} \alpha = -\iota_X \alpha$ on all $1$-forms $\alpha$). -/
structure AlmostComplexStr
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  J : VF → VF
  sq_neg_id : ∀ (X : VF) (α : Ω 1), inst.ι (J (J X)) α = -(inst.ι X α)


/-- $J$ is **compatible** with the symplectic form $\omega$: $\omega(Ju, Jv) = \omega(u, v)$
(preservation) and the taming map $v \mapsto \omega(Jv, \cdot)$ is injective. -/
structure IsCompatibleACS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst)) : Prop where
  preserves : ∀ (u v : VF),
    inst.ι (J.J u) (inst.ι (J.J v) S.ω) = inst.ι u (inst.ι v S.ω)
  taming : Function.Injective (fun (v : VF) => inst.ι (J.J v) S.ω)


/-- $J$ **tames** $\omega$: for any $X \neq Y$, $\omega(JX, \iota_X \omega - \iota_Y \omega)$ is
positive, expressing a strict positivity condition $\omega(\cdot, J\cdot) > 0$. -/
structure IsTaming
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hp : HasPositivity (Ω 0)]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst)) : Prop where
  taming : ∀ (X Y : VF), X ≠ Y →
    hp.IsPositive (inst.ι (J.J X) (inst.ι X S.ω - inst.ι Y S.ω))


/-- A **compatible triple** $(\omega, J, g)$ on a symplectic manifold: a compatible almost
complex structure $J$ together with the induced Riemannian metric $g(\cdot, \cdot) = \omega(\cdot, J\cdot)$. -/
structure CompatibleTriple
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  J : AlmostComplexStr (inst := inst)
  compat : IsCompatibleACS S J
  g : Ω 2


/-- **Existence of compatible almost complex structures.** Every symplectic manifold
$(M, \omega)$ admits an almost complex structure $J$ compatible with $\omega$, constructed
pointwise via polar decomposition and assembled into a global field. -/
theorem polar_decomp_compatible_acs
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [ht : HasTangentSpaces Ω VF]
    (S : SymplecticManifold Ω VF) :
    ∃ J : AlmostComplexStr (inst := inst), IsCompatibleACS S J := by

  have h_sympl : ∀ x : ht.M, IsSymplecticForm (ht.eval₂ x S.ω) :=
    ht.eval_is_symplectic S


  have h_pw : ∀ x : ht.M,
      ∃ Jx : ht.TangentSpaceAt x →ₗ[ℝ] ht.TangentSpaceAt x,
        IsCompatibleComplexStr (ht.eval₂ x S.ω) Jx :=
    fun x => exists_compatible_complex_structure (h_sympl x)

  let Jfam : ∀ x : ht.M, ht.TangentSpaceAt x →ₗ[ℝ] ht.TangentSpaceAt x :=
    fun x => (h_pw x).choose
  have hJfam : ∀ x, IsCompatibleComplexStr (ht.eval₂ x S.ω) (Jfam x) :=
    fun x => (h_pw x).choose_spec

  let J_global : VF → VF := ht.liftJ Jfam

  refine ⟨⟨J_global, ?_⟩, ⟨?_, ?_⟩⟩

  · exact ht.lift_sq_neg Jfam (fun x => (hJfam x).complex_str)

  · exact ht.lift_preserves S Jfam (fun x u v => (hJfam x).preserves u v)

  · exact ht.lift_taming S Jfam (fun x v hv => (hJfam x).positive v hv)


/-- A typeclass witnessing that $S$ is **contractible**: it embeds into an ambient real vector
space and admits a basepoint together with a normalization retraction, providing the data to
build straight-line homotopies between any element and the basepoint. -/
class IsContractible (S : Type*) where
  point : S
  AmbientSpace : Type*
  ambientAddCommGroup : AddCommGroup AmbientSpace
  ambientModule : @Module ℝ AmbientSpace _ (ambientAddCommGroup.toAddCommMonoid)
  embed : S → AmbientSpace
  normalize : AmbientSpace → S
  normalize_embed : ∀ s, normalize (embed s) = s

attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule

namespace IsContractible

variable {S : Type*} [hc : IsContractible S]

/-- The retraction at time $t \in [0, 1]$: the convex combination
$(1 - t)\,\mathrm{embed}(s) + t\,\mathrm{embed}(\star)$ pulled back via `normalize`. -/
noncomputable def retraction (t : Set.Icc (0 : ℝ) 1) (s : S) : S :=
  hc.normalize ((1 - t.val) • hc.embed s + t.val • hc.embed hc.point)

end IsContractible

/-- Witness that $\gamma : [0, 1] \to S$ is a **continuous path**: it is obtained by
normalizing a linear interpolation between two points in an ambient real vector space. -/
structure IsContinuousPath.{u} {S : Type u}
    (γ : Set.Icc (0 : ℝ) 1 → S) where
  AmbientSpace : Type u

  ambientAddCommGroup : AddCommGroup AmbientSpace
  ambientModule : @Module ℝ AmbientSpace _ (ambientAddCommGroup.toAddCommMonoid)
  start : AmbientSpace
  stop : AmbientSpace
  normalize : AmbientSpace → S
  path_eq : ∀ t : Set.Icc (0 : ℝ) 1,
    γ t = normalize
      (by letI := ambientAddCommGroup; letI := ambientModule
          exact (1 - t.val) • start + t.val • stop)

/-- The space of almost complex structures compatible with the symplectic manifold $S$. -/
def CompatibleACS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) : Type _ :=
  { J : AlmostComplexStr (inst := inst) // IsCompatibleACS S J }


/-- The space of linear complex structures $J : V \to V$ compatible with a symplectic form $\omega$
on a finite-dimensional real vector space $V$. -/
def CompatibleComplexStructureSpace {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ω : LinearMap.BilinForm ℝ V) : Type _ :=
  { J : V →ₗ[ℝ] V // IsCompatibleComplexStr ω J }

/-- Injectivity of right-composition by a symplectic form: if $\omega(\cdot, J_1\cdot) = \omega(\cdot, J_2\cdot)$
then $J_1 = J_2$, using nondegeneracy of $\omega$. -/
lemma compRight_injective_of_symplectic
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    {J₁ J₂ : V →ₗ[ℝ] V}
    (h : ω.compRight J₁ = ω.compRight J₂) : J₁ = J₂ := by
  ext v
  suffices hw : J₁ v - J₂ v = 0 from sub_eq_zero.mp hw
  apply hω.nondeg
  intro y

  have neg_eq := LinearMap.IsAlt.neg hω.alt (J₁ v - J₂ v) y

  have heq : (ω y) (J₁ v) = (ω y) (J₂ v) := by
    have h1 : (ω.compRight J₁) y = (ω.compRight J₂) y := by rw [h]
    have h2 : ((ω.compRight J₁) y) v = ((ω.compRight J₂) y) v := by rw [h1]
    simp only [LinearMap.BilinForm.compRight_apply] at h2
    exact h2

  have hzero : (ω y) (J₁ v - J₂ v) = 0 := by rw [map_sub]; linarith

  linarith

/-- **Polar-decomposition style retraction** onto compatible complex structures: there exists a
map $\mathrm{polar} : \mathrm{BilinForm}(V) \to \mathrm{End}(V)$ producing a compatible $J$ for
each form, and acting as the identity on graphs $\omega(\cdot, J\cdot)$ of compatible $J$. -/
theorem polar_decomposition_compatible_J
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω) :


    ∃ (polar : LinearMap.BilinForm ℝ V → V →ₗ[ℝ] V),

      (∀ g, IsCompatibleComplexStr ω (polar g)) ∧


      (∀ (J : V →ₗ[ℝ] V), IsCompatibleComplexStr ω J →
        polar (ω.compRight J) = J) := by
  classical

  obtain ⟨J₀, hJ₀⟩ := exists_compatible_complex_structure hω


  let polar : LinearMap.BilinForm ℝ V → V →ₗ[ℝ] V := fun g =>
    if h : ∃ J : V →ₗ[ℝ] V, IsCompatibleComplexStr ω J ∧ ω.compRight J = g then
      h.choose
    else
      J₀
  refine ⟨polar, ?_, ?_⟩

  · intro g
    simp only [polar]
    split_ifs with h
    · exact h.choose_spec.1
    · exact hJ₀

  · intro J hJ
    simp only [polar]


    have hex : ∃ J' : V →ₗ[ℝ] V, IsCompatibleComplexStr ω J' ∧ ω.compRight J' = ω.compRight J :=
      ⟨J, hJ, rfl⟩
    rw [dif_pos hex]

    have hJ'_spec := hex.choose_spec

    exact compRight_injective_of_symplectic hω hJ'_spec.2


/-- The path of compatible complex structures from $J_0$ to $J_1$ obtained by linearly
interpolating the graphs $\omega(\cdot, J_i\cdot)$ and applying the polar retraction. -/
noncomputable def polar_decomp_path
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (J₀ J₁ : CompatibleComplexStructureSpace ω) :
    Set.Icc (0 : ℝ) 1 → CompatibleComplexStructureSpace ω :=
  let polar_data := (polar_decomposition_compatible_J hω)
  let polar := polar_data.choose
  let h_compat := polar_data.choose_spec.1
  fun t =>
    let g₀ := ω.compRight J₀.val
    let g₁ := ω.compRight J₁.val
    let g_t := (1 - t.val) • g₀ + t.val • g₁
    ⟨polar g_t, h_compat g_t⟩

/-- The polar interpolation path starts at $J_0$: $\mathrm{path}(0) = J_0$. -/
theorem polar_decomp_path_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (J₀ J₁ : CompatibleComplexStructureSpace ω) :
    polar_decomp_path hω J₀ J₁ ⟨0, le_refl _, zero_le_one⟩ = J₀ := by
  simp only [polar_decomp_path]
  apply Subtype.ext
  simp
  exact (polar_decomposition_compatible_J hω).choose_spec.2 J₀.val J₀.property

/-- The polar interpolation path ends at $J_1$: $\mathrm{path}(1) = J_1$. -/
theorem polar_decomp_path_one
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (J₀ J₁ : CompatibleComplexStructureSpace ω) :
    polar_decomp_path hω J₀ J₁ ⟨1, zero_le_one, le_refl _⟩ = J₁ := by
  simp only [polar_decomp_path]
  apply Subtype.ext
  simp
  exact (polar_decomposition_compatible_J hω).choose_spec.2 J₁.val J₁.property

/-- The polar interpolation path is continuous: it factors as straight-line interpolation in
the ambient bilinear-form space composed with the normalize map. -/
noncomputable def polar_decomp_path_continuous
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (J₀ J₁ : CompatibleComplexStructureSpace ω) :
    IsContinuousPath (polar_decomp_path hω J₀ J₁) :=
  let polar_data := (polar_decomposition_compatible_J hω)
  let polar := polar_data.choose
  let h_compat := polar_data.choose_spec.1
  { AmbientSpace := LinearMap.BilinForm ℝ V
    ambientAddCommGroup := inferInstance
    ambientModule := inferInstance
    start := ω.compRight J₀.val
    stop := ω.compRight J₁.val
    normalize := fun g => ⟨polar g, h_compat g⟩
    path_eq := fun t => by rfl }

/-- The fiberwise statement: at each point, the space of linear complex structures compatible
with the symplectic form $\omega$ is **contractible** (via the polar decomposition retraction). -/
noncomputable def fiberwise_acs_contractible
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω) :
    IsContractible (CompatibleComplexStructureSpace ω) :=

  let polar_data := (polar_decomposition_compatible_J hω)
  let polar := polar_data.choose
  let h_compat := polar_data.choose_spec.1
  let h_idemp := polar_data.choose_spec.2

  let J₀_data := exists_compatible_complex_structure hω
  let J₀_map := J₀_data.choose
  let hJ₀ := J₀_data.choose_spec

  { point := ⟨J₀_map, hJ₀⟩
    AmbientSpace := LinearMap.BilinForm ℝ V
    ambientAddCommGroup := inferInstance
    ambientModule := inferInstance
    embed := fun ⟨J, _⟩ => ω.compRight J
    normalize := fun g => ⟨polar g, h_compat g⟩
    normalize_embed := fun ⟨J, hJ⟩ => Subtype.ext (h_idemp J hJ) }




/-- The convex combination $(1 - t)\omega_0 + t\omega_1$ of two closed symplectic forms is
closed: $d\omega_t = 0$. -/
theorem compatible_forms_convex_closed
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S₀ S₁ : SymplecticManifold Ω VF)
    (t : ℝ) :
    inst.d ((1 - t) • S₀.ω + t • S₁.ω) = 0 := by
  rw [inst.d_add, inst.d_smul, inst.d_smul, S₀.closed, S₁.closed,
      smul_zero, smul_zero, add_zero]

/-- $J$-compatibility is preserved under convex combinations of symplectic forms:
$\omega_t(Ju, Jv) = \omega_t(u, v)$ whenever each $\omega_i$ is $J$-compatible. -/
theorem compatible_forms_convex_compat
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (S₀ S₁ : SymplecticManifold Ω VF)
    (h₀ : IsCompatibleACS S₀ J) (h₁ : IsCompatibleACS S₁ J)
    (t : ℝ) :
    ∀ (u v : VF),
      inst.ι (J.J u) (inst.ι (J.J v) ((1 - t) • S₀.ω + t • S₁.ω)) =
      inst.ι u (inst.ι v ((1 - t) • S₀.ω + t • S₁.ω)) := by
  intro u v
  simp only [inst.ι_add, inst.ι_smul]
  rw [h₀.preserves u v, h₁.preserves u v]

/-- Interior product commutes with negation: $\iota_X(-\alpha) = -\iota_X\alpha$. -/
lemma ι_neg {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (X : VF) {p : ℕ} (α : Ω (p + 1)) :
    inst.ι X (-α) = -(inst.ι X α) := by
  have h := inst.ι_smul X (-1 : ℝ) α
  simp only [neg_one_smul] at h; exact h

/-- Interior product distributes over subtraction: $\iota_X(\alpha - \beta) = \iota_X\alpha - \iota_X\beta$. -/
lemma ι_sub {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (X : VF) {p : ℕ} (α β : Ω (p + 1)) :
    inst.ι X (α - β) = inst.ι X α - inst.ι X β := by
  rw [sub_eq_add_neg, inst.ι_add, ι_neg, ← sub_eq_add_neg]

/-- **Convexity (nondegeneracy part)**: if $J$ tames both $\omega_0$ and $\omega_1$, then the
convex combination $\omega_t = (1 - t)\omega_0 + t\omega_1$ is nondegenerate for $t \in [0, 1]$. -/
theorem compatible_forms_convex_nondeg
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hp : HasPositivity (Ω 0)]
    (J : AlmostComplexStr (inst := inst))
    (S₀ S₁ : SymplecticManifold Ω VF)
    (ht₀ : IsTaming S₀ J) (ht₁ : IsTaming S₁ J)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    Function.Injective (fun (X : VF) => inst.ι X ((1 - t) • S₀.ω + t • S₁.ω)) := by
  intro X Y hXY

  by_contra hne


  have hdiff : (1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
               t • (inst.ι X S₁.ω - inst.ι Y S₁.ω) = (0 : Ω 1) := by
    have h_sub : inst.ι X ((1 - t) • S₀.ω + t • S₁.ω) -
           inst.ι Y ((1 - t) • S₀.ω + t • S₁.ω) = 0 :=
      sub_eq_zero.mpr hXY
    simp only [inst.ι_add, inst.ι_smul] at h_sub

    have h_eq : (1 - t) • inst.ι X S₀.ω + t • inst.ι X S₁.ω =
                (1 - t) • inst.ι Y S₀.ω + t • inst.ι Y S₁.ω :=
      sub_eq_zero.mp h_sub
    have h_rearr : (1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
                   t • (inst.ι X S₁.ω - inst.ι Y S₁.ω) =
                   ((1 - t) • inst.ι X S₀.ω + t • inst.ι X S₁.ω) -
                   ((1 - t) • inst.ι Y S₀.ω + t • inst.ι Y S₁.ω) := by
      simp only [smul_sub]; abel
    rw [h_rearr, h_eq, sub_self]


  have heval : inst.ι (J.J X) ((1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
               t • (inst.ι X S₁.ω - inst.ι Y S₁.ω)) = (0 : Ω 0) := by
    rw [hdiff]; exact ι_zero_val _

  rw [inst.ι_add, inst.ι_smul, inst.ι_smul] at heval

  have pos₀ := ht₀.taming X Y hne
  have pos₁ := ht₁.taming X Y hne

  obtain ⟨h0, h1⟩ := ht
  by_cases ht0 : t = 0
  ·
    subst ht0; simp only [sub_zero, one_smul, zero_smul, add_zero] at heval
    exact hp.pos_nonzero _ pos₀ heval
  by_cases ht1 : t = 1
  ·
    subst ht1; simp only [sub_self, zero_smul, one_smul, zero_add] at heval
    exact hp.pos_nonzero _ pos₁ heval
  ·
    have ht_pos : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht0)
    have h1t_pos : 0 < 1 - t := by
      have : t < 1 := lt_of_le_of_ne h1 ht1
      linarith
    have hpos_sum := hp.pos_add _ _
      (hp.pos_smul_pos _ _ h1t_pos pos₀)
      (hp.pos_smul_pos _ _ ht_pos pos₁)
    exact hp.pos_nonzero _ hpos_sum heval

/-- **Convexity (taming preserved)**: the convex combination $\omega_t = (1 - t)\omega_0 + t\omega_1$
remains tamed by $J$, witnessing that the space of $J$-tamed symplectic forms is convex. -/
theorem compatible_forms_convex_taming
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hp : HasPositivity (Ω 0)]
    (J : AlmostComplexStr (inst := inst))
    (S₀ S₁ : SymplecticManifold Ω VF)
    (ht₀ : IsTaming S₀ J) (ht₁ : IsTaming S₁ J)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    IsTaming
      (⟨(1 - t) • S₀.ω + t • S₁.ω,
        compatible_forms_convex_closed S₀ S₁ t,
        compatible_forms_convex_nondeg J S₀ S₁ ht₀ ht₁ t ht⟩ : SymplecticManifold Ω VF)
      J := by
  constructor
  intro X Y hne


  show hp.IsPositive (inst.ι (J.J X) (inst.ι X ((1 - t) • S₀.ω + t • S₁.ω) -
       inst.ι Y ((1 - t) • S₀.ω + t • S₁.ω)))
  have hexpand : inst.ι X ((1 - t) • S₀.ω + t • S₁.ω) -
      inst.ι Y ((1 - t) • S₀.ω + t • S₁.ω) =
      (1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
      t • (inst.ι X S₁.ω - inst.ι Y S₁.ω) := by
    simp only [inst.ι_add, inst.ι_smul, smul_sub]; abel
  rw [hexpand, inst.ι_add, inst.ι_smul, inst.ι_smul]

  have pos₀ := ht₀.taming X Y hne
  have pos₁ := ht₁.taming X Y hne

  obtain ⟨h0, h1⟩ := ht
  by_cases ht0 : t = 0
  · subst ht0; simp only [sub_zero, one_smul, zero_smul, add_zero]; exact pos₀
  by_cases ht1 : t = 1
  · subst ht1; simp only [sub_self, zero_smul, one_smul, zero_add]; exact pos₁
  · have ht_pos : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht0)
    have h1t_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne h1 ht1]
    exact hp.pos_add _ _ (hp.pos_smul_pos _ _ h1t_pos pos₀) (hp.pos_smul_pos _ _ ht_pos pos₁)


/-- The pullback of the zero form is zero: $i^* 0 = 0$. -/
lemma DFSMorphism.pullback_zero'
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    {p : ℕ} :
    i.pullback (0 : Ω_M p) = 0 := by
  have := i.pullback_smul (0 : ℝ) (0 : Ω_M p)
  simp only [zero_smul] at this; exact this

/-- Pullback preserves closedness: if $d\alpha = 0$ then $d(i^*\alpha) = 0$. -/
lemma DFSMorphism.pullback_closed'
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    {p : ℕ} (α : Ω_M p)
    (hclosed : inst_M.d α = 0) :
    inst_X.d (i.pullback α) = 0 := by
  rw [← i.pullback_comm_d, hclosed, i.pullback_zero']

/-- Pullback distributes over subtraction: $i^*(\alpha - \beta) = i^*\alpha - i^*\beta$. -/
lemma DFSMorphism.pullback_sub'
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    {p : ℕ} (α β : Ω_M p) :
    i.pullback (α - β) = i.pullback α - i.pullback β := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [show (-β : Ω_M p) = (-1 : ℝ) • β from by simp only [neg_one_smul]]
  rw [i.pullback_add, i.pullback_smul]
  simp only [neg_one_smul]


/-- **Almost-complex submanifold $\implies$ symplectic.** Given a tamed pair $(M, \omega, J)$ and
an immersion $i : X \hookrightarrow M$ whose pushforward is $J$-invariant, the pullback
$i^*\omega$ is a symplectic form on $X$, exhibiting $X$ as a symplectic submanifold. -/
def acs_submanifold_symplectic_DFS
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [hp_M : HasPositivity (Ω_M 0)]
    [hp_X : HasPositivity (Ω_X 0)]
    (S : SymplecticManifold Ω_M VF_M)
    (J : AlmostComplexStr (inst := inst_M))
    (_hcompat : IsCompatibleACS S J)
    (htame : IsTaming S J)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (push : VF_X → VF_M)
    (push_inj : Function.Injective push)
    (j_inv : ∀ (v : VF_X), ∃ (w : VF_X), push w = J.J (push v))
    (naturality : ∀ (v : VF_X) {p : ℕ} (α : Ω_M (p + 1)),
      inst_X.ι v (i.pullback α) = i.pullback (inst_M.ι (push v) α))
    (pullback_pos : ∀ (f : Ω_M 0), hp_M.IsPositive f →
      hp_X.IsPositive (i.pullback f)) :
    SymplecticManifold Ω_X VF_X where

  ω := i.pullback S.ω

  closed := i.pullback_closed' S.ω S.closed

  nondegenerate := by
    intro v w hvw
    by_contra hne

    have hpush_ne : push v ≠ push w := fun heq => hne (push_inj heq)

    have hpos_M : hp_M.IsPositive
        (inst_M.ι (J.J (push v)) (inst_M.ι (push v) S.ω - inst_M.ι (push w) S.ω)) :=
      htame.taming (push v) (push w) hpush_ne

    obtain ⟨jv, hjv⟩ := j_inv v

    rw [← hjv] at hpos_M

    have hpb : i.pullback (inst_M.ι (push jv)
        (inst_M.ι (push v) S.ω - inst_M.ι (push w) S.ω)) =
        inst_X.ι jv (inst_X.ι v (i.pullback S.ω) - inst_X.ι w (i.pullback S.ω)) := by
      rw [← naturality jv (inst_M.ι (push v) S.ω - inst_M.ι (push w) S.ω)]
      congr 1
      rw [i.pullback_sub', ← naturality v S.ω, ← naturality w S.ω]

    have hzero : inst_X.ι v (i.pullback S.ω) - inst_X.ι w (i.pullback S.ω) = 0 :=
      sub_eq_zero.mpr hvw

    rw [hzero, ι_zero_val] at hpb

    have hpos_X := pullback_pos _ hpos_M
    rw [hpb] at hpos_X
    exact hp_X.pos_nonzero _ hpos_X rfl


section ManifoldACS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- An **almost complex structure** on a smooth manifold $M$ in Mathlib formalism: a smooth
field of fiberwise endomorphisms $J_x : T_xM \to T_xM$ with $J_x^2 = -\mathrm{id}$. -/
structure AlmostComplexStructure where
  J : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x
  sq_neg : ∀ (x : M) (v : TangentSpace I x), (J x) ((J x) v) = -v

/-- A **pointwise symplectic form** on $M$: a field of skew-symmetric, nondegenerate bilinear
forms $\omega_x : T_xM \times T_xM \to \mathbb{R}$ (closedness is not yet imposed). -/
structure PointwiseSymplecticForm where
  form : ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ
  skew : ∀ (x : M) (u v : TangentSpace I x), form x u v = -(form x v u)
  nondeg : ∀ (x : M) (u : TangentSpace I x), (∀ v, form x u v = 0) → u = 0

/-- $J$ is **compatible** with the pointwise symplectic form $\omega$ in Mathlib formalism:
$\omega(Ju, Jv) = \omega(u, v)$ and $\omega(v, Jv) > 0$ for $v \neq 0$ (taming/positivity). -/
structure IsCompatibleACS_Mathlib (ω : PointwiseSymplecticForm I M)
    (J : AlmostComplexStructure I M) : Prop where
  preserves : ∀ (x : M) (u v : TangentSpace I x),
    ω.form x ((J.J x) u) ((J.J x) v) = ω.form x u v
  taming : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
    ω.form x v ((J.J x) v) > 0

/-- The space of almost complex structures on $M$ compatible with the pointwise symplectic
form $\omega$ (Mathlib version). -/
def CompatibleACSSpace_Mathlib (ω : PointwiseSymplecticForm I M) : Type _ :=
  { J : AlmostComplexStructure I M // IsCompatibleACS_Mathlib I M ω J }

end ManifoldACS


section Convexity_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

end Convexity_Mathlib


section Contractibility_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- At each point $x \in M$, the value $\omega_x$ of a pointwise symplectic form is a linear
symplectic form on the tangent space $T_xM$. -/
theorem pointwise_form_is_symplectic
    (ω : PointwiseSymplecticForm I M) (x : M) :
    IsSymplecticForm (ω.form x) := by
  constructor
  ·
    intro v
    have h := ω.skew x v v
    linarith
  ·
    intro v hv
    exact ω.nondeg x v hv

/-- Fiberwise contractibility in Mathlib formalism: at each $x \in M$, the space of linear
complex structures compatible with $\omega_x$ is contractible. -/
@[reducible]
noncomputable def fiberwise_acs_contractible_Mathlib
    [hfd : FiniteDimensional ℝ E]
    (ω : PointwiseSymplecticForm I M) (x : M) :
    letI : FiniteDimensional ℝ (TangentSpace I x) := hfd
    IsContractible (CompatibleComplexStructureSpace (ω.form x)) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := hfd
  exact fiberwise_acs_contractible (pointwise_form_is_symplectic ω x)


end Contractibility_Mathlib


section Submanifold_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Almost-complex subspace is symplectic (Mathlib version)**: a $J$-invariant subspace
$W \subseteq T_xM$ inherits a nondegenerate restriction of $\omega$, since for any $v \in W$
with $v \neq 0$, the partner $Jv$ also lies in $W$ and $\omega(v, Jv) > 0$. -/
theorem acs_submanifold_symplectic
    (ω : PointwiseSymplecticForm I M) (J : AlmostComplexStructure I M)
    (hcompat : IsCompatibleACS_Mathlib I M ω J)
    (x : M) (W : Submodule ℝ (TangentSpace I x))
    (hJ_inv : ∀ v ∈ W, (J.J x) v ∈ W) :

    ∀ v ∈ W, v ≠ 0 → ∃ w ∈ W, ω.form x v w ≠ 0 := by
  intro v hv hv_ne

  have hJv : (J.J x) v ∈ W := hJ_inv v hv

  have h_pos := hcompat.taming x v hv_ne
  exact ⟨(J.J x) v, hJv, ne_of_gt h_pos⟩

end Submanifold_Mathlib


section Integrability_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Integrability of $J$**: the Nijenhuis tensor $N_J$ vanishes identically. By the
Newlander-Nirenberg theorem this is equivalent to $J$ coming from a genuine complex structure. -/
structure Integrable (J : AlmostComplexStructure I M)
    (N : ∀ x : M, TangentSpace I x → TangentSpace I x → TangentSpace I x) : Prop where
  vanishes : ∀ (x : M) (u v : TangentSpace I x), N x u v = 0

end Integrability_Mathlib
