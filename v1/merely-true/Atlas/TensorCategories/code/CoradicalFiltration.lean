/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.CoalgebraBialgebra
import Atlas.TensorCategories.code.HopfAlgebra
import Atlas.TensorCategories.code.FiniteTensorCategory
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Simple
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.RingTheory.Coalgebra.Hom

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra

universe u v

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]


namespace Submodule

/-- A submodule `S` of a coalgebra `C` is a subcoalgebra if it is closed under the
comultiplication: `comul(S) ⊆ S ⊗ S`. -/
def IsSubcoalgebra (S : Submodule R C) : Prop :=
  ∀ a ∈ S, Coalgebra.comul (R := R) a ∈ Submodule.map₂ (TensorProduct.mk R C C) S S

/-- A submodule `S` is a simple subcoalgebra if it is nonzero, is a subcoalgebra, and has
no proper nonzero sub-subcoalgebra. -/
def IsSimpleCoalgebra (S : Submodule R C) : Prop :=
  S ≠ ⊥ ∧ S.IsSubcoalgebra ∧
    ∀ T : Submodule R C, T.IsSubcoalgebra → T ≤ S → T = ⊥ ∨ T = S

/-- An arbitrary supremum of subcoalgebras is again a subcoalgebra. -/
theorem iSup_isSubcoalgebra {ι : Sort*} {S : ι → Submodule R C}
    (hS : ∀ i, (S i).IsSubcoalgebra) :
    (⨆ i, S i).IsSubcoalgebra := by
  intro a ha
  refine iSup_induction (p := S) (motive := fun x =>
      Coalgebra.comul (R := R) x ∈
        Submodule.map₂ (TensorProduct.mk R C C) (⨆ i, S i) (⨆ i, S i)) ha ?_ ?_ ?_
  · intro i x hx
    exact map₂_le_map₂ (le_iSup S i) (le_iSup S i) (hS i x hx)
  · simp [map_zero]
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy

end Submodule


/-- The coradical of a coalgebra `C`: the sum of all simple subcoalgebras of `C`. -/
noncomputable def coradical : Submodule R C :=
  ⨆ (S : Submodule R C) (_ : S.IsSimpleCoalgebra), S

/-- The coradical is itself a subcoalgebra. -/
theorem coradical_isSubcoalgebra : (coradical (R := R) (C := C)).IsSubcoalgebra := by
  unfold coradical; rw [iSup_subtype']
  exact Submodule.iSup_isSubcoalgebra (fun ⟨_, _, hSub, _⟩ => hSub)

/-- Every simple subcoalgebra is contained in the coradical. -/
theorem le_coradical_of_isSimpleCoalgebra {S : Submodule R C}
    (hS : S.IsSimpleCoalgebra) : S ≤ coradical (R := R) (C := C) :=
  le_iSup₂ (f := fun (S : Submodule R C) (_ : S.IsSimpleCoalgebra) => S) S hS


/-- The coradical filtration `C_0 ⊆ C_1 ⊆ ⋯` of a coalgebra `C`: `C_0` is the coradical
and `C_{n+1}` is the preimage under `comul` of `C_n ⊗ C + C ⊗ C_0`. -/
noncomputable def coradicalFiltration : ℕ → Submodule R C
  | 0 => coradical
  | n + 1 =>
    (Submodule.map₂ (TensorProduct.mk R C C) (coradicalFiltration n) ⊤ ⊔
     Submodule.map₂ (TensorProduct.mk R C C) ⊤ coradical).comap
      (Coalgebra.comul (R := R))

/-- The zeroth term of the coradical filtration is the coradical. -/
@[simp]
theorem coradicalFiltration_zero :
    coradicalFiltration (R := R) (C := C) 0 = coradical := rfl

/-- Unfolding lemma for the successor case of the coradical filtration. -/
theorem coradicalFiltration_succ (n : ℕ) :
    coradicalFiltration (R := R) (C := C) (n + 1) =
    (Submodule.map₂ (TensorProduct.mk R C C) (coradicalFiltration n) ⊤ ⊔
     Submodule.map₂ (TensorProduct.mk R C C) ⊤ coradical).comap
      (Coalgebra.comul (R := R)) := rfl

/-- Membership characterization in `C_{n+1}` of the coradical filtration. -/
theorem mem_coradicalFiltration_succ (n : ℕ) (x : C) :
    x ∈ coradicalFiltration (R := R) (C := C) (n + 1) ↔
    Coalgebra.comul (R := R) x ∈
      Submodule.map₂ (TensorProduct.mk R C C) (coradicalFiltration n) ⊤ ⊔
      Submodule.map₂ (TensorProduct.mk R C C) ⊤ coradical := by
  simp [coradicalFiltration_succ, Submodule.mem_comap]

/-- The coradical filtration is increasing: `C_n ⊆ C_{n+1}` for every `n`. -/
theorem coradicalFiltration_le_succ (n : ℕ) :
    coradicalFiltration (R := R) (C := C) n ≤ coradicalFiltration (n + 1) := by
  cases n with
  | zero =>

    intro x hx
    simp only [coradicalFiltration]
    rw [Submodule.mem_comap]
    exact Submodule.mem_sup_left
      (Submodule.map₂_le_map₂_right le_top (coradical_isSubcoalgebra x hx))
  | succ k =>

    apply Submodule.comap_mono
    exact sup_le_sup_right
      (Submodule.map₂_le_map₂_left (coradicalFiltration_le_succ k)) _

/-- The coradical filtration is monotone in `n`. -/
theorem coradicalFiltration_mono :
    Monotone (coradicalFiltration (R := R) (C := C)) :=
  monotone_nat_of_le_succ coradicalFiltration_le_succ

/-- A grouplike element of a coalgebra: an element `g` satisfying `Δ(g) = g ⊗ g` and
`ε(g) = 1`. -/
def IsGrouplike (g : C) : Prop :=
  Coalgebra.comul (R := R) g = g ⊗ₜ g ∧ Coalgebra.counit (R := R) g = 1

/-- A grouplike element is nonzero (over a nontrivial base ring). -/
theorem IsGrouplike.ne_zero [Nontrivial R] {g : C} (hg : IsGrouplike (R := R) g) : g ≠ 0 := by
  intro h
  have := hg.2
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- The set of grouplike elements of `C`. -/
def grouplikes : Set C := {g : C | IsGrouplike (R := R) g}

/-- An `(g, h)`-skew primitive element: `x ∈ C` such that `Δ(x) = x ⊗ g + h ⊗ x`. -/
def IsSkewPrimitive (g h x : C) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x

/-- The submodule of `(g, h)`-skew primitive elements of `C`. -/
def skewPrimitiveSpace (g h : C) : Submodule R C where
  carrier := {x : C | IsSkewPrimitive (R := R) g h x}
  add_mem' {x y} (hx : IsSkewPrimitive g h x) (hy : IsSkewPrimitive g h y) := by
    show IsSkewPrimitive (R := R) g h (x + y)
    unfold IsSkewPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show IsSkewPrimitive (R := R) g h 0
    simp [IsSkewPrimitive, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x (hx : IsSkewPrimitive g h x) := by
    show IsSkewPrimitive (R := R) g h (r • x)
    unfold IsSkewPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


/-- A coalgebra is cosemisimple if its coradical is the entire coalgebra. -/
def IsCosemisimple : Prop := coradical (R := R) (C := C) = ⊤

/-- Definition 1.29.3 (EGNO): a coalgebra `C` is cosemisimple iff `C_0 = C`. -/
abbrev def_1_29_3 := @IsCosemisimple R C _ _ _ _

/-- A coalgebra `C` is pointed if every simple subcoalgebra of `C` is one-dimensional, i.e.
spanned by a grouplike element. -/
def IsPointedCoalgebra : Prop :=
  ∀ S : Submodule R C, S.IsSimpleCoalgebra →
    ∃ g : C, S = Submodule.span R {g}


/-- The one-dimensional subspace spanned by a grouplike element is a subcoalgebra. -/
theorem span_grouplike_isSubcoalgebra (g : C)
    (hg : Coalgebra.comul (R := R) g = g ⊗ₜ g) :
    (Submodule.span R ({g} : Set C)).IsSubcoalgebra := by
  intro a ha
  rw [Submodule.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  simp only [LinearMap.map_smul, hg, TensorProduct.smul_tmul']
  exact Submodule.apply_mem_map₂ (TensorProduct.mk R C C)
    (Submodule.mem_span_singleton.mpr ⟨r, rfl⟩)
    (Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩)

/-- A grouplike element whose span is a simple subcoalgebra lies in the coradical. -/
theorem grouplike_mem_coradical (g : C) (_hg : IsGrouplike (R := R) g)
    (hSimple : (Submodule.span R ({g} : Set C)).IsSimpleCoalgebra) :
    g ∈ coradical (R := R) (C := C) :=
  le_coradical_of_isSimpleCoalgebra hSimple (Submodule.subset_span (Set.mem_singleton _))

/-- A `(g, h)`-skew primitive element with `g, h` in the coradical lies in `C_1`. -/
theorem skewPrimitive_mem_coradicalFiltration_one
    (g h x : C) (hg : g ∈ coradical (R := R) (C := C))
    (hh : h ∈ coradical (R := R) (C := C))
    (hx : IsSkewPrimitive (R := R) g h x) :
    x ∈ coradicalFiltration (R := R) (C := C) 1 := by
  simp only [coradicalFiltration]
  rw [Submodule.mem_comap]
  rw [show Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x from hx]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right
      (Submodule.apply_mem_map₂ (TensorProduct.mk R C C) Submodule.mem_top hg))
    (Submodule.mem_sup_left
      (Submodule.apply_mem_map₂ (TensorProduct.mk R C C) hh Submodule.mem_top))


/-- The submodule `∑_{i+j=n} C_i ⊗ C_j ⊆ C ⊗ C` used to formulate the comultiplication
compatibility of the coradical filtration. -/
noncomputable def filtrationTensorSum (n : ℕ) : Submodule R (C ⊗[R] C) :=
  ⨆ (i : Fin (n + 1)),
    Submodule.map₂ (TensorProduct.mk R C C)
      (coradicalFiltration i.val) (coradicalFiltration (n - i.val))

/-- Base case: `comul` sends `C_0` into `filtrationTensorSum 0 = C_0 ⊗ C_0`. -/
theorem comul_coradicalFiltration_zero (x : C)
    (hx : x ∈ coradicalFiltration (R := R) (C := C) 0) :
    Coalgebra.comul (R := R) x ∈ filtrationTensorSum (R := R) (C := C) 0 := by
  apply Submodule.mem_iSup_of_mem (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  simp only [coradicalFiltration]
  exact coradical_isSubcoalgebra x hx





/-- Over a field, if a simple subcoalgebra is spanned by a vector `g`, then it is in fact
spanned by a grouplike element `g'`. -/
theorem pointed_simple_generator_grouplike (R : Type u) (C : Type v)
    [Field R] [AddCommGroup C] [Module R C] [Coalgebra R C]
    (S : Submodule R C) (hS : S.IsSimpleCoalgebra)
    (g : C) (hg_span : S = Submodule.span R {g}) :
    ∃ g' : C, g' ∈ grouplikes (R := R) (C := C) ∧ S = Submodule.span R {g'} := by

  have hg_mem : g ∈ S := hg_span ▸ Submodule.subset_span (Set.mem_singleton _)

  have hcomul_mem := hS.2.1 g hg_mem
  have hSS : Submodule.map₂ (TensorProduct.mk R C C) S S =
      Submodule.span R {g ⊗ₜ[R] g} := by
    rw [hg_span, Submodule.map₂_span_span]; simp
  rw [hSS, Submodule.mem_span_singleton] at hcomul_mem
  obtain ⟨c, hc⟩ := hcomul_mem

  have hcomul : Coalgebra.comul (R := R) g = c • (g ⊗ₜ[R] g) := hc.symm

  have hg_ne : g ≠ 0 := by
    intro h; apply hS.1; rw [hg_span, h]; exact Submodule.span_singleton_eq_bot.mpr rfl
  set eg := Coalgebra.counit (R := R) g with heg_def

  have hc_eg : c * eg = 1 := by
    have hax := Coalgebra.rTensor_counit_comp_comul (R := R) (A := C)
    have heval : LinearMap.rTensor C (Coalgebra.counit (R := R))
        (Coalgebra.comul (R := R) g) =
      (TensorProduct.mk R R C) 1 g := congr_fun (congr_arg DFunLike.coe hax) g
    rw [hcomul, LinearMap.map_smul, LinearMap.rTensor_tmul] at heval
    have := congr_arg (TensorProduct.lid R C) heval
    simp only [TensorProduct.lid_tmul, map_smul, smul_smul, TensorProduct.mk_apply] at this
    have h1 : (c * eg - 1) • g = 0 := by rw [sub_smul, this, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hg_ne)

  have heg_ne : eg ≠ 0 := right_ne_zero_of_mul (by rw [hc_eg]; exact one_ne_zero)

  have hc_eq : c = eg⁻¹ := by
    rw [show c = c * 1 from (mul_one c).symm, ← mul_inv_cancel₀ heg_ne,
        ← mul_assoc, hc_eg, one_mul]

  refine ⟨eg⁻¹ • g, ⟨?_, ?_⟩, ?_⟩
  ·
    rw [LinearMap.map_smul, hcomul, smul_smul, hc_eq]
    conv_rhs => rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
    rw [smul_smul, mul_comm]
  ·
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ heg_ne]
  ·
    rw [hg_span]
    exact (Submodule.span_singleton_smul_eq (IsUnit.mk0 eg⁻¹ (inv_ne_zero heg_ne)) g).symm


/-- In a pointed coalgebra over a field, the span of any grouplike element is a simple
subcoalgebra. -/
theorem span_grouplike_simple_in_pointed (R : Type u) (C : Type v)
    [Field R] [AddCommGroup C] [Module R C] [Coalgebra R C] :
    IsPointedCoalgebra (R := R) (C := C) →
    ∀ (g : C), g ∈ grouplikes (R := R) (C := C) →
    (Submodule.span R ({g} : Set C)).IsSimpleCoalgebra := by
  intro _ g hg
  refine ⟨?_, span_grouplike_isSubcoalgebra g hg.1, ?_⟩
  ·
    intro h
    have hg_ne : g ≠ 0 := by
      intro hg0; have := hg.2; rw [hg0, map_zero] at this; exact zero_ne_one this
    exact hg_ne (Submodule.span_singleton_eq_bot.mp h)
  ·
    intro T _hT_sub hT_le
    by_cases hT_ne : T = ⊥
    · exact Or.inl hT_ne
    · right

      obtain ⟨t_val, t_mem, t_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT_ne

      have ht_span : t_val ∈ Submodule.span R ({g} : Set C) := hT_le t_mem
      rw [Submodule.mem_span_singleton] at ht_span
      obtain ⟨r, hr⟩ := ht_span

      have hr_ne : r ≠ 0 := by
        intro hr0; rw [hr0, zero_smul] at hr; exact t_ne hr.symm

      have hg_in_T : g ∈ T := by
        have : g = r⁻¹ • t_val := by rw [← hr, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]
        rw [this]; exact T.smul_mem _ t_mem
      exact le_antisymm hT_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hg_in_T))





/-- Independence from projections: a family of submodules is `iSupIndep` whenever there exist
linear maps `π i` that act as identity on `t i` and as zero on `t j` for `j ≠ i`. -/
lemma iSupIndep_of_projections {R' : Type*} {M : Type*}
    [CommRing R'] [AddCommGroup M] [Module R' M]
    {ι : Type*} {t : ι → Submodule R' M}
    (π : ι → (M →ₗ[R'] M))
    (hProject : ∀ i, ∀ x ∈ t i, π i x = x)
    (hOrth : ∀ i j, i ≠ j → ∀ x ∈ t j, π i x = 0) :
    iSupIndep t := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff]
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · rintro ⟨hxi, hxS⟩
    have h1 : (π i) x = x := hProject i x hxi
    have h2 : (π i) x = 0 := by
      have hker : (⨆ j, ⨆ (_ : j ≠ i), t j) ≤ LinearMap.ker (π i) := by
        apply iSup_le; intro j
        apply iSup_le; intro hji z hz
        simp only [LinearMap.mem_ker]
        exact hOrth i j (Ne.symm hji) z hz
      exact LinearMap.mem_ker.mp (hker hxS)
    rw [← h1, h2]
  · rintro rfl
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩

/-- The right slice operator on `C` associated to a functional `f : C → R`: applies
`comul` then contracts the right factor through `f`. -/
noncomputable def coalgebraRightSlice (f : C →ₗ[R] R) : C →ₗ[R] C :=
  (TensorProduct.rid R C).toLinearMap.comp
    ((LinearMap.lTensor C f).comp (Coalgebra.comul (R := R)))

/-- The left slice operator on `C` associated to a functional `f : C → R`: applies
`comul` then contracts the left factor through `f`. -/
noncomputable def coalgebraLeftSlice (f : C →ₗ[R] R) : C →ₗ[R] C :=
  (TensorProduct.lid R C).toLinearMap.comp
    ((LinearMap.rTensor C f).comp (Coalgebra.comul (R := R)))

/-- The right slice of a `(g, h)`-skew primitive element equals `f(g) • x + f(x) • h`. -/
lemma coalgebraRightSlice_skewPrim {f : C →ₗ[R] R} {x g h : C}
    (hskew : Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x) :
    coalgebraRightSlice (R := R) f x = f g • x + f x • h := by
  simp only [coalgebraRightSlice, LinearMap.comp_apply, hskew, map_add,
    LinearMap.lTensor_tmul]
  simp [TensorProduct.rid_tmul]

/-- The left slice of a `(g, h)`-skew primitive element equals `f(x) • g + f(h) • x`. -/
lemma coalgebraLeftSlice_skewPrim {f : C →ₗ[R] R} {x g h : C}
    (hskew : Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x) :
    coalgebraLeftSlice (R := R) f x = f x • g + f h • x := by
  simp only [coalgebraLeftSlice, LinearMap.comp_apply, hskew, map_add,
    LinearMap.rTensor_tmul]
  simp [TensorProduct.lid_tmul]

/-- The left slice of a grouplike element `g` equals `f(g) • g`. -/
lemma coalgebraLeftSlice_grouplike {f : C →ₗ[R] R} {g : C}
    (hgl : Coalgebra.comul (R := R) g = g ⊗ₜ g) :
    coalgebraLeftSlice (R := R) f g = f g • g := by
  simp only [coalgebraLeftSlice, LinearMap.comp_apply, hgl,
    LinearMap.rTensor_tmul]
  simp [TensorProduct.lid_tmul]







/-- In a pointed coalgebra over a field, every grouplike element lies in the coradical. -/
theorem grouplike_mem_coradical_pointed (R : Type u) (C : Type v)
    [Field R] [AddCommGroup C] [Module R C] [Coalgebra R C]
    (hPointed : IsPointedCoalgebra (R := R) (C := C))
    (g : C) (hg : g ∈ grouplikes (R := R) (C := C)) :
    g ∈ coradical (R := R) (C := C) :=
  le_coradical_of_isSimpleCoalgebra
    (span_grouplike_simple_in_pointed R C hPointed g hg)
    (Submodule.subset_span (Set.mem_singleton _))

/-- Taft-Wilson, part 1: in a pointed coalgebra over a field, the coradical equals the
span of the grouplike elements. -/
theorem taftWilson_coradical_eq_span_grouplikes (R : Type u) (C : Type v)
    [Field R] [AddCommGroup C] [Module R C] [Coalgebra R C]
    (hPointed : IsPointedCoalgebra (R := R) (C := C)) :
    coradical (R := R) (C := C) =
      ⨆ (g : C) (_ : g ∈ grouplikes (R := R) (C := C)), Submodule.span R {g} := by
  apply le_antisymm
  ·
    apply iSup₂_le
    intro S hS
    obtain ⟨g, hg_span⟩ := hPointed S hS
    obtain ⟨g', hg'_gl, hg'_span⟩ := pointed_simple_generator_grouplike R C S hS g hg_span
    rw [hg'_span]
    exact le_iSup₂ (f := fun (g : C) (_ : g ∈ grouplikes (R := R) (C := C)) =>
      Submodule.span R {g}) g' hg'_gl

  ·
    apply iSup₂_le
    intro g hg
    exact le_coradical_of_isSimpleCoalgebra
      (span_grouplike_simple_in_pointed R C hPointed g hg)




/-- Counit summation identity: for any Sweedler-like representation of `a ∈ A`, the sum of
`ε(a₍₂₎) • a₍₁₎` recovers `a`. -/
lemma Coalgebra.sum_smul_counit_right {R : Type*} {A : Type*}
    [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]
    {a : A} (repr : Coalgebra.Repr R a) :
    ∑ x ∈ repr.index, Coalgebra.counit (R := R) (repr.right x) • repr.left x = a := by
  have h := Coalgebra.sum_tmul_counit_eq repr
  have h2 : TensorProduct.lift ((LinearMap.lsmul R A).flip)
      (∑ i ∈ repr.index, repr.left i ⊗ₜ[R] Coalgebra.counit (R := R) (repr.right i))
    = TensorProduct.lift ((LinearMap.lsmul R A).flip) (a ⊗ₜ[R] (1 : R)) := by rw [h]
  simp only [map_sum, TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.lsmul_apply,
    one_smul] at h2
  exact h2




/-- If `C_0 = C_1` then the coradical filtration is stationary: `C_n = C_0` for every `n`. -/
theorem coradicalFiltration_eq_of_C0_eq_C1
    (h : coradicalFiltration (R := R) (C := C) 0 = coradicalFiltration 1)
    (n : ℕ) : coradicalFiltration (R := R) (C := C) n = coradicalFiltration 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show coradicalFiltration (k + 1) = coradicalFiltration 0
    conv_lhs => simp only [coradicalFiltration]
    rw [ih]
    exact h.symm



/-- If `y ∈ I^n` and `y - z ∈ I^{n+1}`, then `z ∈ I^n`. -/
lemma ideal_pow_mem_of_sub_mem_higher {B : Type*} [CommRing B] {I : Ideal B}
    {y z : B} {n : ℕ} (hy : y ∈ I ^ n) (hz : y - z ∈ I ^ (n + 1)) :
    z ∈ I ^ n := by
  rw [show z = y - (y - z) from by ring]
  exact (I ^ n).sub_mem hy (Ideal.pow_le_pow_right (by omega) hz)

/-- Successive approximation lemma: if `f : A → B` is surjective modulo `I^2`, then any
element of `I^{n+1}` can be approximated by an image from `A` up to `I^{n+2}`. -/
lemma lift_from_ideal_pow {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal B)
    (hsurj : ∀ b : B, ∃ a : A, b - f a ∈ I ^ 2) :
    ∀ n : ℕ, ∀ c ∈ I ^ (n + 1), ∃ a : A, c - f a ∈ I ^ (n + 2) := by
  intro n
  induction n with
  | zero => intro c _; exact hsurj c
  | succ k ih =>
    intro c hc
    rw [show k + 1 + 1 = k + 2 from by omega] at hc
    rw [pow_succ'] at hc

    refine Submodule.mul_induction_on hc ?_ ?_
    ·
      intro x hx y hy
      obtain ⟨α, hα⟩ := hsurj x
      obtain ⟨β, hβ⟩ := ih y hy
      refine ⟨α * β, ?_⟩

      rw [map_mul, show x * y - f α * f β = x * (y - f β) + (x - f α) * f β from by ring,
          show k + 1 + 2 = 1 + (k + 2) from by omega]
      exact (I ^ (1 + (k + 2))).add_mem

        (by rw [pow_add, pow_one]; exact Ideal.mul_mem_mul hx hβ)

        (by rw [show 1 + (k + 2) = 2 + (k + 1) from by omega, pow_add]
            exact Ideal.mul_mem_mul hα (ideal_pow_mem_of_sub_mem_higher hy hβ))
    ·
      intro x y ⟨ax, hax⟩ ⟨ay, hay⟩
      exact ⟨ax + ay, by
        rw [map_add, show x + y - (f ax + f ay) = (x - f ax) + (y - f ay) from by ring]
        exact (I ^ (k + 1 + 2)).add_mem hax hay⟩

/-- A ring homomorphism `f : A → B` is surjective whenever the target has a nilpotent ideal
`I` and `f` is surjective modulo `I^2`. -/
theorem algebra_hom_surjective_of_surjective_mod_sq
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal B)
    (hnil : ∃ N : ℕ, I ^ N = ⊥)
    (hsurj : ∀ b : B, ∃ a : A, b - f a ∈ I ^ 2) :
    Function.Surjective f := by
  obtain ⟨N, hN⟩ := hnil
  intro b

  suffices h : ∀ k : ℕ, ∃ a : A, b - f a ∈ I ^ (k + 2) by
    obtain ⟨a, ha⟩ := h N
    refine ⟨a, ?_⟩
    have : I ^ (N + 2) = ⊥ := le_bot_iff.mp
      ((Ideal.pow_le_pow_right (by omega : N ≤ N + 2)).trans (le_of_eq hN))
    rw [this, Ideal.mem_bot] at ha
    exact (sub_eq_zero.mp ha).symm
  intro k
  induction k with
  | zero => exact hsurj b
  | succ m ihm =>
    obtain ⟨a₀, ha₀⟩ := ihm

    obtain ⟨a₁, ha₁⟩ := lift_from_ideal_pow f I hsurj (m + 1) (b - f a₀)
      (by rwa [show m + 1 + 1 = m + 2 from by omega])
    refine ⟨a₀ + a₁, ?_⟩
    rw [map_add, show b - (f a₀ + f a₁) = (b - f a₀) - f a₁ from by ring,
        show m + 1 + 2 = m + 1 + 2 from rfl]
    exact ha₁





/-- `Ext^1(X, Y) = 0` for all pairs of simple objects `X, Y` of `𝒞`. -/
def Ext1VanishesForSimples (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] [CategoryTheory.HasExt 𝒞]
    [CategoryTheory.Limits.HasZeroMorphisms 𝒞] : Prop :=
  ∀ (X Y : 𝒞) [CategoryTheory.Simple X] [CategoryTheory.Simple Y],
    Subsingleton (CategoryTheory.Abelian.Ext X Y 1)

/-- An abelian category is semisimple if `Ext^1` vanishes between all pairs of objects. -/
def IsSemisimpleCat (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] [CategoryTheory.HasExt 𝒞] : Prop :=
  ∀ (X Y : 𝒞), Subsingleton (CategoryTheory.Abelian.Ext X Y 1)

/-- A locally finite-length category: each non-simple non-zero object admits a short exact
sequence with simple quotient and a strictly shorter subobject. -/
class IsLocallyFiniteLength (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] where
  length : 𝒞 → ℕ
  exists_ses_simple_quotient : ∀ (Y : 𝒞),
    ¬ CategoryTheory.Limits.IsZero Y → ¬ CategoryTheory.Simple Y →
    ∃ (S : CategoryTheory.ShortComplex 𝒞), S.ShortExact ∧ S.X₂ = Y ∧
      CategoryTheory.Simple S.X₃ ∧ length S.X₁ < length Y

section Prop_1_29_4

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

variable {𝒞 : Type*} [CategoryTheory.Category 𝒞] [CategoryTheory.Abelian 𝒞]
    [CategoryTheory.HasExt 𝒞]

/-- Covariant five-lemma reasoning: `Ext^1(X, S.X₂)` is subsingleton whenever
`Ext^1(X, S.X₁)` and `Ext^1(X, S.X₃)` are, for `S` a short exact sequence. -/
lemma ext1_subsingleton_of_ses_cov {X : 𝒞} {S : ShortComplex 𝒞} (hS : S.ShortExact)
    (h1 : Subsingleton (Ext X S.X₁ 1)) (h3 : Subsingleton (Ext X S.X₃ 1)) :
    Subsingleton (Ext X S.X₂ 1) := by
  constructor; intro a b
  have ha : a.comp (Ext.mk₀ S.g) (add_zero 1) = 0 := h3.elim _ _
  have hb : b.comp (Ext.mk₀ S.g) (add_zero 1) = 0 := h3.elim _ _
  obtain ⟨a₁, ha₁⟩ := Ext.covariant_sequence_exact₂ X hS a ha
  obtain ⟨b₁, hb₁⟩ := Ext.covariant_sequence_exact₂ X hS b hb
  rw [← ha₁, ← hb₁, h1.elim a₁ b₁]

/-- Contravariant five-lemma reasoning: `Ext^1(S.X₂, Y)` is subsingleton whenever
`Ext^1(S.X₁, Y)` and `Ext^1(S.X₃, Y)` are, for `S` a short exact sequence. -/
lemma ext1_subsingleton_of_ses_contra {Y : 𝒞} {S : ShortComplex 𝒞} (hS : S.ShortExact)
    (h1 : Subsingleton (Ext S.X₁ Y 1)) (h3 : Subsingleton (Ext S.X₃ Y 1)) :
    Subsingleton (Ext S.X₂ Y 1) := by
  constructor; intro a b
  have ha : (Ext.mk₀ S.f).comp a (zero_add 1) = 0 := h1.elim _ _
  have hb : (Ext.mk₀ S.f).comp b (zero_add 1) = 0 := h1.elim _ _
  obtain ⟨a₃, ha₃⟩ := Ext.contravariant_sequence_exact₂ hS Y a ha
  obtain ⟨b₃, hb₃⟩ := Ext.contravariant_sequence_exact₂ hS Y b hb
  rw [← ha₃, ← hb₃, h3.elim a₃ b₃]

/-- If `Ext^1` vanishes on simples and `𝒞` is locally finite-length, then `Ext^1(X, Y)` is
subsingleton whenever `X` is simple, by induction on the length of `Y`. -/
lemma ext1_subsingleton_of_simple_source
    [hLF : IsLocallyFiniteLength 𝒞]
    (hvan : ∀ (X Y : 𝒞) [Simple X] [Simple Y], Subsingleton (Ext X Y 1))
    (X : 𝒞) [hX : Simple X] (Y : 𝒞) : Subsingleton (Ext X Y 1) := by
  suffices ∀ (n : ℕ) (Y : 𝒞), hLF.length Y = n → Subsingleton (Ext X Y 1) from
    this (hLF.length Y) Y rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Y hY
    by_cases hYz : IsZero Y
    · haveI : Injective Y := hYz.injective
      exact subsingleton_of_forall_eq 0 (fun e => Ext.eq_zero_of_injective e)
    by_cases hYs : Simple Y
    · exact hvan X Y
    · obtain ⟨S, hSE, hS2, hS3, hlen⟩ :=
        IsLocallyFiniteLength.exists_ses_simple_quotient Y hYz hYs
      subst hS2
      exact ext1_subsingleton_of_ses_cov hSE
        (ih (hLF.length S.X₁) (by omega) S.X₁ rfl)
        (by haveI := hS3; exact hvan X S.X₃)

/-- A locally finite-length abelian category is semisimple iff `Ext^1` vanishes between all
pairs of simple objects (used in the proof of Proposition 1.29.4 in EGNO). -/
theorem ext1_vanishes_for_simples_implies_semisimple
    (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] [CategoryTheory.HasExt 𝒞]
    [hLF : IsLocallyFiniteLength 𝒞] :
    Ext1VanishesForSimples 𝒞 → IsSemisimpleCat 𝒞 := by
  intro hvan X Y

  suffices ∀ (n : ℕ) (X : 𝒞), hLF.length X = n → Subsingleton (Ext X Y 1) from
    this (hLF.length X) X rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro X hX
    by_cases hXz : IsZero X
    · haveI : Projective X := hXz.projective
      exact subsingleton_of_forall_eq 0 (fun e => Ext.eq_zero_of_projective e)
    by_cases hXs : Simple X
    · haveI := hXs
      exact ext1_subsingleton_of_simple_source (fun X Y => hvan X Y) X Y
    · obtain ⟨S, hSE, hS2, hS3, hlen⟩ :=
        IsLocallyFiniteLength.exists_ses_simple_quotient X hXz hXs
      subst hS2
      exact ext1_subsingleton_of_ses_contra hSE
        (ih (hLF.length S.X₁) (by omega) S.X₁ rfl)
        (by haveI := hS3
            exact ext1_subsingleton_of_simple_source (fun X Y => hvan X Y) S.X₃ Y)

end Prop_1_29_4






/-- Multiplicative compatibility of submodule tensor products: `(M₁ ⊗ N₁) · (M₂ ⊗ N₂) ⊆
(M₁ M₂) ⊗ (N₁ N₂)` in `H ⊗ H`. -/
lemma tensor_submodule_mul_le
    {R : Type*} {H : Type*} [CommRing R] [Ring H] [HopfAlgebra R H]
    (M₁ M₂ N₁ N₂ : Submodule R H) :
    Submodule.map₂ (TensorProduct.mk R H H) M₁ N₁ *
    Submodule.map₂ (TensorProduct.mk R H H) M₂ N₂ ≤
    Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂) := by
  rw [Submodule.mul_le]
  intro x hx y hy
  suffices h : ∀ m₁ ∈ M₁, ∀ n₁ ∈ N₁, (m₁ ⊗ₜ[R] n₁) * y ∈
      Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂) by
    have : Submodule.map₂ (TensorProduct.mk R H H) M₁ N₁ ≤
        (Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂)).comap
          (LinearMap.mulRight R y) := by
      rw [Submodule.map₂_le]
      intro m₁ hm₁ n₁ hn₁
      simp only [Submodule.mem_comap, LinearMap.mulRight_apply]
      exact h m₁ hm₁ n₁ hn₁
    exact this hx
  intro m₁ hm₁ n₁ hn₁
  suffices h₂ : ∀ m₂ ∈ M₂, ∀ n₂ ∈ N₂, (m₁ ⊗ₜ[R] n₁) * (m₂ ⊗ₜ[R] n₂) ∈
      Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂) by
    have : Submodule.map₂ (TensorProduct.mk R H H) M₂ N₂ ≤
        (Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂)).comap
          (LinearMap.mulLeft R (m₁ ⊗ₜ n₁)) := by
      rw [Submodule.map₂_le]
      intro m₂ hm₂ n₂ hn₂
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      exact h₂ m₂ hm₂ n₂ hn₂
    exact this hy
  intro m₂ hm₂ n₂ hn₂
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact Submodule.apply_mem_map₂ _ (Submodule.mul_mem_mul hm₁ hm₂)
    (Submodule.mul_mem_mul hn₁ hn₂)

/-- The product of two grouplike elements in a Hopf algebra is grouplike. -/
theorem mul_grouplikes
    {R : Type*} {H : Type*}
    [CommRing R] [Ring H] [HopfAlgebra R H]
    (g h : H) (hg : g ∈ grouplikes (R := R) (C := H))
    (hh : h ∈ grouplikes (R := R) (C := H)) :
    g * h ∈ grouplikes (R := R) (C := H) := by
  constructor
  · rw [Bialgebra.comul_mul, hg.1, hh.1, Algebra.TensorProduct.tmul_mul_tmul]
  · rw [Bialgebra.counit_mul, hg.2, hh.2, one_mul]

/-- In a pointed Hopf algebra over a field, the coradical `C_0` is closed under multiplication:
`C_0 · C_0 ⊆ C_0`. -/
theorem coradical_mul_self_le
    {R : Type*} {H : Type*}
    [Field R] [Ring H] [HopfAlgebra R H]
    (hpt : IsPointedCoalgebra (R := R) (C := H)) :
    coradicalFiltration (R := R) (C := H) 0 * coradicalFiltration 0 ≤
    coradicalFiltration 0 := by

  simp only [coradicalFiltration_zero]
  rw [Submodule.mul_le]
  intro x hx y hy

  have h_eq := taftWilson_coradical_eq_span_grouplikes R H hpt
  rw [h_eq] at hx hy ⊢
  rw [iSup_subtype'] at hx hy ⊢

  refine Submodule.iSup_induction (motive := fun x => x * y ∈ ⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)})
    (fun (g : {g // g ∈ grouplikes (R := R) (C := H)}) => Submodule.span R {(g : H)})
    hx (fun g x hx_span => ?_) ?_ (fun x₁ x₂ hx₁ hx₂ => ?_)
  ·

    refine Submodule.iSup_induction (motive := fun y => x * y ∈ ⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)})
      (fun (g' : {g // g ∈ grouplikes (R := R) (C := H)}) => Submodule.span R {(g' : H)})
      hy (fun g' y hy_span => ?_) ?_ (fun y₁ y₂ hy₁ hy₂ => ?_)
    ·
      rw [Submodule.mem_span_singleton] at hx_span hy_span
      obtain ⟨r₁, rfl⟩ := hx_span
      obtain ⟨r₂, rfl⟩ := hy_span

      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

      have hgg' : (g : H) * (g' : H) ∈ grouplikes (R := R) (C := H) :=
        mul_grouplikes _ _ g.2 g'.2

      exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).smul_mem _
        ((⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).smul_mem _
          (Submodule.mem_iSup_of_mem ⟨_, hgg'⟩
            (Submodule.subset_span (Set.mem_singleton _))))
    ·
      show x * 0 ∈ _
      rw [mul_zero]
      exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).zero_mem
    ·
      show x * (y₁ + y₂) ∈ _
      rw [mul_add]
      exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).add_mem hy₁ hy₂
  ·
    show 0 * y ∈ _
    rw [zero_mul]
    exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).zero_mem
  ·
    show (x₁ + x₂) * y ∈ _
    rw [add_mul]
    exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).add_mem hx₁ hx₂


/-- A Hopf-algebra filtration on `H`: an increasing family of submodules satisfying
`F i · F j ⊆ F (i+j)` and stable under the antipode at each level. -/
structure IsHopfAlgebraFiltration {R : Type*} {H : Type*}
    [CommRing R] [Ring H] [HopfAlgebra R H]
    (F : ℕ → Submodule R H) : Prop where
  mul_le : ∀ i j : ℕ, F i * F j ≤ F (i + j)
  antipode_eq : ∀ n : ℕ, Submodule.map (HopfAlgebra.antipode R) (F n) = F n

/-- The `n`-th associated graded piece of a filtration `F`: `F n / F (n-1)`, with the
convention that for `n = 0` the bottom level is `⊥`. -/
noncomputable def associatedGraded {R : Type*} {H : Type*}
    [CommRing R] [AddCommGroup H] [Module R H]
    (F : ℕ → Submodule R H) (n : ℕ) : Type _ :=
  ↥(F n) ⧸ (Submodule.comap (F n).subtype (if n = 0 then ⊥ else F (n - 1)))





open CategoryTheory MonoidalCategory CategoryTheory.Limits

/-- An object `X` is semisimple if it is isomorphic to a finite biproduct of simple objects. -/
def IsSemisimpleObject (C : Type*) [Category C] [HasZeroMorphisms C] (X : C) : Prop :=
  ∃ (n : ℕ) (f : Fin n → C) (_ : HasBiproduct f),
    (∀ i, Simple (f i)) ∧ Nonempty (X ≅ @biproduct _ _ _ _ f ‹HasBiproduct f›)

/-- A tensor category is pointed if every simple object has a tensor inverse, i.e.
the simples form a group under `⊗`. -/
class IsPointedTensorCategory (C : Type*) [Category C] [MonoidalCategory C]
    [HasZeroMorphisms C] : Prop where
  simple_has_inverse : ∀ (X : C) [Simple X],
    ∃ (Y : C), Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C)


section AlgebraGeneration

universe u_ag v_ag

variable (R : Type u_ag) (H : Type v_ag)
variable [CommRing R] [AddCommGroup H] [Module R H] [Coalgebra R H]
variable [Ring H] [Algebra R H]

/-- The union of grouplikes and all skew-primitive spaces, viewed as a subset of `H`. -/
def grouplikesAndSkewPrimitives : Set H :=
  grouplikes (R := R) ∪
    ⋃ (g : H) (_ : g ∈ grouplikes (R := R) (C := H))
      (h : H) (_ : h ∈ grouplikes (R := R) (C := H)),
      (skewPrimitiveSpace (R := R) g h : Set H)

/-- `H` is generated as an `R`-algebra by its grouplike and skew-primitive elements. -/
def IsGeneratedByGrouplikesAndSkewPrimitives : Prop :=
  Algebra.adjoin R (grouplikesAndSkewPrimitives R H) = ⊤

end AlgebraGeneration

section Conjecture_1_32

universe u_c v_c

variable (k : Type u_c) (H : Type v_c)
variable [Field k] [CharZero k]
variable [AddCommGroup H] [Module k H] [Coalgebra k H]
variable [Ring H] [Algebra k H]

/-- The Andruskiewitsch-Schneider conjecture: any finite dimensional pointed Hopf algebra
over a field of characteristic zero is generated by its grouplike and skew-primitive
elements (in degree 1 of the coradical filtration). -/
def AndruskiewitschSchneiderConjecture : Prop :=
  FiniteDimensional k H →
  IsPointedCoalgebra (R := k) (C := H) →
  IsGeneratedByGrouplikesAndSkewPrimitives k H

/-- Conjecture 1.32.1 (EGNO): the Andruskiewitsch-Schneider conjecture. -/
abbrev Conjecture_1_32_1 := @AndruskiewitschSchneiderConjecture

end Conjecture_1_32

section TensorGenerated

universe v_tg u_tg

variable {C : Type u_tg} [Category.{v_tg} C]

/-- `Y` is a subquotient of `X` if there exists `Z` with a mono `Z ↪ X` and an epi `Z ↠ Y`. -/
def IsSubquotient (Y X : C) : Prop :=
  ∃ (Z : C) (i : Z ⟶ X) (p : Z ⟶ Y), Mono i ∧ Epi p

variable [MonoidalCategory C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The tensor-and-biproduct closure of a class `P` of objects: smallest class containing
`P`, the unit object, and closed under tensor product and direct sum. -/
inductive IsInTensorClosure (P : C → Prop) : C → Prop where
  | of_base {X : C} (hX : P X) : IsInTensorClosure P X
  | of_unit : IsInTensorClosure P (𝟙_ C)
  | of_tensor {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊗ Y)
  | of_directSum {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊞ Y)

/-- A tensor category is tensor-generated by a class `P` if every object is a subquotient of
a finite direct sum of tensor products of objects in `P`. -/
class IsTensorGenerated (P : C → Prop) : Prop where
  subquotient_of_tensorClosure :
    ∀ (X : C), ∃ (T : C), IsInTensorClosure P T ∧ IsSubquotient X T

/-- Definition 1.32.2 (EGNO): a tensor category `C` is tensor-generated by a collection of
objects `X_α` if every object of `C` is a subquotient of a finite direct sum of tensor
products of `X_α`. -/
abbrev Definition_1_32_2 := @IsTensorGenerated

end TensorGenerated

section LoewyLength2

universe v_ll u_ll

variable (C : Type u_ll) [Category.{v_ll} C]
variable [HasZeroMorphisms C] [HasCokernels C]

/-- An object `X` has Loewy length at most 2 if it admits a semisimple subobject `Y` such
that the cokernel `X/Y` is also semisimple. -/
def HasLoewyLengthAtMostTwo (X : C) : Prop :=
  ∃ (Y : C) (i : Y ⟶ X), Mono i ∧
    IsSemisimpleObject C Y ∧
    IsSemisimpleObject C (cokernel i)

end LoewyLength2

/-- A category `D` is the comodule category of a Hopf algebra `H` over `k`. -/
class IsComoduleCategoryOf (k : Type*) (H : Type*) (D : Type*)
    [CommSemiring k] [Ring H] [HopfAlgebra k H] [Category D] : Prop




section CategoricalConjecture

universe w_cc v_cc u_cc

variable (k : Type w_cc) [Field k] [CharZero k]
variable (C : Type u_cc) [Category.{v_cc} C] [FiniteTensorCategory k C]

/-- Categorical form of the Andruskiewitsch-Schneider conjecture: any finite pointed tensor
category over a field of characteristic zero is tensor-generated by its objects of Loewy
length at most 2. -/
def AndruskiewitschSchneiderCategorical
    [CharZero k] (_hPointed : IsPointedTensorCategory C) : Prop :=
  IsTensorGenerated (fun X => HasLoewyLengthAtMostTwo C X) (C := C)

/-- Conjecture 1.32.4 (EGNO): the categorical Andruskiewitsch-Schneider conjecture about
cocommutative Hopf algebras over algebraically closed fields of characteristic zero. -/
abbrev Conjecture_1_32_4 := @AndruskiewitschSchneiderCategorical

end CategoricalConjecture

section ChevalleyProperty

universe v_cp u_cp

variable (C : Type u_cp) [Category.{v_cp} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A tensor category has the Chevalley property if the tensor product of any two
semisimple objects is semisimple. -/
class HasChevalleyProperty : Prop where
  tensor_semisimple : ∀ (X Y : C),
    IsSemisimpleObject C X → IsSemisimpleObject C Y → IsSemisimpleObject C (X ⊗ Y)

/-- Definition 1.31.1 (EGNO): a pointed tensor category has the Chevalley property. -/
def Definition_1_31_1 : Prop := HasChevalleyProperty C

end ChevalleyProperty
