/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HarishChandraIsomorphism
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm

noncomputable section

open scoped TensorProduct

variable (R : Type*) [Field R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
variable {R 𝔤}

structure ChevalleyRestrictionData (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) where
  S𝔤 : Type*
  [instRing : Ring S𝔤]
  [instAlgebra : Algebra R S𝔤]
  adInvariant : Subalgebra R S𝔤
  restrictionAlgHom : S𝔤 →ₐ[R] UniversalEnvelopingAlgebra R Δ.𝔥
  algActionOnS𝔤 : wg.W →* (S𝔤 ≃ₐ[R] S𝔤)
  restriction_equivariant :
    ∀ (w : wg.W) (f : S𝔤),
      restrictionAlgHom ((algActionOnS𝔤 w) f) =
      (wg.algAction w) (restrictionAlgHom f)
  adInvariant_W_fixed :
    ∀ (w : wg.W) (f : S𝔤), f ∈ adInvariant →
      (algActionOnS𝔤 w) f = f
  eval𝔤 : S𝔤 → (𝔤 → R)
  eval𝔥 : UniversalEnvelopingAlgebra R Δ.𝔥 → (Δ.𝔥 → R)
  eval𝔤_injective : Function.Injective eval𝔤
  eval𝔥_injective : Function.Injective eval𝔥
  eval_restriction_compat : ∀ (f : S𝔤) (h : Δ.𝔥),
      eval𝔥 (restrictionAlgHom f) h = eval𝔤 f (h : 𝔤)
  adInvariant_eval_determined_by_h : ∀ (f₁ f₂ : S𝔤),
      f₁ ∈ adInvariant → f₂ ∈ adInvariant →
      (∀ h : Δ.𝔥, eval𝔤 f₁ (h : 𝔤) = eval𝔤 f₂ (h : 𝔤)) →
      ∀ x : 𝔤, eval𝔤 f₁ x = eval𝔤 f₂ x
  trace_function_surjectivity : ∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥),
      p ∈ wg.invariantSubalgebra →
      ∃ f : S𝔤, f ∈ adInvariant ∧
        ∀ h : Δ.𝔥, eval𝔥 (restrictionAlgHom f) h = eval𝔥 p h

attribute [instance] ChevalleyRestrictionData.instRing
  ChevalleyRestrictionData.instAlgebra

noncomputable def killingFormDualIso
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    Δ.𝔥 ≃ₗ[R] (Δ.𝔥 →ₗ[R] R) := by
  haveI : Δ.𝔥.IsCartanSubalgebra := Δ.is_cartan
  exact LieAlgebra.IsKilling.cartanEquivDual Δ.𝔥

noncomputable def TriangularDecomposition.projectToH
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (x : 𝔤) : Δ.𝔥 :=
  (Δ.decomp_exists x).choose_spec.choose

theorem TriangularDecomposition.projectToH_of_mem_h
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (h : Δ.𝔥) :
    Δ.projectToH (h : 𝔤) = h := by
  unfold TriangularDecomposition.projectToH

  set n_neg := (Δ.decomp_exists (h : 𝔤)).choose
  set h₀ := (Δ.decomp_exists (h : 𝔤)).choose_spec.choose
  set n_pos := (Δ.decomp_exists (h : 𝔤)).choose_spec.choose_spec.choose
  have hdecomp := (Δ.decomp_exists (h : 𝔤)).choose_spec.choose_spec.choose_spec

  have heq : (n_neg : 𝔤) + (h₀ : 𝔤) + (n_pos : 𝔤) =
      (0 : Δ.𝔫_neg) + (h : 𝔤) + (0 : Δ.𝔫_pos) := by
    rw [← hdecomp]
    simp [ZeroMemClass.coe_zero, zero_add, add_zero]
  exact (Δ.decomp_unique n_neg 0 h₀ h n_pos 0 heq).2.1

noncomputable def chevalleyEval𝔥
    {R : Type*} [Field R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (p : UniversalEnvelopingAlgebra R Δ.𝔥) (h : Δ.𝔥) : R :=
  evalWeight Δ (killingFormDualIso Δ h) p



omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_lands_in_W_invariants_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg)
    (f : crd.S𝔤) (hf : f ∈ crd.adInvariant) :
    (crd.restrictionAlgHom f) ∈
      (wg.invariantSubalgebra : Set (UniversalEnvelopingAlgebra R Δ.𝔥)) := by


  intro w
  rw [← crd.restriction_equivariant w f, crd.adInvariant_W_fixed w f hf]

def ChevalleyRestrictionData.restrictionMap
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    crd.adInvariant →ₐ[R] wg.invariantSubalgebra :=
  (crd.restrictionAlgHom.comp crd.adInvariant.val).codRestrict
    wg.invariantSubalgebra (fun ⟨x, hx⟩ =>
      chevalley_restriction_lands_in_W_invariants_aux crd x hx)

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_injective_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    Function.Injective crd.restrictionMap := by
  intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ heq
  have h_res : crd.restrictionAlgHom f₁ = crd.restrictionAlgHom f₂ := by
    have := congr_arg Subtype.val heq
    simpa [ChevalleyRestrictionData.restrictionMap, AlgHom.codRestrict] using this
  have h_eval_h : ∀ h : Δ.𝔥, crd.eval𝔤 f₁ (h : 𝔤) = crd.eval𝔤 f₂ (h : 𝔤) := by
    intro h
    rw [← crd.eval_restriction_compat f₁ h, ← crd.eval_restriction_compat f₂ h, h_res]
  have h_eval_all : ∀ x : 𝔤, crd.eval𝔤 f₁ x = crd.eval𝔤 f₂ x :=
    crd.adInvariant_eval_determined_by_h f₁ f₂ hf₁ hf₂ h_eval_h
  have h_eq : f₁ = f₂ := crd.eval𝔤_injective (funext h_eval_all)
  exact Subtype.ext h_eq

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_surjective_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    Function.Surjective crd.restrictionMap := by
  intro ⟨p, hp⟩
  obtain ⟨f, hf_inv, hf_eval⟩ := crd.trace_function_surjectivity p hp
  have h_eq : crd.restrictionAlgHom f = p :=
    crd.eval𝔥_injective (funext hf_eval)
  exact ⟨⟨f, hf_inv⟩, Subtype.ext h_eq⟩

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem chevalley_restriction_bijective_aux
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (crd : ChevalleyRestrictionData Δ wg) :
    Function.Bijective crd.restrictionMap :=
  ⟨chevalley_restriction_injective_aux crd, chevalley_restriction_surjective_aux crd⟩






structure IsComplexReflection {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (g : V ≃ₗ[k] V) : Prop where
  rank_eq_one : Module.finrank k (LinearMap.range ((g : V →ₗ[k] V) - LinearMap.id)) = 1
  ne_id : g ≠ LinearEquiv.refl k V

structure IsComplexReflectionGroup {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (G : Type*) [Group G] [Fintype G]
    (ρ : G →* V ≃ₗ[k] V) : Prop where
  generated_by_reflections :
    ∀ g : G, ∃ (n : ℕ) (reflections : Fin n → G),
      (∀ i, IsComplexReflection (ρ (reflections i))) ∧
      g = (List.ofFn reflections).prod

lemma isComplexReflection_inv {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (g : V ≃ₗ[k] V) (h : IsComplexReflection g) :
    IsComplexReflection g.symm where
  rank_eq_one := by
    have key : -(g.symm.toLinearMap - LinearMap.id) =
        g.symm.toLinearMap.comp (g.toLinearMap - LinearMap.id) := by
      ext v; simp [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
            LinearMap.id_apply, map_sub]
    have hrange : (g.symm.toLinearMap - LinearMap.id).range =
        (g.toLinearMap - LinearMap.id).range.map g.symm.toLinearMap := by
      rw [← LinearMap.range_neg, key, LinearMap.range_comp]
    rw [hrange, LinearEquiv.finrank_map_eq]; exact h.rank_eq_one
  ne_id := by
    intro h_eq; apply h.ne_id; ext v
    have : g.symm (g v) = v := g.symm_apply_apply v
    rw [h_eq] at this; simpa using this

lemma isComplexReflectionGroup_of_closure_eq_top {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {G : Type*} [Group G] [Fintype G]
    (ρ : G →* V ≃ₗ[k] V)
    (hclosure : Subgroup.closure { g : G | IsComplexReflection (ρ g) } = ⊤) :
    IsComplexReflectionGroup G ρ where
  generated_by_reflections g := by
    have hg : g ∈ Subgroup.closure { g : G | IsComplexReflection (ρ g) } := by
      rw [hclosure]; exact Subgroup.mem_top g
    suffices key : ∃ (l : List G), (∀ x ∈ l, IsComplexReflection (ρ x)) ∧ g = l.prod by
      obtain ⟨l, hl, rfl⟩ := key
      refine ⟨l.length, fun i => l.get i, fun i => hl _ (l.get_mem i), ?_⟩
      rw [List.ofFn_get]
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact ⟨[x], by simpa, by simp⟩
    | one => exact ⟨[], by simp, by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨lx, hlx, rfl⟩ := ihx
      obtain ⟨ly, hly, rfl⟩ := ihy
      exact ⟨lx ++ ly, fun a ha => by
        simp only [List.mem_append] at ha; exact ha.elim (hlx a) (hly a),
        by rw [List.prod_append]⟩
    | inv x _ ihx =>
      obtain ⟨lx, hlx, hprod⟩ := ihx
      refine ⟨(lx.map (·⁻¹)).reverse, fun a ha => ?_, ?_⟩
      · simp only [List.mem_reverse, List.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        show IsComplexReflection (ρ b⁻¹)
        rw [show ρ b⁻¹ = (ρ b).symm from by rw [map_inv]; rfl]
        exact isComplexReflection_inv _ (hlx b hb)
      · rw [hprod, List.prod_inv_reverse]

def polynomialInvariantSubalgebra (k : Type*) [CommSemiring k]
    (G : Type*) [Group G] (ι : Type*)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)) :
    Subalgebra k (MvPolynomial ι k) :=
  Subalgebra.invariants G algAct

def IsInducedPolynomialAction {k : Type*} [CommRing k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V)
    (G : Type*) [Group G]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)) : Prop :=
  ∀ (g : G) (i : ι),
    algAct g (MvPolynomial.X i) =
    Finset.univ.sum fun j =>
      MvPolynomial.C (b.repr (ρ g (b i)) j) * MvPolynomial.X j

def IsPolynomialAlgebra {R : Type*} [CommSemiring R]
    (A : Type*) [Semiring A] [Algebra R A] : Prop :=
  ∃ (n : ℕ), Nonempty (MvPolynomial (Fin n) R ≃ₐ[R] A)



lemma isInducedPolynomialAction_deg_pres
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {G : Type*} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V)
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (hcompat : IsInducedPolynomialAction b G ρ algAct)
    (g : G) (p : MvPolynomial ι k) :
    ((algAct g) p).totalDegree ≤ p.totalDegree := by

  have hX_deg : ∀ i : ι,
      ((algAct g : MvPolynomial ι k →ₐ[k] MvPolynomial ι k) (MvPolynomial.X i)).totalDegree ≤ 1 := by
    intro i
    change ((algAct g) (MvPolynomial.X i)).totalDegree ≤ 1
    rw [hcompat g i]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
    refine Finset.sup_le (fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C]
    simp only [zero_add]
    exact le_of_eq (MvPolynomial.totalDegree_X j)


  let φ : MvPolynomial ι k →ₐ[k] MvPolynomial ι k := (algAct g).toAlgHom
  suffices (φ p).totalDegree ≤ p.totalDegree by exact this
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le (fun v hv => ?_)
  rw [MvPolynomial.monomial_eq, map_mul]
  have hC : φ (MvPolynomial.C (MvPolynomial.coeff v p)) =
      MvPolynomial.C (MvPolynomial.coeff v p) := by
    show (algAct g).toAlgHom (MvPolynomial.C (MvPolynomial.coeff v p)) =
      MvPolynomial.C (MvPolynomial.coeff v p)
    rw [MvPolynomial.algHom_C]; rfl
  rw [hC]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  rw [Finsupp.prod, map_prod]
  simp_rw [map_pow]
  calc (∏ x ∈ v.support, φ (MvPolynomial.X x) ^ v x).totalDegree
      ≤ ∑ x ∈ v.support, (φ (MvPolynomial.X x) ^ v x).totalDegree :=
        MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ x ∈ v.support, v x * (φ (MvPolynomial.X x)).totalDegree :=
        Finset.sum_le_sum (fun i _ => MvPolynomial.totalDegree_pow _ _)
    _ ≤ ∑ x ∈ v.support, v x * 1 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hX_deg i))
    _ = v.sum (fun _ e => e) := by simp [mul_one, Finsupp.sum]
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hv


noncomputable def orbitPoly {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) : Polynomial (MvPolynomial ι k) :=
  Finset.univ.prod (fun g => Polynomial.X - Polynomial.C ((algAct g) p))

lemma orbitPoly_monic {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) : (orbitPoly algAct p).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

lemma orbitPoly_eval {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) : (orbitPoly algAct p).eval p = 0 := by
  simp only [orbitPoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, map_one]

lemma orbitPoly_map_invariant {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) (h : G) :
    (orbitPoly algAct p).map (algAct h).toAlgHom.toRingHom = orbitPoly algAct p := by
  simp only [orbitPoly]
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  conv_lhs =>
    arg 2
    ext g
    rw [show (algAct h).toAlgHom.toRingHom ((algAct g) p) = (algAct (h * g)) p from by
      simp [map_mul]]
  exact Fintype.prod_equiv (Equiv.mulLeft h) _ _
    (fun g => by simp [Equiv.mulLeft])

lemma orbitPoly_coeff_mem {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) (n : ℕ) :
    (orbitPoly algAct p).coeff n ∈ polynomialInvariantSubalgebra k G ι algAct := by
  show ∀ g : G, (algAct g) ((orbitPoly algAct p).coeff n) = (orbitPoly algAct p).coeff n
  intro g
  have hmapinv := orbitPoly_map_invariant algAct p g
  have := congr_arg (fun q => Polynomial.coeff q n) hmapinv
  simp only [Polynomial.coeff_map] at this
  exact this

lemma orbitPoly_coeffs_subset {k : Type*} [Field k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) :
    (↑(orbitPoly algAct p).coeffs : Set (MvPolynomial ι k)) ⊆
      (polynomialInvariantSubalgebra k G ι algAct).toSubring := by
  intro c hc
  obtain ⟨n, _, hn⟩ := Polynomial.mem_coeffs_iff.1 hc
  exact hn ▸ orbitPoly_coeff_mem algAct p n

lemma isIntegral_over_invariantSubalgebra
    {k : Type*} [Field k] [CharZero k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k) :
    IsIntegral (polynomialInvariantSubalgebra k G ι algAct) p := by
  let S := polynomialInvariantSubalgebra k G ι algAct
  let q := orbitPoly algAct p

  let q' := q.toSubring S.toSubring (orbitPoly_coeffs_subset algAct p)

  have hq'_monic : q'.Monic := by
    rw [Polynomial.monic_toSubring]
    exact orbitPoly_monic algAct p

  have hq'_eval : Polynomial.eval₂ (Subring.subtype S.toSubring) p q' = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_toSubring]
    exact orbitPoly_eval algAct p


  refine ⟨q', hq'_monic, ?_⟩
  rw [show algebraMap ↥S (MvPolynomial ι k) = S.toSubring.subtype from
    (S.toSubring_subtype).symm]
  exact hq'_eval

theorem remark_11_5_generators_eq_dim
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (G : Type*) [Group G] [Fintype G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (r : ℕ) (f : Fin r → MvPolynomial ι k)
    (_hf_inv : ∀ i, f i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hf_alg : AlgebraicIndependent k f)
    (hf_gen : polynomialInvariantSubalgebra k G ι algAct = Algebra.adjoin k (Set.range f)) :
    r = Fintype.card ι := by

  classical

  have h_int_inv : ∀ x : MvPolynomial ι k,
      IsIntegral (↥(polynomialInvariantSubalgebra k G ι algAct)) x :=
    fun x => isIntegral_over_invariantSubalgebra algAct x

  have h_int_S : ∀ x : MvPolynomial ι k,
      IsIntegral (↥(Algebra.adjoin k (Set.range f))) x := by
    intro x; have := h_int_inv x; rwa [hf_gen] at this

  have h_isAlgebraic : Algebra.IsAlgebraic (↥(Algebra.adjoin k (Set.range f)))
      (MvPolynomial ι k) := (⟨h_int_S⟩ : Algebra.IsIntegral _ _).isAlgebraic

  have hf_basis : IsTranscendenceBasis k f :=
    hf_alg.isTranscendenceBasis_iff_isAlgebraic.mpr h_isAlgebraic

  have hX_basis : IsTranscendenceBasis k (MvPolynomial.X : ι → MvPolynomial ι k) :=
    IsTranscendenceBasis.mvPolynomial ι k

  have h_eq := hf_basis.lift_cardinalMk_eq hX_basis
  rw [Cardinal.mk_fin, Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_natCast] at h_eq
  exact_mod_cast h_eq



lemma reflection_subgroup_is_reflection_group
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {G : Type*} [Group G] [Fintype G]
    (ρ : G →* V ≃ₗ[k] V)
    (H : Subgroup G) [Fintype H]
    (hH : H = Subgroup.closure { g : G | IsComplexReflection (ρ g) }) :
    IsComplexReflectionGroup H (ρ.comp H.subtype) := by
  apply isComplexReflectionGroup_of_closure_eq_top (ρ.comp H.subtype)


  have hset : {h : H | IsComplexReflection ((ρ.comp H.subtype) h)} =
      H.subtype ⁻¹' {g : G | IsComplexReflection (ρ g)} := by
    ext ⟨g, _⟩; simp [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [hset, hH]
  exact Subgroup.closure_preimage_eq_top _

lemma isInducedPolynomialAction_restrict
    {k : Type*} [CommRing k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V)
    {G : Type*} [Group G]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (hcompat : IsInducedPolynomialAction b G ρ algAct)
    (H : Subgroup G) :
    IsInducedPolynomialAction b H (ρ.comp H.subtype) (algAct.comp H.subtype) := by
  intro ⟨g, _⟩ i; exact hcompat g i






structure ChevalleyRestrictionPolyData
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ)
    (n m : ℕ) where
  G : Type*
  [instGroupG : Group G]


  G_action : G →* (MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R)
  W_action : wg.W →* (MvPolynomial (Fin m) R ≃ₐ[R] MvPolynomial (Fin m) R)
  Res : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin m) R
  Res_components : Fin n → MvPolynomial (Fin m) R
  Res_eq_aeval : Res = MvPolynomial.aeval Res_components
  Res_components_homogeneous : ∀ i, (Res_components i).IsHomogeneous 1
  Res_action_compat : ∀ (w : wg.W), ∃ (g : G),
    ∀ (p : MvPolynomial (Fin n) R),
      Res ((G_action g) p) = (W_action w) (Res p)
  kernel_trivial : ∀ (p : MvPolynomial (Fin n) R),
    p ∈ Subalgebra.invariants G G_action → Res p = 0 → p = 0


attribute [instance] ChevalleyRestrictionPolyData.instGroupG

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem ChevalleyRestrictionPolyData.Res_preserves_degree
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m)
    (p : MvPolynomial (Fin n) R) (d : ℕ)
    (hp : p.IsHomogeneous d) : (cpd.Res p).IsHomogeneous d := by
  rw [cpd.Res_eq_aeval]
  have h := hp.aeval cpd.Res_components cpd.Res_components_homogeneous
  rwa [one_mul] at h

omit [LieAlgebra.IsKilling R 𝔤] [FiniteDimensional R 𝔤] in
theorem ChevalleyRestrictionPolyData.Res_maps_invariants
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m)
    (p : MvPolynomial (Fin n) R)
    (hp : p ∈ Subalgebra.invariants cpd.G cpd.G_action) :
    (cpd.Res p) ∈ Subalgebra.invariants wg.W cpd.W_action := by


  intro w
  obtain ⟨g, hg⟩ := cpd.Res_action_compat w
  rw [← hg p, hp g]



theorem invariant_vanishes_on_semisimple_locus
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m)
    (S : Set (Fin n → R))
    (hconj : ∀ v ∈ S, ∀ p : MvPolynomial (Fin n) R,
        p ∈ Subalgebra.invariants cpd.G cpd.G_action →
        ∃ (h : Fin m → R),
          MvPolynomial.eval v p = MvPolynomial.eval h (cpd.Res p))
    (p : MvPolynomial (Fin n) R)
    (hp : p ∈ Subalgebra.invariants cpd.G cpd.G_action)
    (hker : cpd.Res p = 0) :
    ∀ v ∈ S, MvPolynomial.eval v p = 0 := by
  intro v hv
  obtain ⟨h, heq⟩ := hconj v hv p hp
  rw [heq, hker, map_zero]




def ChevalleyRestrictionPolyData.restrictionMapPoly
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {n m : ℕ}
    (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m) :
    Subalgebra.invariants cpd.G cpd.G_action →ₐ[R]
    Subalgebra.invariants wg.W cpd.W_action :=
  (cpd.Res.comp (Subalgebra.invariants cpd.G cpd.G_action).val).codRestrict
    (Subalgebra.invariants wg.W cpd.W_action)
    (fun ⟨x, hx⟩ => cpd.Res_maps_invariants x hx)




theorem chevalley_res_kernel_trivial_on_invariants
    {k : Type*} [CommRing k]
    {n m : ℕ}
    (G : Type*) [Group G]
    (G_action : G →* (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k))
    (Res : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k)


    (hRes_kernel_trivial : ∀ (q : MvPolynomial (Fin n) k),
      q ∈ Subalgebra.invariants G G_action → Res q = 0 → q = 0)
    (p : MvPolynomial (Fin n) k)
    (hp_inv : p ∈ Subalgebra.invariants G G_action)
    (hp_ker : Res p = 0) : p = 0 :=
  hRes_kernel_trivial p hp_inv hp_ker

theorem chevalley_res_injective_on_invariants
    {k : Type*} [CommRing k]
    {n m : ℕ}
    (G : Type*) [Group G]
    (G_action : G →* (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k))
    (Res : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k)


    (hRes_kernel_trivial : ∀ (q : MvPolynomial (Fin n) k),
      q ∈ Subalgebra.invariants G G_action → Res q = 0 → q = 0)
    (p₁ p₂ : MvPolynomial (Fin n) k)
    (hp₁ : p₁ ∈ Subalgebra.invariants G G_action)
    (hp₂ : p₂ ∈ Subalgebra.invariants G G_action)
    (h : Res p₁ = Res p₂) :
    p₁ = p₂ := by

  have hker : Res (p₁ - p₂) = 0 := by rw [map_sub, h, sub_self]

  have hinv : (p₁ - p₂) ∈ Subalgebra.invariants G G_action := by
    intro g; simp [map_sub, hp₁ g, hp₂ g]

  have h0 := hRes_kernel_trivial (p₁ - p₂) hinv hker

  exact eq_of_sub_eq_zero h0






end
