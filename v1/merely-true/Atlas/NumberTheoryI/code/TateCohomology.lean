/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Atlas.NumberTheoryI.code.Cor2328

noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

section AugmentationMapAndIdeal

variable (k : Type u) [CommRing k] (G : Type u) [Group G]

def augmentationMap : MonoidAlgebra k G →ₐ[k] k :=
  MonoidAlgebra.lift k k G 1

def augmentationIdeal : Ideal (MonoidAlgebra k G) :=
  RingHom.ker (augmentationMap k G).toRingHom

end AugmentationMapAndIdeal

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

def normMap (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G]
    (A : Rep k G) : A →ₗ[k] A :=
  A.ρ.norm

theorem normMap_range_le_invariants (A : Rep k G) :
    LinearMap.range (normMap k G A) ≤ A.ρ.invariants := by
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  intro g
  exact Representation.self_norm_apply A.ρ g y

def augmentationSubmodule (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep k G) : Submodule k A :=
  Submodule.span k {x : A | ∃ (g : G) (a : A), x = A.ρ g a - a}

def GCoinvariants (k : Type u) [CommRing k] (G : Type u) [Group G]
    (A : Rep k G) : Type u :=
  A ⧸ (augmentationSubmodule k G A)

instance GCoinvariants.addCommGroup (A : Rep k G) : AddCommGroup (GCoinvariants k G A) :=
  Submodule.Quotient.addCommGroup _

instance GCoinvariants.module (A : Rep k G) : Module k (GCoinvariants k G A) :=
  Submodule.Quotient.module _

theorem augmentationSubmodule_le_ker_norm (A : Rep k G) :
    augmentationSubmodule k G A ≤ LinearMap.ker (normMap k G A) := by
  apply Submodule.span_le.mpr
  intro x ⟨g, a, hx⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  subst hx
  simp only [map_sub, normMap, Representation.norm_self_apply, sub_self]

def normImageInInvariants (A : Rep k G) : Submodule k A.ρ.invariants :=
  Submodule.comap A.ρ.invariants.subtype (LinearMap.range (normMap k G A))

def tateH0 (A : Rep k G) : Type u :=
  A.ρ.invariants ⧸ normImageInInvariants A

instance tateH0.addCommGroup (A : Rep k G) : AddCommGroup (tateH0 A) :=
  Submodule.Quotient.addCommGroup _

instance tateH0.module (A : Rep k G) : Module k (tateH0 A) :=
  Submodule.Quotient.module _

def augInKerNorm (A : Rep k G) : Submodule k (LinearMap.ker (normMap k G A)) :=
  Submodule.comap (LinearMap.ker (normMap k G A)).subtype (augmentationSubmodule k G A)

def tateMinus1 (A : Rep k G) : Type u :=
  LinearMap.ker (normMap k G A) ⧸ augInKerNorm A

instance tateMinus1.addCommGroup (A : Rep k G) : AddCommGroup (tateMinus1 A) :=
  Submodule.Quotient.addCommGroup _

instance tateMinus1.module (A : Rep k G) : Module k (tateMinus1 A) :=
  Submodule.Quotient.module _

def tateH0.mk (A : Rep k G) : A.ρ.invariants →ₗ[k] tateH0 A :=
  Submodule.mkQ _

def tateMinus1.mk (A : Rep k G) : LinearMap.ker (normMap k G A) →ₗ[k] tateMinus1 A :=
  Submodule.mkQ _

def herbrandQuotient [IsCyclic G] (A : Rep k G)
    [Fintype (tateH0 A)] [Fintype (tateMinus1 A)] : ℚ :=
  (Fintype.card (tateH0 A) : ℚ) / (Fintype.card (tateMinus1 A) : ℚ)

lemma finite_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] [Finite C]
    (f : A →+ B) (g : B →+ C) (hex : Function.Exact f g) : Finite B := by
  rw [AddMonoidHom.finite_iff_finite_ker_range g]
  constructor
  · have hker : g.ker = f.range := by
      ext b; constructor
      · intro hb; exact (hex b).mp (AddMonoidHom.mem_ker.mp hb)
      · rintro ⟨a, rfl⟩; exact AddMonoidHom.mem_ker.mpr ((hex (f a)).mpr ⟨a, rfl⟩)
    rw [hker]
    exact Finite.of_surjective
      (fun a => ⟨f a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩)
      (fun ⟨b, hb⟩ => by
        obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hb
        exact ⟨a, Subtype.ext ha⟩)
  · exact Finite.of_injective Subtype.val Subtype.val_injective

lemma card_eq_of_exact_pair {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (hex : Function.Exact f g) :
    Nat.card B = Nat.card f.range * Nat.card g.range := by
  have hker : g.ker = f.range := by
    ext b; simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · exact (hex b).mp
    · rintro ⟨a, rfl⟩; exact (hex (f a)).mpr ⟨a, rfl⟩
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hker, mul_comm]

lemma exact_hexagon_card_eq_general
    {A₁ A₂ A₃ A₄ A₅ A₆ : Type*}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    [AddCommGroup A₄] [AddCommGroup A₅] [AddCommGroup A₆]
    [Fintype A₁] [Fintype A₂] [Fintype A₃]
    [Fintype A₄] [Fintype A₅] [Fintype A₆]
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄)
    (f₄ : A₄ →+ A₅) (f₅ : A₅ →+ A₆) (f₆ : A₆ →+ A₁)
    (h₁₂ : Function.Exact f₁ f₂) (h₂₃ : Function.Exact f₂ f₃)
    (h₃₄ : Function.Exact f₃ f₄) (h₄₅ : Function.Exact f₄ f₅)
    (h₅₆ : Function.Exact f₅ f₆) (h₆₁ : Function.Exact f₆ f₁) :
    Fintype.card A₁ * Fintype.card A₃ * Fintype.card A₅ =
    Fintype.card A₂ * Fintype.card A₄ * Fintype.card A₆ := by
  simp only [Fintype.card_eq_nat_card]
  rw [card_eq_of_exact_pair f₆ f₁ h₆₁, card_eq_of_exact_pair f₁ f₂ h₁₂,
      card_eq_of_exact_pair f₂ f₃ h₂₃, card_eq_of_exact_pair f₃ f₄ h₃₄,
      card_eq_of_exact_pair f₄ f₅ h₄₅, card_eq_of_exact_pair f₅ f₆ h₅₆]
  ring

def tateHnAux {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]
    (A : Rep k G) : Bool → Type u
  | true  => tateH0 A
  | false => tateMinus1 A

instance tateHnAux.addCommGroup {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]
    (A : Rep k G) : (b : Bool) → AddCommGroup (tateHnAux A b)
  | true  => tateH0.addCommGroup A
  | false => tateMinus1.addCommGroup A

def parityBool (n : ℤ) : Bool := n % 2 == 0

def tateHn (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G]
    [IsCyclic G] (A : Rep k G) (n : ℤ) : Type u :=
  tateHnAux A (parityBool n)

instance tateHn.addCommGroup {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]
    [IsCyclic G] (A : Rep k G) (n : ℤ) : AddCommGroup (tateHn k G A n) :=
  tateHnAux.addCommGroup A (parityBool n)







theorem tateH0_subsingleton_of_induced {k : Type u} [CommRing k] {G : Type u}
    [Group G] [Fintype G] (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Subsingleton (tateH0 (Rep.ind (⊥ : Subgroup G).subtype B)) := by
  open Representation Finsupp Classical in


  rw [tateH0, Submodule.Quotient.subsingleton_iff]
  ext ⟨v, hv_mem⟩
  simp only [Submodule.mem_top, iff_true]
  rw [normImageInInvariants, Submodule.mem_comap]

  rw [LinearMap.mem_range]


  have coordMap_def : ∀ (h₀ : G) (a : ↑B),
      (Coinvariants.lift _
        (TensorProduct.finsuppScalarLeft k (↑B) G)
        (fun g => by
          have hg : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
          subst hg; simp only [map_one]; exact LinearMap.comp_id _) :
        IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] (G →₀ ↑B))
      (IndV.mk (⊥ : Subgroup G).subtype B.ρ h₀ a) = Finsupp.single h₀ a := by
    intro h₀ a₀
    simp only [Coinvariants.lift_mk, IndV.mk, LinearMap.comp_apply, TensorProduct.mk_apply]
    ext g; simp [Finsupp.single_apply]
  set φ : IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] (G →₀ ↑B) :=
    Coinvariants.lift _
      (TensorProduct.finsuppScalarLeft k (↑B) G)
      (fun g => by
        have hg : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
        subst hg; simp only [map_one]; exact LinearMap.comp_id _)
  have φ_inj : Function.Injective φ := by
    intro v₁ v₂ h
    obtain ⟨x₁, rfl⟩ := Coinvariants.mk_surjective _ v₁
    obtain ⟨x₂, rfl⟩ := Coinvariants.mk_surjective _ v₂
    simp only [φ, Coinvariants.lift_mk] at h
    exact congr_arg _ ((TensorProduct.finsuppScalarLeft k (↑B) G).injective h)
  have φ_mk : ∀ (h₀ : G) (a : ↑B),
      φ (IndV.mk (⊥ : Subgroup G).subtype B.ρ h₀ a) = Finsupp.single h₀ a :=
    coordMap_def

  have eval_equiv : ∀ g₀ : G,
      (Finsupp.lapply (1 : G) : (G →₀ (↑B)) →ₗ[k] ↑B) ∘ₗ φ ∘ₗ
        (B.ρ.ind (⊥ : Subgroup G).subtype g₀) =
      (Finsupp.lapply g₀ : (G →₀ (↑B)) →ₗ[k] ↑B) ∘ₗ φ := by
    intro g₀
    apply IndV.hom_ext; intro h₀; ext a₀
    simp only [LinearMap.comp_apply, φ, Coinvariants.lift_mk, IndV.mk, TensorProduct.mk_apply]
    simp [TensorProduct.finsuppScalarLeft_apply, LinearMap.rTensor_tmul,
      Finsupp.lapply_apply, Finsupp.single_apply, mul_inv_eq_one]

  rw [Representation.mem_invariants] at hv_mem
  have hconst : ∀ g₀ : G, (φ v) g₀ = (φ v) 1 := by
    intro g₀
    have := congr_fun (congr_arg DFunLike.coe (eval_equiv g₀)) v
    simp only [LinearMap.comp_apply, Finsupp.lapply_apply] at this
    rw [hv_mem g₀] at this; exact this.symm

  have norm_eq : ∀ (a₀ : ↑B) (h₀ : G),
      (B.ρ.ind (⊥ : Subgroup G).subtype).norm (IndV.mk _ B.ρ h₀ a₀) =
      ∑ g₀ : G, IndV.mk (⊥ : Subgroup G).subtype B.ρ g₀ a₀ := by
    intro a₀ h₀
    simp only [Representation.norm, LinearMap.sum_apply, ind_mk]
    exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft h₀)) _ _ (fun g => by simp)

  have hv_eq : v = (B.ρ.ind (⊥ : Subgroup G).subtype).norm
      (IndV.mk (⊥ : Subgroup G).subtype B.ρ 1 ((φ v) 1)) := by
    apply φ_inj
    rw [norm_eq, map_sum]
    ext g₀
    simp only [φ_mk]
    simp [hconst g₀]
  exact ⟨_, hv_eq.symm⟩


def tateMinus1_ind_augRetract {k : Type u} [CommRing k] {G : Type u} [Group G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Representation.IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] ↑B := by
  apply Representation.Coinvariants.lift _
    (TensorProduct.lift ((LinearMap.lsmul k (↑B : Type u)) ∘ₗ
      Finsupp.linearCombination k (fun (_ : G) => (1 : k))))
  intro g
  have : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
  subst this
  rw [map_one]
  exact LinearMap.comp_id _


def tateMinus1_ind_proj1 {k : Type u} [CommRing k] {G : Type u} [Group G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Representation.IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] ↑B := by
  apply Representation.Coinvariants.lift _
    (TensorProduct.lift ((LinearMap.lsmul k (↑B : Type u)) ∘ₗ
      (Finsupp.lapply (1 : G))))
  intro g
  have : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
  subst this
  rw [map_one]
  exact LinearMap.comp_id _

lemma tateMinus1_ind_augRetract_mk {k : Type u} [CommRing k] {G : Type u} [Group G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (h : G) (b : B) :
    tateMinus1_ind_augRetract B (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ h b) = b := by
  simp [tateMinus1_ind_augRetract, Representation.IndV.mk, Representation.Coinvariants.lift_mk,
    Finsupp.linearCombination_single]

lemma tateMinus1_ind_proj1_mk_inv {k : Type u} [CommRing k] {G : Type u} [Group G]
    [DecidableEq G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (g : G) (b : B) :
    tateMinus1_ind_proj1 B
      (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ g⁻¹ b) =
      if g = 1 then b else 0 := by
  simp only [tateMinus1_ind_proj1, Representation.IndV.mk, LinearMap.comp_apply,
    Representation.Coinvariants.lift_mk, Finsupp.lapply]
  split_ifs with hg
  · subst hg; simp
  · simp [inv_ne_one.mpr hg]

lemma tateMinus1_ind_proj1_norm_mk1 {k : Type u} [CommRing k] {G : Type u} [Group G]
    [Fintype G]
    (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) (b : B) :
    tateMinus1_ind_proj1 B
      ((Representation.ind (⊥ : Subgroup G).subtype B.ρ).norm
        (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ (1 : G) b)) = b := by
  classical
  show tateMinus1_ind_proj1 B
    ((∑ g : G, Representation.ind (⊥ : Subgroup G).subtype B.ρ g)
      (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ 1 b)) = b
  simp only [LinearMap.sum_apply, map_sum, Representation.ind_mk, one_mul]
  simp only [tateMinus1_ind_proj1_mk_inv]
  rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
  simp

theorem tateMinus1_subsingleton_of_induced {k : Type u} [CommRing k] {G : Type u}
    [Group G] [Fintype G] (B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    Subsingleton (tateMinus1 (Rep.ind (⊥ : Subgroup G).subtype B)) := by
  classical
  show Subsingleton (LinearMap.ker (normMap k G (Rep.ind (⊥ : Subgroup G).subtype B)) ⧸
    augInKerNorm (Rep.ind (⊥ : Subgroup G).subtype B))
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro ⟨x, hx_ker⟩ _
  change x ∈ augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)

  let r := tateMinus1_ind_augRetract B
  let p := tateMinus1_ind_proj1 B
  let s := Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ (1 : G)

  have hx_norm : normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) x = 0 :=
    LinearMap.mem_ker.mp hx_ker

  have normMap_eq : (Representation.ind (⊥ : Subgroup G).subtype B.ρ).norm =
      normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) := rfl

  have hD : ∀ y : Representation.IndV (⊥ : Subgroup G).subtype B.ρ,
      y - s (r y) ∈ augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B) := by
    suffices h : (augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)).mkQ ∘ₗ
        (LinearMap.id - s ∘ₗ r) = 0 by
      intro y
      have := LinearMap.ext_iff.mp h y
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.zero_apply] at this
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    apply Representation.IndV.hom_ext
    intro h
    ext b
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.zero_apply, Submodule.mkQ_apply]
    change (augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)).mkQ
      (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ h b) -
      (augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)).mkQ
      (s (r (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ h b))) = 0
    rw [tateMinus1_ind_augRetract_mk, sub_eq_zero,
      ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply Submodule.subset_span
    exact ⟨h⁻¹, s b, by

      congr 1
      exact ((Representation.ind_mk (⊥ : Subgroup G).subtype B.ρ h⁻¹ 1 b).trans
        (by simp [one_mul])).symm⟩

  have hAug_le_ker := augmentationSubmodule_le_ker_norm (Rep.ind (⊥ : Subgroup G).subtype B)

  have hD_ker : normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) (x - s (r x)) = 0 :=
    LinearMap.mem_ker.mp (hAug_le_ker (hD x))

  have hsr_ker : normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) (s (r x)) = 0 := by
    have h := map_sub (normMap k G (Rep.ind (⊥ : Subgroup G).subtype B)) x (s (r x))
    rw [hx_norm, hD_ker] at h
    simp at h
    exact h

  have hr_zero : r x = 0 := by
    have h1 : p ((Representation.ind (⊥ : Subgroup G).subtype B.ρ).norm (s (r x))) = r x :=
      tateMinus1_ind_proj1_norm_mk1 B (r x)
    rw [normMap_eq, hsr_ker, map_zero] at h1
    exact h1.symm

  have := hD x
  rw [hr_zero, map_zero, sub_zero] at this
  exact this










def HerbrandMultiplicative [IsCyclic G] (S : ShortComplex (Rep k G)) : Prop :=
  ∀ (i₁ : Fintype (tateH0 S.X₁)) (i₂ : Fintype (tateMinus1 S.X₁))
    (i₃ : Fintype (tateH0 S.X₂)) (i₄ : Fintype (tateMinus1 S.X₂))
    (i₅ : Fintype (tateH0 S.X₃)) (i₆ : Fintype (tateMinus1 S.X₃)),
    @herbrandQuotient _ _ _ _ _ _ S.X₂ i₃ i₄ =
      @herbrandQuotient _ _ _ _ _ _ S.X₁ i₁ i₂ *
      @herbrandQuotient _ _ _ _ _ _ S.X₃ i₅ i₆







lemma card_eq_card_ker_mul_card_range {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup,
      mul_comm]
  congr 1
  exact Nat.card_congr (f.quotKerEquivRange.toAddEquiv.toEquiv)

lemma ker_rho_sub_one_eq_invariants (A : Rep k G)
    (σ : G) (hσ : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    LinearMap.ker (A.ρ σ - LinearMap.id) = A.ρ.invariants := by
  ext a
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (A.ρ.mem_invariants_iff_of_forall_mem_zpowers σ hσ a).symm

lemma rho_pow_sub_mem_range_nat (A : Rep k G) (σ : G) (n : ℕ) (a : A) :
    A.ρ (σ ^ n) a - a ∈ LinearMap.range (A.ρ σ - LinearMap.id) := by
  induction n with
  | zero => simp [pow_zero, map_one]
  | succ n ih =>
    set f : Module.End k A := A.ρ σ - LinearMap.id
    have hpow : σ ^ (n + 1) = σ * σ ^ n := by rw [pow_succ']
    have heq : A.ρ (σ ^ (n + 1)) a - a =
        f (A.ρ (σ ^ n) a) + (A.ρ (σ ^ n) a - a) := by
      rw [hpow, A.ρ.map_mul]
      change (A.ρ σ) ((A.ρ (σ ^ n)) a) - a =
        ((A.ρ σ) ((A.ρ (σ ^ n)) a) - (A.ρ (σ ^ n)) a) + ((A.ρ (σ ^ n)) a - a)
      abel
    rw [heq]
    exact Submodule.add_mem _ (LinearMap.mem_range_self _ _) ih

lemma rho_inv_pow_sub_mem_range (A : Rep k G) (σ : G) (n : ℕ) (a : A) :
    A.ρ (σ⁻¹ ^ n) a - a ∈ LinearMap.range (A.ρ σ - LinearMap.id) := by
  induction n with
  | zero => simp [pow_zero, map_one]
  | succ n ih =>
    set f : Module.End k A := A.ρ σ - LinearMap.id
    have hpow : σ⁻¹ ^ (n + 1) = σ⁻¹ * σ⁻¹ ^ n := by rw [pow_succ']
    have hmul : (A.ρ σ) ((A.ρ σ⁻¹) (A.ρ (σ⁻¹ ^ n) a)) = A.ρ (σ⁻¹ ^ n) a := by
      calc (A.ρ σ) ((A.ρ σ⁻¹) (A.ρ (σ⁻¹ ^ n) a))
          = (A.ρ σ * A.ρ σ⁻¹) (A.ρ (σ⁻¹ ^ n) a) := rfl
        _ = (A.ρ (σ * σ⁻¹)) (A.ρ (σ⁻¹ ^ n) a) := by rw [A.ρ.map_mul]
        _ = (A.ρ 1) (A.ρ (σ⁻¹ ^ n) a) := by rw [mul_inv_cancel]
        _ = A.ρ (σ⁻¹ ^ n) a := by simp [A.ρ.map_one]
    have hinv_in_range :
        A.ρ σ⁻¹ (A.ρ (σ⁻¹ ^ n) a) - A.ρ (σ⁻¹ ^ n) a ∈ LinearMap.range f := by
      set b := A.ρ (σ⁻¹ ^ n) a
      have : A.ρ σ⁻¹ b - b = -(f (A.ρ σ⁻¹ b)) := by
        show (A.ρ σ⁻¹) b - b = -((A.ρ σ) ((A.ρ σ⁻¹) b) - (A.ρ σ⁻¹) b)
        rw [hmul]; abel
      rw [this]
      exact Submodule.neg_mem _ (LinearMap.mem_range_self f _)
    have heq : A.ρ (σ⁻¹ ^ (n + 1)) a - a =
        (A.ρ σ⁻¹ (A.ρ (σ⁻¹ ^ n) a) - A.ρ (σ⁻¹ ^ n) a) + (A.ρ (σ⁻¹ ^ n) a - a) := by
      rw [hpow, A.ρ.map_mul]
      change (A.ρ σ⁻¹) ((A.ρ (σ⁻¹ ^ n)) a) - a = _
      abel
    rw [heq]
    exact Submodule.add_mem _ hinv_in_range ih

lemma rho_zpow_sub_mem_range (A : Rep k G) (σ : G) (n : ℤ) (a : A) :
    A.ρ (σ ^ n) a - a ∈ LinearMap.range (A.ρ σ - LinearMap.id) := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact rho_pow_sub_mem_range_nat A σ n a
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [← inv_pow]
    exact rho_inv_pow_sub_mem_range A σ (n + 1) a

lemma range_rho_sub_one_eq_augmentationSubmodule [IsCyclic G] (A : Rep k G)
    (σ : G) (hσ : ∀ x : G, x ∈ Subgroup.zpowers σ) :
    LinearMap.range (A.ρ σ - LinearMap.id) = augmentationSubmodule k G A := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    apply Submodule.subset_span
    exact ⟨σ, a, rfl⟩
  · unfold augmentationSubmodule
    apply Submodule.span_le.mpr
    intro x ⟨g, a, hx⟩
    rw [hx]
    obtain ⟨n, rfl⟩ := hσ g
    exact rho_zpow_sub_mem_range A σ n a

theorem card_invariants_mul_augmentation [IsCyclic G] (A : Rep k G) [Finite A] :
    Nat.card A = Nat.card A.ρ.invariants * Nat.card (augmentationSubmodule k G A) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := G)
  set f : Module.End k A := A.ρ σ - LinearMap.id
  have h := card_eq_card_ker_mul_card_range f
  rw [ker_rho_sub_one_eq_invariants A σ hσ,
      range_rho_sub_one_eq_augmentationSubmodule A σ hσ] at h
  exact h

theorem herbrand_quotient_eq_one_of_finite [IsCyclic G] (A : Rep k G)
    [Finite (tateH0 A)] [Finite (tateMinus1 A)] [Finite A] :
    Nat.card (tateH0 A) = Nat.card (tateMinus1 A) := by
  set inv := A.ρ.invariants
  set kerN := LinearMap.ker (normMap k G A)
  set ranN := LinearMap.range (normMap k G A)
  set augS := augmentationSubmodule k G A
  set nimI := normImageInInvariants A
  set aikN := augInKerNorm A
  change Nat.card (inv ⧸ nimI) = Nat.card (kerN ⧸ aikN)

  have h1 : Nat.card inv = Nat.card (inv ⧸ nimI) * Nat.card nimI :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup nimI.toAddSubgroup

  have h2 : Nat.card kerN = Nat.card (kerN ⧸ aikN) * Nat.card aikN :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup aikN.toAddSubgroup

  have h3 := card_eq_card_ker_mul_card_range (normMap k G A)

  have h4 := card_invariants_mul_augmentation A

  have h5 : Nat.card nimI = Nat.card ranN :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (normMap_range_le_invariants A)).toEquiv

  have h6 : Nat.card aikN = Nat.card augS :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (augmentationSubmodule_le_ker_norm A)).toEquiv
  rw [h5] at h1; rw [h6] at h2; rw [h2] at h3; rw [h1] at h4


  have hr : 0 < Nat.card ranN := Nat.card_pos
  have hs : 0 < Nat.card augS := Nat.card_pos
  have key : Nat.card (kerN ⧸ aikN) * (Nat.card ranN * Nat.card augS) =
    Nat.card (inv ⧸ nimI) * (Nat.card ranN * Nat.card augS) := by linarith
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hr hs) key).symm


lemma ker_normMap_trivial_int {G₀ : Type} [Group G₀] [Fintype G₀] :
    LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ ℤ)) = ⊥ := by
  ext n
  simp only [LinearMap.mem_ker, Submodule.mem_bot, normMap, Representation.norm]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [Representation.trivial_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).elim (absurd · (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) id
  · intro h; rw [h, mul_zero]

def invEquivTrivInt {G₀ : Type} [Group G₀] [Fintype G₀] :
    (Rep.trivial ℤ G₀ ℤ).ρ.invariants ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofEq _ _ (by ext x; simp [Representation.mem_invariants])).trans
    Submodule.topEquiv

lemma invEquivTrivInt_apply {G₀ : Type} [Group G₀] [Fintype G₀]
    (x : (Rep.trivial ℤ G₀ ℤ).ρ.invariants) :
    (invEquivTrivInt (G₀ := G₀)) x = x.1 := by
  simp [invEquivTrivInt, Submodule.topEquiv]

lemma map_normImage_trivInt {G₀ : Type} [Group G₀] [Fintype G₀] :
    Submodule.map (invEquivTrivInt (G₀ := G₀)).toLinearMap
      (normImageInInvariants (Rep.trivial ℤ G₀ ℤ)) =
      Submodule.span ℤ {(Fintype.card G₀ : ℤ)} := by
  ext n; simp only [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show invEquivTrivInt.toLinearMap x = x.1 from invEquivTrivInt_apply x]
    simp only [normImageInInvariants, normMap, Submodule.mem_comap,
      Submodule.coe_subtype, LinearMap.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.mem_span_singleton]
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
      Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm
    exact ⟨m, by rw [smul_eq_mul, ← hm]; ring⟩
  · intro hn
    rw [Submodule.mem_span_singleton] at hn
    obtain ⟨c, hc⟩ := hn; rw [smul_eq_mul] at hc
    refine ⟨⟨n, by rw [Representation.mem_invariants]; intro g; simp⟩, ?_, ?_⟩
    · simp only [normImageInInvariants, normMap, Submodule.mem_comap,
        Submodule.coe_subtype, LinearMap.mem_range]
      refine ⟨c, ?_⟩
      simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
        Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linarith
    · exact invEquivTrivInt_apply _

def tateH0_equiv_zmod {G₀ : Type} [Group G₀] [Fintype G₀] :
    tateH0 (Rep.trivial ℤ G₀ ℤ) ≃ ZMod (Fintype.card G₀) :=
  (Submodule.Quotient.equiv _ _ invEquivTrivInt map_normImage_trivInt).toEquiv.trans
    ((Int.quotientSpanEquivZMod (Fintype.card G₀ : ℤ)).toEquiv.trans
      (Equiv.cast (by simp [Int.natAbs_natCast])))

def Rep.trivialHom {G₀ : Type*} [Monoid G₀]
    {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (f : M →ₗ[ℤ] N) :
    Rep.trivial ℤ G₀ M ⟶ Rep.trivial ℤ G₀ N :=
  Rep.ofHom ⟨f, fun g => by ext x; simp [Representation.trivial]⟩

lemma Rep.trivialHom_comp {G₀ : Type*} [Monoid G₀]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) :
    Rep.trivialHom (G₀ := G₀) f ≫ Rep.trivialHom g = Rep.trivialHom (g.comp f) := by
  ext x; simp [Rep.trivialHom, Rep.ofHom]

lemma Rep.trivialHom_id {G₀ : Type*} [Monoid G₀]
    {M : Type} [AddCommGroup M] :
    Rep.trivialHom (G₀ := G₀) (LinearMap.id (M := M) (R := ℤ)) = 𝟙 _ := by
  ext x; simp [Rep.trivialHom, Rep.ofHom]




lemma finite_kernel_of_mono {A B : Rep k G} (ι : B ⟶ A) [Mono ι] :
    Finite (Limits.kernel ι : Rep k G) := by
  have hz := Limits.isZero_kernel_of_mono ι
  haveI : Subsingleton (Limits.kernel ι : Rep k G) := by
    constructor
    intro a b
    have : ∀ x : (Limits.kernel ι : Rep k G), x = 0 := by
      intro x
      have key := congr_arg (fun g => (show Limits.kernel ι ⟶ Limits.kernel ι from g).hom)
        (hz.eq_of_src (𝟙 (Limits.kernel ι)) 0)
      have := congr_fun (congr_arg DFunLike.coe key) x
      simpa using this
    rw [this a, this b]
  exact Finite.of_subsingleton


omit [Fintype G] in
lemma ker_normMap_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ))) = ⊥ := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_bot, normMap, Representation.norm]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [Representation.trivial_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  constructor
  · intro h
    ext i
    have hi := congr_fun h i
    simp only [Pi.mul_apply, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).elim
      (absurd · (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) id
  · intro h; rw [h]; simp

lemma card_tateMinus1_trivial_finFun (G₀ : Type) [Group G₀] [Fintype G₀]
    [IsCyclic G₀] (n : ℕ)
    [Fintype (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ)))] :
    Fintype.card (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) = 1 := by
  haveI : Subsingleton (LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ)))) := by
    rw [ker_normMap_trivial_finFun n]; infer_instance
  haveI : Subsingleton (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
    Quotient.instSubsingletonQuotient _
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    |>.antisymm (Fintype.card_pos)


def invEquivTrivFinFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants ≃ₗ[ℤ] (Fin n → ℤ) :=
  (LinearEquiv.ofEq _ _ (by ext x; simp [Representation.mem_invariants])).trans
    Submodule.topEquiv

lemma invEquivTrivFinFun_apply {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ)
    (x : (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants) :
    (invEquivTrivFinFun n (G₀ := G₀)) x = x.1 := by
  simp [invEquivTrivFinFun, Submodule.topEquiv]

lemma map_normImage_trivFinFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Submodule.map (invEquivTrivFinFun n (G₀ := G₀)).toLinearMap
      (normImageInInvariants (Rep.trivial ℤ G₀ (Fin n → ℤ))) =
      LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) := by
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show (invEquivTrivFinFun n).toLinearMap x = x.1 from invEquivTrivFinFun_apply n x]
    simp only [normImageInInvariants, normMap, Submodule.mem_comap,
      Submodule.coe_subtype, LinearMap.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, ?_⟩
    ext i
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
      Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm ⊢
    exact congr_fun hm i
  · rintro ⟨c, rfl⟩
    have hmem : (↑(Fintype.card G₀) : ℤ) • c ∈ (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants := by
      rw [Representation.mem_invariants]; intro g; simp
    refine ⟨⟨(↑(Fintype.card G₀) : ℤ) • c, hmem⟩, ?_, ?_⟩
    · simp only [normImageInInvariants, normMap, Submodule.mem_comap,
        Submodule.coe_subtype, LinearMap.mem_range]
      refine ⟨c, ?_⟩
      ext i
      simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
        Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Pi.smul_apply, smul_eq_mul]
    · exact invEquivTrivFinFun_apply n _

lemma range_smul_id_eq_pi {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) =
    Submodule.pi Set.univ (fun _ : Fin n => Submodule.span ℤ {(Fintype.card G₀ : ℤ)}) := by
  ext f
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩ i
    exact ⟨g i, by simp [Pi.smul_apply, mul_comm]⟩
  · intro h
    choose c hc using h
    exact ⟨c, by ext i; simp only [Pi.smul_apply, smul_eq_mul]; linarith [hc i]⟩

noncomputable def tateH0_equiv_pi_zmod {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ)) ≃ (Fin n → ZMod (Fintype.card G₀)) := by

  refine (Submodule.Quotient.equiv _ _ (invEquivTrivFinFun n)
    (map_normImage_trivFinFun n)).toEquiv |>.trans ?_

  rw [range_smul_id_eq_pi]

  refine (Submodule.quotientPi _).toEquiv |>.trans ?_

  exact Equiv.piCongrRight (fun _ =>
    (Int.quotientSpanEquivZMod _).toEquiv.trans
      (Equiv.cast (by simp [Int.natAbs_natCast])))

lemma card_tateH0_trivial_finFun (G₀ : Type) [Group G₀] [Fintype G₀]
    [IsCyclic G₀] (n : ℕ)
    [Fintype (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ)))] :
    Fintype.card (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ))) = Fintype.card G₀ ^ n := by
  rw [Fintype.card_congr (tateH0_equiv_pi_zmod n), Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem herbrandQuotient_trivial_finFun (G₀ : Type) [Group G₀] [Fintype G₀] [IsCyclic G₀]
    (n : ℕ)
    [Fintype (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ)))]
    [Fintype (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ)))] :
    herbrandQuotient (Rep.trivial ℤ G₀ (Fin n → ℤ)) = (Fintype.card G₀ : ℚ) ^ n := by
  simp only [herbrandQuotient,
    card_tateH0_trivial_finFun G₀ n, card_tateMinus1_trivial_finFun G₀ n,
    Nat.cast_one, div_one, Nat.cast_pow]

instance tateH0.finite_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Finite (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
  Finite.of_equiv _ (tateH0_equiv_pi_zmod n).symm

instance tateMinus1.finite_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Finite (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) := by
  haveI : Subsingleton (LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ)))) := by
    rw [ker_normMap_trivial_finFun n]; infer_instance
  haveI : Subsingleton (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
    Quotient.instSubsingletonQuotient _
  exact Finite.of_subsingleton

end TateCohomology
