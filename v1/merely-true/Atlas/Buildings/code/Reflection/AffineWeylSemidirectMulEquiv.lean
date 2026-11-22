/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylGroupData

variable (d : AffineWeylGroupData E)

/-- The additive automorphism of the coroot lattice $Λ(\check Φ)$ induced by an element
$w$ of the linear Weyl group. -/
def weylActionAddAut (w : ↥d.weylGroup) : AddAut ↥d.corootLattice where
  toFun v := ⟨(w : E ≃ₗᵢ[ℝ] E) v, d.weylGroup_stable_corootLattice w w.prop v v.prop⟩
  invFun v := ⟨(w : E ≃ₗᵢ[ℝ] E)⁻¹ v, by
    have : (↑w⁻¹ : E ≃ₗᵢ[ℝ] E) ↑v ∈ d.corootLattice :=
      d.weylGroup_stable_corootLattice w⁻¹ (d.weylGroup.inv_mem w.prop) v v.prop
    convert this using 1⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  map_add' a b := by ext; simp [map_add]

/-- The induced homomorphism $W → \mathrm{MulAut}(\mathrm{Multiplicative}\ Λ(\check Φ))$
used to form the semidirect product $W_a = Λ(\check Φ) ⋊ W$. -/
def weylActionMulAutHom :
    ↥d.weylGroup →* MulAut (Multiplicative ↥d.corootLattice) where
  toFun w := AddEquiv.toMultiplicative (d.weylActionAddAut w)
  map_one' := by
    ext ⟨v⟩; simp [weylActionAddAut, AddEquiv.toMultiplicative]
  map_mul' w₁ w₂ := by
    ext ⟨v⟩; simp [weylActionAddAut, AddEquiv.toMultiplicative]

/-- The abstract semidirect product $Λ(\check Φ) ⋊ W$ associated to the affine Weyl
group data. -/
abbrev AffineWeylSemidirect :=
  (Multiplicative ↥d.corootLattice) ⋊[d.weylActionMulAutHom] ↥d.weylGroup

end AffineWeylGroupData

/-- Data witnessing that a concrete subgroup of $\mathrm{Isom}(E)$ realizes the affine
Weyl group as a semidirect product: every element decomposes as a linear part plus a
coroot translation, with the linear part in $W$ and the translation in $Λ(\check Φ)$, and
every pair $(w, v) ∈ W × Λ(\check Φ)$ is realized. -/
structure AffineWeylSemidirectData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] extends AffineWeylGroupFullData E where
  affineWeylSubgroup : Subgroup (E ≃ᵃⁱ[ℝ] E)
  affine_decomp : ∀ g ∈ affineWeylSubgroup, ∀ x : E,
    (g : E ≃ᵃⁱ[ℝ] E) x = (linearPartHom g : E ≃ₗᵢ[ℝ] E) x + (g : E ≃ᵃⁱ[ℝ] E) 0
  translationPart_mem : ∀ g ∈ affineWeylSubgroup,
    (g : E ≃ᵃⁱ[ℝ] E) 0 ∈ corootLattice
  linearPart_mem : ∀ g ∈ affineWeylSubgroup,
    linearPartHom g ∈ weylGroup
  pair_mem : ∀ w ∈ weylGroup, ∀ v ∈ corootLattice,
    ∃ g ∈ affineWeylSubgroup,
      linearPartHom g = (w : E ≃ₗᵢ[ℝ] E) ∧
      (g : E ≃ᵃⁱ[ℝ] E) 0 = v

namespace AffineWeylSemidirectData

variable (d : AffineWeylSemidirectData E)

/-- Shorthand for the abstract semidirect product type. -/
abbrev SemiType := d.toAffineWeylGroupData.AffineWeylSemidirect

/-- Map sending $g ∈ W_a$ to the pair $(g\cdot 0,\ \mathrm{linearPart}(g))$ in the
semidirect product. -/
def toSemidirect (g : ↥d.affineWeylSubgroup) : d.SemiType :=
  ⟨Multiplicative.ofAdd ⟨(g : E ≃ᵃⁱ[ℝ] E) 0, d.translationPart_mem g g.prop⟩,
   ⟨linearPartHom (g : E ≃ᵃⁱ[ℝ] E), d.linearPart_mem g g.prop⟩⟩

/-- Two elements of $W_a$ with the same linear part and translation part agree. -/
theorem ext_of_decomp (g₁ g₂ : ↥d.affineWeylSubgroup)
    (hlin : linearPartHom (g₁ : E ≃ᵃⁱ[ℝ] E) = linearPartHom (g₂ : E ≃ᵃⁱ[ℝ] E))
    (htrans : (g₁ : E ≃ᵃⁱ[ℝ] E) 0 = (g₂ : E ≃ᵃⁱ[ℝ] E) 0) :
    g₁ = g₂ := by
  ext x : 2
  rw [d.affine_decomp g₁ g₁.prop x, d.affine_decomp g₂ g₂.prop x, hlin, htrans]

/-- The map $g \mapsto (g\cdot 0, \mathrm{linearPart}(g))$ is injective. -/
theorem toSemidirect_injective : Function.Injective d.toSemidirect := by
  intro g₁ g₂ h
  apply d.ext_of_decomp
  ·
    have hr := congr_arg SemidirectProduct.right h
    simp only [toSemidirect] at hr
    exact congr_arg Subtype.val hr
  ·
    have hl := congr_arg SemidirectProduct.left h
    simp only [toSemidirect] at hl
    exact congr_arg (fun x => (Multiplicative.toAdd x).val) hl

/-- Every pair $(w, v) ∈ W × Λ(\check Φ)$ comes from some $g ∈ W_a$. -/
theorem toSemidirect_surjective : Function.Surjective d.toSemidirect := by
  intro ⟨mv, w⟩
  set v := Multiplicative.toAdd mv
  obtain ⟨g, hg_mem, hg_lin, hg_trans⟩ := d.pair_mem w w.prop v v.prop
  refine ⟨⟨g, hg_mem⟩, ?_⟩
  unfold toSemidirect
  apply SemidirectProduct.ext
  ·
    show Multiplicative.ofAdd ⟨g 0, _⟩ = mv
    exact Subtype.ext hg_trans
  ·
    show (⟨linearPartHom g, _⟩ : ↥d.weylGroup) = w
    exact Subtype.ext hg_lin

/-- The map `toSemidirect` is multiplicative: it preserves the group law of $W_a$. -/
theorem toSemidirect_mul (g₁ g₂ : ↥d.affineWeylSubgroup) :
    d.toSemidirect (g₁ * g₂) = d.toSemidirect g₁ * d.toSemidirect g₂ := by
  unfold toSemidirect
  rw [SemidirectProduct.ext_iff]
  constructor
  ·


    simp only [SemidirectProduct.mul_left]


    show Multiplicative.ofAdd (⟨(↑(g₁ * g₂) : E ≃ᵃⁱ[ℝ] E) 0, _⟩ : ↥d.corootLattice) =
      Multiplicative.ofAdd ⟨(g₁ : E ≃ᵃⁱ[ℝ] E) 0, _⟩ *
        (d.toAffineWeylGroupData.weylActionMulAutHom
          ⟨linearPartHom (g₁ : E ≃ᵃⁱ[ℝ] E), _⟩)
          (Multiplicative.ofAdd ⟨(g₂ : E ≃ᵃⁱ[ℝ] E) 0, _⟩)

    change Multiplicative.ofAdd (⟨(↑(g₁ * g₂) : E ≃ᵃⁱ[ℝ] E) 0, _⟩ : ↥d.corootLattice) =
      Multiplicative.ofAdd (⟨(g₁ : E ≃ᵃⁱ[ℝ] E) 0, _⟩ +
        (d.toAffineWeylGroupData.weylActionAddAut
          ⟨linearPartHom (g₁ : E ≃ᵃⁱ[ℝ] E), _⟩)
          ⟨(g₂ : E ≃ᵃⁱ[ℝ] E) 0, _⟩)
    congr 1
    ext
    simp only [AffineWeylGroupData.weylActionAddAut, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      AddSubgroup.coe_add]
    simp only [Subgroup.coe_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply]
    rw [d.affine_decomp g₁ g₁.prop ((g₂ : E ≃ᵃⁱ[ℝ] E) 0)]
    exact add_comm _ _
  ·
    simp only [SemidirectProduct.mul_right]
    show (⟨linearPartHom (↑(g₁ * g₂) : E ≃ᵃⁱ[ℝ] E), _⟩ : ↥d.weylGroup) =
      ⟨linearPartHom ↑g₁, _⟩ * ⟨linearPartHom ↑g₂, _⟩
    ext
    simp only [Subgroup.coe_mul, map_mul]

/-- The promised group isomorphism $W_a ≃ Λ(\check Φ) ⋊ W$. -/
def affineWeyl_semidirect_equiv : ↥d.affineWeylSubgroup ≃* d.SemiType where
  toFun := d.toSemidirect
  invFun := Function.surjInv d.toSemidirect_surjective
  left_inv _ := d.toSemidirect_injective (Function.surjInv_eq d.toSemidirect_surjective _)
  right_inv s := Function.surjInv_eq d.toSemidirect_surjective s
  map_mul' := d.toSemidirect_mul

end AffineWeylSemidirectData

namespace AffineWeylGroup

variable (Wa : AffineWeylGroup E)

/-- The set of affine reflections of the affine Weyl group $W_a$. -/
def affineReflections : Set (E ≃ᵃⁱ[ℝ] E) :=
  {s | s ∈ Wa.reflGroup.group ∧
    ∃ η ∈ Wa.reflGroup.arrangement.hyperplanes,
      (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1}

/-- The affine Weyl group is generated by its affine reflections. -/
theorem reflections_generate_affineWeylGroup :
    Subgroup.closure (Wa.affineReflections) = Wa.reflGroup.group :=
  Wa.reflGroup.generated_by_reflections.symm

end AffineWeylGroup

namespace AffineWeylGroupFullData

variable (d : AffineWeylGroupFullData E)

/-- Translation by $\check α$ is the product of two affine reflections $s_{α,1} s_{α,0}$. -/
theorem coroot_translation_is_product_of_reflections (α : E) (hα : α ∈ d.roots) :
    ∀ v : E, v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v) :=
  d.corootTranslation_eq_comp_affineRefls α hα

end AffineWeylGroupFullData
