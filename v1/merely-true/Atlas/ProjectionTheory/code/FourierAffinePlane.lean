/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.FourierFF

open Finset hiding card
open Fintype (card)
open scoped BigOperators Classical

attribute [local instance] Fintype.ofFinite

namespace FourierFF

variable {p : ℕ} [Fact (Nat.Prime p)] {d : ℕ}

/-- The annihilator (orthogonal complement) of a subspace `V ⊂ 𝔽_p^d` with respect
to the standard dot product: `V^⊥ = {ξ : ⟨ξ, v⟩ = 0 for all v ∈ V}`. -/
def dotProdAnnihilator (V : Submodule (ZMod p) (Fin d → ZMod p)) :
    Set (Fin d → ZMod p) :=
  {ξ | ∀ v : Fin d → ZMod p, v ∈ V → dotProd ξ v = 0}

/-- The characteristic function of the affine subspace `a + V ⊂ 𝔽_p^d`: it equals
`1` on the coset `{a + v : v ∈ V}` and `0` elsewhere. -/
noncomputable def cosetIndicator (V : Submodule (ZMod p) (Fin d → ZMod p))
    (a : Fin d → ZMod p) : (Fin d → ZMod p) → ℂ :=
  fun x => if x - a ∈ V then 1 else 0

/--
Lemma 2.7 (Fourier transform of the indicator of an affine plane). If `P = a + V`
is an affine `k`-plane in `𝔽_p^d`, then
$$\bigl|\widehat{\mathbf{1}_P}(\xi)\bigr| = \begin{cases} |V| = q^k & \xi \in V^\perp \\ 0 & \xi \notin V^\perp.\end{cases}$$
The proof shifts to the linear case using the character `e(-⟨ξ,a⟩)`, then evaluates
the sum `∑_{v∈V} e(⟨ξ, v⟩)` using the standard orthogonality relations for
characters on the finite abelian group `V`.
-/
theorem norm_dft_cosetIndicator (e : AddChar (ZMod p) ℂ) (he : e ≠ 0)
    (V : Submodule (ZMod p) (Fin d → ZMod p))
    (a ξ : Fin d → ZMod p) :
    ‖dft e (cosetIndicator V a) ξ‖ =
      if ξ ∈ dotProdAnnihilator V then (card V : ℝ) else 0 := by

  have hdft : dft e (cosetIndicator V a) ξ =
      e (-(dotProd ξ a)) * ∑ v : V, e (-(dotProd ξ (↑v : Fin d → ZMod p))) := by
    simp only [dft, cosetIndicator, fourierChar, AddChar.compAddMonoidHom_apply,
      dotProd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddChar.inv_apply, boole_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

    have hfilt : Finset.univ.filter (fun x => x - a ∈ V) =
      Finset.univ.image (fun v : V => (↑v : Fin d → ZMod p) + a) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Subtype.exists]
      exact ⟨fun hx => ⟨x - a, hx, sub_add_cancel x a⟩,
        fun ⟨v, hv, h⟩ => by rw [← h]; simpa using hv⟩
    rw [hfilt, Finset.sum_image (fun v1 _ v2 _ h => Subtype.ext (add_right_cancel h))]

    rw [Finset.mul_sum]
    congr 1; ext v
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]

  rw [hdft, norm_mul, AddChar.norm_apply, one_mul]


  set ψ : AddChar V ℂ :=
    (e.compAddMonoidHom (dotProd (-ξ))).compAddMonoidHom V.subtype.toAddMonoidHom

  have hsum_eq : ∑ v : V, e (-(dotProd ξ (↑v : Fin d → ZMod p))) = ∑ v : V, ψ v := by
    congr 1; ext ⟨v, hv⟩
    simp [ψ, AddChar.compAddMonoidHom_apply, dotProd, mul_neg, Finset.sum_neg_distrib]
  rw [hsum_eq]
  by_cases hann : ξ ∈ dotProdAnnihilator V
  ·
    rw [if_pos hann]
    have htriv : ψ = 0 := by
      rw [show (0 : AddChar V ℂ) = 1 from by ext; simp]
      ext ⟨v, hv⟩
      simp only [ψ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
        Submodule.subtype_apply, AddChar.one_apply]
      have hdp : dotProd (-ξ) v = 0 := by
        simp [dotProd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero]
        exact hann v hv
      rw [hdp]; exact AddChar.map_zero_eq_one e
    simp [htriv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ·
    rw [if_neg hann]
    have hne : ψ ≠ 0 := by
      rw [show (0 : AddChar V ℂ) = 1 from by ext; simp]
      intro h; apply hann
      intro v hv
      have := DFunLike.ext_iff.mp h ⟨v, hv⟩
      simp only [ψ, AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe,
        Submodule.subtype_apply, AddChar.one_apply] at this
      have h01 : (0 : AddChar (ZMod p) ℂ) = 1 := by ext x; simp
      have he1 : e ≠ 1 := by rwa [← h01]
      have hprim := AddChar.IsPrimitive.of_ne_one he1
      have hdp : dotProd (-ξ) v = 0 := (hprim.zmod_char_eq_one_iff p _).mp this
      simp [dotProd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at hdp
      exact hdp
    rw [AddChar.sum_eq_zero_iff_ne_zero.mpr hne, norm_zero]

end FourierFF
