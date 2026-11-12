/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.SemidirectProduct
import Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
import Atlas.Buildings.code.AffineCoxeter.TransitiveAlcovesHelper

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- Discreteness of the translation subgroup: if the translation subgroup acts
freely on a nonempty open alcove $C$ by genuine additive translations, then there
is a uniform lower bound $\varepsilon > 0$ on the norm of every nontrivial
translation vector $w \cdot 0$. -/
theorem translation_subgroup_discrete
    (C : W.Alcove)
    (hC_open : IsOpen C.set)
    (hC_nonempty : C.set.Nonempty)
    (hdisjoint : ∀ w ∈ W.TranslationSubgroup, w ≠ 1 →
      Disjoint C.set ((w : E ≃ᵃⁱ[ℝ] E) '' C.set))
    (htransl : ∀ w ∈ W.TranslationSubgroup, ∀ y : E,
      (w : E ≃ᵃⁱ[ℝ] E) y = y + (w : E ≃ᵃⁱ[ℝ] E) 0) :
    ∃ ε > 0, ∀ w ∈ W.TranslationSubgroup, w ≠ 1 →
      ‖((w : E ≃ᵃⁱ[ℝ] E) 0 : E)‖ ≥ ε := by
  obtain ⟨x0, hx0⟩ := hC_nonempty
  obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hC_open x0 hx0
  refine ⟨ε, hε_pos, ?_⟩
  intro w hw hw_ne
  by_contra h_small
  push Not at h_small
  have h_wx0 : (w : E ≃ᵃⁱ[ℝ] E) x0 ∈ Metric.ball x0 ε := by
    rw [Metric.mem_ball, dist_eq_norm, htransl w hw x0, add_sub_cancel_left]
    exact h_small
  exact Set.disjoint_iff.mp (hdisjoint w hw hw_ne)
    ⟨hball h_wx0, x0, hx0, rfl⟩

/-- Existence of a compact fundamental domain for the translation subgroup: with
finite linear-part group and a closed-alcove cover by $W$, the union
$Y = \bigcup_{\bar w} \bar w \cdot \overline C$ is compact and is hit by every
$W_T$-orbit. This realises $E / W_T$ as a torus quotient. -/
theorem exists_compact_fundamental_domain
    (C : W.Alcove)
    (hWbar_finite : Set.Finite W.LinearPartGroup.carrier)
    (hC_compact : IsCompact (closure C.set))
    (hcovers_W : ∀ x : E, ∃ w ∈ W.group,
      ((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x ∈ closure C.set)
    (hgen : ∀ wbar ∈ W.LinearPartGroup,
      ∃ g ∈ W.Stabilizer 0, linearPartHom g = wbar)
    (hx : W.SpecialPoint (0 : E)) :
    ∃ Y : Set E, IsCompact Y ∧
      (∀ x : E, ∃ w ∈ W.TranslationSubgroup,
        ((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x ∈ Y) := by
  set Y := ⋃ wbar ∈ W.LinearPartGroup,
    (fun v => (wbar : E ≃ₗᵢ[ℝ] E) v) '' closure C.set
  refine ⟨Y, ?_, ?_⟩
  · exact hWbar_finite.isCompact_biUnion (fun wbar _ =>
      hC_compact.image (wbar : E ≃ₗᵢ[ℝ] E).continuous)
  · intro x
    obtain ⟨w, hw, hw_inv⟩ := hcovers_W x
    obtain ⟨t, ht, s, hs, hws⟩ :=
      W.semidirect_product_decomposition 0 hx hgen w hw
    refine ⟨t, ht, ?_⟩


    have h_eq : ((t : E ≃ᵃⁱ[ℝ] E)⁻¹) x = (s : E ≃ᵃⁱ[ℝ] E) (((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x) := by
      have hinv : (w : E ≃ᵃⁱ[ℝ] E)⁻¹ = (s : E ≃ᵃⁱ[ℝ] E)⁻¹ * (t : E ≃ᵃⁱ[ℝ] E)⁻¹ := by
        rw [hws]; group
      show (t : E ≃ᵃⁱ[ℝ] E)⁻¹ x = s (((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x)
      rw [hinv]
      show (t : E ≃ᵃⁱ[ℝ] E)⁻¹ x =
        (s : E ≃ᵃⁱ[ℝ] E) ((s : E ≃ᵃⁱ[ℝ] E)⁻¹ ((t : E ≃ᵃⁱ[ℝ] E)⁻¹ x))
      rw [show (s : E ≃ᵃⁱ[ℝ] E) ((s : E ≃ᵃⁱ[ℝ] E)⁻¹ ((t : E ≃ᵃⁱ[ℝ] E)⁻¹ x)) =
        ((s * s⁻¹ : E ≃ᵃⁱ[ℝ] E)) ((t : E ≃ᵃⁱ[ℝ] E)⁻¹ x) from rfl]
      simp
    rw [h_eq]

    have hs_fix : (s : E ≃ᵃⁱ[ℝ] E) (0 : E) = 0 := hs.2
    have hs_lin : linearPartHom s ∈ W.LinearPartGroup :=
      ⟨s, W.stabilizer_le_group 0 hs, rfl⟩


    suffices hsact : (s : E ≃ᵃⁱ[ℝ] E) (((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x) =
        (linearPartHom s : E ≃ₗᵢ[ℝ] E) (((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x) by
      rw [hsact]
      exact Set.mem_biUnion hs_lin ⟨((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x, hw_inv, rfl⟩


    have h_diff := AffineIsometryEquiv.map_vsub s
      (((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x) (0 : E)
    simp only [vsub_eq_sub, sub_zero] at h_diff

    rw [hs_fix, sub_zero] at h_diff
    exact h_diff.symm

/-- Cleanup of `exists_compact_fundamental_domain`: dropping the explicit
stabiliser-surjection hypothesis by using the unconditional surjection
`W.stabilizer_surjects_unconditional`. -/
theorem exists_compact_fundamental_domain_unconditional
    (C : W.Alcove)
    (hWbar_finite : Set.Finite W.LinearPartGroup.carrier)
    (hC_compact : IsCompact (closure C.set))
    (hcovers_W : ∀ x : E, ∃ w ∈ W.group,
      ((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x ∈ closure C.set)
    (hx : W.SpecialPoint (0 : E)) :
    ∃ Y : Set E, IsCompact Y ∧
      (∀ x : E, ∃ w ∈ W.TranslationSubgroup,
        ((w : E ≃ᵃⁱ[ℝ] E)⁻¹) x ∈ Y) :=
  W.exists_compact_fundamental_domain C hWbar_finite hC_compact hcovers_W
    (W.stabilizer_surjects_unconditional 0 hx) hx

/-- Translation elements act by addition: any $w$ in the kernel of the linear-part
homomorphism is a genuine translation $y \mapsto y + w(0)$. -/
theorem translation_acts_additively (w : E ≃ᵃⁱ[ℝ] E) (hw : w ∈ W.TranslationSubgroup)
    (y : E) : (w : E ≃ᵃⁱ[ℝ] E) y = y + (w : E ≃ᵃⁱ[ℝ] E) 0 := by
  have hw_ker : w ∈ linearPartHom.ker := hw.2
  rw [MonoidHom.mem_ker] at hw_ker
  have h_diff := AffineIsometryEquiv.map_vsub w y (0 : E)
  simp only [vsub_eq_sub, sub_zero] at h_diff
  have h_lin : (AffineIsometryEquiv.linearIsometryEquiv w) y = y := by
    have : (AffineIsometryEquiv.linearIsometryEquiv w) = (1 : E ≃ₗᵢ[ℝ] E) := hw_ker
    simp [this]
  rw [h_lin] at h_diff
  exact eq_add_of_sub_eq h_diff.symm

/-- Every alcove is nonempty, since it is connected by definition. -/
theorem alcove_nonempty (C : W.Alcove) : C.set.Nonempty :=
  C.isConnected.nonempty

/-- For an essential indecomposable affine reflection group, at least one alcove
exists: the connected component of any point in the complement of the locally
finite hyperplane arrangement. -/
theorem alcove_exists (hess : W.IsEssential) (hind : W.IsIndecomposable) :
    Nonempty W.Alcove := by


  have h_carrier_closed : ∀ h : AffineHyperplane E, IsClosed h.carrier :=
    fun h => isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have h_carrier_interior : ∀ h : AffineHyperplane E, interior h.carrier = ∅ := by
    intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
    obtain ⟨r, hr_pos, hr_sub⟩ := hx

    have hn_ne : h.normal ≠ 0 := h.normal_ne_zero
    have hn_pos : 0 < ‖h.normal‖ := norm_pos_iff.mpr hn_ne
    set y := x + (r / (2 * ‖h.normal‖)) • h.normal
    have hy_ball : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr_pos (mul_pos two_pos hn_pos))]
      field_simp; linarith
    have hy_carrier : y ∉ h.carrier := by
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, y]
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      have hx_on : ⟪h.normal, x⟫_ℝ = h.offset := by
        have := hr_sub (Metric.mem_ball_self hr_pos)
        simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at this
        exact this
      rw [hx_on]
      intro heq
      have h1 : r / (2 * ‖h.normal‖) > 0 := div_pos hr_pos (mul_pos two_pos hn_pos)
      have h2 : ‖h.normal‖ ^ 2 > 0 := pow_pos hn_pos 2
      linarith [mul_pos h1 h2]
    exact hy_carrier (hr_sub hy_ball)


  obtain ⟨ε, hε_pos, hS_fin⟩ := W.locallyFinite 0
  set S := {h ∈ W.arrangement.hyperplanes | (Metric.ball 0 ε ∩ h.carrier).Nonempty}

  have hS_union_closed : IsClosed (⋃ h ∈ S, h.carrier) :=
    hS_fin.isClosed_biUnion (fun h _ => h_carrier_closed h)
  have hS_union_interior : interior (⋃ h ∈ S, h.carrier) = ∅ := by
    classical
    set T := hS_fin.toFinset
    have hST : S = ↑T := (Set.Finite.coe_toFinset hS_fin).symm
    rw [hST]
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.coe_insert, Set.biUnion_insert, Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
      obtain ⟨r, hr_pos, hr_sub⟩ := hx
      have ha_dense : Dense a.carrierᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact h_carrier_interior a
      have h_rest_dense : Dense (⋃ h ∈ (s : Set (AffineHyperplane E)), h.carrier)ᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact ih
      have hU_open : IsOpen (Metric.ball x r ∩ a.carrierᶜ) :=
        Metric.isOpen_ball.inter (h_carrier_closed a).isOpen_compl
      obtain ⟨z, hz_ball, hz_not_a⟩ := ha_dense.inter_open_nonempty
        (Metric.ball x r) Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr_pos⟩
      obtain ⟨w, ⟨hw_ball, hw_not_a⟩, hw_not_rest⟩ := h_rest_dense.inter_open_nonempty
        (Metric.ball x r ∩ a.carrierᶜ) hU_open ⟨z, hz_ball, hz_not_a⟩
      rcases hr_sub hw_ball with h | h
      · exact hw_not_a h
      · exact hw_not_rest h


  have h_compl_ne : (Metric.ball (0 : E) ε \ ⋃ h ∈ S, h.carrier).Nonempty := by
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h_empty

    have : Metric.ball (0 : E) ε ⊆ interior (⋃ h ∈ S, h.carrier) :=
      Metric.isOpen_ball.subset_interior_iff.mpr h_empty
    have h_ne : (interior (⋃ h ∈ S, h.carrier)).Nonempty :=
      ⟨0, this (Metric.mem_ball_self hε_pos)⟩
    rw [hS_union_interior] at h_ne
    exact Set.not_nonempty_empty h_ne

  obtain ⟨x₀, hx₀_ball, hx₀_not_S⟩ := h_compl_ne

  have hx₀_compl : x₀ ∈ W.arrangement.complement := by
    constructor
    · exact Set.mem_univ x₀
    · intro hx₀_union
      obtain ⟨h, hh_arr, hx₀_h⟩ := Set.mem_iUnion₂.mp hx₀_union

      have hh_S : h ∈ S := ⟨hh_arr, ⟨x₀, hx₀_ball, hx₀_h⟩⟩
      exact hx₀_not_S (Set.mem_biUnion hh_S hx₀_h)

  set F := W.arrangement.complement
  set CC := connectedComponentIn F x₀
  have hx₀_F : x₀ ∈ F := hx₀_compl
  exact ⟨{
    set := CC
    subset_complement := connectedComponentIn_subset F x₀
    isConnected := isConnected_connectedComponentIn_iff.mpr hx₀_F
    is_maximal := by
      intro S' hS'_sub hS'_conn hCC_sub

      have hx₀_S' : x₀ ∈ S' := hCC_sub (mem_connectedComponentIn hx₀_F)

      exact hS'_conn.isPreconnected.subset_connectedComponentIn hx₀_S' hS'_sub
  }⟩

/-- Alcoves are open in $E$: each point of $C$ has a small ball avoiding every
hyperplane locally near it, and the union with $C$ is connected and still in the
complement, hence is contained in $C$ by maximality. -/
theorem alcove_isOpen (hess : W.IsEssential) (hind : W.IsIndecomposable)
    (C : W.Alcove) : IsOpen C.set := by

  rw [isOpen_iff_forall_mem_open]
  intro x hx

  have hx_compl := C.subset_complement hx

  obtain ⟨ε₀, hε₀_pos, hfin⟩ := W.locallyFinite x

  have hx_not_on : ∀ h ∈ W.arrangement.hyperplanes, x ∉ h.carrier := by
    intro h hh habs
    have : x ∈ W.arrangement.unionSet := Set.mem_biUnion hh habs
    exact (hx_compl.2 this).elim

  have h_closed : ∀ h : AffineHyperplane E, IsClosed h.carrier := by
    intro h
    exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

  set S := {h ∈ W.arrangement.hyperplanes | (Metric.ball x ε₀ ∩ h.carrier).Nonempty}
  have hS_fin : S.Finite := hfin

  have h_S_union_closed : IsClosed (⋃ h ∈ S, h.carrier) := by
    exact hS_fin.isClosed_biUnion (fun h _ => h_closed h)

  have hx_not_in_S_union : x ∉ ⋃ h ∈ S, h.carrier := by
    intro habs
    obtain ⟨h, hh, hxh⟩ := Set.mem_iUnion₂.mp habs
    exact hx_not_on h hh.1 hxh

  obtain ⟨δ₁, hδ₁_pos, hδ₁_disj⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (h_S_union_closed.isOpen_compl.mem_nhds (Set.mem_compl hx_not_in_S_union))
  set δ := min δ₁ ε₀ with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hε₀_pos

  have h_ball_compl : Metric.ball x δ ⊆ W.arrangement.complement := by
    intro z hz
    constructor
    · exact Set.mem_univ z
    · intro hz_union
      obtain ⟨h, hh_arr, hz_carrier⟩ := Set.mem_iUnion₂.mp hz_union

      have hz_ball_ε : z ∈ Metric.ball x ε₀ :=
        Metric.ball_subset_ball (min_le_right _ _) hz
      have hh_S : h ∈ S := ⟨hh_arr, ⟨z, hz_ball_ε, hz_carrier⟩⟩

      have hz_ball_δ₁ : z ∈ Metric.ball x δ₁ :=
        Metric.ball_subset_ball (min_le_left _ _) hz
      have hz_not_union : z ∉ ⋃ h ∈ S, h.carrier := hδ₁_disj hz_ball_δ₁
      exact hz_not_union (Set.mem_biUnion hh_S hz_carrier)

  have h_ball_conn : IsConnected (Metric.ball x δ) :=
    (convex_ball x δ).isConnected (Metric.nonempty_ball.mpr hδ_pos)

  have h_inter_ne : (C.set ∩ Metric.ball x δ).Nonempty :=
    ⟨x, hx, Metric.mem_ball_self hδ_pos⟩
  have h_union_conn : IsConnected (C.set ∪ Metric.ball x δ) :=
    IsConnected.union h_inter_ne C.isConnected h_ball_conn

  have h_union_compl : C.set ∪ Metric.ball x δ ⊆ W.arrangement.complement :=
    Set.union_subset C.subset_complement h_ball_compl

  refine ⟨Metric.ball x δ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hδ_pos⟩
  exact fun y hy => C.is_maximal _ h_union_compl h_union_conn
    Set.subset_union_left (Set.subset_union_right hy)


/-- The "normal direction" of an affine hyperplane: the 1-dimensional submodule
spanned by its normal vector. Two parallel hyperplanes share the same normal
direction. -/
def normalDirection (η : AffineHyperplane E) : Submodule ℝ E :=
  Submodule.span ℝ {η.normal}





/-- Two hyperplanes with nonzero scalar-multiple normals have the same normal
direction. -/
lemma normalDirection_eq_of_smul_normal
    {η η' : AffineHyperplane E} {t : ℝ} (ht : t ≠ 0)
    (h : η'.normal = t • η.normal) :
    normalDirection η' = normalDirection η := by
  simp only [normalDirection]
  rw [h]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 t ht) η.normal


/-- If an affine isometry $g$ maps the carrier of $\eta$ bijectively to that of
$\eta'$, then the linear part sends vectors orthogonal to $\eta.\mathrm{normal}$
to vectors orthogonal to $\eta'.\mathrm{normal}$. -/
lemma stable_orthogonal_preserve
    (g : E ≃ᵃⁱ[ℝ] E) (η η' : AffineHyperplane E)
    (hη'_eq : ∀ x : E, g x ∈ η'.carrier ↔ x ∈ η.carrier)
    (v : E) (hv : @inner ℝ _ _ η.normal v = 0) :
    @inner ℝ _ _ η'.normal ((AffineIsometryEquiv.linearIsometryEquiv g) v) = 0 := by

  have hx₀ : ∃ x₀ : E, x₀ ∈ η.carrier := by
    use (η.offset / @inner ℝ _ _ η.normal η.normal) • η.normal
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr η.normal_ne_zero)
  obtain ⟨x₀, hx₀_mem⟩ := hx₀
  set wbar := AffineIsometryEquiv.linearIsometryEquiv g with wbar_def
  have hgx₀ : g x₀ ∈ η'.carrier := (hη'_eq x₀).mpr hx₀_mem
  have hxv : x₀ + v ∈ η.carrier := by
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hx₀_mem ⊢
    rw [inner_add_right, hv, add_zero]; exact hx₀_mem
  have hgxv : g (x₀ + v) ∈ η'.carrier := (hη'_eq (x₀ + v)).mpr hxv

  have hg_add : g (x₀ + v) = g x₀ + wbar v := by
    have h := AffineIsometryEquiv.map_vsub g (x₀ + v) x₀
    simp only [vsub_eq_sub, add_sub_cancel_left] at h

    have : g (x₀ + v) - g x₀ = wbar v := by
      rw [← vsub_eq_sub]; exact h.symm
    rw [← this]; abel
  rw [hg_add] at hgxv
  simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hgx₀ hgxv
  rw [inner_add_right] at hgxv; linarith

/-- Inner-product characterisation of $\mathrm{span}\{a\}$: if every vector
orthogonal to $a$ is also orthogonal to $b$, then $b \in \mathrm{span}\{a\}$. -/
lemma mem_span_singleton_of_orthogonal_implication
    (a b : E) (ha : a ≠ 0)
    (h : ∀ v : E, @inner ℝ _ _ a v = 0 → @inner ℝ _ _ b v = 0) :
    b ∈ Submodule.span ℝ {a} := by
  rw [Submodule.mem_span_singleton]
  use @inner ℝ _ _ b a / @inner ℝ _ _ a a
  have ha_sq_ne : @inner ℝ _ _ a a ≠ (0 : ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)

  set c := @inner ℝ _ _ b a / @inner ℝ _ _ a a
  set diff := b - c • a
  suffices h_zero : diff = 0 by rw [sub_eq_zero] at h_zero; exact h_zero.symm
  rw [← @inner_self_eq_zero ℝ]

  have h_diff_a : @inner ℝ _ _ diff a = 0 := by
    show @inner ℝ _ _ (b - c • a) a = 0
    rw [inner_sub_left, inner_smul_left, conj_trivial, div_mul_cancel₀ _ ha_sq_ne, sub_self]

  have h_a_diff : @inner ℝ _ _ a diff = 0 := by rw [real_inner_comm]; exact h_diff_a
  have h_b_diff : @inner ℝ _ _ b diff = 0 := h diff h_a_diff

  show @inner ℝ _ _ diff diff = 0
  rw [show diff = b - c • a from rfl, inner_sub_left, inner_smul_left, conj_trivial,
    h_b_diff, h_a_diff, mul_zero, sub_zero]

/-- The linear-part group permutes the set of normal directions of the
hyperplane arrangement: $\bar w(\mathrm{normalDirection}(\eta))$ is again the
normal direction of some hyperplane in the arrangement. -/
theorem linearPart_permutes_normalDirections (W : AffineReflectionGroup E)
    (wbar : E ≃ₗᵢ[ℝ] E) (hwbar : wbar ∈ W.LinearPartGroup)
    (d : Submodule ℝ E) (hd : d ∈ normalDirection '' W.arrangement.hyperplanes) :
    Submodule.map wbar.toLinearEquiv.toLinearMap d ∈
      normalDirection '' W.arrangement.hyperplanes := by
  obtain ⟨η, hη_arr, rfl⟩ := hd
  rw [AffineReflectionGroup.LinearPartGroup, Subgroup.mem_map] at hwbar
  obtain ⟨g, hg_mem, hg_eq⟩ := hwbar
  obtain ⟨η', hη'_arr, hη'_eq⟩ := W.stable g hg_mem η hη_arr
  refine ⟨η', hη'_arr, ?_⟩
  simp only [normalDirection, Submodule.map_span, Set.image_singleton]


  have hwbar_eq : AffineIsometryEquiv.linearIsometryEquiv g = wbar := by
    exact_mod_cast hg_eq

  have h1 : η'.normal ∈ Submodule.span ℝ ({(wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal} : Set E) := by
    apply mem_span_singleton_of_orthogonal_implication
    · intro h; exact η.normal_ne_zero (wbar.injective (by simp [show (wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal = wbar η.normal from rfl] at h; rw [h, map_zero]))
    · intro v hv

      have h_inv : @inner ℝ _ _ η.normal (wbar.symm v) = 0 := by
        have hi := LinearIsometryEquiv.inner_map_map wbar η.normal (wbar.symm v)
        simp [LinearIsometryEquiv.apply_symm_apply] at hi
        rw [← hi]; convert hv using 2

      have := stable_orthogonal_preserve g η η' hη'_eq (wbar.symm v) h_inv
      rw [hwbar_eq] at this
      simp [LinearIsometryEquiv.apply_symm_apply] at this
      exact this

  have h2 : (wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal ∈ Submodule.span ℝ ({η'.normal} : Set E) := by
    apply mem_span_singleton_of_orthogonal_implication
    · exact η'.normal_ne_zero
    · intro v hv


      suffices h_goal : @inner ℝ _ _ η.normal (wbar.symm v) = 0 by
        have hi := LinearIsometryEquiv.inner_map_map wbar η.normal (wbar.symm v)
        simp [LinearIsometryEquiv.apply_symm_apply] at hi
        have : (wbar.toLinearEquiv : E →ₗ[ℝ] E) η.normal = wbar η.normal := rfl
        rw [this, hi]; exact h_goal


      have hη_inv : ∀ x : E, (g⁻¹ : E ≃ᵃⁱ[ℝ] E) x ∈ η.carrier ↔ x ∈ η'.carrier := by
        intro x; constructor
        · intro hx
          have := (hη'_eq ((g⁻¹ : E ≃ᵃⁱ[ℝ] E) x)).mpr hx
          rwa [show (g : E ≃ᵃⁱ[ℝ] E) ((g⁻¹ : E ≃ᵃⁱ[ℝ] E) x) = x from by
            show (g * g⁻¹ : E ≃ᵃⁱ[ℝ] E) x = x; rw [mul_inv_cancel]; rfl] at this
        · intro hx; rw [← hη'_eq]
          show (g * g⁻¹ : E ≃ᵃⁱ[ℝ] E) x ∈ η'.carrier
          rw [mul_inv_cancel]; exact hx

      have h_lin_inv : AffineIsometryEquiv.linearIsometryEquiv g⁻¹ = wbar.symm := by
        have : linearPartHom g⁻¹ = (linearPartHom g)⁻¹ := map_inv linearPartHom g
        rw [hg_eq] at this
        ext v; show AffineIsometryEquiv.linearIsometryEquiv g⁻¹ v = wbar.symm v
        have hv := congr_fun (congr_arg (↑·) this) v
        simp only [LinearIsometryEquiv.coe_inv, linearPartHom, MonoidHom.coe_mk, OneHom.coe_mk] at hv
        exact hv

      have := stable_orthogonal_preserve g⁻¹ η' η hη_inv v hv
      rw [h_lin_inv] at this
      exact this
  apply le_antisymm
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact h1
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact h2

/-- An isometry that fixes the line $\mathbb R n$ sends $n$ to either $n$ or
$-n$, since $|a| = 1$ for the scalar $a$ with $\bar w n = a n$. -/
lemma isometry_fixes_span_pm (wbar : E ≃ₗᵢ[ℝ] E) (n : E) (hn : n ≠ 0)
    (h : Submodule.map wbar.toLinearEquiv.toLinearMap (Submodule.span ℝ {n}) =
         Submodule.span ℝ {n}) :
    wbar n = n ∨ wbar n = -n := by
  have hmem : wbar n ∈ Submodule.span ℝ ({n} : Set E) := by
    rw [← h]
    exact Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_singleton n))
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hnorm : ‖wbar n‖ = ‖n‖ := wbar.norm_map n
  rw [← ha, norm_smul, Real.norm_eq_abs] at hnorm
  have hn_pos : (0 : ℝ) < ‖n‖ := norm_pos_iff.mpr hn
  have ha_abs : |a| = 1 := by nlinarith [hn_pos]
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha_abs with h1 | h1
  · left; rw [← ha, h1, one_smul]
  · right; rw [← ha, h1, neg_one_smul]

/-- The linear part of an affine reflection $s$ across $\eta$ fixes every vector
orthogonal to the normal of $\eta$. -/
lemma reflection_linearPart_fixes_orthogonal
    (s : E ≃ᵃⁱ[ℝ] E) (η : AffineHyperplane E)
    (hs_fix : ∀ y ∈ η.carrier, s y = y) (hs_inv : s * s = 1)
    (v : E) (hv : @inner ℝ _ _ η.normal v = 0) :
    (linearPartHom s : E ≃ₗᵢ[ℝ] E) v = v := by

  have ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ∈ η.carrier := by
    use (η.offset / @inner ℝ _ _ η.normal η.normal) • η.normal
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr η.normal_ne_zero)

  have hxv : x₀ + v ∈ η.carrier := by
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hx₀ ⊢
    rw [inner_add_right, hv, add_zero]; exact hx₀

  have hs_x₀ : s x₀ = x₀ := hs_fix x₀ hx₀
  have hs_xv : s (x₀ + v) = x₀ + v := hs_fix (x₀ + v) hxv

  change AffineIsometryEquiv.linearIsometryEquiv s v = v
  have h := AffineIsometryEquiv.map_vsub s (x₀ + v) x₀
  simp only [vsub_eq_sub, add_sub_cancel_left] at h
  rw [h, hs_xv, hs_x₀, add_sub_cancel_left]

/-- A consequence of essentiality: a vector orthogonal to every hyperplane normal
is zero, since the only $\bar W$-invariant vector is $0$. -/
lemma orthogonal_to_normals_eq_zero
    (hess : W.IsEssential) (w : E)
    (hw : ∀ η ∈ W.arrangement.hyperplanes, @inner ℝ _ _ η.normal w = 0) :
    w = 0 := by

  apply hess w
  intro wbar hwbar_mem

  rw [AffineReflectionGroup.LinearPartGroup, Subgroup.mem_map] at hwbar_mem
  obtain ⟨g, hg_mem, hg_eq⟩ := hwbar_mem
  rw [W.generated_by_reflections] at hg_mem
  suffices h_refl : ∀ s, s ∈ Subgroup.closure
      {s | s ∈ W.group ∧ ∃ η ∈ W.arrangement.hyperplanes,
        (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1} →
      (linearPartHom s : E ≃ₗᵢ[ℝ] E) w = w by
    have := h_refl g hg_mem
    show wbar w = w
    rw [← hg_eq]; exact this
  apply Subgroup.closure_induction
  · intro s hs
    obtain ⟨_, η, hη, hs_fix, hs_inv⟩ := hs
    have hv_orth : @inner ℝ _ _ η.normal w = 0 := hw η hη
    exact reflection_linearPart_fixes_orthogonal s η hs_fix hs_inv w hv_orth
  ·
    rfl
  · intro s₁ s₂ _ _ ih₁ ih₂
    simp only [map_mul, LinearIsometryEquiv.coe_mul] at ih₁ ih₂ ⊢
    rw [Function.comp_apply, ih₂, ih₁]
  · intro s _ ih
    have hinv : linearPartHom s⁻¹ = (linearPartHom s)⁻¹ := map_inv linearPartHom s
    simp only [hinv, LinearIsometryEquiv.coe_inv]
    have := congr_arg (linearPartHom s).symm ih
    simp only [LinearIsometryEquiv.symm_apply_apply] at this
    exact this.symm

/-- If an isometry sends $n_1$ to $\varepsilon_1 n_1$ and $n_2$ to
$\varepsilon_2 n_2$ with $\varepsilon_i \in \{\pm 1\}$ and $\varepsilon_1 \neq
\varepsilon_2$, then $n_1 \perp n_2$. -/
lemma inner_eq_zero_of_different_signs
    (wbar : E ≃ₗᵢ[ℝ] E) (n₁ n₂ : E)
    (ε₁ ε₂ : ℝ) (h1 : wbar n₁ = ε₁ • n₁) (h2 : wbar n₂ = ε₂ • n₂)
    (hne : ε₁ ≠ ε₂)
    (hε1 : ε₁ = 1 ∨ ε₁ = -1) (hε2 : ε₂ = 1 ∨ ε₂ = -1) :
    @inner ℝ _ _ n₁ n₂ = 0 := by
  have preserve := LinearIsometryEquiv.inner_map_map wbar n₁ n₂
  rw [h1, h2] at preserve
  simp only [inner_smul_left, inner_smul_right, conj_trivial] at preserve
  have hprod : ε₁ * ε₂ = -1 := by
    rcases hε1 with rfl | rfl <;> rcases hε2 with rfl | rfl <;> simp at hne ⊢
  have : ε₂ * (ε₁ * @inner ℝ _ _ n₁ n₂) = (ε₁ * ε₂) * @inner ℝ _ _ n₁ n₂ := by ring
  rw [this, hprod] at preserve
  linarith

/-- The linear-isometry part of an affine isometry that pointwise fixes $\eta$
fixes every vector orthogonal to $\eta.\mathrm{normal}$. -/
lemma linearIsometryEquiv_fixes_orthogonal
    (s : E ≃ᵃⁱ[ℝ] E) (η : AffineHyperplane E)
    (hfix : ∀ y ∈ η.carrier, s y = y) (v : E)
    (hv : @inner ℝ _ _ η.normal v = 0) :
    s.linearIsometryEquiv v = v := by
  have hp := η.basePoint_mem_carrier
  have hpv : η.basePoint + v ∈ η.carrier := by
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, inner_add_right, hv, add_zero]
    exact hp
  have key : s.linearIsometryEquiv v = s (η.basePoint + v) -ᵥ s η.basePoint := by
    rw [← AffineIsometryEquiv.map_vsub s (η.basePoint + v) η.basePoint]
    simp [vsub_eq_sub, add_sub_cancel_left]
  rw [key, hfix _ hpv, hfix _ hp]
  simp [vsub_eq_sub, add_sub_cancel_left]

/-- Reconstruction formula: if $s$ fixes $p$, then $s(x) = s_{\mathrm{lin}}(x-p)+p$. -/
lemma affineIsometryEquiv_eq_linear_sub_add
    (s : E ≃ᵃⁱ[ℝ] E) (p x : E) (hp : s p = p) :
    s x = s.linearIsometryEquiv (x - p) + p := by
  have h := AffineIsometryEquiv.map_vsub s x p
  change s.linearIsometryEquiv (x -ᵥ p) = s x -ᵥ s p at h
  rw [vsub_eq_sub, vsub_eq_sub, hp] at h
  rw [h]; abel

/-- If $s$ fixes $\eta'$ and the two normals $\eta.\mathrm{normal}$ and
$\eta'.\mathrm{normal}$ are orthogonal, then $s$ preserves the inner product
$\langle \eta.\mathrm{normal}, \cdot\rangle$. -/
lemma inner_affineIsometry_eq
    (s : E ≃ᵃⁱ[ℝ] E) (η η' : AffineHyperplane E)
    (hfix : ∀ y ∈ η'.carrier, s y = y)
    (horth : @inner ℝ _ _ η.normal η'.normal = 0) (x : E) :
    @inner ℝ _ _ η.normal (s x) = @inner ℝ _ _ η.normal x := by
  have hLn : s.linearIsometryEquiv η.normal = η.normal :=
    linearIsometryEquiv_fixes_orthogonal s η' hfix η.normal
      (real_inner_comm η'.normal η.normal ▸ horth)
  have hinner_L (y : E) : @inner ℝ _ _ η.normal (s.linearIsometryEquiv y) =
      @inner ℝ _ _ η.normal y := by
    conv_lhs => rw [← hLn]; exact LinearIsometryEquiv.inner_map_map _ _ _
  have hp := hfix _ η'.basePoint_mem_carrier
  rw [affineIsometryEquiv_eq_linear_sub_add s η'.basePoint x hp,
      inner_add_right, hinner_L, inner_sub_right]
  linarith

/-- If the linear part of $s$ fixes $y - x$, then $s$ translates $x$ to
$y$ by the same vector: $s(y) = s(x) + (y - x)$. -/
lemma affineIsometryEquiv_add_diff
    (s : E ≃ᵃⁱ[ℝ] E) (x y : E)
    (hfix : s.linearIsometryEquiv (y - x) = y - x) :
    s y = s x + (y - x) := by
  have h := AffineIsometryEquiv.map_vsub s y x
  change s.linearIsometryEquiv (y -ᵥ x) = s y -ᵥ s x at h
  rw [vsub_eq_sub, vsub_eq_sub, hfix] at h
  rw [h]; abel

/-- Two affine reflections whose hyperplane normals are orthogonal commute: this
is the classical commutativity criterion $s_{\eta_1} s_{\eta_2} = s_{\eta_2}
s_{\eta_1}$ when $\eta_1 \perp \eta_2$. -/
theorem affine_reflections_commute_of_orthogonal_normals
    (s₁ s₂ : E ≃ᵃⁱ[ℝ] E)
    (η₁ η₂ : AffineHyperplane E)
    (h₁_fix : ∀ y ∈ η₁.carrier, s₁ y = y) (h₁_inv : s₁ * s₁ = 1)
    (h₂_fix : ∀ y ∈ η₂.carrier, s₂ y = y) (h₂_inv : s₂ * s₂ = 1)
    (horth : @inner ℝ _ _ η₁.normal η₂.normal = 0) :
    s₁ * s₂ = s₂ * s₁ := by
  ext x
  simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply]
  have horth' : @inner ℝ _ _ η₂.normal η₁.normal = 0 := by
    rw [real_inner_comm]; exact horth

  have hL₁ : s₁.linearIsometryEquiv (s₂ x - x) = s₂ x - x :=
    linearIsometryEquiv_fixes_orthogonal s₁ η₁ h₁_fix (s₂ x - x)
      (by rw [inner_sub_right]; linarith [inner_affineIsometry_eq s₂ η₁ η₂ h₂_fix horth x])

  have hL₂ : s₂.linearIsometryEquiv (s₁ x - x) = s₁ x - x :=
    linearIsometryEquiv_fixes_orthogonal s₂ η₂ h₂_fix (s₁ x - x)
      (by rw [inner_sub_right]; linarith [inner_affineIsometry_eq s₁ η₂ η₁ h₁_fix horth' x])

  rw [affineIsometryEquiv_add_diff s₁ x (s₂ x) hL₁,
      affineIsometryEquiv_add_diff s₂ x (s₁ x) hL₂]
  abel

/-- An affine reflection group is `NegIdFree` if the linear-part group does not
contain the negation $-\mathrm{id}_E$. This rules out the "$\bar W = \{\pm 1\}$"
degeneracy that would obstruct faithfulness of $\bar W$ on normal directions. -/
class NegIdFree (W : AffineReflectionGroup E) : Prop where
  neg_id_not_mem : ∀ (wbar : E ≃ₗᵢ[ℝ] E), wbar ∈ W.LinearPartGroup →
    (∀ v : E, wbar v = -v) → False







/-- Every point of $E$ is in the closure of some alcove: this is a key step
toward the cover-by-translates theorem, using a small ball around $x$ avoiding
the locally finite hyperplane union and a segment argument to find a nearby
point in the complement. -/
lemma arrangement_closure_covers (x : E) :
    ∃ D : W.Alcove, x ∈ closure D.set := by

  have h_carrier_closed : ∀ h : AffineHyperplane E, IsClosed h.carrier :=
    fun h => isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have h_carrier_interior : ∀ h : AffineHyperplane E, interior h.carrier = ∅ := by
    intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
    obtain ⟨r, hr_pos, hr_sub⟩ := hz
    have hn_ne : h.normal ≠ 0 := h.normal_ne_zero
    have hn_pos : 0 < ‖h.normal‖ := norm_pos_iff.mpr hn_ne
    set w := z + (r / (2 * ‖h.normal‖)) • h.normal
    have hw_ball : w ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr_pos (mul_pos two_pos hn_pos))]
      field_simp; linarith
    have hw_carrier : w ∉ h.carrier := by
      simp only [AffineHyperplane.carrier, Set.mem_setOf_eq, w]
      rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      have hz_on : ⟪h.normal, z⟫_ℝ = h.offset := by
        have := hr_sub (Metric.mem_ball_self hr_pos)
        simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at this
        exact this
      rw [hz_on]
      intro heq
      have h1 : r / (2 * ‖h.normal‖) > 0 := div_pos hr_pos (mul_pos two_pos hn_pos)
      have h2 : ‖h.normal‖ ^ 2 > 0 := pow_pos hn_pos 2
      linarith [mul_pos h1 h2]
    exact hw_carrier (hr_sub hw_ball)

  obtain ⟨ε, hε_pos, hS_fin⟩ := W.locallyFinite x
  set S := {h ∈ W.arrangement.hyperplanes | (Metric.ball x ε ∩ h.carrier).Nonempty}

  have hS_union_interior : interior (⋃ h ∈ S, h.carrier) = ∅ := by
    classical
    set T := hS_fin.toFinset
    have hST : S = ↑T := (Set.Finite.coe_toFinset hS_fin).symm
    rw [hST]
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.coe_insert, Set.biUnion_insert, Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
      obtain ⟨r, hr_pos, hr_sub⟩ := hz
      have ha_dense : Dense a.carrierᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact h_carrier_interior a
      have h_rest_dense : Dense (⋃ h ∈ (s : Set (AffineHyperplane E)), h.carrier)ᶜ := by
        rw [← interior_eq_empty_iff_dense_compl]; exact ih
      have hU_open : IsOpen (Metric.ball z r ∩ a.carrierᶜ) :=
        Metric.isOpen_ball.inter (h_carrier_closed a).isOpen_compl
      obtain ⟨p, hp_ball, hp_not_a⟩ := ha_dense.inter_open_nonempty
        (Metric.ball z r) Metric.isOpen_ball ⟨z, Metric.mem_ball_self hr_pos⟩
      obtain ⟨q, ⟨hq_ball, hq_not_a⟩, hq_not_rest⟩ := h_rest_dense.inter_open_nonempty
        (Metric.ball z r ∩ a.carrierᶜ) hU_open ⟨p, hp_ball, hp_not_a⟩
      rcases hr_sub hq_ball with hcase | hcase
      · exact hq_not_a hcase
      · exact hq_not_rest hcase

  have h_find_compl : ∀ r : ℝ, 0 < r → r ≤ ε →
      (Metric.ball x r \ ⋃ h ∈ S, h.carrier).Nonempty := by
    intro r hr_pos _hr_le
    by_contra h_empty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h_empty
    have : Metric.ball x r ⊆ interior (⋃ h ∈ S, h.carrier) :=
      Metric.isOpen_ball.subset_interior_iff.mpr h_empty
    have h_ne : (interior (⋃ h ∈ S, h.carrier)).Nonempty :=
      ⟨x, this (Metric.mem_ball_self hr_pos)⟩
    rw [hS_union_interior] at h_ne
    exact Set.not_nonempty_empty h_ne

  have h_in_compl : ∀ y, y ∈ Metric.ball x ε → y ∉ ⋃ h ∈ S, h.carrier →
      y ∈ W.arrangement.complement := by
    intro y hy_ball hy_not_S
    constructor
    · exact Set.mem_univ y
    · intro hy_union
      obtain ⟨h, hh_arr, hy_h⟩ := Set.mem_iUnion₂.mp hy_union
      have hh_S : h ∈ S := ⟨hh_arr, ⟨y, hy_ball, hy_h⟩⟩
      exact hy_not_S (Set.mem_biUnion hh_S hy_h)

  obtain ⟨y₀, hy₀_ball, hy₀_not_S⟩ :=
    h_find_compl (ε / 2) (half_pos hε_pos) (half_le_self (le_of_lt hε_pos))
  have hy₀_in_big_ball : y₀ ∈ Metric.ball x ε :=
    Metric.ball_subset_ball (half_le_self (le_of_lt hε_pos)) hy₀_ball
  have hy₀_compl : y₀ ∈ W.arrangement.complement :=
    h_in_compl y₀ hy₀_in_big_ball hy₀_not_S

  by_cases hxy : x = y₀
  ·
    subst hxy
    set F := W.arrangement.complement
    set CC := connectedComponentIn F x
    have hx_F : x ∈ F := hy₀_compl
    refine ⟨{
      set := CC
      subset_complement := connectedComponentIn_subset F x
      isConnected := isConnected_connectedComponentIn_iff.mpr hx_F
      is_maximal := by
        intro S' hS'_sub hS'_conn hCC_sub
        have hx_S' : x ∈ S' := hCC_sub (mem_connectedComponentIn hx_F)
        exact hS'_conn.isPreconnected.subset_connectedComponentIn hx_S' hS'_sub
    }, ?_⟩
    exact subset_closure (mem_connectedComponentIn hx_F)
  ·


    have hy₀_ne : y₀ - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)

    have h_crossing_finite : (⋃ h ∈ S,
        if ⟪h.normal, y₀ - x⟫_ℝ = 0 then ∅
        else {(h.offset - ⟪h.normal, x⟫_ℝ) / ⟪h.normal, y₀ - x⟫_ℝ}).Finite := by
      apply Set.Finite.biUnion hS_fin
      intro h _
      split_ifs with hif
      · exact Set.finite_empty
      · exact Set.finite_singleton _
    set crossingTimes := ⋃ h ∈ S,
      if ⟪h.normal, y₀ - x⟫_ℝ = 0 then ∅
      else {(h.offset - ⟪h.normal, x⟫_ℝ) / ⟪h.normal, y₀ - x⟫_ℝ}
    set posCT := crossingTimes ∩ Set.Ioi (0 : ℝ)
    have hposCT_finite : posCT.Finite := h_crossing_finite.subset Set.inter_subset_left

    have h_exists_delta : ∃ δ > 0, δ < 1 ∧ ∀ t : ℝ, 0 < t → t < δ →
        ∀ h ∈ S, ⟪h.normal, x + t • (y₀ - x)⟫_ℝ ≠ h.offset := by

      have h_crossing_mem : ∀ (t : ℝ) (h : AffineHyperplane E), h ∈ S →
          ⟪h.normal, x + t • (y₀ - x)⟫_ℝ = h.offset → 0 < t → t ∈ posCT := by
        intro t h hh_S heq ht_pos
        constructor
        · simp only [crossingTimes, Set.mem_iUnion₂]
          refine ⟨h, hh_S, ?_⟩
          have h_inner_ne : ⟪h.normal, y₀ - x⟫_ℝ ≠ 0 := by
            intro h_eq_zero

            rw [inner_add_right, inner_smul_right, h_eq_zero, mul_zero, add_zero] at heq

            have hy₀_on : y₀ ∈ h.carrier := by
              simp only [AffineHyperplane.carrier, Set.mem_setOf_eq]
              rw [inner_sub_right] at h_eq_zero
              linarith
            exact hy₀_not_S (Set.mem_biUnion hh_S hy₀_on)
          rw [if_neg h_inner_ne]
          rw [Set.mem_singleton_iff]
          rw [inner_add_right, inner_smul_right] at heq
          field_simp
          linarith
        · exact ht_pos
      by_cases hposCT_empty : posCT = ∅
      · refine ⟨1/2, one_half_pos, one_half_lt_one, ?_⟩
        intro t ht_pos ht_lt h hh_S heq
        have ht_posCT := h_crossing_mem t h hh_S heq ht_pos
        rw [hposCT_empty] at ht_posCT
        exact absurd ht_posCT (Set.notMem_empty _)
      · have hposCT_ne : posCT.Nonempty := Set.nonempty_iff_ne_empty.mpr hposCT_empty
        set m := hposCT_finite.toFinset.min' (by rwa [Set.Finite.toFinset_nonempty])
        have hm_mem : m ∈ posCT := by
          rw [← Set.Finite.mem_toFinset hposCT_finite]
          exact Finset.min'_mem _ _
        have hm_pos : 0 < m := hm_mem.2
        refine ⟨min (m / 2) (1 / 2), lt_min (half_pos hm_pos) one_half_pos,
          lt_of_le_of_lt (min_le_right _ _) one_half_lt_one, ?_⟩
        intro t ht_pos ht_lt h hh_S heq
        have ht_posCT := h_crossing_mem t h hh_S heq ht_pos
        have ht_ge_m : m ≤ t := by
          exact Finset.min'_le _ _ (Set.Finite.mem_toFinset hposCT_finite |>.mpr ht_posCT)
        have : t < m / 2 := lt_of_lt_of_le ht_lt (min_le_left _ _)
        linarith
    obtain ⟨δ, hδ_pos, hδ_lt_one, h_no_cross⟩ := h_exists_delta

    have h_seg_compl : ∀ t : ℝ, 0 < t → t < δ →
        x + t • (y₀ - x) ∈ W.arrangement.complement := by
      intro t ht_pos ht_lt
      constructor
      · exact Set.mem_univ _
      · intro h_union
        obtain ⟨h, hh_arr, hh_mem⟩ := Set.mem_iUnion₂.mp h_union
        simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hh_mem

        have hy₀_dist : dist y₀ x < ε / 2 := by
          exact Metric.mem_ball.mp hy₀_ball
        have h_pt_ball : x + t • (y₀ - x) ∈ Metric.ball x ε := by
          rw [Metric.mem_ball, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
          calc t * ‖y₀ - x‖ < 1 * ‖y₀ - x‖ := by
                apply mul_lt_mul_of_pos_right (lt_trans ht_lt hδ_lt_one)
                exact norm_pos_iff.mpr hy₀_ne
              _ = ‖y₀ - x‖ := one_mul _
              _ = dist y₀ x := (dist_eq_norm y₀ x).symm
              _ < ε / 2 := hy₀_dist
              _ ≤ ε := half_le_self (le_of_lt hε_pos)
        have hh_S : h ∈ S := ⟨hh_arr, ⟨x + t • (y₀ - x), h_pt_ball, by
          simp only [AffineHyperplane.carrier, Set.mem_setOf_eq]; exact hh_mem⟩⟩
        exact h_no_cross t ht_pos ht_lt h hh_S hh_mem

    set seg := (fun t => x + t • (y₀ - x)) '' Set.Ioo 0 δ
    have h_seg_conn : IsConnected seg := by
      apply IsConnected.image
      · exact isConnected_Ioo (by linarith)
      · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    have h_seg_ne : seg.Nonempty :=
      ⟨x + (δ/2) • (y₀ - x), ⟨δ/2, ⟨half_pos hδ_pos, by linarith⟩, rfl⟩⟩
    have h_seg_sub_compl : seg ⊆ W.arrangement.complement := by
      rintro _ ⟨t, ⟨ht_pos, ht_lt⟩, rfl⟩
      exact h_seg_compl t ht_pos ht_lt

    obtain ⟨z₀, hz₀⟩ := h_seg_ne
    have hz₀_compl : z₀ ∈ W.arrangement.complement := h_seg_sub_compl hz₀
    set F := W.arrangement.complement
    set CC := connectedComponentIn F z₀
    have hz₀_F : z₀ ∈ F := hz₀_compl
    set D : W.Alcove := {
      set := CC
      subset_complement := connectedComponentIn_subset F z₀
      isConnected := isConnected_connectedComponentIn_iff.mpr hz₀_F
      is_maximal := by
        intro S' hS'_sub hS'_conn hCC_sub
        have hz₀_S' : z₀ ∈ S' := hCC_sub (mem_connectedComponentIn hz₀_F)
        exact hS'_conn.isPreconnected.subset_connectedComponentIn hz₀_S' hS'_sub
    }
    refine ⟨D, ?_⟩


    have h_seg_sub_CC : seg ⊆ CC :=
      h_seg_conn.isPreconnected.subset_connectedComponentIn hz₀ h_seg_sub_compl

    rw [mem_closure_iff]
    intro U hU_open hx_U

    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU_open x hx_U

    have hy₀_norm_pos : 0 < ‖y₀ - x‖ := norm_pos_iff.mpr hy₀_ne
    set t₀ := min (δ / 2) (r / (2 * ‖y₀ - x‖))
    have ht₀_pos : 0 < t₀ := lt_min (half_pos hδ_pos) (div_pos hr_pos (by positivity))
    have ht₀_lt_δ : t₀ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    set p := x + t₀ • (y₀ - x)
    have hp_seg : p ∈ seg := ⟨t₀, ⟨ht₀_pos, ht₀_lt_δ⟩, rfl⟩
    have hp_CC : p ∈ CC := h_seg_sub_CC hp_seg
    have hp_ball : p ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [p, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht₀_pos]
      calc t₀ * ‖y₀ - x‖
          ≤ r / (2 * ‖y₀ - x‖) * ‖y₀ - x‖ := by
            apply mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ = r / 2 := by field_simp
        _ < r := by linarith
    exact ⟨p, hr_sub hp_ball, hp_CC⟩




end AffineReflectionGroup

namespace AffineWeylGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (Wa : AffineWeylGroup E)

/-- For an affine Weyl group, the parallel-through-origin hyperplane of any
arrangement hyperplane $\eta$ is itself in the arrangement (it corresponds to
the integer offset $k = 0$ for the root $\alpha = \eta.\mathrm{normal}$). -/
theorem origin_hyperplane_in_arrangement
    (η : AffineHyperplane E) (hη : η ∈ Wa.reflGroup.arrangement.hyperplanes) :
    ⟨η.normal, 0, η.normal_ne_zero⟩ ∈ Wa.reflGroup.arrangement.hyperplanes := by
  rw [Wa.arrangement_eq] at hη ⊢
  simp only [AffineWeylGroupData.affineArrangement, Set.mem_setOf_eq] at hη ⊢
  obtain ⟨α, hα_mem, _, hα_eq, _⟩ := hη
  exact ⟨α, hα_mem, 0, hα_eq, Int.cast_zero.symm⟩

/-- The origin is a special point of the affine Weyl group: for each hyperplane
$\eta$ there is a parallel hyperplane in the arrangement passing through $0$. -/
theorem special_point_exists
    (hess : Wa.reflGroup.IsEssential) (hind : Wa.reflGroup.IsIndecomposable) :
    Wa.reflGroup.SpecialPoint (0 : E) := by
  intro η hη
  refine ⟨⟨η.normal, 0, η.normal_ne_zero⟩,
    Wa.origin_hyperplane_in_arrangement η hη,
    ⟨1, ?_⟩, ?_⟩
  · exact (one_smul ℝ η.normal).symm
  · simp [AffineHyperplane.carrier, inner_zero_right]

end AffineWeylGroup

namespace AffineWeylGroupData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (d : AffineWeylGroupData E)

/-- Extensionality for affine hyperplanes: two affine hyperplanes are equal iff
their `normal` and `offset` fields agree. -/
theorem AffineHyperplane_ext (h1 h2 : AffineHyperplane E)
    (hn : h1.normal = h2.normal) (ho : h1.offset = h2.offset) :
    h1 = h2 := by
  cases h1; cases h2; simp_all

/-- The affine arrangement $\{H_{\alpha,k} : \alpha \in \Phi, k \in \mathbb Z\}$
is locally finite: around any point $x$, only finitely many hyperplanes meet the
unit ball, because $|k - \langle \alpha, x \rangle| < \|\alpha\| + 1$ bounds $k$
to a finite range for each fixed root $\alpha$ in the finite root set. -/
theorem affineArrangement_locallyFinite
    (hfin : Set.Finite d.roots) :
    d.affineArrangement.IsLocallyFinite := by
  intro x
  refine ⟨1, one_pos, ?_⟩


  have hS_fin : Set.Finite (⋃ α ∈ d.roots,
    ⋃ k ∈ {k : ℤ | |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1},
      ({⟨α, ↑k, d.roots_ne_zero α ‹_›⟩} : Set (AffineHyperplane E))) := by
    apply Set.Finite.biUnion' hfin
    intro α hα
    apply Set.Finite.biUnion
    · apply Set.Finite.subset (Set.finite_Icc
        (⌊⟪α, x⟫_ℝ - (‖α‖ + 1)⌋)
        (⌈⟪α, x⟫_ℝ + (‖α‖ + 1)⌉))
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      simp only [Set.mem_Icc]
      have hk_abs := abs_sub_lt_iff.mp hk
      exact ⟨Int.floor_le_iff.mpr (by linarith [hk_abs.2]),
             (Int.le_ceil_iff.mpr (by linarith [hk_abs.1]))⟩
    · intro _ _; exact Set.finite_singleton _
  apply hS_fin.subset
  intro η ⟨hη_arr, hη_meet⟩
  obtain ⟨y, hy_ball, hy_carrier⟩ := hη_meet
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη_arr
  simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hy_carrier
  rw [Metric.mem_ball] at hy_ball
  have h_cs : |⟪α, y - x⟫_ℝ| ≤ ‖α‖ * ‖y - x‖ := abs_real_inner_le_norm α (y - x)
  have h_dist : ‖y - x‖ < 1 := by rwa [← dist_eq_norm]
  have h_bound : |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1 := by
    have h1 : ⟪η.normal, y⟫_ℝ = η.offset := hy_carrier
    rw [hα_eq] at h1
    calc |↑k - ⟪α, x⟫_ℝ|
        = |⟪α, y⟫_ℝ - ⟪α, x⟫_ℝ| := by congr 1; linarith [h1, hk_eq]
      _ = |⟪α, y - x⟫_ℝ| := by rw [inner_sub_right]
      _ ≤ ‖α‖ * ‖y - x‖ := h_cs
      _ < ‖α‖ * 1 := by
          rcases eq_or_lt_of_le (norm_nonneg α) with h0 | h0
          · exfalso
            have : α = 0 := norm_eq_zero.mp h0.symm
            exact d.roots_ne_zero α hα this
          · exact mul_lt_mul_of_pos_left h_dist h0
      _ ≤ ‖α‖ + 1 := by linarith [norm_nonneg α]
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
  exact ⟨α, hα, k, h_bound, AffineHyperplane_ext _ _ hα_eq (by linarith [hk_eq])⟩

/-- The (finite) Weyl group $W$ normalizes the coroot lattice $\Lambda(\Phi^\vee)$:
this is the structural input to the semi-direct product decomposition
$W_a = \Lambda(\Phi^\vee) \rtimes W$. -/
theorem weylGroup_normalizes_corootLattice :
    ∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice,
      (w : E ≃ₗᵢ[ℝ] E) v ∈ d.corootLattice :=
  d.weylGroup_stable_corootLattice

end AffineWeylGroupData

namespace AffineWeylGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (Wa : AffineWeylGroup E)

/-- Convenience restatement of `AffineWeylGroupData.weylGroup_normalizes_corootLattice`
for the bundled `AffineWeylGroup` $Wa$. -/
theorem weylGroup_normalizes_corootLattice :
    ∀ w ∈ Wa.data.weylGroup, ∀ v ∈ Wa.data.corootLattice,
      (w : E ≃ₗᵢ[ℝ] E) v ∈ Wa.data.corootLattice :=
  Wa.data.weylGroup_stable_corootLattice


/-- Section 12.4 main result: the affine Weyl subgroup is isomorphic, as a group,
to the semi-direct product $\Lambda(\Phi^\vee) \rtimes W$. -/
def semidirect_product_decomposition_group
    (d : AffineWeylSemidirectData E) :
    ↥d.affineWeylSubgroup ≃* d.SemiType :=
  d.affineWeyl_semidirect_equiv

end AffineWeylGroup
