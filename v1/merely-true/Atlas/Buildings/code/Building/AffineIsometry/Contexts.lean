/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineIsometryGroups.StrongTransitivity
import Atlas.Buildings.code.Building.AffineIsometryGroups.GroupAction
set_option linter.unusedSectionVars false

open AffineIsometryBuilding DVRContext

/-- Data for the Bruhat-Tits building of type $\tilde C_n$ associated to a
non-degenerate alternating bilinear form on a $2n$-dimensional space over a
complete DVR $k$. The structure bundles the form, its hyperbolic basis
$(e_i, f_i)$, the standard $\mathfrak{o}$-lattice $\Lambda_0$ on which the
form is integral and unimodular, and the requisite non-degeneracy
hypothesis modulo $\mathfrak{m}$. -/
structure AlternatingBuildingContext where
  C : DVRContext
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  wittIndex : ℕ
  dim_eq : C.n = 2 * wittIndex
  form_alt : ∀ v : Fin C.n → C.k, form v v = 0
  form_add_left : ∀ v₁ v₂ w : Fin C.n → C.k,
    form (v₁ + v₂) w = form v₁ w + form v₂ w
  form_add_right : ∀ v w₁ w₂ : Fin C.n → C.k,
    form v (w₁ + w₂) = form v w₁ + form v w₂
  form_smul_left : ∀ (c : C.k) (v w : Fin C.n → C.k),
    form (c • v) w = c * form v w
  form_nondeg : ∀ v : Fin C.n → C.k, (∀ w, form v w = 0) → v = 0
  hyp_pairs : Fin wittIndex → ((Fin C.n → C.k) × (Fin C.n → C.k))
  pairs_unit : ∀ i, C.isUnitInO (form (hyp_pairs i).1 (hyp_pairs i).2)
  pairs_iso_e : ∀ i, form (hyp_pairs i).1 (hyp_pairs i).1 = 0
  pairs_iso_f : ∀ i, form (hyp_pairs i).2 (hyp_pairs i).2 = 0
  pairs_ortho : ∀ i j, i ≠ j →
    form (hyp_pairs i).1 (hyp_pairs j).1 = 0 ∧
    form (hyp_pairs i).1 (hyp_pairs j).2 = 0 ∧
    form (hyp_pairs i).2 (hyp_pairs j).1 = 0 ∧
    form (hyp_pairs i).2 (hyp_pairs j).2 = 0
  stdLattice : OLattice C
  std_contains_e : ∀ i, (hyp_pairs i).1 ∈ stdLattice.carrier
  std_contains_f : ∀ i, (hyp_pairs i).2 ∈ stdLattice.carrier
  std_form_integral : ∀ v ∈ stdLattice.carrier, ∀ w ∈ stdLattice.carrier,
    C.isInO (form v w)
  std_nondeg_mod : ∀ v ∈ stdLattice.carrier,
    (¬ ∃ w ∈ stdLattice.carrier, v = C.oscal C.uniformizer w) →
    ∃ w ∈ stdLattice.carrier, C.isUnitInO (form v w)

/-- Data for the double oriflamme building (type $\tilde D_n$, $n \ge 4$): a
symmetric bilinear form with a hyperbolic basis of half-dimension $\ge 4$,
together with a standard unimodular lattice and the modular non-degeneracy
condition. -/
structure DoubleOriflammeContext where
  C : DVRContext
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  halfDim : ℕ
  halfDim_ge_4 : halfDim ≥ 4
  dim_eq : C.n = 2 * halfDim
  form_symm : ∀ v w : Fin C.n → C.k, form v w = form w v
  form_add_left : ∀ v₁ v₂ w : Fin C.n → C.k,
    form (v₁ + v₂) w = form v₁ w + form v₂ w
  form_smul_left : ∀ (c : C.k) (v w : Fin C.n → C.k),
    form (c • v) w = c * form v w
  form_nondeg : ∀ v : Fin C.n → C.k, (∀ w, form v w = 0) → v = 0
  hyp_pairs : Fin halfDim → ((Fin C.n → C.k) × (Fin C.n → C.k))
  pairs_unit : ∀ i, C.isUnitInO (form (hyp_pairs i).1 (hyp_pairs i).2)
  pairs_iso_e : ∀ i, form (hyp_pairs i).1 (hyp_pairs i).1 = 0
  pairs_iso_f : ∀ i, form (hyp_pairs i).2 (hyp_pairs i).2 = 0
  pairs_ortho : ∀ i j, i ≠ j →
    form (hyp_pairs i).1 (hyp_pairs j).1 = 0 ∧
    form (hyp_pairs i).1 (hyp_pairs j).2 = 0 ∧
    form (hyp_pairs i).2 (hyp_pairs j).1 = 0 ∧
    form (hyp_pairs i).2 (hyp_pairs j).2 = 0
  stdLattice : OLattice C
  std_contains_e : ∀ i, (hyp_pairs i).1 ∈ stdLattice.carrier
  std_contains_f : ∀ i, (hyp_pairs i).2 ∈ stdLattice.carrier
  std_form_integral : ∀ v ∈ stdLattice.carrier, ∀ w ∈ stdLattice.carrier,
    C.isInO (form v w)
  std_nondeg_mod : ∀ v ∈ stdLattice.carrier,
    (¬ ∃ w ∈ stdLattice.carrier, v = C.oscal C.uniformizer w) →
    ∃ w ∈ stdLattice.carrier, C.isUnitInO (form v w)

/-- Data for the single oriflamme building (type $\tilde B_n$): a symmetric
bilinear form with an anisotropic vector, a primitive lattice on which the
form is integral, Hensel's lemma for the quadratic form, and the assumption
that $2$ is a unit. -/
structure SingleOriflammeContext where
  C : DVRContext
  form : (Fin C.n → C.k) → (Fin C.n → C.k) → C.k
  wittIndex : ℕ
  form_symm : ∀ v w : Fin C.n → C.k, form v w = form w v
  form_add_left : ∀ v₁ v₂ w : Fin C.n → C.k,
    form (v₁ + v₂) w = form v₁ w + form v₂ w
  form_smul_left : ∀ (c : C.k) (v w : Fin C.n → C.k),
    form (c • v) w = c * form v w
  form_nondeg : ∀ v : Fin C.n → C.k, (∀ w, form v w = 0) → v = 0
  primLat : OLattice C
  primLat_integral : ∀ v ∈ primLat.carrier, ∀ w ∈ primLat.carrier,
    C.isInO (form v w)
  primLat_nondeg : ∀ v ∈ primLat.carrier,
    (¬ ∃ w ∈ primLat.carrier, v = C.oscal C.uniformizer w) →
    ∃ w ∈ primLat.carrier, C.isUnitInO (form v w)
  anisotropic_exists : ∃ v ∈ primLat.carrier,
    (¬ ∃ w ∈ primLat.carrier, v = C.oscal C.uniformizer w) ∧
    C.isUnitInO (form v v)
  aniso_nondeg : ∀ v : Fin C.n → C.k,
    (∀ w ∈ primLat.carrier, form w w = 0 → form v w = 0) →
    form v v = 0 → v = 0
  two_is_unit : C.isUnitInO (C.embed (1 + 1 : C.𝔬))
  hensel : ∀ (b c : C.k),
    C.isUnitInO b → C.isInMaxIdeal c →
    ∃ α : C.k, α * α + b * α + c = 0
