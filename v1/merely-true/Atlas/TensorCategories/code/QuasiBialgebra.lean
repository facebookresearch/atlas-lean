/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


namespace QuasiBialgebra

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Algebra R H]

/-- The algebra map `(Id ⊗ Δ) ∘ Δ : H → H ⊗ (H ⊗ H)` used in the quasi-coassociativity axiom. -/
noncomputable def idTensorComul (Δ : H →ₐ[R] H ⊗[R] H) :
    H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.map (AlgHom.id R H) Δ).comp Δ

/-- The algebra map `((Δ ⊗ Id) ∘ Δ)` reassociated to `H ⊗ (H ⊗ H)`, used in the
quasi-coassociativity axiom. -/
noncomputable def comulTensorId (Δ : H →ₐ[R] H ⊗[R] H) :
    H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  ((Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map Δ (AlgHom.id R H))).comp Δ

/-- The contraction `(Id ⊗ ε ⊗ Id) : H ⊗ (H ⊗ H) → H ⊗ H` used in stating
`(Id ⊗ ε ⊗ Id)(Φ) = 1 ⊗ 1`. -/
noncomputable def idCounitId (ε : H →ₐ[R] R) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    ((Algebra.TensorProduct.lid R H).toAlgHom.comp
      (Algebra.TensorProduct.map ε (AlgHom.id R H)))

/-- `(Id ⊗ Id ⊗ Δ)`, the map embedding into `H ⊗ (H ⊗ (H ⊗ H))`, used in the pentagon axiom. -/
noncomputable def idIdComul (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    (Algebra.TensorProduct.map (AlgHom.id R H) Δ)

/-- `(Δ ⊗ Id ⊗ Id)`, reassociated into `H ⊗ (H ⊗ (H ⊗ H))`, used in the pentagon axiom. -/
noncomputable def comulIdId (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  (Algebra.TensorProduct.assoc R R R H H (H ⊗[R] H)).toAlgHom.comp
    (Algebra.TensorProduct.map Δ (AlgHom.id R (H ⊗[R] H)))

/-- `(Id ⊗ Δ ⊗ Id)`, the middle inflation used in the pentagon axiom. -/
noncomputable def idComulId (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    ((Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
      (Algebra.TensorProduct.map Δ (AlgHom.id R H)))

/-- The right-tensoring embedding `H ⊗ (H ⊗ H) → H ⊗ (H ⊗ (H ⊗ H))` realizing
`Φ ⊗ 1` in the pentagon axiom. -/
noncomputable def embedPhiRight :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    (Algebra.TensorProduct.map (AlgHom.id R H)
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)))

/-- Right multiplication by `c`, as an `R`-linear map. -/
def rmulMap (c : H) : H →ₗ[R] H := (LinearMap.mul R H).flip c

/-- The linear map `x ⊗ y ↦ S(x) · α · y`, used to express the left antipode axiom. -/
noncomputable def sAlphaMap (S : H →ₗ[R] H) (α_elem : H) : H ⊗[R] H →ₗ[R] H :=
  TensorProduct.lift ((LinearMap.mul R H).comp ((rmulMap R H α_elem).comp S))

/-- The linear map `x ⊗ y ↦ x · β · S(y)`, used to express the right antipode axiom. -/
noncomputable def betaSMap (S : H →ₗ[R] H) (β_elem : H) : H ⊗[R] H →ₗ[R] H :=
  LinearMap.mul' R H ∘ₗ TensorProduct.map (rmulMap R H β_elem) S

/-- The map `x ⊗ y ⊗ z ↦ x · β · S(y) · α · z` evaluating the antipode identity
`∑ Φ¹ β S(Φ²) α Φ³ = 1` from Proposition 1.35.1. -/
noncomputable def phiBetaSAlphaMap (S : H →ₗ[R] H) (α_elem β_elem : H) :
    H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
  LinearMap.mul' R H ∘ₗ
    TensorProduct.map (rmulMap R H β_elem) (sAlphaMap R H S α_elem)

/-- The map `x ⊗ y ⊗ z ↦ S(x) · α · y · β · S(z)` evaluating the dual antipode
identity `∑ S(Φ̄¹) α Φ̄² β S(Φ̄³) = 1` from Proposition 1.35.1. -/
noncomputable def phiInvSAlphaBetaSMap (S : H →ₗ[R] H) (α_elem β_elem : H) :
    H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
  LinearMap.mul' R H ∘ₗ
    TensorProduct.map ((rmulMap R H α_elem).comp S) (betaSMap R H S β_elem)

end QuasiBialgebra


/-- Definition 1.34.5 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-bialgebra over `R`
consists of an associative unital `R`-algebra `H` together with a coproduct
`comul : H → H ⊗ H`, a counit `counit : H → R` (both unital algebra
homomorphisms), and an invertible associator `Φ ∈ H^{⊗3}` satisfying the
quasi-coassociativity, counit and pentagon axioms. -/
class QuasiBialgebra (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H] where
  comul : H →ₐ[R] H ⊗[R] H
  counit : H →ₐ[R] R
  Φ : (H ⊗[R] (H ⊗[R] H))ˣ
  quasi_coassoc : ∀ a : H,
    QuasiBialgebra.idTensorComul R H comul a * (Φ : H ⊗[R] (H ⊗[R] H)) =
    (Φ : H ⊗[R] (H ⊗[R] H)) * QuasiBialgebra.comulTensorId R H comul a
  left_counit :
    (Algebra.TensorProduct.lid R H).toAlgHom.comp
      ((Algebra.TensorProduct.map counit (AlgHom.id R H)).comp comul) =
    AlgHom.id R H
  right_counit :
    (Algebra.TensorProduct.rid R R H).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R H) counit).comp comul) =
    AlgHom.id R H
  Φ_counit :
    QuasiBialgebra.idCounitId R H counit (Φ : H ⊗[R] (H ⊗[R] H)) = 1
  pentagon :
    (1 : H) ⊗ₜ[R] (Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebra.idComulId R H comul (Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebra.embedPhiRight R H (Φ : H ⊗[R] (H ⊗[R] H)) =
    QuasiBialgebra.idIdComul R H comul (Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebra.comulIdId R H comul (Φ : H ⊗[R] (H ⊗[R] H))

/-- Accessor: the associator element `Φ` of a quasi-bialgebra. -/
noncomputable def QuasiBialgebra.associator {R : Type u} {H : Type v}
    [CommSemiring R] [Semiring H] [Algebra R H]
    [qb : QuasiBialgebra R H] : (H ⊗[R] (H ⊗[R] H))ˣ :=
  qb.Φ


/-- Definition 1.35.2 (Etingof–Gelaki–Nikshych–Ostrik): An antipode on a
quasi-bialgebra is a triple `(S, α, β)` with `S : H → H` a unital algebra
antihomomorphism and `α, β ∈ H` satisfying the antipode identities
(1.35.1) and (1.35.2). -/
structure QuasiBialgebraAntipode (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H]
    [qb : QuasiBialgebra R H] where
  S : H →ₗ[R] H
  α_elem : H
  β_elem : H
  S_anti_mul : ∀ a b : H, S (a * b) = S b * S a
  S_one : S 1 = 1
  left_antipode : ∀ b : H,
    QuasiBialgebra.sAlphaMap R H S α_elem (qb.comul b) = qb.counit b • α_elem
  right_antipode : ∀ b : H,
    QuasiBialgebra.betaSMap R H S β_elem (qb.comul b) = qb.counit b • β_elem
  phi_beta_S_alpha :
    QuasiBialgebra.phiBetaSAlphaMap R H S α_elem β_elem
      (qb.Φ : H ⊗[R] (H ⊗[R] H)) = 1
  phiInv_S_alpha_beta_S :
    QuasiBialgebra.phiInvSAlphaBetaSMap R H S α_elem β_elem
      (↑qb.Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1


/-- Definition 1.35.2 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-Hopf algebra is
a quasi-bialgebra `(H, Δ, ε, Φ)` equipped with an antipode `(S, α, β)` where
`S` is bijective. -/
class QuasiHopfAlgebra (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H]
    extends QuasiBialgebra R H where
  S : H ≃ₗ[R] H
  α_elem : H
  β_elem : H
  S_anti_mul : ∀ a b : H, S (a * b) = S b * S a
  S_one : S 1 = 1
  left_antipode : ∀ b : H,
    QuasiBialgebra.sAlphaMap R H S.toLinearMap α_elem (comul b) = counit b • α_elem
  right_antipode : ∀ b : H,
    QuasiBialgebra.betaSMap R H S.toLinearMap β_elem (comul b) = counit b • β_elem
  phi_beta_S_alpha :
    QuasiBialgebra.phiBetaSAlphaMap R H S.toLinearMap α_elem β_elem
      (Φ : H ⊗[R] (H ⊗[R] H)) = 1
  phiInv_S_alpha_beta_S :
    QuasiBialgebra.phiInvSAlphaBetaSMap R H S.toLinearMap α_elem β_elem
      (↑Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1


section BasicProperties

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]
variable [QuasiBialgebra R H]

end BasicProperties

namespace QuasiBialgebraTwist

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Algebra R H]

/-- `(ε ⊗ Id) : H ⊗ H → H`, used in the twist counit normalization. -/
noncomputable def counitTensorId (ε : H →ₐ[R] R) : H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.lid R H).toAlgHom.comp
    (Algebra.TensorProduct.map ε (AlgHom.id R H))

/-- `(Id ⊗ ε) : H ⊗ H → H`, used in the twist counit normalization. -/
noncomputable def idTensorCounit (ε : H →ₐ[R] R) : H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.rid R R H).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R H) ε)

/-- `(Id ⊗ Δ) : H ⊗ H → H ⊗ (H ⊗ H)`, used in the formula for the twisted associator. -/
noncomputable def idTensorComul (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.map (AlgHom.id R H) Δ

/-- `(Δ ⊗ Id) : H ⊗ H → H ⊗ (H ⊗ H)`, reassociated, used in the formula for the
twisted associator. -/
noncomputable def comulTensorId (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map Δ (AlgHom.id R H))

/-- The embedding `x ↦ 1 ⊗ x : H ⊗ H → H ⊗ (H ⊗ H)`, realizing `1 ⊗ J` in the
twisted associator formula. -/
noncomputable def embedRight :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.includeRight

/-- The embedding `x ↦ x ⊗ 1 : H ⊗ H → H ⊗ (H ⊗ H)`, realizing `J ⊗ 1` in the
twisted associator formula. -/
noncomputable def embedLeft :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    Algebra.TensorProduct.includeLeft

end QuasiBialgebraTwist

/-- A twist for a quasi-bialgebra `H`: an invertible element `J ∈ H ⊗ H` with
`(ε ⊗ Id)(J) = (Id ⊗ ε)(J) = 1` (Definition 1.34.6). -/
structure QuasiBialgebraTwist (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H]
    [QuasiBialgebra R H] where
  J : (H ⊗[R] H)ˣ
  counit_left :
    QuasiBialgebraTwist.counitTensorId R H (QuasiBialgebra.counit) (J : H ⊗[R] H) = 1
  counit_right :
    QuasiBialgebraTwist.idTensorCounit R H (QuasiBialgebra.counit) (J : H ⊗[R] H) = 1

/-- The twisted coproduct `Δ^J(x) = J^{-1} Δ(x) J` (Definition 1.34.6). -/
noncomputable def QuasiBialgebraTwist.twistedComul
    {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]
    [QuasiBialgebra R H] (tw : QuasiBialgebraTwist R H) (x : H) : H ⊗[R] H :=
  (↑tw.J⁻¹ : H ⊗[R] H) * QuasiBialgebra.comul x * (↑tw.J : H ⊗[R] H)

/-- The twisted associator
`Φ^J = (1 ⊗ J)^{-1} (Id ⊗ Δ)(J)^{-1} Φ (Δ ⊗ Id)(J) (J ⊗ 1)`
(Definition 1.34.6). -/
noncomputable def QuasiBialgebraTwist.twistedAssociator
    {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]
    [qb : QuasiBialgebra R H] (tw : QuasiBialgebraTwist R H) :
    H ⊗[R] (H ⊗[R] H) :=
  QuasiBialgebraTwist.embedRight R H (↑tw.J⁻¹ : H ⊗[R] H) *
  QuasiBialgebraTwist.idTensorComul R H qb.comul (↑tw.J⁻¹ : H ⊗[R] H) *
  (qb.Φ : H ⊗[R] (H ⊗[R] H)) *
  QuasiBialgebraTwist.comulTensorId R H qb.comul (↑tw.J : H ⊗[R] H) *
  QuasiBialgebraTwist.embedLeft R H (↑tw.J : H ⊗[R] H)

/-- Twist equivalence of quasi-bialgebras: two quasi-bialgebra structures on the
same underlying algebra `H` are twist equivalent if one is obtained from the other
by conjugation by a normalized invertible twist `J` (Definition 1.34.6). -/
def QuasiBialgebraTwistEquiv
    {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]
    (qb₁ qb₂ : QuasiBialgebra R H) : Prop :=
  ∃ J : (H ⊗[R] H)ˣ,

    QuasiBialgebraTwist.counitTensorId R H qb₁.counit (↑J : H ⊗[R] H) = 1 ∧
    QuasiBialgebraTwist.idTensorCounit R H qb₁.counit (↑J : H ⊗[R] H) = 1 ∧

    qb₂.counit = qb₁.counit ∧

    (∀ x : H, qb₂.comul x = (↑J⁻¹ : H ⊗[R] H) * qb₁.comul x * (↑J : H ⊗[R] H)) ∧

    (qb₂.Φ.val =
      QuasiBialgebraTwist.embedRight R H (↑J⁻¹ : H ⊗[R] H) *
      QuasiBialgebraTwist.idTensorComul R H qb₁.comul (↑J⁻¹ : H ⊗[R] H) *
      (qb₁.Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebraTwist.comulTensorId R H qb₁.comul (↑J : H ⊗[R] H) *
      QuasiBialgebraTwist.embedLeft R H (↑J : H ⊗[R] H))


section Proposition_1_34_7

open CategoryTheory MonoidalCategory


end Proposition_1_34_7

section TwistEquiv_Refl

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]

end TwistEquiv_Refl


/-- Reference abbreviation for Definition 1.34.5: a quasi-bialgebra. -/
abbrev Definition_1_34_5_QuasiBialgebra := @QuasiBialgebra

/-- Reference abbreviation for Definition 1.34.6: a twist for a quasi-bialgebra. -/
abbrev Definition_1_34_6 := @QuasiBialgebraTwist

/-- Reference abbreviation for Definition 1.34.6: the twist data. -/
abbrev Definition_1_34_6_Twist := @QuasiBialgebraTwist

/-- Reference abbreviation for Definition 1.34.6: twist equivalence of quasi-bialgebras. -/
abbrev Definition_1_34_6_TwistEquiv := @QuasiBialgebraTwistEquiv

/-- Reference abbreviation for Definition 1.35.2: an antipode on a quasi-bialgebra. -/
abbrev Definition_1_35_2_Antipode := @QuasiBialgebraAntipode

/-- Reference abbreviation for Definition 1.35.2: a quasi-Hopf algebra. -/
abbrev Definition_1_35_2_QuasiHopfAlgebra := @QuasiHopfAlgebra
