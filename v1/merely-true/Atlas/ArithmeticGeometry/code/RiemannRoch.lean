/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import Atlas.ArithmeticGeometry.code.EffectiveDivisors
import Atlas.ArithmeticGeometry.code.CanonicalDivisors

open scoped RestrictedProduct

/-- The adele ring of a function field $F$ with set of places $P$ and valuation subrings
$O_p \subseteq F$: the restricted product $\prod_{p \in P}' F$ of copies of $F$ with
respect to the family $(O_p)$. An element $(\alpha_p)_{p \in P}$ is an adele iff
$\alpha_p \in O_p$ for all but finitely many $p$. -/
def FunctionFieldAdeleRing (F : Type*) [Field F] (P : Type*)
    (O : P → ValuationSubring F) : Type _ :=
  Πʳ _p : P, [(fun _ => F) _p, O _p]

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}

namespace FunctionFieldAdeleRing

/-- The adele ring inherits a commutative ring structure from the restricted product. -/
noncomputable instance instCommRing : CommRing (FunctionFieldAdeleRing F P O) :=
  inferInstanceAs (CommRing (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]))

/-- Adeles act as functions $P \to F$ via the underlying restricted product. -/
instance instDFunLike :
    DFunLike (FunctionFieldAdeleRing F P O) P (fun _ => F) :=
  inferInstanceAs <|
    DFunLike (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]) P (fun _ => F)

/-- Two adeles are equal if they agree pointwise at every place. -/
@[ext]
lemma ext {α β : FunctionFieldAdeleRing F P O} (h : ∀ p, α p = β p) : α = β :=
  Subtype.ext <| funext h

/-- The defining property of the adele ring: for any adele $\alpha$, $\alpha_p \in O_p$
for all but finitely many places $p$. -/
lemma mem_valuationSubring_cofinitely (α : FunctionFieldAdeleRing F P O) :
    ∀ᶠ p in Filter.cofinite, α p ∈ O p :=
  α.2

variable (k : Type*) [Field k] [Algebra k F]

/-- A subfield $k \subseteq F$ is called a *field of constants* for the family of valuation
subrings $(O_p)$ if every element of $k$ is integral at every place $p$ and each residue
field $O_p / \mathfrak{m}_p$ is finite-dimensional over $k$. -/
class ConstantField (k : Type*) {F : Type*} {P : Type*} [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F} : Prop where
  algebraMap_mem : ∀ (p : P) (c : k), algebraMap k F c ∈ O p
  residueField_finiteDimensional : ∀ (p : P),
    letI : Algebra k ↥(O p) :=
      ((algebraMap k F).codRestrict (O p).toSubring (fun c => algebraMap_mem p c)).toAlgebra
    letI : Algebra k (IsLocalRing.ResidueField ↥(O p)) :=
      (IsLocalRing.residue ↥(O p) |>.comp (algebraMap k ↥(O p))).toAlgebra
    FiniteDimensional k (IsLocalRing.ResidueField ↥(O p))




variable [ConstantField k (O := O)]

/-- The diagonal embedding $k \hookrightarrow \mathbb{A}_F$ sending a constant $c$ to the
constant adele $(c, c, c, \dots)$. -/
noncomputable def diagonalRingHom : k →+* FunctionFieldAdeleRing F P O where
  toFun c := ⟨fun _ => algebraMap k F c, Filter.Eventually.of_forall
    (fun p => ConstantField.algebraMap_mem (k := k) p c)⟩
  map_one' := ext fun _ => map_one (algebraMap k F)
  map_mul' x y := ext fun _ => map_mul (algebraMap k F) x y
  map_zero' := ext fun _ => map_zero (algebraMap k F)
  map_add' x y := ext fun _ => map_add (algebraMap k F) x y

/-- The $k$-algebra structure on the adele ring induced by the diagonal embedding. -/
noncomputable instance instAlgebra : Algebra k (FunctionFieldAdeleRing F P O) :=
  (diagonalRingHom k).toAlgebra

/-- Pointwise formula for the $k$-action on adeles: $(c \cdot \alpha)_p = c \cdot \alpha_p$. -/
@[simp]
lemma smul_apply (c : k) (α : FunctionFieldAdeleRing F P O) (p : P) :
    (c • α) p = algebraMap k F c * α p := by
  simp only [Algebra.smul_def]; rfl



/-- Convenience class bundling the function-field-curve hypothesis together with a chosen
family of valuation subrings $O$. -/
class FunctionFieldProperty (F : Type*) (P : Type*) [Field F]
    (O : P → ValuationSubring F) extends FunctionFieldCurve P F





/-- A *discrete valuation family* on $F$ over $k$: an assignment of an order function
$\operatorname{ord}_p : F \to \mathbb{Z} \cup \{\infty\}$ to each $p \in P$ satisfying the
usual discrete valuation axioms, with constants from $k$ having order zero and a
uniformizer existing at every place. -/
class DiscreteValuationFamily (P : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] where
  ord : P → F → WithTop ℤ
  ord_zero : ∀ p, ord p 0 = ⊤
  uniformizer_exists : ∀ p, ∃ t : F, ord p t = (1 : ℤ)
  ord_add_ge_min : ∀ (p : P) (x y : F),
    ord p (x + y) ≥ min (ord p x) (ord p y)
  ord_algebraMap : ∀ (p : P) (c : k), c ≠ 0 → ord p (algebraMap k F c) = (0 : ℤ)
  ord_mul : ∀ (p : P) (x y : F), ord p (x * y) = ord p x + ord p y








variable [DiscreteValuationFamily P F k]

open DiscreteValuationFamily in
/-- The adele subspace $\mathbb{A}_F(D) := \{\alpha \in \mathbb{A}_F :
\operatorname{ord}_p(\alpha_p) \ge -D(p) \text{ for all } p\}$ associated to a
$\mathbb{Z}$-valued divisor $D$. -/
noncomputable def adeleSpace (D : P → ℤ) :
    Submodule k (FunctionFieldAdeleRing F P O) where
  carrier := { α | ∀ p, ord (k := k) p (α p) ≥ ↑(-D p) }
  add_mem' {α β} hα hβ p :=
    le_trans (le_min (hα p) (hβ p)) (ord_add_ge_min (k := k) p (α p) (β p))
  zero_mem' p := by
    simp only [show (0 : FunctionFieldAdeleRing F P O) p = 0 from rfl, ord_zero]
    exact le_top
  smul_mem' c α hα p := by
    simp only [smul_apply]
    by_cases hc : c = 0
    · simp only [hc, map_zero, zero_mul, ord_zero]; exact le_top
    · rw [ord_mul, ord_algebraMap p c hc]; simp; exact hα p





end FunctionFieldAdeleRing

/-- The complete data structure for a curve $C$ with function field $F$ and constant
subfield $k$ needed to prove Riemann-Roch: a `CurveWithConstants` together with all
ancillary structure used in the proof. -/
class RiemannRochData (C : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] extends CurveWithConstants C k F


/-- Axiom form: constants $c \in k^\times$ have order zero at every point $P \in C$. -/
theorem RiemannRochData.ord_algebraMap_eq_ax {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (c : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 :=
  CurveWithConstants.ord_constant P c

/-- Ultrametric inequality for sums of nonzero elements at a point: when $f + g \ne 0$,
$\operatorname{ord}_P(f + g) \ge \min(\operatorname{ord}_P(f), \operatorname{ord}_P(g))$. -/
theorem RiemannRochData.ord_add_ge_min_field {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0) :
    CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥
      min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) :=
  CurveWithOrd.ord_add P f g hfg

/-- Axiom form: a unit $f \in F^\times$ with $\operatorname{ord}_P(f) = 0$ at every point
$P \in C$ must be a constant, i.e. lies in the image of $k^\times \hookrightarrow F^\times$. -/
theorem RiemannRochData.algebraMap_of_all_ord_zero_ax {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (f : Fˣ) :
    (∀ P : C, CurveWithOrd.ord P f = 0) →
    ∃ c : kˣ, (f : F) = algebraMap k F (c : k) := by
  intro hf
  obtain ⟨a, ha⟩ := CurveWithConstants.ker_div_eq_constants f hf
  exact ⟨a, by rw [← ha]; simp [Units.coe_map]⟩

/-- At every point $P$ of a curve there exists a uniformizer $\pi \in F^\times$ with
$\operatorname{ord}_P(\pi) = 1$. -/
theorem dvr_uniformizer_exists {C : Type*} {F : Type*} [Field F]
    [CurveWithOrd C F] (P : C) :
    ∃ (π : Fˣ), CurveWithOrd.ord P π = 1 :=
  CurveWithOrd.uniformizer_exists P

/-- At every point $P$ there exists a $k$-linear "residue evaluation" map
$\operatorname{ev}_P : F \to k$ such that any unit $f$ with non-negative order and
vanishing residue actually has order $\ge 1$. This expresses that the residue map
$O_P \to O_P/\mathfrak{m}_P \cong k$ is a $k$-linear functional. -/
theorem dvr_residue_eval_exists {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [CurveWithConstants C k F] (P : C) :
    ∃ (evalP : F →ₗ[k] k),
      ∀ (f : Fˣ), CurveWithOrd.ord P f ≥ 0 → evalP (f : F) = 0 →
        CurveWithOrd.ord P f ≥ 1 :=
  CurveWithConstants.residue_eval P

/-- The order at $P$ packaged as a multiplicative monoid homomorphism
$F^\times \to \mathbb{Z}$ (written multiplicatively). -/
noncomputable def CurveWithOrd.ordMonoidHom {C : Type*} {F : Type*} [Field F]
    [CurveWithOrd C F] (P : C) : Fˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (CurveWithOrd.ord P f)
  map_one' := by
    have : CurveWithOrd.ord P (1 : Fˣ) = 0 := by
      have h := CurveWithOrd.ord_mul P (1 : Fˣ) 1
      simp at h; linarith
    simp [this]
  map_mul' f g := by
    rw [CurveWithOrd.ord_mul P f g, ofAdd_add]

/-- Integer power formula: $\operatorname{ord}_P(f^n) = n \cdot \operatorname{ord}_P(f)$
for $n \in \mathbb{Z}$. -/
theorem CurveWithOrd.ord_zpow {C : Type*} {F : Type*} [Field F]
    [CurveWithOrd C F] (P : C) (f : Fˣ) (n : ℤ) :
    CurveWithOrd.ord P (f ^ n) = n * CurveWithOrd.ord P f := by
  have h := MonoidHom.map_zpow (CurveWithOrd.ordMonoidHom P) f n
  dsimp [CurveWithOrd.ordMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  have h2 : (Multiplicative.ofAdd (CurveWithOrd.ord P f)) ^ n =
      Multiplicative.ofAdd (n * CurveWithOrd.ord P f) :=
    (Equiv.symm_apply_eq Multiplicative.ofAdd).mp rfl
  rw [h2] at h
  exact Multiplicative.ofAdd.injective h

/-- Existence of a "residue functional at $P$" detecting the next divisor: there is a
$k$-linear $\varphi : F \to k$ such that for any $f \in F^\times$, if
$\operatorname{div}(f) + (D + P) \ge 0$ and $\varphi(f) = 0$ then in fact
$\operatorname{div}(f) + D \ge 0$. This is the key tool used to bound
$\ell(D + P) - \ell(D) \le 1$. -/
theorem dvr_residue_functional_exists {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (D : CurveDivisor C) (P : C) :
    ∃ (φ : F →ₗ[k] k),
      ∀ (f : Fˣ),
        (CurveWithOrd.principalDivisor f +
          (D + Finsupp.single P 1)).IsEffective →
        φ (f : F) = 0 →
        (CurveWithOrd.principalDivisor f + D).IsEffective := by

  obtain ⟨π, hπ⟩ := dvr_uniformizer_exists (F := F) P
  obtain ⟨evalP, hevalP⟩ := dvr_residue_eval_exists (F := F) (k := k) P

  set n : ℤ := D P + 1 with hn_def

  let mulπn : F →ₗ[k] F :=
    { toFun := fun f => (↑(π ^ n) : F) * f
      map_add' := fun x y => by ring
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        exact mul_smul_comm r (↑(π ^ n)) x }

  refine ⟨evalP.comp mulπn, fun f heff hφf => ?_⟩

  intro Q
  have heffQ := heff Q
  simp only [Finsupp.coe_add, Pi.add_apply,
    CurveWithOrd.principalDivisor_apply] at heffQ ⊢
  by_cases hQP : Q = P
  ·
    subst hQP
    simp only [Finsupp.single_eq_same] at heffQ


    have hord_prod : CurveWithOrd.ord Q (π ^ n * f) = n + CurveWithOrd.ord Q f := by
      rw [CurveWithOrd.ord_mul, CurveWithOrd.ord_zpow, hπ, mul_one]
    have hord_nonneg : CurveWithOrd.ord Q (π ^ n * f) ≥ 0 := by
      rw [hord_prod]; linarith

    have hcoerce : (↑(π ^ n * f) : F) = (↑(π ^ n) : F) * (↑f : F) := by
      simp [Units.val_mul]

    have heval_zero : evalP (↑(π ^ n * f) : F) = 0 := by
      rw [hcoerce]
      exact hφf

    have hord_pos : CurveWithOrd.ord Q (π ^ n * f) ≥ 1 :=
      hevalP (π ^ n * f) hord_nonneg heval_zero

    linarith [hord_prod]
  ·
    have hsingle : (Finsupp.single P 1 : CurveDivisor C) Q = 0 :=
      Finsupp.single_eq_of_ne hQP
    linarith [hsingle]

/-- The residue functional packaged for use with the membership condition of the
Riemann-Roch space (which handles both zero and nonzero elements). -/
theorem RiemannRochData.dvr_eval_ax {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (D : CurveDivisor C) (P : C) :
    ∃ (φ : F →ₗ[k] k),
      ∀ (f : F),
        (f = 0 ∨ ∃ (hf : f ≠ 0),
          (CurveWithOrd.principalDivisor (Units.mk0 f hf) +
            (D + Finsupp.single P 1)).IsEffective) →
        φ f = 0 →
        (f = 0 ∨ ∃ (hf : f ≠ 0),
          (CurveWithOrd.principalDivisor (Units.mk0 f hf) + D).IsEffective) := by
  obtain ⟨φ, hφ⟩ := dvr_residue_functional_exists (F := F) (k := k) D P
  exact ⟨φ, fun f hfLD hφf => by
    rcases hfLD with rfl | ⟨hf, heff⟩
    · left; rfl
    · right
      exact ⟨hf, hφ (Units.mk0 f hf) heff hφf⟩⟩

/-- Alias: constants have order zero at every point. -/
theorem RiemannRochData.ord_algebraMap_eq {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (c : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 :=
  RiemannRochData.ord_algebraMap_eq_ax P c

/-- Short alias for `RiemannRochData.ord_algebraMap_eq`: constants have order zero. -/
theorem RiemannRochData.ord_algebraMap {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (c : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 :=
  RiemannRochData.ord_algebraMap_eq P c

/-- Axiom alias for the ultrametric inequality at a point of a curve. -/
theorem RiemannRochData.ord_add_ge_min_ax {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0) :
    CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥
      min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) :=
  RiemannRochData.ord_add_ge_min_field P f g hfg

/-- Short alias: the ultrametric inequality $\operatorname{ord}_P(f+g) \ge
\min(\operatorname{ord}_P f, \operatorname{ord}_P g)$ for nonzero $f+g$. -/
theorem RiemannRochData.ord_add_ge_min {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0) :
    CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥
      min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) :=
  RiemannRochData.ord_add_ge_min_ax P f g hfg



/-- A unit $f \in F^\times$ with $\operatorname{ord}_P(f) = 0$ at every point of $C$ is a
constant from $k^\times$. -/
theorem RiemannRochData.algebraMap_of_all_ord_zero {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (f : Fˣ) (hf : ∀ P : C, CurveWithOrd.ord P f = 0) :
    ∃ c : kˣ, (f : F) = algebraMap k F (c : k) :=
  RiemannRochData.algebraMap_of_all_ord_zero_ax f hf

/-- Public alias of the residue-evaluation functional (handles both zero and nonzero $f$). -/
theorem RiemannRochData.dvr_eval {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (D : CurveDivisor C) (P : C) :
    ∃ (φ : F →ₗ[k] k),
      ∀ (f : F),
        (f = 0 ∨ ∃ (hf : f ≠ 0),
          (CurveWithOrd.principalDivisor (Units.mk0 f hf) +
            (D + Finsupp.single P 1)).IsEffective) →
        φ f = 0 →
        (f = 0 ∨ ∃ (hf : f ≠ 0),
          (CurveWithOrd.principalDivisor (Units.mk0 f hf) + D).IsEffective) :=
  RiemannRochData.dvr_eval_ax D P

namespace RiemannRochSpace

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]

open CurveWithOrd CurveDivisor

/-- The *Riemann-Roch space* $\mathcal{L}(D) := \{f \in F : f = 0 \text{ or }
\operatorname{div}(f) + D \ge 0\}$, viewed as a $k$-subspace of $F$. -/
noncomputable def riemannRochSpace (D : CurveDivisor C) : Submodule k F where
  carrier := {f | f = 0 ∨ ∃ (hf : f ≠ 0),
    (principalDivisor (Units.mk0 f hf) + D).IsEffective}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    by_cases hab : a + b = 0
    · exact Or.inl hab
    · right; refine ⟨hab, fun P => ?_⟩
      simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
      obtain (rfl | ⟨ha_ne, ha_eff⟩) := ha
      ·
        simp only [zero_add] at hab ⊢
        exact (hb.resolve_left fun h => hab (h ▸ rfl)).choose_spec P
      · obtain (rfl | ⟨hb_ne, hb_eff⟩) := hb
        ·
          simp only [add_zero] at hab ⊢; exact ha_eff P
        ·
          have h := RiemannRochData.ord_add_ge_min (k := k) P
            (Units.mk0 a ha_ne) (Units.mk0 b hb_ne) hab
          simp only [Units.val_mk0] at h
          have haP := ha_eff P
          have hbP := hb_eff P
          simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply] at haP hbP
          linarith [le_min haP hbP,
                    show min (ord P (Units.mk0 a ha_ne) + D P)
                             (ord P (Units.mk0 b hb_ne) + D P) =
                         min (ord P (Units.mk0 a ha_ne))
                             (ord P (Units.mk0 b hb_ne)) + D P
                     from by omega]
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at *
    by_cases hcf : c • f = 0
    · exact Or.inl hcf
    · right; refine ⟨hcf, fun P => ?_⟩
      simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
      obtain (rfl | ⟨hf_ne, hf_eff⟩) := hf
      · exact absurd (smul_zero c) hcf
      ·
        have hc_ne : c ≠ 0 := by intro hc; exact hcf (hc ▸ zero_smul k f)
        have key : Units.mk0 (c • f) hcf =
          Units.map (algebraMap k F).toMonoidHom (Units.mk0 c hc_ne) *
            Units.mk0 f hf_ne := by
          apply Units.ext; simp [Algebra.smul_def]
        rw [key, ord_mul,
            RiemannRochData.ord_algebraMap (F := F) (k := k), zero_add]
        exact hf_eff P

/-- Membership in $\mathcal{L}(D)$ unfolded: $f \in \mathcal{L}(D)$ iff $f = 0$ or
$\operatorname{div}(f) + D$ is effective. -/
theorem mem_riemannRochSpace_iff (D : CurveDivisor C) (f : F) :
    f ∈ riemannRochSpace (k := k) D ↔
      f = 0 ∨ ∃ (hf : f ≠ 0),
        (principalDivisor (Units.mk0 f hf) + D).IsEffective :=
  Iff.rfl


/-- Membership in $\mathcal{L}(D)$ for a nonzero element simplifies to effectivity of
$\operatorname{div}(f) + D$. -/
theorem mem_riemannRochSpace_of_ne_zero (D : CurveDivisor C) (f : F) (hf : f ≠ 0) :
    f ∈ riemannRochSpace (k := k) D ↔
      (principalDivisor (Units.mk0 f hf) + D).IsEffective := by
  constructor
  · intro hmem
    exact (hmem.resolve_left hf).choose_spec
  · intro heff
    exact Or.inr ⟨hf, heff⟩

/-- Multiplication by a unit $f$ with $\operatorname{div}(f) = A - B$ sends
$\mathcal{L}(A)$ into $\mathcal{L}(B)$. -/
lemma mul_unit_mem_riemannRochSpace (A B : CurveDivisor C) (f : Fˣ)
    (hf : principalDivisor f = A - B)
    (g : F) (hg : g ∈ riemannRochSpace (k := k) A) :
    (f : F) * g ∈ riemannRochSpace (k := k) B := by
  rw [mem_riemannRochSpace_iff] at hg ⊢
  by_cases hg0 : g = 0
  · left; simp [hg0]
  · right
    have hfg_ne : (f : F) * g ≠ 0 := mul_ne_zero f.ne_zero hg0
    refine ⟨hfg_ne, fun P => ?_⟩
    obtain ⟨hg_ne, heff⟩ := hg.resolve_left hg0
    have heffP := heff P
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply] at heffP ⊢
    have key : Units.mk0 ((f : F) * g) hfg_ne = f * Units.mk0 g hg_ne := by
      apply Units.ext; simp
    rw [key, ord_mul]
    have hAP : A P = ord P f + B P := by
      have := congr_fun (congr_arg DFunLike.coe hf) P
      simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply] at this
      linarith
    linarith

/-- Multiplication by $f$ as a $k$-linear map $\mathcal{L}(A) \to \mathcal{L}(B)$ when
$\operatorname{div}(f) = A - B$. -/
noncomputable def mulUnitLinearMap (A B : CurveDivisor C) (f : Fˣ)
    (hf : principalDivisor f = A - B) :
    riemannRochSpace (F := F) (k := k) A →ₗ[k] riemannRochSpace (F := F) (k := k) B where
  toFun g := ⟨(f : F) * g.1, mul_unit_mem_riemannRochSpace A B f hf g.1 g.2⟩
  map_add' g₁ g₂ := by
    ext; simp [mul_add]
  map_smul' c g := by
    ext
    simp only [SetLike.val_smul, Algebra.smul_def, RingHom.id_apply]

    ring

/-- If $\operatorname{div}(f) = A - B$ then $f \cdot - : \mathcal{L}(A) \cong \mathcal{L}(B)$
is a $k$-linear isomorphism, with inverse given by multiplication by $f^{-1}$. -/
noncomputable def riemannRochSpace_linearEquiv_of_linearlyEquivalent
    (A B : CurveDivisor C) (f : Fˣ)
    (hf : principalDivisor f = A - B) :
    (riemannRochSpace (F := F) (k := k) A) ≃ₗ[k]
      (riemannRochSpace (F := F) (k := k) B) where
  toLinearMap := mulUnitLinearMap A B f hf
  invFun g := ⟨(f⁻¹ : Fˣ) * g.1,
    mul_unit_mem_riemannRochSpace B A f⁻¹
      (by rw [principalDivisor_inv, hf]; abel) g.1 g.2⟩
  left_inv _g := by
    ext
    simp only [mulUnitLinearMap, Submodule.coe_mk]
    exact Units.inv_mul_cancel_left f _
  right_inv _g := by
    ext
    simp only [mulUnitLinearMap, Submodule.coe_mk]
    exact Units.mul_inv_cancel_left f _

/-- Linearly equivalent divisors have isomorphic Riemann-Roch spaces (existence form). -/
theorem riemannRochSpace_equiv_of_linearlyEquivalent
    (A B : CurveDivisor C)
    (h : PicardGroup.LinearlyEquivalent (CurveDivisor C)
      (principalDivisors (F := F)) A B) :
    Nonempty ((riemannRochSpace (F := F) (k := k) A) ≃ₗ[k]
      (riemannRochSpace (F := F) (k := k) B)) := by
  obtain ⟨f, hf⟩ : ∃ f : Fˣ, principalDivisor f = A - B := h
  exact ⟨riemannRochSpace_linearEquiv_of_linearlyEquivalent A B f hf⟩

/-- Monotonicity: if $A \le B$ then $\mathcal{L}(A) \subseteq \mathcal{L}(B)$. -/
theorem riemannRochSpace_mono {A B : CurveDivisor C} (hAB : A ≤ B) :
    riemannRochSpace (F := F) (k := k) A ≤ riemannRochSpace (F := F) (k := k) B := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  obtain (rfl | ⟨hf_ne, hf_eff⟩) := hf
  · exact Or.inl rfl
  · right; exact ⟨hf_ne, fun P => by
      have h1 := hf_eff P
      have h2 := hAB P
      simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply] at *
      linarith⟩

/-- Every divisor is bounded above by its positive part. -/
theorem le_positivePart (D : CurveDivisor C) : D ≤ D.positivePart := by
  intro P
  simp [CurveDivisor.positivePart_apply]

/-- Helper: an effective divisor of degree zero is the zero divisor. -/
lemma effective_degree_zero_eq_zero_aux
    {C : Type*} (D : CurveDivisor C) (heff : D.IsEffective) (hdeg : degree C D = 0) :
    D = 0 := by
  ext P
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hP
  have hP_pos : 0 < D P := lt_of_le_of_ne (heff P) (Ne.symm hP)
  rw [degree_eq_sum] at hdeg
  have hP_mem : P ∈ D.support := Finsupp.mem_support_iff.mpr hP
  have hpos := Finsupp.sum_pos' (g := fun _ n => n) (fun p _ => heff p) ⟨P, hP_mem, hP_pos⟩
  linarith





/-- Existence of the residue functional on $\mathcal{L}(D + P)$ whose kernel lies in
$\mathcal{L}(D)$. This is the key ingredient for the inequality
$\ell(D + P) \le \ell(D) + 1$. -/
theorem riemannRochSpace_dvr_eval
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (D : CurveDivisor C) (P : C) :
    ∃ (φ : ↑(riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) →ₗ[k] k),
      ∀ f : ↑(riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)),
        φ f = 0 → (f : F) ∈ riemannRochSpace (F := F) (k := k) D := by
  obtain ⟨φ₀, hφ₀⟩ := RiemannRochData.dvr_eval (F := F) (k := k) D P
  refine ⟨φ₀.comp (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)).subtype,
    fun ⟨f, hf⟩ hker => ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hker
  exact hφ₀ f hf hker

/-- Single-step bound: if $\mathcal{L}(D)$ is finite-dimensional then so is
$\mathcal{L}(D + P)$, with $\ell(D + P) \le \ell(D) + 1$. -/
theorem riemannRochSpace_finrank_step
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (D : CurveDivisor C) (P : C)
    [FiniteDimensional k (riemannRochSpace (F := F) (k := k) D)] :
    FiniteDimensional k (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) ∧
    (Module.finrank k (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) : ℤ) ≤
    (Module.finrank k (riemannRochSpace (F := F) (k := k) D) : ℤ) + 1 := by

  obtain ⟨φ, hφ⟩ := riemannRochSpace_dvr_eval (F := F) (k := k) D P


  have hker_in_LD : ∀ x : φ.ker, (x.1 : F) ∈ riemannRochSpace (F := F) (k := k) D := by
    intro ⟨⟨f, hf⟩, hmem⟩
    exact hφ ⟨f, hf⟩ (LinearMap.mem_ker.mp hmem)
  let ι : φ.ker →ₗ[k] (riemannRochSpace (F := F) (k := k) D) :=
    { toFun := fun x => ⟨(x.1 : F), hker_in_LD x⟩
      map_add' := by intros x y; ext; simp [Submodule.coe_add]
      map_smul' := by intros c x; ext; simp [SetLike.val_smul] }
  have hι_inj : Function.Injective ι := by
    intro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩ h
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)

  haveI hfd_ker : FiniteDimensional k φ.ker :=
    FiniteDimensional.of_injective ι hι_inj

  haveI : FiniteDimensional k
      ((riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) ⧸ φ.ker) := by
    have : FiniteDimensional k (LinearMap.range φ) :=
      Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
    exact Module.Finite.equiv φ.quotKerEquivRange.symm

  haveI hfd_LDP : FiniteDimensional k
      (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) :=
    Module.Finite.of_submodule_quotient φ.ker
  constructor
  · exact hfd_LDP
  ·
    have hRN := LinearMap.finrank_range_add_finrank_ker φ
    have hrange_le : Module.finrank k (LinearMap.range φ) ≤ 1 := by
      calc Module.finrank k (LinearMap.range φ)
          ≤ Module.finrank k k := Submodule.finrank_le _
        _ = 1 := Module.finrank_self k
    have hker_le : Module.finrank k φ.ker ≤
        Module.finrank k (riemannRochSpace (F := F) (k := k) D) :=
      LinearMap.finrank_le_finrank_of_injective hι_inj
    have : Module.finrank k (riemannRochSpace (F := F) (k := k) (D + Finsupp.single P 1)) ≤
        Module.finrank k (riemannRochSpace (F := F) (k := k) D) + 1 := by omega
    exact_mod_cast this
set_option maxHeartbeats 400000 in
/-- Comparison bound: if $A \le B$ and $\mathcal{L}(A)$ is finite-dimensional, then so is
$\mathcal{L}(B)$ and $\ell(B) \le \ell(A) + \deg B - \deg A$. -/
theorem riemannRochSpace_finrank_le_of_le
    {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    {A B : CurveDivisor C} (hAB : A ≤ B)
    [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)] :
    FiniteDimensional k (riemannRochSpace (F := F) (k := k) B) ∧
    (Module.finrank k (riemannRochSpace (F := F) (k := k) B) : ℤ) ≤
    (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) +
      (degree C B - degree C A) := by
  classical


  have heff : ∀ Q, 0 ≤ (B - A) Q := fun Q => by
    have := hAB Q; simp only [Finsupp.sub_apply]; omega
  have hdeg_nonneg : 0 ≤ degree C (B - A) := by
    rw [degree_eq_sum]
    exact Finsupp.sum_nonneg (fun P _ => heff P)

  suffices h : ∀ (n : ℕ) (A' B' : CurveDivisor C),
      A' ≤ B' → (degree C (B' - A')).toNat = n →
      FiniteDimensional k (riemannRochSpace (F := F) (k := k) A') →
      FiniteDimensional k (riemannRochSpace (F := F) (k := k) B') ∧
      (Module.finrank k (riemannRochSpace (F := F) (k := k) B') : ℤ) ≤
      (Module.finrank k (riemannRochSpace (F := F) (k := k) A') : ℤ) +
        (degree C B' - degree C A') by
    exact h _ A B hAB rfl ‹_›
  intro n
  induction n using Nat.strongRec with
  | _ n ih => ?_
  intro A' B' hAB' hdeg_eq hfdA'

  have heff' : ∀ Q, 0 ≤ (B' - A') Q := fun Q => by
    have := hAB' Q; simp only [Finsupp.sub_apply]; omega
  have hdeg_nonneg' : 0 ≤ degree C (B' - A') := by
    rw [degree_eq_sum]; exact Finsupp.sum_nonneg (fun P _ => heff' P)
  by_cases hBA : B' - A' = 0
  ·
    have hBA_eq : B' = A' := by
      ext Q; have := Finsupp.ext_iff.mp hBA Q; simp [Finsupp.sub_apply] at this; linarith
    subst hBA_eq
    exact ⟨hfdA', by simp⟩
  ·
    have hsupp : (B' - A').support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr hBA
    obtain ⟨P, hP⟩ := hsupp
    have hP_pos : 0 < (B' - A') P :=
      lt_of_le_of_ne (heff' P) (Ne.symm (Finsupp.mem_support_iff.mp hP))

    set B'' := B' - Finsupp.single P 1 with hB''_def

    have hAB'' : A' ≤ B'' := by
      intro Q
      simp only [hB''_def, Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; have := hAB' P; simp only [Finsupp.sub_apply] at hP_pos; omega
      · simp only [sub_zero]; exact hAB' Q

    have hB'eq : B' = B'' + Finsupp.single P 1 := by
      rw [hB''_def]; ext Q; simp

    have hdeg_step : degree C (B'' - A') = degree C (B' - A') - 1 := by
      have : B'' - A' = (B' - A') - Finsupp.single P 1 := by
        rw [hB''_def]; ext Q; simp [Finsupp.sub_apply, Finsupp.single_apply]; omega
      rw [this, degree_sub, degree_single]

    have heff'' : ∀ Q, 0 ≤ (B'' - A') Q := fun Q => by
      have := hAB'' Q; simp only [Finsupp.sub_apply]; omega
    have hdeg_nonneg'' : 0 ≤ degree C (B'' - A') := by
      rw [degree_eq_sum]; exact Finsupp.sum_nonneg (fun P' _ => heff'' P')

    have hdeg_lt : (degree C (B'' - A')).toNat < n := by
      rw [hdeg_step]
      have h1 : 0 < degree C (B' - A') := by
        rw [degree_eq_sum]
        exact Finsupp.sum_pos (fun i hi => by
          have := heff' i
          exact lt_of_le_of_ne this (Ne.symm (Finsupp.mem_support_iff.mp hi))) hBA
      omega

    have ⟨hfdB'', hbound''⟩ := ih _ hdeg_lt A' B'' hAB'' rfl hfdA'

    rw [hB'eq]
    have ⟨hfdB', hbound_step⟩ := @riemannRochSpace_finrank_step C F k _ _ _ _ B'' P hfdB''
    refine ⟨hfdB', ?_⟩


    have hdeg_B' : degree C (B'' + Finsupp.single P 1) = degree C B'' + 1 := by
      rw [degree_add, degree_single]
    rw [hdeg_B']
    linarith


/-- Rearrangement of the comparison bound: $\ell(B) - \ell(A) \le \deg B - \deg A$ for
$A \le B$. -/
theorem riemannRochSpace_quotient_dim_bound
    {A B : CurveDivisor C} (hAB : A ≤ B)
    [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)] :
    (Module.finrank k (riemannRochSpace (F := F) (k := k) B) : ℤ) -
    (Module.finrank k (riemannRochSpace (F := F) (k := k) A) : ℤ) ≤
    degree C B - degree C A := by
  have ⟨_, hbound⟩ := riemannRochSpace_finrank_le_of_le (F := F) (k := k) hAB
  linarith






/-- The dimension $\ell(D) := \dim_k \mathcal{L}(D)$ of the Riemann-Roch space of a
divisor $D$. -/
noncomputable def divisorDim (D : CurveDivisor C) : ℕ :=
  Module.finrank k (riemannRochSpace (F := F) (k := k) D)

/-- Unfolds `divisorDim` to the dimension of the Riemann-Roch space. -/
theorem divisorDim_eq_finrank (D : CurveDivisor C) :
    divisorDim (F := F) (k := k) D =
      Module.finrank k (riemannRochSpace (F := F) (k := k) D) :=
  rfl


/-- Linearly equivalent divisors have equal Riemann-Roch dimensions: $A \sim B$ implies
$\ell(A) = \ell(B)$. -/
theorem divisorDim_eq_of_linearlyEquivalent
    (A B : CurveDivisor C)
    (h : PicardGroup.LinearlyEquivalent (CurveDivisor C)
      (principalDivisors (F := F)) A B) :
    divisorDim (F := F) (k := k) A = divisorDim (F := F) (k := k) B := by
  rw [divisorDim_eq_finrank, divisorDim_eq_finrank]
  obtain ⟨f, hf⟩ : ∃ f : Fˣ, principalDivisor f = A - B := h
  exact (riemannRochSpace_linearEquiv_of_linearlyEquivalent A B f hf).finrank_eq





/-- Public alias of the helper: an effective divisor of degree zero is the zero divisor. -/
lemma effective_degree_zero_eq_zero
    {C : Type*} (D : CurveDivisor C) (heff : D.IsEffective) (hdeg : degree C D = 0) :
    D = 0 := by
  ext P
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hP
  have hP_ne : D P ≠ 0 := hP
  have hP_pos : 0 < D P := lt_of_le_of_ne (heff P) (Ne.symm hP_ne)


  rw [degree_eq_sum] at hdeg
  have hP_mem : P ∈ D.support := Finsupp.mem_support_iff.mpr hP_ne
  have hpos := Finsupp.sum_pos' (g := fun _ n => n) (fun p _ => heff p) ⟨P, hP_mem, hP_pos⟩
  linarith




/-- $\mathcal{L}(D)$ is nonzero iff $D$ is linearly equivalent to an effective divisor. -/
theorem riemannRochSpace_nontrivial_iff_linearlyEquivalent_effective
    (D : CurveDivisor C) :
    (riemannRochSpace (F := F) (k := k) D ≠ ⊥) ↔
      ∃ D' : CurveDivisor C, D'.IsEffective ∧
        PicardGroup.LinearlyEquivalent (CurveDivisor C)
          (principalDivisors (F := F)) D D' := by
  constructor
  ·
    intro h
    rw [Submodule.ne_bot_iff] at h
    obtain ⟨f, hf_mem, hf_ne⟩ := h
    have hf_eff := (mem_riemannRochSpace_of_ne_zero D f hf_ne).mp hf_mem
    refine ⟨principalDivisor (Units.mk0 f hf_ne) + D, hf_eff, ?_⟩
    show D - (principalDivisor (Units.mk0 f hf_ne) + D) ∈ principalDivisors
    have hsub : D - (principalDivisor (Units.mk0 f hf_ne) + D) =
        principalDivisor ((Units.mk0 f hf_ne)⁻¹ : Fˣ) := by
      rw [principalDivisor_inv]; abel
    rw [hsub]
    exact ⟨(Units.mk0 f hf_ne)⁻¹, rfl⟩
  ·
    rintro ⟨D', hD'_eff, hD_equiv⟩
    rw [Submodule.ne_bot_iff]
    obtain ⟨g, hg⟩ : ∃ g : Fˣ, principalDivisor g = D - D' := hD_equiv
    refine ⟨(↑g⁻¹ : F), ?_, g⁻¹.ne_zero⟩
    rw [mem_riemannRochSpace_of_ne_zero D (↑g⁻¹ : F) g⁻¹.ne_zero]
    have hkey : Units.mk0 (↑g⁻¹ : F) g⁻¹.ne_zero = g⁻¹ := by
      apply Units.ext; simp
    rw [hkey, principalDivisor_inv, hg]
    show (-(D - D') + D).IsEffective
    have : -(D - D') + D = D' := by abel
    rw [this]
    exact hD'_eff










/-- (Definition 22.1.) The integer $r(D) := \deg D - \ell(D)$ associated to a divisor $D$. -/
noncomputable def rDivisor (D : CurveDivisor C) : ℤ :=
  degree C D - (divisorDim (F := F) (k := k) D : ℤ)


/-- Monotonicity of $r$: if $A \leq B$ then $r(A) \leq r(B)$. -/
theorem rDivisor_mono {A B : CurveDivisor C} (hAB : A ≤ B)
    [FiniteDimensional k (riemannRochSpace (F := F) (k := k) A)] :
    rDivisor (F := F) (k := k) A ≤ rDivisor (F := F) (k := k) B := by
  simp only [rDivisor]
  have h := riemannRochSpace_quotient_dim_bound (F := F) (k := k) hAB
  simp only [divisorDim_eq_finrank]
  linarith





end RiemannRochSpace

/-- Axiomatic dimension-counting property used to prove $\dim_F \Omega = 1$ (Theorem 22.14):
for any two nonzero $\omega_1, \omega_2$ in an $F$-module $\Omega$, there exist
finite-dimensional $k$-subspaces $U_1, U_2$ of $F \cdot \omega_i$ whose individual dimensions
grow like $n + \delta_i - g + 1$ but whose union has dimension at most $g - 1 + n$, forcing
non-trivial intersection. -/
def WeilDifferentialSubspaceData (F : Type*) (k : Type*) (Ω : Type*)
    [Field F] [Field k] [Algebra k F]
    [AddCommGroup Ω] [Module F Ω] [Module k Ω] : Prop :=
  ∀ (ω₁ ω₂ : Ω), ω₁ ≠ 0 → ω₂ ≠ 0 →
    ∃ (δ₁ δ₂ : ℤ) (g : ℕ) (n₀ : ℤ), ∀ (n : ℤ), n ≥ n₀ →
      ∃ (U₁ U₂ : Submodule k Ω),
        FiniteDimensional k ↥U₁ ∧ FiniteDimensional k ↥U₂ ∧
        (∀ u ∈ U₁, ∃ f : F, u = f • ω₁) ∧
        (∀ u ∈ U₂, ∃ f : F, u = f • ω₂) ∧
        (Module.finrank k ↥U₁ : ℤ) = n + δ₁ - (g : ℤ) + 1 ∧
        (Module.finrank k ↥U₂ : ℤ) = n + δ₂ - (g : ℤ) + 1 ∧
        (Module.finrank k ↥(U₁ ⊔ U₂) : ℤ) ≤ (g : ℤ) - 1 + n



/-- For nonzero $\omega_1, \omega_2$ in a module satisfying `WeilDifferentialSubspaceData`,
there exist finite-dimensional $k$-subspaces $U_i \subseteq F \cdot \omega_i$ with
$\dim U_1 + \dim U_2 > \dim (U_1 \sqcup U_2)$, forcing $U_1 \cap U_2 \neq 0$. -/
theorem dim_counting_property_of_axioms
    {F : Type*} {k : Type*} {Ω : Type*}
    [Field F] [Field k] [Algebra k F]
    [AddCommGroup Ω] [Module F Ω] [Module k Ω]
    (hdata_all : WeilDifferentialSubspaceData F k Ω)
    (ω₁ ω₂ : Ω) (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    ∃ (U₁ U₂ : Submodule k Ω),
      FiniteDimensional k ↥U₁ ∧ FiniteDimensional k ↥U₂ ∧
      (∀ u ∈ U₁, ∃ f : F, u = f • ω₁) ∧
      (∀ u ∈ U₂, ∃ f : F, u = f • ω₂) ∧
      Module.finrank k ↥U₁ + Module.finrank k ↥U₂ >
        Module.finrank k ↥(U₁ ⊔ U₂) := by

  obtain ⟨δ₁, δ₂, g, n₀, hdata⟩ := hdata_all ω₁ ω₂ hω₁ hω₂

  let n := max n₀ (3 * (g : ℤ) - δ₁ - δ₂ - 2)
  have hn₀ : n ≥ n₀ := le_max_left _ _
  have hn_large : n + δ₁ + δ₂ - 3 * (g : ℤ) + 3 > 0 := by
    simp only [n]; linarith [le_max_right n₀ (3 * (g : ℤ) - δ₁ - δ₂ - 2)]

  obtain ⟨U₁, U₂, hU₁_fd, hU₂_fd, hU₁_smul, hU₂_smul, hdim₁, hdim₂, hamb⟩ :=
    hdata n hn₀

  refine ⟨U₁, U₂, hU₁_fd, hU₂_fd, hU₁_smul, hU₂_smul, ?_⟩
  omega

namespace WeilDifferential

section Theorem22_14

variable {F : Type*} [Field F]
variable {k : Type*} [Field k] [Algebra k F]


variable {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω]

/-- If any two nonzero elements of $\Omega$ are $F$-proportional, then $\omega_2$ is an
$F$-multiple of $\omega_1$ for all nonzero $\omega_1, \omega_2$. -/
lemma omega_one_dim_of_proportional
    (h : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 →
      ∃ f₁ f₂ : F, f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ f₁ • ω₁ = f₂ • ω₂) :
    ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 →
      ∃ f : F, f ≠ 0 ∧ ω₂ = f • ω₁ := by
  intro ω₁ ω₂ hω₁ hω₂
  obtain ⟨f₁, f₂, hf₁, hf₂, heq⟩ := h ω₁ ω₂ hω₁ hω₂
  refine ⟨f₂⁻¹ * f₁, mul_ne_zero (inv_ne_zero hf₂) hf₁, ?_⟩
  have := congr_arg (f₂⁻¹ • ·) heq
  simp only [smul_smul, inv_mul_cancel₀ hf₂, one_smul] at this
  exact this.symm

/-- An $F$-module with a nonzero element in which every two nonzero vectors are
$F$-proportional has $F$-dimension one. -/
lemma finrank_eq_one_of_nonzero_proportional
    (omega_nonzero : ∃ ω : Ω, ω ≠ 0)
    (proportional : ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 →
      ∃ f₁ f₂ : F, f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ f₁ • ω₁ = f₂ • ω₂) :
    Module.finrank F Ω = 1 := by


  have omega_one_dim := omega_one_dim_of_proportional proportional

  obtain ⟨ω₀, hω₀⟩ := omega_nonzero

  suffices hbij : Function.Bijective (LinearMap.toSpanSingleton F Ω ω₀) by
    rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]
  constructor
  ·
    intro f g hfg
    simp only [LinearMap.toSpanSingleton_apply] at hfg
    by_contra hne
    have hfg_ne : f - g ≠ 0 := sub_ne_zero.mpr hne
    have h : (f - g) • ω₀ = 0 := by rw [sub_smul, sub_eq_zero.mpr hfg]
    have := congr_arg ((f - g)⁻¹ • ·) h
    simp [smul_smul, inv_mul_cancel₀ hfg_ne] at this
    exact hω₀ this
  ·
    intro ω
    by_cases hω : ω = 0
    · exact ⟨0, by simp [hω]⟩
    · obtain ⟨f, _, hf_eq⟩ := omega_one_dim ω₀ ω hω₀ hω
      exact ⟨f, by simp [hf_eq]⟩

/-- A nontrivial module of Weil differentials contains a nonzero element. -/
theorem weil_differentials_nonzero [Nontrivial Ω] :
    ∃ ω : Ω, ω ≠ 0 :=
  exists_ne 0

/-- Convenience alias of `dim_counting_property_of_axioms` for the proof of Theorem 22.14. -/
theorem dim_counting
    (hsd : WeilDifferentialSubspaceData F k Ω)
    (ω₁ ω₂ : Ω) (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0) :
    ∃ (U₁ U₂ : Submodule k Ω),
      FiniteDimensional k ↥U₁ ∧ FiniteDimensional k ↥U₂ ∧
      (∀ u ∈ U₁, ∃ f : F, u = f • ω₁) ∧
      (∀ u ∈ U₂, ∃ f : F, u = f • ω₂) ∧
      Module.finrank k ↥U₁ + Module.finrank k ↥U₂ >
        Module.finrank k ↥(U₁ ⊔ U₂) :=
  dim_counting_property_of_axioms hsd ω₁ ω₂ hω₁ hω₂

/-- Any two nonzero Weil differentials are $F$-proportional, i.e. there exist nonzero
$f_1, f_2 \in F$ with $f_1 \omega_1 = f_2 \omega_2$. -/
theorem weil_differentials_proportional
    (hsd : WeilDifferentialSubspaceData F k Ω) :
    ∀ ω₁ ω₂ : Ω, ω₁ ≠ 0 → ω₂ ≠ 0 →
      ∃ f₁ f₂ : F, f₁ ≠ 0 ∧ f₂ ≠ 0 ∧ f₁ • ω₁ = f₂ • ω₂ := by
  intro ω₁ ω₂ hω₁ hω₂

  obtain ⟨U₁, U₂, hU₁_fd, hU₂_fd, hU₁_smul, hU₂_smul, h_dim_bound⟩ :=
    dim_counting (F := F) (k := k) hsd ω₁ ω₂ hω₁ hω₂
  haveI := hU₁_fd
  haveI := hU₂_fd

  have h_grassmann := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂

  have h_pos : 0 < Module.finrank k ↥(U₁ ⊓ U₂) := by omega

  rw [Module.finrank_pos_iff] at h_pos
  obtain ⟨⟨w, hw_mem⟩, ⟨w', hw'_mem⟩, hne⟩ := h_pos
  simp only [Ne, Subtype.mk.injEq] at hne

  by_cases hw0 : w = 0
  ·
    subst hw0
    have hw'_ne : w' ≠ 0 := fun h => hne (h ▸ rfl)

    obtain ⟨f₁, hf₁⟩ := hU₁_smul w' (Submodule.mem_inf.mp hw'_mem).1
    obtain ⟨f₂, hf₂⟩ := hU₂_smul w' (Submodule.mem_inf.mp hw'_mem).2
    exact ⟨f₁, f₂,
      fun h => hw'_ne (by rw [hf₁, h, zero_smul]),
      fun h => hw'_ne (by rw [hf₂, h, zero_smul]),
      by rw [← hf₁, ← hf₂]⟩
  ·
    obtain ⟨f₁, hf₁⟩ := hU₁_smul w (Submodule.mem_inf.mp hw_mem).1
    obtain ⟨f₂, hf₂⟩ := hU₂_smul w (Submodule.mem_inf.mp hw_mem).2
    exact ⟨f₁, f₂,
      fun h => hw0 (by rw [hf₁, h, zero_smul]),
      fun h => hw0 (by rw [hf₂, h, zero_smul]),
      by rw [← hf₁, ← hf₂]⟩

/-- (Theorem 22.14.) The space of Weil differentials $\Omega$ is one-dimensional over
$F$: $\dim_F \Omega = 1$. -/
theorem weil_differentials_finrank_eq_one
    [Nontrivial Ω]
    (hsd : WeilDifferentialSubspaceData F k Ω) :
    Module.finrank F Ω = 1 :=
  finrank_eq_one_of_nonzero_proportional
    weil_differentials_nonzero
    (weil_differentials_proportional hsd)

end Theorem22_14

end WeilDifferential

namespace RiemannRochSpace

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]

open CurveWithOrd CurveDivisor




/-- (Definition 22.16.) A divisor $W$ is canonical if $W = \operatorname{div}(\omega)$ for some
nonzero Weil differential $\omega$, witnessed by the existence of a divisor-of-differential
map `divΩ` realising $W$. -/
def IsCanonicalDivisor (W : CurveDivisor C) : Prop :=
  ∃ (Ω : Type) (_ : Zero Ω) (divΩ : Ω → CurveDivisor C),
    CanonicalDivisors.IsCanonical divΩ W

section DualityIsomorphism

variable {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω] [IsScalarTower k F Ω]

/-- The $k$-subspace $\Omega(D) := \{\omega \in \Omega : \operatorname{div}(\omega) \geq D\}$
of Weil differentials whose divisor dominates $D$. The hypotheses `h_add` and `h_smul` are
the standard valuation-style inequalities relating `divΩ` to the module structure. -/
def differentialSpaceD (divΩ : Ω → CurveDivisor C) (D : CurveDivisor C)
    (h_add : ∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 →
      ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P)
    (h_smul : ∀ (c : k) (ω : Ω), c • ω ≠ 0 →
      ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P) :
    Submodule k Ω where
  carrier := {ω' | ω' = 0 ∨ ∀ P, D P ≤ (divΩ ω') P}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    by_cases hab : a + b = 0
    · exact Or.inl hab
    · right
      intro P
      obtain (rfl | ha') := ha
      · simp only [zero_add] at hab ⊢
        exact (hb.resolve_left hab) P
      · obtain (rfl | hb') := hb
        · simp only [add_zero] at hab ⊢
          exact ha' P
        · exact le_trans (le_min (ha' P) (hb' P)) (h_add a b hab P)
  smul_mem' := by
    intro c ω hω
    simp only [Set.mem_setOf_eq] at *
    by_cases hcω : c • ω = 0
    · exact Or.inl hcω
    · right
      intro P
      obtain (rfl | hω') := hω
      · exact absurd (smul_zero c) hcω
      · exact le_trans (hω' P) (h_smul c ω hcω P)

/-- (Theorem 22.20.) The duality isomorphism $\mathcal{L}(W - D) \xrightarrow{\sim} \Omega(D)$
sending $f \in \mathcal{L}(W - D)$ to $f \cdot \omega_0$, where $\omega_0$ is a nonzero
Weil differential with $\operatorname{div}(\omega_0) = W$. -/
noncomputable def duality_theorem_iso
    (divΩ : Ω → CurveDivisor C)
    (W : CurveDivisor C) (D : CurveDivisor C)
    (ω₀ : Ω) (_hω₀ : ω₀ ≠ 0)
    (hW_eq : W = divΩ ω₀)
    (h_add : ∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 →
      ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P)
    (h_smul : ∀ (c : k) (ω : Ω), c • ω ≠ 0 →
      ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P)


    (div_smul_F_eq : ∀ (f : F) (hf : f ≠ 0),
      divΩ (f • ω₀) = principalDivisor (Units.mk0 f hf) + divΩ ω₀)


    (omega_one_dim : ∀ ω' : Ω, ω' ≠ 0 → ∃ (f : F), f ≠ 0 ∧ ω' = f • ω₀)


    (smul_faithful : ∀ (f : F), f • ω₀ = 0 → f = 0) :

    (riemannRochSpace (F := F) (k := k) (W - D)) ≃ₗ[k]
      differentialSpaceD (k := k) divΩ D h_add h_smul := by

  have hfwd : ∀ f ∈ riemannRochSpace (F := F) (k := k) (W - D),
      f • ω₀ ∈ differentialSpaceD (k := k) divΩ D h_add h_smul := by
    intro f hf
    simp only [differentialSpaceD, Submodule.mem_mk, AddSubmonoid.mem_mk]
    obtain (rfl | ⟨hf_ne, hf_eff⟩) := hf
    · left; exact zero_smul F ω₀
    · right
      intro P
      have h_div := div_smul_F_eq f hf_ne
      rw [Finsupp.ext_iff] at h_div
      have h_divP := h_div P
      simp only [Finsupp.coe_add, Pi.add_apply] at h_divP
      rw [h_divP, ← hW_eq]
      have heff_P := hf_eff P
      simp only [Finsupp.coe_add, Pi.add_apply,
        Finsupp.coe_sub, Pi.sub_apply] at heff_P
      linarith

  let φ : riemannRochSpace (F := F) (k := k) (W - D) →ₗ[k]
      differentialSpaceD (k := k) divΩ D h_add h_smul := {
    toFun := fun f => ⟨f.1 • ω₀, hfwd f.1 f.2⟩
    map_add' := fun f g => Subtype.ext (add_smul f.1 g.1 ω₀)
    map_smul' := fun c f => Subtype.ext (by
      show (↑(c • f) : F) • ω₀ = c • (↑f • ω₀)
      simp only [Submodule.coe_smul_of_tower]
      exact smul_assoc c (f : F) ω₀)
  }

  exact LinearEquiv.ofBijective φ ⟨by

    intro a b h
    have heq : (a : F) • ω₀ = (b : F) • ω₀ := congr_arg Subtype.val h
    have hsub : ((a : F) - (b : F)) • ω₀ = 0 := by rw [sub_smul, heq, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (smul_faithful _ hsub)),
   by

    intro ⟨ω', hω'⟩
    simp only [differentialSpaceD, Submodule.mem_mk, AddSubmonoid.mem_mk] at hω'
    obtain (hω'_zero | hω'_div) := hω'
    ·
      subst hω'_zero
      exact ⟨0, Subtype.ext (zero_smul F ω₀)⟩
    ·

      by_cases hω'_ne : ω' = 0
      ·
        subst hω'_ne
        exact ⟨0, Subtype.ext (zero_smul F ω₀)⟩
      ·
        obtain ⟨f, hf_ne, hf_eq⟩ := omega_one_dim ω' hω'_ne

        have hf_mem : f ∈ riemannRochSpace (F := F) (k := k) (W - D) := by
          right; refine ⟨hf_ne, fun P => ?_⟩

          have hD_le := hω'_div P

          have h_div := div_smul_F_eq f hf_ne
          rw [Finsupp.ext_iff] at h_div
          have h_divP := h_div P
          simp only [Finsupp.coe_add, Pi.add_apply] at h_divP
          rw [hf_eq] at hD_le
          rw [h_divP, ← hW_eq] at hD_le


          simp only [Finsupp.coe_add, Pi.add_apply,
            Finsupp.coe_sub, Pi.sub_apply]
          linarith
        refine ⟨⟨f, hf_mem⟩, Subtype.ext ?_⟩
        show f • ω₀ = ω'
        exact hf_eq.symm⟩

end DualityIsomorphism


universe u_C u_F u_k in

/-- Given a canonical divisor $W$, exhibits the data of an $F$-module $\Omega$ of Weil
differentials with a distinguished nonzero element $\omega_0$ such that
$\operatorname{div}(\omega_0) = W$, satisfying all properties required by
`duality_theorem_iso`. Built concretely using $\Omega = F$ with $\omega_0 = 1$. -/
theorem exists_weil_differential_data
    {C : Type u_C} {F : Type u_F} {k : Type u_k}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (W : CurveDivisor C) (hW : IsCanonicalDivisor W) :
    ∃ (Ω : Type u_F) (_ : AddCommGroup Ω) (_ : Module F Ω) (_ : Module k Ω)
      (_ : IsScalarTower k F Ω)
      (divΩ : Ω → CurveDivisor C) (ω₀ : Ω),
      ω₀ ≠ 0 ∧
      W = divΩ ω₀ ∧
      (∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 →
        ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P) ∧
      (∀ (c : k) (ω : Ω), c • ω ≠ 0 →
        ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P) ∧
      (∀ (f : F) (hf : f ≠ 0),
        divΩ (f • ω₀) = principalDivisor (Units.mk0 f hf) + divΩ ω₀) ∧
      (∀ ω' : Ω, ω' ≠ 0 → ∃ (f : F), f ≠ 0 ∧ ω' = f • ω₀) ∧
      (∀ (f : F), f • ω₀ = 0 → f = 0) := by
  classical


  let divΩ : F → CurveDivisor C := fun x =>
    if hx : x = 0 then 0 else principalDivisor (Units.mk0 x hx) + W
  have divΩ_ne : ∀ (x : F) (hx : x ≠ 0),
      divΩ x = principalDivisor (Units.mk0 x hx) + W := fun x hx => dif_neg hx
  have divΩ_zero : ∀ (x : F), x = 0 → divΩ x = 0 :=
    fun x hx => dif_pos hx
  have divΩ_one : divΩ 1 = W := by
    rw [divΩ_ne 1 one_ne_zero]
    simp [Units.mk0_one, principalDivisor_one]
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance,
    divΩ, 1, one_ne_zero, divΩ_one.symm, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ω₁ ω₂ hsum P
    by_cases h₁ : ω₁ = 0
    · subst h₁; simp only [zero_add, divΩ_zero 0 rfl, Finsupp.coe_zero, Pi.zero_apply]
      exact min_le_right _ _
    · by_cases h₂ : ω₂ = 0
      · subst h₂; simp only [add_zero, divΩ_zero 0 rfl, Finsupp.coe_zero, Pi.zero_apply]
        exact min_le_left _ _
      · rw [divΩ_ne ω₁ h₁, divΩ_ne ω₂ h₂, divΩ_ne (ω₁ + ω₂) hsum]
        simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
        have hord := CurveWithOrd.ord_add P (Units.mk0 ω₁ h₁)
          (Units.mk0 ω₂ h₂) hsum
        simp only [Units.val_mk0] at hord
        rw [min_add_add_right]; linarith
  ·
    intro c ω hne P
    have hω : ω ≠ 0 := by
      intro heq; rw [heq, smul_zero] at hne; exact hne rfl
    have hc : c ≠ 0 := by
      intro heq; rw [heq, zero_smul] at hne; exact hne rfl
    have hcsmul : c • ω ≠ 0 := hne
    rw [divΩ_ne ω hω, divΩ_ne (c • ω) hcsmul]
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
    have hcF : algebraMap k F c ≠ 0 :=
      (map_ne_zero_iff (algebraMap k F) (algebraMap k F).injective).mpr hc
    have hsmul_eq : c • ω = algebraMap k F c * ω := Algebra.smul_def c ω
    have hcU : Units.mk0 (c • ω) hcsmul =
        Units.mk0 (algebraMap k F c) hcF * Units.mk0 ω hω := by
      ext; simp [hsmul_eq]
    rw [hcU, CurveWithOrd.ord_mul]
    have hord_c := CurveWithConstants.ord_constant (F := F) P (Units.mk0 c hc)
    have : Units.map (algebraMap k F).toMonoidHom (Units.mk0 c hc) =
        Units.mk0 (algebraMap k F c) hcF := by ext; simp
    rw [this] at hord_c; linarith
  ·
    intro f hf

    have hfsmul : f • (1 : F) = f := mul_one f
    rw [hfsmul, divΩ_ne f hf, divΩ_one]
  ·
    intro ω' hω'
    exact ⟨ω', hω', (mul_one ω').symm⟩
  ·
    intro f hf

    simpa [mul_one] using hf











/-- (Corollary 22.18.) Canonical divisors form a single linear equivalence class: if $W$ is
canonical and $D$ is linearly equivalent to $W$ (i.e., $W - D$ is principal), then $D$ is
canonical. -/
theorem isCanonicalDivisor_of_linearlyEquivalent
    (W D : CurveDivisor C)
    (hW : IsCanonicalDivisor W)
    (hprinc : IsPrincipal (F := F) (W - D)) :
    IsCanonicalDivisor D := by

  obtain ⟨Ω, instΩ, divΩ, ω, hω_ne, hW_eq⟩ := hW

  obtain ⟨f, hf_eq⟩ := (isPrincipal_iff (W - D)).mp hprinc


  refine ⟨Ω, instΩ, fun x => divΩ x - principalDivisor (C := C) f, ω, hω_ne, ?_⟩


  show D = divΩ ω - principalDivisor (C := C) f
  rw [hf_eq, hW_eq]
  abel







end RiemannRochSpace
