/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Atlas.EllipticCurves.code.Isogenies

universe u

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- The multiplication-by-`n` endomorphism `[n]` on the group of points of a Weierstrass
curve, packaged as an additive group homomorphism `W.Point →+ W.Point`. -/
def multiplicationByN (W : WeierstrassCurve.Affine F) (n : ℤ) : W.Point →+ W.Point :=
  zsmulAddGroupHom n

/-- Evaluating the multiplication-by-`n` map at a point `P` is the same as the integer
scalar multiple `n • P`. -/
@[simp]
theorem multiplicationByN_apply (W : WeierstrassCurve.Affine F) (n : ℤ) (P : W.Point) :
    multiplicationByN W n P = n • P :=
  rfl

/-- The `n`-torsion subgroup `E[n]` of a Weierstrass curve, defined as the kernel of the
multiplication-by-`n` homomorphism. -/
def torsionSubgroup (W : WeierstrassCurve.Affine F) (n : ℤ) : AddSubgroup W.Point :=
  (multiplicationByN W n).ker

/-- A point `P` lies in `E[n]` if and only if `n • P = 0`. -/
@[simp]
theorem mem_torsionSubgroup (W : WeierstrassCurve.Affine F) (n : ℤ) (P : W.Point) :
    P ∈ torsionSubgroup W n ↔ n • P = 0 := by
  simp [torsionSubgroup, multiplicationByN, AddMonoidHom.mem_ker]

/-- Any additive group homomorphism between point groups of Weierstrass curves preserves
the `n`-torsion subgroup. -/
theorem map_mem_torsionSubgroup {W₁ W₂ : WeierstrassCurve.Affine F}
    (φ : W₁.Point →+ W₂.Point) (n : ℤ) (P : W₁.Point)
    (hP : P ∈ torsionSubgroup W₁ n) :
    φ P ∈ torsionSubgroup W₂ n := by
  simp only [mem_torsionSubgroup] at hP ⊢
  rw [← φ.map_zsmul, hP, map_zero]

/-- A Weierstrass curve `W` over a field of characteristic `p` is ordinary if its
`p`-torsion `E[p]` is isomorphic to `ℤ/pℤ` (cf. Definition 6.2 of Sutherland). -/
def IsOrdinary (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p] [Fact (Nat.Prime p)] :
    Prop :=
  Nonempty ((torsionSubgroup W (p : ℤ)) ≃+ ZMod p)

/-- A Weierstrass curve `W` over a field of characteristic `p` is supersingular if its
`p`-torsion `E[p]` is trivial (cf. Definition 6.2 of Sutherland). -/
def IsSupersingular (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p]
    [Fact (Nat.Prime p)] : Prop :=
  torsionSubgroup W (p : ℤ) = ⊥

/-- For a supersingular curve, any point killed by multiplication by `p` is the zero
point. -/
theorem IsSupersingular.torsion_eq_zero {W : WeierstrassCurve.Affine F}
    {p : ℕ} [CharP F p] [Fact (Nat.Prime p)]
    (h : IsSupersingular W p) (P : W.Point) (hP : (p : ℤ) • P = 0) : P = 0 := by
  have : P ∈ torsionSubgroup W (p : ℤ) := by simp [hP]
  rw [h] at this
  exact AddSubgroup.mem_bot.mp this

/-- A curve is supersingular if and only if multiplication by `p` is injective on its
group of points. -/
theorem isSupersingular_iff {W : WeierstrassCurve.Affine F}
    {p : ℕ} [CharP F p] [Fact (Nat.Prime p)] :
    IsSupersingular W p ↔ ∀ (P : W.Point), (p : ℤ) • P = 0 → P = 0 := by
  constructor
  · exact fun h P hP => h.torsion_eq_zero P hP
  · intro h
    rw [IsSupersingular, AddSubgroup.eq_bot_iff_forall]
    intro P hP
    exact h P (by rwa [mem_torsionSubgroup] at hP)

namespace Isogeny

variable {E₁ E₂ : WeierstrassCurve.Affine F}

end Isogeny

variable {E₁ E₂ : WeierstrassCurve.Affine F}

/-- Multiplication-by-`n` is natural with respect to additive group homomorphisms between
point groups: `[n] ∘ α = α ∘ [n]` (cf. Proposition 6.5 of Sutherland). -/
theorem multiplicationByN_comp_hom
    (α : E₁.Point →+ E₂.Point) (n : ℤ) :
    (multiplicationByN E₂ n).comp α = α.comp (multiplicationByN E₁ n) := by
  ext P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply]
  exact (α.map_zsmul P n).symm

/-- The pointwise version of `multiplicationByN_comp_hom`: `n • (α P) = α (n • P)`. -/
theorem multiplicationByN_comm_hom_apply
    (α : E₁.Point →+ E₂.Point) (n : ℤ) (P : E₁.Point) :
    n • (α P) = α (n • P) :=
  (α.map_zsmul P n).symm




section Lemma66

variable {E₀ E₁ E₂ : WeierstrassCurve.Affine F}

/-- Right-cancellation for isogenies (one half of Lemma 6.6): if `α ∘ γ = β ∘ γ` with
`γ` an isogeny (hence surjective), then `α = β` as homomorphisms. -/
theorem Isogeny.right_cancel
    (α β : Isogeny E₁ E₂) (γ : Isogeny E₀ E₁)
    (h : α.toAddMonoidHom.comp γ.toAddMonoidHom = β.toAddMonoidHom.comp γ.toAddMonoidHom) :
    α.toAddMonoidHom = β.toAddMonoidHom := by
  ext Q
  obtain ⟨P, hP⟩ := γ.surjective Q
  have := DFunLike.congr_fun h P
  simp only [AddMonoidHom.comp_apply] at this
  rwa [hP] at this



end Lemma66

end WeierstrassCurve.Affine

noncomputable section

open WeierstrassCurve

/-- The `n`-torsion subgroup `E(K)[n]` of an elliptic curve `E/k` after base change to a
field extension `K`, defined as the torsion subgroup of the projective point group. -/
def EllipticCurve.torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) : AddSubgroup (E.map (algebraMap k K)).toProjective.Point :=
  AddSubgroup.torsionBy (E.map (algebraMap k K)).toProjective.Point n

/-- Membership characterisation: a point `P ∈ E(K)` lies in `E(K)[n]` iff `n • P = 0`. -/
@[simp]
lemma EllipticCurve.mem_torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) (P : (E.map (algebraMap k K)).toProjective.Point) :
    P ∈ EllipticCurve.torsionSubgroup k E K n ↔ n • P = 0 := by
  simp [EllipticCurve.torsionSubgroup]







/-- Supersingularity is preserved under powers of `p`: if `E[p] = 0` then `E[pᵉ] = 0`
for all `e ≥ 1`. -/
theorem EllipticCurve.torsion_prime_char_supersingular
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (p : ℕ) [CharP k p] [Fact (Nat.Prime p)]
    (e : ℕ) (he : 0 < e)
    (hss : EllipticCurve.torsionSubgroup k E K (p : ℤ) = ⊥) :
    EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ e) = ⊥ := by

  induction e with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    ·
      subst hn
      simpa [pow_one] using hss
    ·
      have ih' : EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ n) = ⊥ :=
        ih (Nat.pos_of_ne_zero hn)
      rw [AddSubgroup.eq_bot_iff_forall]
      intro P hP
      rw [EllipticCurve.mem_torsionSubgroup] at hP


      have hpP_mem : (p : ℤ) • P ∈ EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ n) := by
        rw [EllipticCurve.mem_torsionSubgroup, ← mul_smul]


        rw [show (p : ℤ) ^ n * (p : ℤ) = (p : ℤ) ^ (n + 1) from by ring]
        exact hP
      rw [ih'] at hpP_mem
      rw [AddSubgroup.mem_bot] at hpP_mem

      have hP_mem : P ∈ EllipticCurve.torsionSubgroup k E K (p : ℤ) := by
        rw [EllipticCurve.mem_torsionSubgroup]
        exact hpP_mem
      rw [hss] at hP_mem
      exact AddSubgroup.mem_bot.mp hP_mem




end

section Theorem67

open WeierstrassCurve.Affine in
/-- The degree of a composition of isogenies is the product of the degrees:
`deg(ψ ∘ φ) = deg ψ · deg φ`. -/
@[simp] theorem Isogeny.degree_comp {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
    (ψ : Isogeny E₂ E₃) (φ : Isogeny E₁ E₂) :
    (Isogeny.comp ψ φ).degree = ψ.degree * φ.degree := rfl









set_option maxHeartbeats 800000 in
open WeierstrassCurve.Affine in
/-- Existence of the dual via composition: if `α` factors as `γ ∘ β` with duals existing
for both `β` and `γ`, then a dual exists for `α` (used in the inductive proof of 6.7). -/
theorem Isogeny.dual_exists_of_comp {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ E_mid : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂)
    (hcomp : γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom)
    (hdeg : γ.degree * β.degree = α.degree)
    (hβ_dual : ∃ (βd : Isogeny E_mid E₁),
      βd.toAddMonoidHom.comp β.toAddMonoidHom =
        multiplicationByN E₁ (β.degree : ℤ))
    (hγ_dual : ∃ (γd : Isogeny E₂ E_mid),
      γd.toAddMonoidHom.comp γ.toAddMonoidHom =
        multiplicationByN E_mid (γ.degree : ℤ)) :
    ∃ (αd : Isogeny E₂ E₁),
      αd.toAddMonoidHom.comp α.toAddMonoidHom =
        multiplicationByN E₁ (α.degree : ℤ) := by
  obtain ⟨βd, hβd⟩ := hβ_dual
  obtain ⟨γd, hγd⟩ := hγ_dual

  refine ⟨Isogeny.comp βd γd, ?_⟩


  have key : ∀ P : E₁.Point,
      βd.toAddMonoidHom (γd.toAddMonoidHom (γ.toAddMonoidHom (β.toAddMonoidHom P))) =
        (↑α.degree : ℤ) • P := by
    intro P

    have h1 : γd.toAddMonoidHom (γ.toAddMonoidHom (β.toAddMonoidHom P)) =
        (γ.degree : ℤ) • (β.toAddMonoidHom P) := by
      have := DFunLike.congr_fun hγd (β.toAddMonoidHom P)
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
      exact this
    rw [h1]

    rw [map_zsmul βd.toAddMonoidHom]

    have h2 : βd.toAddMonoidHom (β.toAddMonoidHom P) = (β.degree : ℤ) • P := by
      have := DFunLike.congr_fun hβd P
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
      exact this
    rw [h2, ← mul_smul]
    congr 1
    exact_mod_cast hdeg

  ext P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply]


  have hαP : α.toAddMonoidHom P = γ.toAddMonoidHom (β.toAddMonoidHom P) := by
    have := DFunLike.congr_fun hcomp P
    simp only [AddMonoidHom.comp_apply] at this
    exact this.symm


  show βd.toAddMonoidHom (γd.toAddMonoidHom (α.toAddMonoidHom P)) = _
  rw [hαP]
  exact key P





open WeierstrassCurve.Affine in
/-- Factoring through the kernel: if `ker φ ⊆ ker ψ`, then `ψ` factors as `λ ∘ φ` for
some isogeny `λ` (existence statement). -/
theorem Isogeny.factor_through_kernel {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
    (φ : Isogeny E₁ E₂) (ψ : Isogeny E₁ E₃)
    (hker : φ.toAddMonoidHom.ker ≤ ψ.toAddMonoidHom.ker) :
    ∃ (lam : Isogeny E₂ E₃),
      lam.toAddMonoidHom.comp φ.toAddMonoidHom = ψ.toAddMonoidHom := by


  let lamHom : E₂.Point →+ E₃.Point :=
    φ.toAddMonoidHom.liftOfSurjective φ.surjective ⟨ψ.toAddMonoidHom, hker⟩
  have hcomp : lamHom.comp φ.toAddMonoidHom = ψ.toAddMonoidHom := by simp [lamHom]

  have hlam_surj : Function.Surjective lamHom := by
    intro z
    obtain ⟨x, hx⟩ := ψ.surjective z
    exact ⟨φ.toAddMonoidHom x, by simp [lamHom, hx]⟩

  exact ⟨⟨lamHom, hlam_surj, ψ.degree, ψ.degree_pos⟩, hcomp⟩



end Theorem67

open WeierstrassCurve.Affine in
/-- Uniqueness of the dual at the homomorphism level (cf. Theorem 6.7): any two isogenies
`αd₁, αd₂` satisfying the defining equation of the dual agree as homomorphisms. -/
theorem Isogeny.dual_unique {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂)
    (αd₁ αd₂ : Isogeny E₂ E₁)
    (h₁ : αd₁.toAddMonoidHom.comp α.toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ))
    (h₂ : αd₂.toAddMonoidHom.comp α.toAddMonoidHom =
      WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ)) :
    αd₁.toAddMonoidHom = αd₂.toAddMonoidHom :=
  WeierstrassCurve.Affine.Isogeny.right_cancel αd₁ αd₂ α (h₁.trans h₂.symm)


/-- Extensionality for `Isogeny`: two isogenies are equal if their underlying homs and
degrees agree. -/
@[ext]
theorem Isogeny.ext {F : Type u} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    {α β : Isogeny E₁ E₂}
    (h_hom : α.toAddMonoidHom = β.toAddMonoidHom)
    (h_deg : α.degree = β.degree) :
    α = β := by
  cases α; cases β
  simp only [Isogeny.mk.injEq]
  exact ⟨h_hom, h_deg⟩






section Lemma610

open WeierstrassCurve.Affine







end Lemma610

section Lemma611

open WeierstrassCurve.Affine



end Lemma611

section Lemma612

open WeierstrassCurve.Affine


end Lemma612

section Definition613

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)

/-- Definition 6.13: the endomorphism ring `End(E) = Hom(E, E)` as the additive monoid of
endomorphisms of `E.Point`, with multiplication given by composition. -/
abbrev EndRing : Type u :=
  AddMonoid.End E.Point

/-- Ring structure on `EndRing E`, inherited from `AddMonoid.End`. -/
instance : Ring (EndRing E) := AddMonoid.End.instRing

variable {E}

/-- The canonical ring homomorphism `ℤ → End(E)` sending `n` to `[n]`. -/
noncomputable def intToEndRingHom : ℤ →+* EndRing E :=
  Int.castRingHom (EndRing E)

/-- Evaluating `intToEndRingHom n` at a point `P` yields `n • P`. -/
@[simp]
theorem intToEndRingHom_apply (n : ℤ) (P : E.Point) :
    (intToEndRingHom (E := E) n) P = n • P := by
  simp [intToEndRingHom]

/-- The image of `n` under `intToEndRingHom` is the `multiplicationByN` endomorphism. -/
theorem intToEndRingHom_eq_multiplicationByN (n : ℤ) :
    intToEndRingHom (E := E) n = multiplicationByN E n :=
  rfl

/-- Integers (viewed as endomorphisms via `[n]`) commute with every endomorphism of `E`,
i.e. `[n]` lies in the center of `End(E)`. -/
theorem intCast_comm_endomorphism (n : ℤ) (α : EndRing E) :
    (n : EndRing E) * α = α * (n : EndRing E) := by
  apply AddMonoidHom.ext
  intro P
  show (n : EndRing E) (α P) = α ((n : EndRing E) P)
  simp only [AddMonoid.End.intCast_def]
  exact (α.map_zsmul P n).symm

/-- The product in `EndRing E` is composition pointwise: `(α * β) P = α (β P)`. -/
@[simp]
theorem EndRing.mul_apply' (α β : EndRing E) (P : E.Point) :
    (α * β) P = α (β P) := rfl

/-- The sum in `EndRing E` is pointwise addition. -/
@[simp]
theorem EndRing.add_apply' (α β : EndRing E) (P : E.Point) :
    (α + β) P = α P + β P := rfl

/-- The unit `1 : EndRing E` is the identity endomorphism. -/
@[simp]
theorem EndRing.one_apply' (P : E.Point) :
    (1 : EndRing E) P = P := rfl

/-- The zero `0 : EndRing E` sends every point to the zero point. -/
@[simp]
theorem EndRing.zero_apply' (P : E.Point) :
    (0 : EndRing E) P = 0 := rfl

end Definition613

section Lemma616

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}



end Lemma616

section Definition617

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}


/-- Auxiliary trace formula `tr α = 1 + deg α - deg(1 - α)` parameterised by a specific
witness of `1 - α` (cf. Definition 6.17). -/
noncomputable def Isogeny.traceAux
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (_ : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) : ℤ :=
  1 + (α.degree : ℤ) - (oneMinusAlpha.degree : ℤ)





end Definition617

section Theorem618

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}








end Theorem618

section Lemma619

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- Two endomorphisms `α, β` of `E` agree on `n`-torsion iff their underlying maps match
on `E[n]`. This is the predicate denoted `αₙ = βₙ` in Lemma 6.19. -/
def Isogeny.agreeOnTorsion (α β : Isogeny E E) (n : ℤ) : Prop :=
  ∀ (P : E.Point), P ∈ torsionSubgroup E n → α.toAddMonoidHom P = β.toAddMonoidHom P









end Lemma619
