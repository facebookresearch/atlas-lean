/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AffineVarieties
import Atlas.ArithmeticGeometry.code.Varieties

noncomputable section

variable (k : Type*) [Field k]

open MvPolynomial

/-- Evaluation at a point $P \in X$ as a ring homomorphism $\bar{k}[X] \to \bar{k}$ from the coordinate ring. -/
def evalOnCoordRing {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X) :
    AffineCoordinateRingBar X →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet X) (MvPolynomial.eval P)
    (fun _ hf => hf P hP)

/-- Evaluating the class of $g$ in the coordinate ring gives $g(P)$. -/
@[simp]
theorem evalOnCoordRing_mk {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (g : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    evalOnCoordRing k X P hP (Ideal.Quotient.mk (idealOfAlgebraicSet X) g) =
    MvPolynomial.eval P g :=
  rfl

/-- If a polynomial map sends $X$ into $Y$, then its substitution operator $\mathrm{bind}_1$ pulls back the vanishing ideal of $Y$ into the vanishing ideal of $X$. -/
lemma bind₁_mem_idealOfAlgebraicSet_of_maps_to {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (hmaps : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y)
    {f : MvPolynomial (Fin n) (AlgebraicClosure k)}
    (hf : f ∈ idealOfAlgebraicSet Y) :
    (MvPolynomial.bind₁ polys) f ∈ idealOfAlgebraicSet X := by
  intro P hP
  have key : MvPolynomial.eval P ((MvPolynomial.bind₁ polys) f) =
      MvPolynomial.eval (polyMapEval k m n polys P) f := by
    simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
    rfl
  rw [key]
  exact hf _ (hmaps P hP)

/-- The pullback ring homomorphism $\varphi^* : \bar{k}[Y] \to \bar{k}[X]$ induced by an affine morphism $\varphi : X \to Y$. -/
def AffineMorphism.pullback {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y) :
    AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X :=
  Ideal.Quotient.lift (idealOfAlgebraicSet Y)
    ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp
      (MvPolynomial.bind₁ φ.polys).toRingHom)
    (fun f hf => by
      simp only [AlgHom.toRingHom_eq_coe]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (bind₁_mem_idealOfAlgebraicSet_of_maps_to k φ.polys φ.maps_to hf))

/-- Pullback acts on the class of $g$ by substituting the components of $\varphi$ into $g$. -/
@[simp]
theorem AffineMorphism.pullback_mk {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y)
    (g : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g) =
    Ideal.Quotient.mk (idealOfAlgebraicSet X) ((MvPolynomial.bind₁ φ.polys) g) :=
  rfl

/-- Evaluation commutes with pullback: $\mathrm{ev}_P(\varphi^* g) = \mathrm{ev}_{\varphi(P)}(g)$. -/
theorem AffineMorphism.pullback_eval {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (φ : AffineMorphism k m n X Y)
    (g : MvPolynomial (Fin n) (AlgebraicClosure k))
    (P : AffineSpace_k k m) (hP : P ∈ X) :
    evalOnCoordRing k X P hP (φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
    evalOnCoordRing k Y (φ.toFun k P) (φ.maps_to P hP)
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g) := by
  simp only [pullback_mk, evalOnCoordRing_mk]
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  rfl

/-- Any $\bar{k}$-algebra map $\theta : \bar{k}[Y] \to \bar{k}[X]$ is determined on the variable classes; evaluating $\mathrm{ev}_P \circ \theta$ at the class of $g$ equals evaluating $g$ at the point given by the chosen polynomial lifts. -/
lemma ringHom_eq_eval_of_alg {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X)
    (hθ_alg : ∀ r : AlgebraicClosure k,
      θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (hpolys : ∀ j : Fin n,
      Ideal.Quotient.mk (idealOfAlgebraicSet X) (polys j) =
      θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j)))
    (P : AffineSpace_k k m) (hP : P ∈ X) :
    ((evalOnCoordRing k X P hP).comp
      (θ.comp (Ideal.Quotient.mk (idealOfAlgebraicSet Y)))) =
    MvPolynomial.eval (polyMapEval k m n polys P) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    show (evalOnCoordRing k X P hP) (θ (Ideal.Quotient.mk _ (C r))) =
        MvPolynomial.eval (polyMapEval k m n polys P) (C r)
    rw [hθ_alg, evalOnCoordRing_mk, MvPolynomial.eval_C, MvPolynomial.eval_C]
  · intro j
    show (evalOnCoordRing k X P hP) (θ (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
        MvPolynomial.eval (polyMapEval k m n polys P) (MvPolynomial.X j)
    rw [← hpolys j, evalOnCoordRing_mk, MvPolynomial.eval_X]
    rfl

/-- (Corollary 14.9 / 15.9) Every $\bar{k}$-algebra homomorphism $\theta : \bar{k}[Y] \to \bar{k}[X]$ is induced by an affine morphism: there exist polynomials whose induced map sends $X$ into $Y$ and whose pullback is $\theta$. -/
theorem algebraHom_induces_morphism {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (hY : Y = AlgebraicSet k n (idealOfAlgebraicSet Y : Set _))
    (θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X)
    (hθ_alg : ∀ r : AlgebraicClosure k,
      θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r)) :
    ∃ (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)),
      (∀ P ∈ X, polyMapEval k m n polys P ∈ Y) ∧
      (∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k)) (P : AffineSpace_k k m) (hP : P ∈ X),
        evalOnCoordRing k X P hP (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) =
        MvPolynomial.eval (polyMapEval k m n polys P) g) := by

  have hsurj : ∀ j : Fin n, ∃ p : MvPolynomial (Fin m) (AlgebraicClosure k),
      Ideal.Quotient.mk (idealOfAlgebraicSet X) p =
      θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j)) :=
    fun j => Ideal.Quotient.mk_surjective _
  choose polys hpolys using hsurj
  refine ⟨polys, ?_, ?_⟩
  ·
    intro P hP
    rw [hY]

    intro f hf

    have heq := ringHom_eq_eval_of_alg k θ hθ_alg polys hpolys P hP

    have hval : (evalOnCoordRing k X P hP) (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) =
        MvPolynomial.eval (polyMapEval k m n polys P) f :=
      congr_fun (congr_arg DFunLike.coe heq) f

    have hmkY : Ideal.Quotient.mk (idealOfAlgebraicSet Y) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hf
    have : θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f) = 0 := by rw [hmkY]; exact θ.map_zero
    rw [this, (evalOnCoordRing k X P hP).map_zero] at hval
    exact hval.symm
  ·
    intro g P hP
    have heq := ringHom_eq_eval_of_alg k θ hθ_alg polys hpolys P hP
    exact congr_fun (congr_arg DFunLike.coe heq) g

/-- The pullback is contravariantly functorial: $(\psi \circ \varphi)^* = \varphi^* \circ \psi^*$. -/
theorem AffineMorphism.pullback_comp {m n r : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    {Z : Set (AffineSpace_k k r)}
    (ψ : AffineMorphism k n r Y Z) (φ : AffineMorphism k m n X Y) :
    (ψ.comp k φ).pullback k = (φ.pullback k).comp (ψ.pullback k) := by


  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  ·
    intro c
    show (ψ.comp k φ).pullback k (Ideal.Quotient.mk _ (C c)) =
        ((φ.pullback k).comp (ψ.pullback k)) (Ideal.Quotient.mk _ (C c))
    simp only [pullback_mk, RingHom.comp_apply, AffineMorphism.comp, MvPolynomial.bind₁_C_right]
  ·
    intro j
    show (ψ.comp k φ).pullback k (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
        ((φ.pullback k).comp (ψ.pullback k)) (Ideal.Quotient.mk _ (MvPolynomial.X j))
    simp only [pullback_mk, RingHom.comp_apply, AffineMorphism.comp]
    congr 1
    simp only [MvPolynomial.bind₁_X_right]

end
