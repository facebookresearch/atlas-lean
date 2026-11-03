/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace OrthogonalityTubes

open MeasureTheory

/-- The perpendicular vector in $\mathbb{R}^2$: $\mathrm{perp}(d_0, d_1) = (-d_1, d_0)$. -/
def perp (d : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(d 1), d 0]

/-- Underlying point set of a rectangle with centre $c$, axis-direction $d$, width $w$ and
length $l$: the set of $x$ with $|\langle x - c, d\rangle| \le l/2$ and
$|\langle x - c, d^\perp\rangle| \le w/2$. -/
def rectangleCarrier (c d : EuclideanSpace ℝ (Fin 2)) (w l : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |@inner ℝ _ _ (x - c) d| ≤ l / 2 ∧ |@inner ℝ _ _ (x - c) (perp d)| ≤ w / 2}

/-- A *tube* of length $R$ in $\mathbb{R}^2$: an oriented $1 \times R$ rectangle parameterised
by a centre point and a unit direction vector. -/
structure Tube (R : ℝ) where
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

/-- The underlying point set of a tube $T$: the $1 \times R$ rectangle with axis along
`T.direction` centred at `T.center`. -/
def Tube.carrier {R : ℝ} (T : Tube R) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleCarrier T.center T.direction 1 R

/-- The open $r$-thickening of a tube's carrier (the set of points within distance $r$). -/
def Tube.rNeighborhood {R : ℝ} (T : Tube R) (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.thickening r T.carrier

/-- An oriented rectangle in $\mathbb{R}^2$ of given width and length, parameterised by a
centre and a unit direction (the axis of the rectangle). -/
structure Rectangle (width length : ℝ) where
  center : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

/-- The underlying point set of a `Rectangle`: a $w \times l$ rectangle centred at
`rect.center` with axis `rect.direction`. -/
def Rectangle.carrier {w l : ℝ} (rect : Rectangle w l) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleCarrier rect.center rect.direction w l

/-- A tube `T` is *contained in* a rectangle `rect` if its carrier is a subset of the
rectangle's carrier. -/
def Tube.containedIn {R : ℝ} (T : Tube R) {w l : ℝ} (rect : Rectangle w l) : Prop :=
  T.carrier ⊆ rect.carrier

/-- The standard bilinear pairing $(v, w) \mapsto \langle v, w\rangle$ on
$\mathbb{R}^2$, packaged as a continuous bilinear map (used to define the Fourier
transform on $\mathbb{R}^2$). -/
def stdBilinR2 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ where
  toFun v := {
    toFun := fun w => @inner ℝ _ _ v w
    map_add' := fun w₁ w₂ => by simp [inner_add_right]
    map_smul' := fun c w => by simp [inner_smul_right]
  }
  map_add' := fun v₁ v₂ => by ext w; simp [inner_add_left]
  map_smul' := fun c v => by ext w; simp [inner_smul_left]

/-- The Fourier transform on $\mathbb{R}^2$:
$\widehat f(\xi) = \int_{\mathbb{R}^2} f(x)\, e^{-2\pi i \langle x, \xi\rangle}\, dx$. -/
def fourierTransformR2 (f : EuclideanSpace ℝ (Fin 2) → ℂ) :
    EuclideanSpace ℝ (Fin 2) → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume stdBilinR2 f

/-- The frequency annulus at scale $r$: $\{\xi : r^{-1}/2 \le \|\xi\| \le 2 r^{-1}\}$. -/
def freqAnnulus (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {ξ | r⁻¹ / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * r⁻¹}


/-- The frequency angular cap supporting $\widehat{\phi_{T, r}}$: frequencies in the annulus
of scale $r$ that lie within angular distance $\lesssim r / R$ of the line $\mathbb{R} \cdot
T.\mathrm{direction}$. -/
def freqAngularCap (R r : ℝ) (T : Tube R) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {ξ | ξ ∈ freqAnnulus r ∧ ‖ξ - (‖ξ‖ • T.direction)‖ ≤ (r / (3 * R)) * ‖ξ‖}


/-- The $L^2$ inner product $\langle f, g\rangle = \int f(x) \overline{g(x)}\, dx$ on
$\mathbb{R}^2$. -/
def l2Inner (f g : EuclideanSpace ℝ (Fin 2) → ℂ) : ℂ :=
  ∫ x, f x * starRingEnd ℂ (g x) ∂volume

/-- A surrogate for the angle between two tubes: $\|T_1.\text{direction} -
T_2.\text{direction}\|$ (which is comparable to $|\sin \theta|$ for the actual angle
$\theta$ between the directions when both are unit vectors). -/
def Tube.angle {R : ℝ} (T₁ T₂ : Tube R) : ℝ :=
  ‖T₁.direction - T₂.direction‖



/-- If at every point $\xi$ either $f(\xi) = 0$ or $g(\xi) = 0$, then $\langle f, g\rangle =
0$ — the integrand vanishes identically. -/
lemma l2Inner_eq_zero_of_pointwise_disjoint
    (f g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (h : ∀ ξ, f ξ = 0 ∨ g ξ = 0) :
    l2Inner f g = 0 := by
  unfold l2Inner
  have heq : (fun x => f x * starRingEnd ℂ (g x)) = 0 := by
    ext x
    cases h x with
    | inl hf => simp [hf]
    | inr hg => simp [hg]
  rw [heq]
  simp


/-- For $R \ge 1$, the carrier of every tube is nonempty (the centre belongs to it). -/
lemma Tube.carrier_nonempty {R : ℝ} (hR : 1 ≤ R) (T : Tube R) :
    (T.carrier : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
  refine ⟨T.center, ?_⟩
  simp only [Tube.carrier, rectangleCarrier, Set.mem_setOf_eq, sub_self, inner_zero_left,
    abs_zero]
  exact ⟨by linarith, by linarith⟩

/-- If the $r$-thickenings of two tubes are disjoint, then for every point $x$ at least one of
the two tubes lies at distance $\ge r$ from $x$. -/
lemma disjoint_thickening_infDist {R : ℝ} (hR : 1 ≤ R)
    {r : ℝ} (T₁ T₂ : Tube R)
    (hdisjoint : Disjoint (T₁.rNeighborhood r) (T₂.rNeighborhood r))
    (x : EuclideanSpace ℝ (Fin 2)) :
    r ≤ Metric.infDist x T₁.carrier ∨ r ≤ Metric.infDist x T₂.carrier := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hx1 : x ∈ T₁.rNeighborhood r := by
    simp only [Tube.rNeighborhood]
    rwa [Metric.mem_thickening_iff_infDist_lt (Tube.carrier_nonempty hR T₁)]
  have hx2 : x ∈ T₂.rNeighborhood r := by
    simp only [Tube.rNeighborhood]
    rwa [Metric.mem_thickening_iff_infDist_lt (Tube.carrier_nonempty hR T₂)]
  exact hdisjoint.ne_of_mem hx1 hx2 rfl









end OrthogonalityTubes
