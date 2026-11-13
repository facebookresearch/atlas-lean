/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.IsogenyVolcano

noncomputable section

open VolcanoStructure

namespace OrdinaryVolcanoStructure

/-- Combinatorial input for the $\ell$-isogeny volcano of an ordinary elliptic curve
$E/\mathbb{F}_q$ (Kohel's Theorem 22.11). It records the prime $\ell \nmid q$, the trace
of Frobenius $t$ (satisfying the strict Hasse bound), the fundamental discriminant
$D_0 < 0$ of the CM order, the prime-to-$\ell$ conductor $f_0$, the global conductor
$f = f_0 \cdot \ell^h$, and the order of the class group acting on the surface. -/
structure OrdinaryCurveData where
  q : ℕ
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  t : ℤ
  hHasse : t ^ 2 < 4 * (q : ℤ)
  D₀ : ℤ
  hD₀_neg : D₀ < 0
  f₀ : ℕ
  hf₀_pos : 0 < f₀
  f : ℕ
  hf_pos : 0 < f
  h : ℕ
  conductor_factorization : f = f₀ * ℓ ^ h
  hℓ_ndvd_f₀ : ¬(ℓ ∣ f₀)
  classOrder : ℕ
  hClassOrder_pos : 0 < classOrder

/-- Forget the volcano depth $h$ and conductor factorization in `OrdinaryCurveData` to
recover the underlying `OrdinaryIsogenyComponent` data used by the abstract volcano
formalism. -/
def OrdinaryCurveData.toComponent (C : OrdinaryCurveData) :
    OrdinaryIsogenyComponent where
  q := C.q
  ℓ := C.ℓ
  hℓ_prime := C.hℓ_prime
  hℓ_ndvd_q := C.hℓ_ndvd_q
  t := C.t
  hHasse := C.hHasse
  D₀ := C.D₀
  hD₀_neg := C.hD₀_neg
  f₀ := C.f₀
  hf₀_pos := C.hf₀_pos
  classOrder := C.classOrder
  hClassOrder_pos := C.hClassOrder_pos

/-- Existence statement for the $\ell$-isogeny volcano of an ordinary elliptic curve:
a `KohelVolcano` over the underlying isogeny component whose depth coincides with the
exponent $h$ in the conductor factorization $f = f_0 \cdot \ell^h$. -/
structure OrdinaryVolcano (C : OrdinaryCurveData) where
  kohelVolcano : KohelVolcano C.toComponent
  depth_eq_h : kohelVolcano.volcano.depth = C.h


variable {C : OrdinaryCurveData} (V : OrdinaryVolcano C)

/-- The conductor of any vertex $v$ in the $\ell$-volcano equals $f_0 \cdot \ell^{\mathrm{lvl}(v)}$
where $\mathrm{lvl}(v)$ is its level. This is the level-conductor correspondence at
the heart of Kohel's volcano structure. -/
theorem conductor_at_level (v : V.kohelVolcano.volcano.V) :
    V.kohelVolcano.conductor v =
      C.f₀ * C.ℓ ^ (V.kohelVolcano.volcano.level v : ℕ) :=
  V.kohelVolcano.conductor_eq_level v

/-- Vertices on the surface (level $0$) of the volcano have conductor exactly $f_0$,
the prime-to-$\ell$ part of the global conductor. -/
theorem surface_conductor (v : V.kohelVolcano.volcano.V)
    (hv : (V.kohelVolcano.volcano.level v : ℕ) = 0) :
    V.kohelVolcano.conductor v = C.f₀ :=
  VolcanoStructure.surface_conductor_eq V.kohelVolcano v hv

/-- Vertices at the floor of the volcano (maximum level $h$) have the maximum
conductor $f_0 \cdot \ell^h = f$. -/
theorem floor_conductor (v : V.kohelVolcano.volcano.V)
    (hv : (V.kohelVolcano.volcano.level v : ℕ) = V.kohelVolcano.volcano.depth) :
    V.kohelVolcano.conductor v = C.f₀ * C.ℓ ^ C.h := by
  rw [conductor_at_level V v, hv, V.depth_eq_h]

/-- The degree of the surface graph equals $1 + \left(\tfrac{D_0}{\ell}\right)$ where the
right-hand factor is the Jacobi/Kronecker symbol. This dichotomy distinguishes split
($+2$), inert ($0$), and ramified ($1$) primes in the CM field. -/
theorem surface_degree_eq :
    (V.kohelVolcano.volcano.surfaceDegree : ℤ) =
      1 + jacobiSym C.D₀ C.ℓ :=
  V.kohelVolcano.surface_degree_eq

end OrdinaryVolcanoStructure

end
