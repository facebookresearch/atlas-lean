/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.EisensteinSeries
import Atlas.EllipticCurves.code.Uniformization

open Complex

open scoped UpperHalfPlane

noncomputable section

namespace ModularInvariants

/-- The Eisenstein-type modular invariant $g_2(\tau)$ of weight $4$ associated to the
lattice $\Lambda_\tau = \mathbb{Z} + \mathbb{Z}\tau$, defined as $g_2 = 60 \sum'_{\lambda \in \Lambda_\tau} \lambda^{-4}$
(Definition in Section 15.2). It is one of the two basic generators of the ring of
modular forms for $\mathrm{SL}_2(\mathbb{Z})$. -/
def g₂ (τ : ℍ) : ℂ := g₂Function τ

/-- The modular invariant $g_3(\tau)$ of weight $6$ for the lattice $\Lambda_\tau$,
defined as $g_3 = 140 \sum'_{\lambda \in \Lambda_\tau} \lambda^{-6}$ (Definition in
Section 15.2). Together with $g_2$ it parametrizes the Weierstrass equation of the
elliptic curve $\mathbb{C}/\Lambda_\tau$. -/
def g₃ (τ : ℍ) : ℂ := g₃Function τ

/-- The discriminant modular form $\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2$, a
nonvanishing weight-$12$ cusp form on $\mathrm{SL}_2(\mathbb{Z})$. -/
def Δ (τ : ℍ) : ℂ := discriminantFunction τ

/-- Klein's $j$-invariant $j(\tau) = 1728 \cdot g_2(\tau)^3 / \Delta(\tau)$, the
holomorphic modular function that generates the function field of the modular curve
$\mathrm{SL}_2(\mathbb{Z}) \backslash \mathcal{H}$ and parametrizes isomorphism classes of
complex elliptic curves. -/
def j (τ : ℍ) : ℂ := jFunction τ

/-- The defining formula for $\Delta$: $\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2$. -/
theorem Δ_eq (τ : ℍ) : Δ τ = g₂ τ ^ 3 - 27 * g₃ τ ^ 2 := rfl

/-- The defining formula for $j$ in terms of lattice invariants: $j(\tau) = 1728 \cdot g_2^3 / \Delta$
where $g_2$ and $\Delta$ are taken from the lattice associated with $\tau$. -/
theorem j_eq (τ : ℍ) : j τ = 1728 * (ComplexLattice.ofUpperHalfPlane τ).g₂ ^ 3 /
    (ComplexLattice.ofUpperHalfPlane τ).discriminantLattice := rfl

end ModularInvariants

end
