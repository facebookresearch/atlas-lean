/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Exact

namespace DirectLimitExact

open Module.DirectLimit in
/-- **Proposition 23.12 (module version)**. Exactness of the direct limit functor on
modules: given a directed system of short exact sequences
$$G' \xrightarrow{p} G \xrightarrow{q} G''$$
of $R$-modules whose squares commute with the structure maps, the induced sequence
$$\varinjlim G' \xrightarrow{\varinjlim p} \varinjlim G \xrightarrow{\varinjlim q} \varinjlim G''$$
is exact. -/
theorem directLimit_map_exact
    {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {f : ∀ i j, i ≤ j → G i →ₗ[R] G j} [DirectedSystem G (f · · ·)]
    {G' : ι → Type*} [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
    {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j} [DirectedSystem G' (f' · · ·)]
    {G'' : ι → Type*} [∀ i, AddCommGroup (G'' i)] [∀ i, Module R (G'' i)]
    {f'' : ∀ i j, i ≤ j → G'' i →ₗ[R] G'' j} [DirectedSystem G'' (f'' · · ·)]
    (p : ∀ i, G i →ₗ[R] G' i) (hp : ∀ i j h, p j ∘ₗ f i j h = f' i j h ∘ₗ p i)
    (q : ∀ i, G' i →ₗ[R] G'' i) (hq : ∀ i j h, q j ∘ₗ f' i j h = f'' i j h ∘ₗ q i)
    (exact_at : ∀ i, Function.Exact (p i) (q i)) :
    Function.Exact
      (Module.DirectLimit.map p hp)
      (Module.DirectLimit.map q hq) := by
  intro y
  constructor
  · intro hy
    obtain ⟨i, yi, rfl⟩ := exists_of y
    rw [map_apply_of] at hy
    obtain ⟨j, hij, hfq⟩ := of.zero_exact hy
    have hqf : q j (f' i j hij yi) = 0 := by
      have := LinearMap.congr_fun (hq i j hij) yi
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      rw [this, hfq]
    obtain ⟨xj, hxj⟩ := ((exact_at j) (f' i j hij yi)).mp hqf
    exact ⟨of R ι G f j xj, by rw [map_apply_of, hxj, of_f]⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨i, xi, rfl⟩ := exists_of x
    simp only [map_apply_of]
    have : q i (p i xi) = 0 := ((exact_at i) (p i xi)).mpr ⟨xi, rfl⟩
    rw [this, _root_.map_zero]

end DirectLimitExact
