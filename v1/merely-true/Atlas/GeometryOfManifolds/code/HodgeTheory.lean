/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.KahlerManifolds

set_option autoImplicit false

open DifferentialFormSpace


/-- A complex-linear structure on the spaces of differential forms.

Equips each $\Omega^p$ with a scalar multiplication by $\mathbb{C}$ compatible with
the existing $\mathbb{R}$-module structure. -/
structure HasComplexStructure
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  complexSmul : ∀ {p : ℕ}, ℂ → Ω p → Ω p
  complexSmul_add : ∀ {p : ℕ} (z : ℂ) (ω₁ ω₂ : Ω p),
    complexSmul z (ω₁ + ω₂) = complexSmul z ω₁ + complexSmul z ω₂
  complexSmul_zero : ∀ {p : ℕ} (ω : Ω p), complexSmul 0 ω = 0
  complexSmul_mul : ∀ {p : ℕ} (z w : ℂ) (ω : Ω p),
    complexSmul z (complexSmul w ω) = complexSmul (z * w) ω
  complexSmul_one : ∀ {p : ℕ} (ω : Ω p), complexSmul 1 ω = ω
  complexSmul_real : ∀ {p : ℕ} (r : ℝ) (ω : Ω p),
    complexSmul (r : ℂ) ω = r • ω


/-- The Hodge star operator $*: \Omega^p \to \Omega^p$ (a simplified involution version);
on an oriented Riemannian $n$-manifold it normally maps $\Omega^k \to \Omega^{n-k}$. -/
structure HodgeStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  star : ∀ {p : ℕ}, Ω p → Ω p
  star_star : ∀ {p : ℕ} (α : Ω p), star (star α) = α


/-- The codifferential $d^*: \Omega^k \to \Omega^{k-1}$, the formal $L^2$-adjoint of $d$.

On an oriented Riemannian $n$-manifold, $d^* = (-1)^{n(k-1)+1} * d *$ where $*$ is the
Hodge star and the sign factor satisfies $(\text{sign})^2 = 1$. -/
structure Codifferential
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  dstar : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  dstar_add : ∀ {p : ℕ} (α β : Ω (p + 1)), dstar (α + β) = dstar α + dstar β
  dstar_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), dstar (r • α) = r • dstar α
  hodge : HodgeStar (inst := inst)
  sign_factor : ℕ → ℝ
  sign_factor_sq : ∀ k, sign_factor k ^ 2 = 1
  manifold_dim : ℕ
  sign_factor_formula : ∀ k, sign_factor k = (-1 : ℝ) ^ (manifold_dim * (k - 1) + 1)
  star_deg : ∀ {k : ℕ}, k ≤ manifold_dim → Ω k → Ω (manifold_dim - k)
  star_deg_star_deg : ∀ {k : ℕ} (hk : k ≤ manifold_dim)
    (hk' : manifold_dim - k ≤ manifold_dim := by omega) (α : Ω k),
    cast (by congr 1; omega) (star_deg hk' (star_deg hk α)) = α
  dstar_formula : ∀ {p : ℕ} (h : p + 1 ≤ manifold_dim) (ω : Ω (p + 1)),
    dstar ω = sign_factor (p + 1) •
      cast (by congr 1; omega)
        (star_deg (by omega : manifold_dim - (p + 1) + 1 ≤ manifold_dim)
          (inst.d (star_deg h ω)))
  dstar_squared : ∀ {p : ℕ} (ω : Ω (p + 2)), dstar (dstar ω) = 0

/-- Restates the explicit formula $d^*\omega = (-1)^{n(k-1)+1} * d * \omega$ for the
codifferential in terms of the Hodge star, packaged from the structure data. -/
theorem Codifferential.formula
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    {p : ℕ} (h : p + 1 ≤ cod.manifold_dim) (ω : Ω (p + 1)) :
    cod.dstar ω = cod.sign_factor (p + 1) •
      cast (by congr 1; omega)
        (cod.star_deg (by omega : cod.manifold_dim - (p + 1) + 1 ≤ cod.manifold_dim)
          (inst.d (cod.star_deg h ω))) :=
  cod.dstar_formula h ω

/-- The composite $* \circ d \circ *: \Omega^{p+1} \to \Omega^p$ (without the sign factor),
the geometric content of the codifferential. -/
def star_d_star
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    {p : ℕ} (h : p + 1 ≤ cod.manifold_dim) (ω : Ω (p + 1)) : Ω p :=

  let star_omega : Ω (cod.manifold_dim - (p + 1)) := cod.star_deg h ω

  let d_star_omega : Ω (cod.manifold_dim - (p + 1) + 1) := inst.d star_omega

  let star_d_star_omega : Ω (cod.manifold_dim - (cod.manifold_dim - (p + 1) + 1)) :=
    cod.star_deg (by omega : cod.manifold_dim - (p + 1) + 1 ≤ cod.manifold_dim) d_star_omega

  cast (by congr 1; omega) star_d_star_omega


/-- The Hodge–de Rham Laplacian $\Delta = dd^* + d^*d: \Omega^k \to \Omega^k$. -/
def laplacian {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  inst.d (cod.dstar α) + cod.dstar (inst.d α)


/-- A form $\alpha$ is *harmonic* if $\Delta \alpha = 0$. -/
def IsHarmonic {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Prop :=
  laplacian cod α = 0

/-- Synonym for `IsHarmonic`: the form $\alpha$ is harmonic. -/
abbrev IsHarmonicForm {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Prop :=
  IsHarmonic cod α

/-- The space $\mathcal{H}^{p+1} = \{\alpha \in \Omega^{p+1} : \Delta \alpha = 0\}$
of harmonic forms of degree $p+1$. -/
def HarmonicForms {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) (p : ℕ) : Set (Ω (p + 1)) :=
  {α | IsHarmonic cod α}


/-- The $L^2$ inner product on differential forms: a symmetric, positive-definite,
$\mathbb{R}$-bilinear form $\langle \cdot, \cdot \rangle$ on each $\Omega^p$ for which
$d$ and $d^*$ are mutually adjoint, i.e. $\langle d\alpha, \beta\rangle = \langle \alpha, d^*\beta\rangle$. -/
structure L2InnerProduct
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) where
  inner : ∀ {p : ℕ}, Ω p → Ω p → ℝ
  inner_self_eq_zero : ∀ {p : ℕ} (α : Ω p), inner α α = 0 → α = 0
  inner_self_nonneg : ∀ {p : ℕ} (α : Ω p), 0 ≤ inner α α
  inner_symm : ∀ {p : ℕ} (α β : Ω p), inner α β = inner β α
  adjoint_d : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (inst.d α) β = inner α (cod.dstar β)
  inner_add_left : ∀ {p : ℕ} (α β γ : Ω p),
    inner (α + β) γ = inner α γ + inner β γ
  inner_smul_left : ∀ {p : ℕ} (r : ℝ) (α β : Ω p),
    inner (r • α) β = r * inner α β


/-- Packages the $L^2$ inner product as a Mathlib `Inner ℝ` instance on $\Omega^p$. -/
noncomputable def L2InnerProduct.toInner
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    (ip : L2InnerProduct cod) (p : ℕ) : Inner ℝ (Ω p) where
  inner := ip.inner

/-- The $L^2$ inner product satisfies the standard inner-product axioms: symmetry,
additivity in the first slot, scalar homogeneity, non-negativity and positive-definiteness. -/
theorem L2InnerProduct.inner_product_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    (ip : L2InnerProduct cod) {p : ℕ} :

    (∀ (α β : Ω p), ip.inner α β = ip.inner β α) ∧

    (∀ (α β γ : Ω p), ip.inner (α + β) γ = ip.inner α γ + ip.inner β γ) ∧

    (∀ (r : ℝ) (α β : Ω p), ip.inner (r • α) β = r * ip.inner α β) ∧

    (∀ (α : Ω p), (0 : ℝ) ≤ ip.inner α α) ∧

    (∀ (α : Ω p), ip.inner α α = 0 → α = 0) :=
  ⟨ip.inner_symm, ip.inner_add_left, ip.inner_smul_left,
   ip.inner_self_nonneg, ip.inner_self_eq_zero⟩


/-- The codifferential vanishes on zero: $d^*(0) = 0$. -/
lemma Codifferential.dstar_zero
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} :
    cod.dstar (0 : Ω (p + 1)) = (0 : Ω p) := by
  have h := cod.dstar_smul (0 : ℝ) (0 : Ω (p + 1))
  simp [zero_smul] at h; exact h

/-- The $L^2$ inner product vanishes when its first argument is zero: $\langle 0, \alpha\rangle = 0$. -/
lemma L2InnerProduct.inner_zero_left
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    (ip : L2InnerProduct cod) {p : ℕ} (α : Ω p) :
    ip.inner 0 α = 0 := by
  have h := ip.inner_smul_left (0 : ℝ) (0 : Ω p) α
  simp [zero_mul] at h; exact h

/-- On a compact oriented Riemannian manifold, a form $\alpha$ is harmonic iff it is both
closed and coclosed: $\Delta\alpha = 0 \iff d\alpha = 0 \text{ and } d^*\alpha = 0$. -/
theorem harmonic_iff_closed_coclosed
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    (ip : L2InnerProduct cod)
    {p : ℕ} (α : Ω (p + 1)) :
    IsHarmonic cod α ↔ (inst.d α = 0 ∧ cod.dstar α = 0) := by
  constructor
  ·
    intro h
    unfold IsHarmonic laplacian at h


    have eq1 : ip.inner (inst.d (cod.dstar α)) α =
        ip.inner (cod.dstar α) (cod.dstar α) :=
      ip.adjoint_d (cod.dstar α) α

    have eq2 : ip.inner (cod.dstar (inst.d α)) α =
        ip.inner (inst.d α) (inst.d α) := by
      rw [ip.inner_symm (cod.dstar (inst.d α)) α,
          ip.adjoint_d α (inst.d α), ip.inner_symm]

    have sum_eq : ip.inner (cod.dstar α) (cod.dstar α) +
        ip.inner (inst.d α) (inst.d α) = 0 := by
      have step : ip.inner (inst.d (cod.dstar α) + cod.dstar (inst.d α)) α =
          ip.inner (cod.dstar α) (cod.dstar α) +
          ip.inner (inst.d α) (inst.d α) := by
        rw [ip.inner_add_left, eq1, eq2]
      rw [h, ip.inner_zero_left] at step
      linarith

    have h_dstar : ip.inner (cod.dstar α) (cod.dstar α) = 0 := by
      linarith [ip.inner_self_nonneg (cod.dstar α),
                ip.inner_self_nonneg (inst.d α)]
    have h_d : ip.inner (inst.d α) (inst.d α) = 0 := by linarith

    exact ⟨ip.inner_self_eq_zero _ h_d, ip.inner_self_eq_zero _ h_dstar⟩
  ·
    intro ⟨hclosed, hcoclosed⟩
    unfold IsHarmonic laplacian
    rw [hclosed, hcoclosed, d_zero_val, Codifferential.dstar_zero]
    simp


/-- Auxiliary data packaging the formal adjoints $\partial^*$ and $\bar\partial^*$ together
with the decomposition $d^* = \partial^* + \bar\partial^*$. -/
structure DolbeaultLaplacian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    (cod : Codifferential (inst := inst)) where
  del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  dstar_decomp : ∀ {p : ℕ} (ω : Ω (p + 1)),
    cod.dstar ω = del_star ω + delbar_star ω
  delbar_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The $\bar\partial$-Laplacian $\bar\square = \bar\partial\bar\partial^* + \bar\partial^*\bar\partial$
on $(p,q)$-forms. -/
def DolbeaultLaplacian.box_bar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)

/-- The $\partial$-Laplacian $\square = \partial\partial^* + \partial^*\partial$. -/
def DolbeaultLaplacian.box
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)


/-- Wells' anticommutation identities for the Dolbeault adjoint operators on a Kähler
manifold: $\partial\bar\partial^* + \bar\partial^*\partial = 0$ and
$\bar\partial\partial^* + \partial^*\bar\partial = 0$, plus an expansion identity. -/
structure KahlerWellsIdentities
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod) where
  del_delbar_star_anticommute : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0
  delbar_del_star_anticommute : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0
  wells_expansion : ∀ {p : ℕ} (α : Ω (p + 1)),
    (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
    (dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α)) -
    (dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α)) -
    (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)) = 0

/-- On a Kähler manifold, the two Dolbeault Laplacians agree: $\square = \bar\square$.

Auxiliary version using abstract `box`, `box_bar`, `del_star`, `delbar_star` parameters
together with Wells' identities. -/
theorem kahler_box_eq_box_bar_blocker
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p)
    (delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p)

    (box : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
    (box_bar : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
    (hbox_def : ∀ {p : ℕ} (α : Ω (p + 1)),
      box α = dol.del (del_star α) + del_star (dol.del α))
    (hbox_bar_def : ∀ {p : ℕ} (α : Ω (p + 1)),
      box_bar α = dol.delbar (delbar_star α) + delbar_star (dol.delbar α))

    (wells : KahlerWellsIdentities S J _hK dol_lap)

    (h_del_star : ∀ {p : ℕ} (α : Ω (p + 1)), del_star α = dol_lap.del_star α)
    (h_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)), delbar_star α = dol_lap.delbar_star α)
    {p : ℕ} (α : Ω (p + 1)) :
    box α = box_bar α := by

  rw [hbox_def α, hbox_bar_def α]

  simp only [h_del_star, h_delbar_star]


  have h_anti1 := wells.del_delbar_star_anticommute α
  have h_anti2 := wells.delbar_del_star_anticommute α
  have h_wells := wells.wells_expansion α

  have hef : (dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α)) = 0 := h_anti1
  have hgh : (dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α)) = 0 := h_anti2
  have key : (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) -
    (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)) = 0 := by
    have := h_wells
    rw [hef, hgh] at this
    simp only [add_zero, sub_zero] at this
    exact this
  exact sub_eq_zero.mp key

/-- Extracts the Wells anticommutation $\partial \bar\partial^* + \bar\partial^* \partial = 0$
from the structure of Kähler identities. -/
theorem kahler_del_delbar_star_anticommute_blocker
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (wells : KahlerWellsIdentities S J _hK dol_lap)
    {p : ℕ} (α : Ω (p + 1)) :
    dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0 :=
  wells.del_delbar_star_anticommute α

/-- Extracts the Wells anticommutation $\bar\partial \partial^* + \partial^* \bar\partial = 0$
from the structure of Kähler identities. -/
theorem kahler_delbar_del_star_anticommute_blocker
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (wells : KahlerWellsIdentities S J _hK dol_lap)
    {p : ℕ} (α : Ω (p + 1)) :
    dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0 :=
  wells.delbar_del_star_anticommute α

/-- On a Kähler manifold, $\Delta = 2\bar\square$ acting on $(p,q)$-forms; concretely
$\bar\square \alpha + \bar\square \alpha = \Delta \alpha$. -/
theorem kahler_two_box_bar_blocker
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)
    (wells : KahlerWellsIdentities S J _hK dol_lap)
    {p : ℕ} (α : Ω (p + 1)) :
    dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α := by

  have h_box_eq : dol_lap.box α = dol_lap.box_bar α :=
    kahler_box_eq_box_bar_blocker S J _hK dol_lap
      dol_lap.del_star dol_lap.delbar_star
      dol_lap.box dol_lap.box_bar
      (fun α => rfl) (fun α => rfl) wells
      (fun α => rfl) (fun α => rfl) α

  have h_anti1 : dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0 :=
    kahler_del_delbar_star_anticommute_blocker S J _hK dol_lap wells α
  have h_anti2 : dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0 :=
    kahler_delbar_del_star_anticommute_blocker S J _hK dol_lap wells α

  show dol_lap.box_bar α + dol_lap.box_bar α =
    inst.d (cod.dstar α) + cod.dstar (inst.d α)

  have h_expand : inst.d (cod.dstar α) + cod.dstar (inst.d α) =
      dol_lap.box α + dol_lap.box_bar α := by
    show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
      (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
      (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α))
    rw [dol_lap.dstar_decomp α]
    rw [inst.d_add]
    rw [dol.decomp (dol_lap.del_star α)]
    rw [dol.decomp (dol_lap.delbar_star α)]
    rw [dol.decomp α]
    rw [cod.dstar_add]
    rw [dol_lap.dstar_decomp (dol.del α)]
    rw [dol_lap.dstar_decomp (dol.delbar α)]
    have hc1' : dol.del (dol_lap.delbar_star α) = -(dol_lap.delbar_star (dol.del α)) :=
      eq_neg_of_add_eq_zero_left h_anti1
    have hc2' : dol.delbar (dol_lap.del_star α) = -(dol_lap.del_star (dol.delbar α)) :=
      eq_neg_of_add_eq_zero_left h_anti2
    rw [hc1', hc2']
    abel

  rw [h_expand, h_box_eq]


/-- Restatement of $2\bar\square = \Delta$ on Kähler manifolds (given as a hypothesis here)
in the form $\bar\square \alpha + \bar\square \alpha = \Delta \alpha$. -/
theorem box_bar_eq_half_laplacian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (_S : SymplecticManifold Ω VF)
    (_J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler _S _J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α
)
    {p : ℕ} (α : Ω (p + 1)) :
    dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
  h_two_box_bar α

/-- On a Kähler manifold, $\Delta = \square + \bar\square$ as a consequence of the
anticommutation identities for the Dolbeault adjoints. -/
theorem kahler_laplacian_eq_box_plus_box_bar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (_S : SymplecticManifold Ω VF)
    (_J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler _S _J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (h_del_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0)
    (h_delbar_del_star : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0)
    {p : ℕ} (α : Ω (p + 1)) :
    laplacian cod α = dol_lap.box α + dol_lap.box_bar α := by

  have h_anti1 := h_del_delbar_star α
  have h_anti2 := h_delbar_del_star α

  show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
    (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
    (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α))

  rw [dol_lap.dstar_decomp α]

  rw [inst.d_add]

  rw [dol.decomp (dol_lap.del_star α)]

  rw [dol.decomp (dol_lap.delbar_star α)]

  rw [dol.decomp α]

  rw [cod.dstar_add]

  rw [dol_lap.dstar_decomp (dol.del α)]
  rw [dol_lap.dstar_decomp (dol.delbar α)]


  have hc1' : dol.del (dol_lap.delbar_star α) = -(dol_lap.delbar_star (dol.del α)) :=
    eq_neg_of_add_eq_zero_left h_anti1

  have hc2' : dol.delbar (dol_lap.del_star α) = -(dol_lap.del_star (dol.delbar α)) :=
    eq_neg_of_add_eq_zero_left h_anti2
  rw [hc1', hc2']
  abel

/-- On a Kähler manifold the two Dolbeault Laplacians are equal: $\square = \bar\square$,
deduced from $\Delta = \square + \bar\square$ and $\Delta = 2\bar\square$. -/
theorem box_eq_box_bar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (h_del_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0)
    (h_delbar_del_star : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0)

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α
)
    {p : ℕ} (α : Ω (p + 1)) :
    dol_lap.box α = dol_lap.box_bar α := by

  have h1 : dol_lap.box α + dol_lap.box_bar α = laplacian cod α :=
    (kahler_laplacian_eq_box_plus_box_bar S J hK dol_lap h_del_delbar_star h_delbar_del_star α).symm

  have h2 : dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
    h_two_box_bar α


  exact add_right_cancel (h1.trans h2.symm)


/-- The Kähler Laplacian identity: $\Delta = 2\square = 2\bar\square$ and $\square = \bar\square$
on a Kähler manifold, packaged together. -/
theorem kahler_laplacian_identity
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    (wells : KahlerWellsIdentities S J _hK dol_lap)
    {p : ℕ} (α : Ω (p + 1)) :
    laplacian cod α = dol_lap.box α + dol_lap.box α
    ∧ laplacian cod α = dol_lap.box_bar α + dol_lap.box_bar α
    ∧ dol_lap.box α = dol_lap.box_bar α := by

  have h_anticomm1 : dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0 :=
    kahler_del_delbar_star_anticommute_blocker S J _hK dol_lap wells α
  have h_anticomm2 : dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0 :=
    kahler_delbar_del_star_anticommute_blocker S J _hK dol_lap wells α

  have h_two_box_bar : dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
    kahler_two_box_bar_blocker S J _hK dol_lap wells α


  have part1 : laplacian cod α = dol_lap.box α + dol_lap.box_bar α := by
    show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
      dol_lap.box α + dol_lap.box_bar α
    show inst.d (cod.dstar α) + cod.dstar (inst.d α) =
      (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
      (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α))
    rw [dol_lap.dstar_decomp α]
    rw [inst.d_add]
    rw [dol.decomp (dol_lap.del_star α)]
    rw [dol.decomp (dol_lap.delbar_star α)]
    rw [dol.decomp α]
    rw [cod.dstar_add]
    rw [dol_lap.dstar_decomp (dol.del α)]
    rw [dol_lap.dstar_decomp (dol.delbar α)]
    have hc1' : dol.del (dol_lap.delbar_star α) = -(dol_lap.delbar_star (dol.del α)) :=
      eq_neg_of_add_eq_zero_left h_anticomm1
    have hc2' : dol.delbar (dol_lap.del_star α) = -(dol_lap.del_star (dol.delbar α)) :=
      eq_neg_of_add_eq_zero_left h_anticomm2
    rw [hc1', hc2']
    abel

  have part3 : dol_lap.box α = dol_lap.box_bar α :=
    add_right_cancel (part1.symm.trans h_two_box_bar.symm)

  have part2 : laplacian cod α = dol_lap.box_bar α + dol_lap.box_bar α :=
    h_two_box_bar.symm

  have part4 : laplacian cod α = dol_lap.box α + dol_lap.box α := by
    rw [part1, ← part3]
  exact ⟨part4, part2, part3⟩


/-- The Hodge bigrading on an almost-complex manifold of complex dimension $n$:
a decomposition $\Omega^k = \bigoplus_{p+q=k} \Omega^{p,q}$ with the Hodge star
acting as $* : \Omega^{p,q} \to \Omega^{n-q, n-p}$. -/
structure HasBigrading
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (n : ℕ) where
  Ω_pq : ℕ → ℕ → Type*
  incl : ∀ (p q : ℕ), Ω_pq p q → Ω (p + q)
  incl_injective : ∀ (p q : ℕ), Function.Injective (incl p q)
  pq_add : ∀ (p q : ℕ), Ω_pq p q → Ω_pq p q → Ω_pq p q
  incl_add : ∀ (p q : ℕ) (α β : Ω_pq p q),
    incl p q (pq_add p q α β) = incl p q α + incl p q β
  pq_zero : ∀ (p q : ℕ), Ω_pq p q
  incl_zero : ∀ (p q : ℕ), incl p q (pq_zero p q) = 0
  incl_cast : ∀ {p₁ q₁ p₂ q₂ : ℕ} (hp : p₁ = p₂) (hq : q₁ = q₂)
      (α : Ω_pq p₁ q₁),
      incl p₂ q₂ (cast (by rw [hp, hq]) α) =
        cast (congrArg Ω (by omega)) (incl p₁ q₁ α)
  star_total : ∀ {k : ℕ}, k ≤ 2 * n → Ω k → Ω (2 * n - k)
  star_abc_decomp : ∀ {p' q' : ℕ} (hp' : p' ≤ n) (hq' : q' ≤ n) (β : Ω_pq p' q'),
    ∃ (a b c : ℕ) (ha : a + c = p') (hb : b + c = q') (habc : a + b + c ≤ n),
      ∃ γ : Ω_pq (a + (n - a - b - c)) (b + (n - a - b - c)),
        incl (a + (n - a - b - c)) (b + (n - a - b - c)) γ =
          cast (congrArg Ω (by omega))
            (star_total (by omega : p' + q' ≤ 2 * n) (incl p' q' β))


/-- Data witnessing that on a Kähler manifold, $\bar\square$ and $\Delta$ preserve the
$(p,q)$ bigrading, and that every harmonic form decomposes into harmonic $(p,q)$-components. -/
structure KahlerBigradedData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    {J : AlmostComplexStr (inst := inst)}
    {n : ℕ}
    (bg : HasBigrading J n) where
  box_bar_preserves_bidegree :
    ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω))


  laplacian_preserves_bidegree :
    ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω))

  harmonic_bigrading_decomposition :
    ∀ {k : ℕ} (h_form : Ω (k + 1)) (_h_harmonic : laplacian cod h_form = 0),
      ∃ (component : Fin (k + 2) → Ω (k + 1)),
        (∀ (j : Fin (k + 2)),
          ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)),
            cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt)))
              (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧
        (∀ j, dol.del (component j) = 0) ∧
        (∀ j, dol.delbar (component j) = 0) ∧
        (∀ j, laplacian cod (component j) = 0) ∧
        h_form = Finset.univ.sum component


/-- On a Kähler manifold, the Laplacian $\Delta$ preserves the Hodge $(p,q)$ bigrading,
deduced from the fact that $\bar\square$ preserves it and $\Delta = 2\bar\square$. -/
theorem laplacian_preserves_bidegree
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J' : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J')
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    {J : AlmostComplexStr (inst := inst)}
    {n : ℕ}
    (bg : HasBigrading J n)

    (h_box_bar_pres : ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)))

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α)
    (k : ℕ) (p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q') :
    ∃ ω' : bg.Ω_pq p' q',
      cast (congrArg Ω h) (bg.incl p' q' ω') =
        laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω)) := by

  obtain ⟨ω₁, hω₁⟩ := h_box_bar_pres k p' q' h ω


  have hΔ : laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω)) =
    dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)) +
    dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)) :=
    (box_bar_eq_half_laplacian S J' hK dol_lap (h_two_box_bar := h_two_box_bar) _).symm

  rw [← hω₁] at hΔ

  refine ⟨bg.pq_add p' q' ω₁ ω₁, ?_⟩

  rw [hΔ]

  have h_add : bg.incl p' q' (bg.pq_add p' q' ω₁ ω₁) =
    bg.incl p' q' ω₁ + bg.incl p' q' ω₁ := bg.incl_add p' q' ω₁ ω₁

  have h_cast_add : ∀ {m n : ℕ} (heq : m = n) (a b : Ω m),
    cast (congrArg Ω heq) (a + b) = cast (congrArg Ω heq) a + cast (congrArg Ω heq) b := by
    intro m n heq; subst heq; intros; rfl
  rw [h_add, h_cast_add h]


/-- On a Kähler manifold a form is $\Delta$-harmonic iff it is $\bar\square$-harmonic:
$\Delta \alpha = 0 \iff \bar\square \alpha = 0$. This gives the identification
$\mathcal{H}^k = \bigoplus_{p+q=k} \mathcal{H}^{p,q}_{\bar\square}$. -/
theorem dolbeault_identification
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α)
    {k : ℕ} (α : Ω (k + 1)) :
    laplacian cod α = 0 ↔ dol_lap.box_bar α = 0 := by
  constructor
  ·
    intro hΔ

    have h := box_bar_eq_half_laplacian S J hK dol_lap (h_two_box_bar := h_two_box_bar) α

    rw [hΔ] at h

    have h2 : (2 : ℝ) • dol_lap.box_bar α = (0 : Ω (k + 1)) := by
      rw [two_smul]; exact h
    rw [smul_eq_zero] at h2
    exact h2.resolve_left (by norm_num)
  ·
    intro hbox

    have h := box_bar_eq_half_laplacian S J hK dol_lap (h_two_box_bar := h_two_box_bar) α
    rw [hbox, add_zero] at h
    exact h.symm


/-- The Lefschetz operator $L: \Omega^p \to \Omega^{p+2}$, $\alpha \mapsto \omega \wedge \alpha$
on a symplectic manifold; it commutes with $d$. -/
structure LefschetzOp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  L_op : ∀ {p : ℕ}, Ω p → Ω (p + 2)
  d_commutes : ∀ {p : ℕ} (α : Ω p), L_op (inst.d α) = inst.d (L_op α)

/-- The dual Lefschetz operator $\Lambda = L^*: \Omega^{p+2} \to \Omega^p$, the formal
$L^2$-adjoint of $L$. -/
structure DualLefschetz
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  Λ_op : ∀ {p : ℕ}, Ω (p + 2) → Ω p


/-- An action of the almost-complex structure $J$ on differential forms:
an $\mathbb{R}$-linear involution-up-to-sign $J: \Omega^p \to \Omega^p$ with $J^2 = -\mathrm{id}$. -/
structure JActsOnForms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  J_form : ∀ {p : ℕ}, Ω p → Ω p
  J_form_sq : ∀ {p : ℕ} (α : Ω p), J_form (J_form α) = -(α)
  J_form_add : ∀ {p : ℕ} (α β : Ω p), J_form (α + β) = J_form α + J_form β
  J_form_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), J_form (r • α) = r • J_form α

/-- The action of $J$ on forms commutes with negation: $J(-\alpha) = -J(\alpha)$. -/
lemma JActsOnForms.J_form_neg
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) : Jf.J_form (-α) = -(Jf.J_form α) := by
  have h := Jf.J_form_smul (-1 : ℝ) α
  simp at h
  exact h

/-- The action of $J$ on forms preserves zero: $J(0) = 0$. -/
lemma JActsOnForms.J_form_zero
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} : Jf.J_form (0 : Ω p) = 0 := by
  have h := Jf.J_form_smul (0 : ℝ) (0 : Ω p)
  simp [zero_smul] at h
  exact h


/-- The twisted differential $d_C = -J d J: \Omega^p \to \Omega^{p+1}$ associated to
an action of $J$ on forms. -/
noncomputable def d_C_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) : Ω (p + 1) :=
  -(Jf.J_form (inst.d (Jf.J_form α)))

/-- The codifferential twisted by $J$: $d_C^* = -J d^* J: \Omega^{p+1} \to \Omega^p$. -/
noncomputable def d_C_star_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : Codifferential (inst := inst))
    {p : ℕ} (α : Ω (p + 1)) : Ω p :=
  -(Jf.J_form (cod.dstar (Jf.J_form α)))

/-- If $d$ and $d^*$ both commute with $J$ on forms, then so does the Laplacian:
$\Delta(J\alpha) = J(\Delta \alpha)$. -/
theorem JActsOnForms.laplacian_commutes_J
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : Codifferential (inst := inst))


    (d_commutes_J : ∀ {p : ℕ} (α : Ω p), inst.d (Jf.J_form α) = Jf.J_form (inst.d α))


    (dstar_commutes_J : ∀ {p : ℕ} (α : Ω (p + 1)),
      cod.dstar (Jf.J_form α) = Jf.J_form (cod.dstar α))
    {p : ℕ} (α : Ω (p + 1)) :
    laplacian cod (Jf.J_form α) = Jf.J_form (laplacian cod α) := by


  unfold laplacian
  rw [dstar_commutes_J α, d_commutes_J (cod.dstar α),
      d_commutes_J α, dstar_commutes_J (inst.d α),
      ← Jf.J_form_add]


/-- The Kähler identity $[\Lambda, d^*] = 0$: the dual Lefschetz operator commutes with
the codifferential, $\Lambda \circ d^* = d^* \circ \Lambda$. Proved from $[L, d] = 0$
by taking $L^2$-adjoints. -/
theorem kahler_identity_Lstar_dstar_commute
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (lef : LefschetzOp S)
    (cod : Codifferential (inst := inst))
    (ip : L2InnerProduct cod)

    (dl : DualLefschetz (inst := inst))


    (adjoint_L : ∀ {q : ℕ} (γ : Ω q) (δ : Ω (q + 2)),
      ip.inner (lef.L_op γ) δ = ip.inner γ (dl.Λ_op δ))
    {p : ℕ} (α : Ω (p + 3)) :
    dl.Λ_op (cod.dstar α) = cod.dstar (dl.Λ_op α) := by


  suffices h : ∀ β : Ω p,
      ip.inner (dl.Λ_op (cod.dstar α)) β = ip.inner (cod.dstar (dl.Λ_op α)) β by

    have hdiff : ∀ β : Ω p,
        ip.inner (dl.Λ_op (cod.dstar α) - cod.dstar (dl.Λ_op α)) β = 0 := by
      intro β
      have hsub : dl.Λ_op (cod.dstar α) - cod.dstar (dl.Λ_op α) =
          dl.Λ_op (cod.dstar α) + (-1 : ℝ) • cod.dstar (dl.Λ_op α) := by
        simp [sub_eq_add_neg]

      rw [hsub, ip.inner_add_left, ip.inner_smul_left, h β]
      ring
    have hself := hdiff (dl.Λ_op (cod.dstar α) - cod.dstar (dl.Λ_op α))
    exact sub_eq_zero.mp (ip.inner_self_eq_zero _ hself)

  intro β


  have adjoint_Lstar : ∀ {q : ℕ} (x : Ω (q + 2)) (y : Ω q),
      ip.inner (dl.Λ_op x) y = ip.inner x (lef.L_op y) := by
    intro q x y
    rw [ip.inner_symm (dl.Λ_op x) y]
    rw [← adjoint_L y x]
    rw [ip.inner_symm]

  calc ip.inner (dl.Λ_op (cod.dstar α)) β


      _ = ip.inner (cod.dstar α) (lef.L_op β) := adjoint_Lstar _ _

      _ = ip.inner (lef.L_op β) (cod.dstar α) := ip.inner_symm _ _


      _ = ip.inner (inst.d (lef.L_op β)) α := by
            exact (ip.adjoint_d (lef.L_op β) α).symm

      _ = ip.inner (lef.L_op (inst.d β)) α := by
            rw [lef.d_commutes β]


      _ = ip.inner (inst.d β) (dl.Λ_op α) := adjoint_L _ _


      _ = ip.inner β (cod.dstar (dl.Λ_op α)) := ip.adjoint_d _ _

      _ = ip.inner (cod.dstar (dl.Λ_op α)) β := ip.inner_symm _ _


/-- The four Kähler identities on a Kähler manifold:
$[L, d] = 0$, $[\Lambda, d^*] = 0$, $[L, d^*] = d_C$, $[\Lambda, d] = -d_C^*$. -/
theorem kahler_identities_all_four
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    (Jf : JActsOnForms J)
    (lef : LefschetzOp S)
    (cod : Codifferential (inst := inst))
    (ip : L2InnerProduct cod)
    (dl : DualLefschetz (inst := inst))


    (adjoint_L : ∀ {q : ℕ} (γ : Ω q) (δ : Ω (q + 2)),
      ip.inner (lef.L_op γ) δ = ip.inner γ (dl.Λ_op δ))

    (identity3_L_dstar : ∀ {p : ℕ} (α : Ω (p + 1)),
      lef.L_op (cod.dstar α) + -(cod.dstar (lef.L_op α)) = d_C_form Jf α)

    (identity4_Λ_d : ∀ {p : ℕ} (α : Ω (p + 2)),
      dl.Λ_op (inst.d α) + -(inst.d (dl.Λ_op α)) = -(d_C_star_form Jf cod α)) :

    (∀ {p : ℕ} (α : Ω p),
      lef.L_op (inst.d α) = inst.d (lef.L_op α)) ∧

    (∀ {p : ℕ} (α : Ω (p + 3)),
      dl.Λ_op (cod.dstar α) = cod.dstar (dl.Λ_op α)) ∧

    (∀ {p : ℕ} (α : Ω (p + 1)),
      lef.L_op (cod.dstar α) + -(cod.dstar (lef.L_op α)) = d_C_form Jf α) ∧

    (∀ {p : ℕ} (α : Ω (p + 2)),
      dl.Λ_op (inst.d α) + -(inst.d (dl.Λ_op α)) = -(d_C_star_form Jf cod α)) :=
  ⟨fun α => lef.d_commutes α,
   fun α => kahler_identity_Lstar_dstar_commute lef cod ip dl adjoint_L α,
   fun α => identity3_L_dstar α,
   fun α => identity4_Λ_d α⟩


/-- On a Kähler manifold the Laplacian is $J$-invariant: $\Delta(J\alpha) = J(\Delta \alpha)$. -/
theorem laplacian_J_invariant
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    (Jf : JActsOnForms J)
    (cod : Codifferential (inst := inst))

    (d_commutes_J : ∀ {p : ℕ} (α : Ω p), inst.d (Jf.J_form α) = Jf.J_form (inst.d α))

    (dstar_commutes_J : ∀ {p : ℕ} (α : Ω (p + 1)),
      cod.dstar (Jf.J_form α) = Jf.J_form (cod.dstar α))
    {p : ℕ} (α : Ω (p + 1)) :
    laplacian cod (Jf.J_form α) = Jf.J_form (laplacian cod α) :=
  Jf.laplacian_commutes_J cod d_commutes_J dstar_commutes_J α


/-- A linear differential operator $L: \Omega^{p+1} \to \Omega^{p+1}$ of order `order`
equipped with its principal symbol $\sigma_k(L)(\xi)$ that is homogeneous of degree
`order` in $\xi$. -/
structure IsDifferentialOperator
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  order : ℕ
  symbol : Ω 1 → (∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
  L_add : ∀ {p : ℕ} (α β : Ω (p + 1)), L (α + β) = L α + L β
  L_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), L (r • α) = r • L α
  symbol_homogeneous : ∀ (r : ℝ) (ξ : Ω 1) {p : ℕ} (α : Ω (p + 1)),
    symbol (r • ξ) α = r ^ order • symbol ξ α

/-- A general elliptic operator $L: \Gamma E \to \Gamma F$: a linear operator
whose principal symbol $\sigma(L)(\xi)$ is a bijection for every nonzero $\xi$. -/
structure IsElliptic
    {ΓE : Type*} {ΓF : Type*} {T : Type*}
    [AddCommGroup ΓE] [Module ℝ ΓE]
    [AddCommGroup ΓF] [Module ℝ ΓF]
    [AddCommGroup T] [Module ℝ T]
    (L : ΓE → ΓF) where
  order : ℕ
  symbol : T → (ΓE → ΓF)
  L_add : ∀ (s t : ΓE), L (s + t) = L s + L t
  L_smul : ∀ (r : ℝ) (s : ΓE), L (r • s) = r • L s
  symbol_homogeneous : ∀ (r : ℝ) (ξ : T) (s : ΓE),
    symbol (r • ξ) s = r ^ order • symbol ξ s
  elliptic : ∀ (ξ : T), ξ ≠ 0 → Function.Bijective (symbol ξ)

/-- An elliptic differential endomorphism $L: \Omega^{p+1} \to \Omega^{p+1}$:
a differential operator whose principal symbol is bijective at every nonzero covector. -/
structure IsEllipticEndo
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
    extends IsDifferentialOperator (inst := inst) L where
  elliptic : ∀ (ξ : Ω 1), ξ ≠ 0 → ∀ {p : ℕ}, Function.Bijective (symbol ξ (p := p))


/-- A compact manifold of positive dimension `dim`. -/
class IsCompactManifold (Ω : ℕ → Type*) (VF : Type*)
    [DifferentialFormSpace Ω VF] where
  dim : ℕ
  dim_pos : 0 < dim

/-- A compact oriented Riemannian manifold equipped with a codifferential, an $L^2$
inner product, a volume form, Stokes' theorem for exact forms, and the integral formula
$\langle \alpha, \beta\rangle = \int_M \alpha \wedge *\beta$. Also assumes finite
dimensionality of harmonic forms in each degree. -/
class IsCompactOrientedRiemannian (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] extends IsCompactManifold Ω VF where
  cod : @Codifferential Ω VF inst
  ip : @L2InnerProduct Ω VF inst cod
  vol : Ω dim
  vol_nonzero : vol ≠ 0
  wedge_star : ∀ (p : ℕ), Ω p → Ω p → Ω dim
  integrate : Ω dim → ℝ
  integrate_linear : ∀ (r : ℝ) (ω₁ ω₂ : Ω dim),
    integrate (r • ω₁ + ω₂) = r * integrate ω₁ + integrate ω₂

  stokes_exact_vanishes : ∀ (p : ℕ) (hp : p + 1 = dim) (η : Ω p),
    integrate (hp ▸ inst.d η) = 0

  inner_eq_integrate_wedge_star : ∀ {p : ℕ} (α β : Ω p),
    ip.inner α β = integrate (wedge_star p α β)
  compact_finite_dim_harmonic : ∀ (k : ℕ),
    ∃ (S : Finset (Ω (k + 1))),
      (∀ s ∈ S, IsHarmonic cod s) ∧
      (∀ (α : Ω (k + 1)), IsHarmonic cod α →
        ∃ (coeffs : Ω (k + 1) → ℝ),
          α = S.sum (fun s => coeffs s • s))


/-- Builds an `IsCompactOrientedRiemannian` structure on a compact symplectic manifold
(of real dimension $2n$) from explicit choices of codifferential, $L^2$ inner product,
volume form, Stokes data, and finite-dimensional harmonic spaces. -/
@[reducible] noncomputable def IsCompactSymplectic.toIsCompactOrientedRiemannian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [h : IsCompactSymplectic Ω VF]
    (cod : Codifferential (inst := inst))
    (ip : @L2InnerProduct Ω VF inst cod)
    (vol : Ω (2 * h.n))
    (vol_nonzero : vol ≠ 0)
    (wedge_star : ∀ (p : ℕ), Ω p → Ω p → Ω (2 * h.n))
    (integrate : Ω (2 * h.n) → ℝ)
    (integrate_linear : ∀ (r : ℝ) (ω₁ ω₂ : Ω (2 * h.n)),
      integrate (r • ω₁ + ω₂) = r * integrate ω₁ + integrate ω₂)
    (stokes : ∀ (p : ℕ) (hp : p + 1 = 2 * h.n) (η : Ω p),
      integrate (hp ▸ inst.d η) = 0)

    (inner_eq : ∀ {p : ℕ} (α β : Ω p),
      ip.inner α β = integrate (wedge_star p α β))
    (finite_harmonic : ∀ (k : ℕ),
      ∃ (S : Finset (Ω (k + 1))),
        (∀ s ∈ S, IsHarmonic cod s) ∧
        (∀ (α : Ω (k + 1)), IsHarmonic cod α →
          ∃ (coeffs : Ω (k + 1) → ℝ),
            α = S.sum (fun s => coeffs s • s)))
    : IsCompactOrientedRiemannian Ω VF where
  dim := 2 * h.n
  dim_pos := Nat.mul_pos (by norm_num) h.n_pos
  cod := cod
  ip := ip
  vol := vol
  vol_nonzero := vol_nonzero
  wedge_star := wedge_star
  integrate := integrate
  integrate_linear := integrate_linear
  stokes_exact_vanishes := stokes
  inner_eq_integrate_wedge_star := inner_eq
  compact_finite_dim_harmonic := finite_harmonic

/-- Every compact symplectic manifold (of complex dimension $n$) is a compact manifold
of real dimension $2n$. -/
instance (priority := 100) IsCompactSymplectic.toIsCompactManifold
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    [h : IsCompactSymplectic Ω VF] : IsCompactManifold Ω VF where
  dim := 2 * h.n
  dim_pos := Nat.mul_pos (by norm_num) h.n_pos

/-- Minimal data required for Hodge theory: a codifferential and a compatible $L^2$
inner product on differential forms. -/
class HasHodgeData (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  codiff : @Codifferential Ω VF inst
  l2ip   : @L2InnerProduct Ω VF inst codiff

/-- Every compact oriented Riemannian manifold provides Hodge data. -/
noncomputable instance (priority := 100) IsCompactOrientedRiemannian.toHasHodgeData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF] : HasHodgeData Ω VF where
  codiff := hR.cod
  l2ip := hR.ip

/-- The Hodge star operator extracted from the codifferential data on a compact oriented
Riemannian manifold. -/
noncomputable def IsCompactOrientedRiemannian.hodgeStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF] : @HodgeStar Ω VF inst :=
  hR.cod.hodge

/-- On a compact oriented Riemannian manifold the codifferential satisfies the standard
formula $d^*\omega = (-1)^{n(k-1)+1} * d * \omega$. -/
theorem IsCompactOrientedRiemannian.codifferential_from_star
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF]
    {p : ℕ} (h : p + 1 ≤ hR.cod.manifold_dim) (ω : Ω (p + 1)) :
    hR.cod.dstar ω = hR.cod.sign_factor (p + 1) •
      cast (by congr 1; omega)
        (hR.cod.star_deg (by omega : hR.cod.manifold_dim - (p + 1) + 1 ≤ hR.cod.manifold_dim)
          (inst.d (hR.cod.star_deg h ω))) :=
  hR.cod.dstar_formula h ω

/-- The $L^2$ inner product equals the integral of the wedge with the star:
$\langle \alpha, \beta \rangle = \int_M \alpha \wedge *\beta$. -/
theorem IsCompactOrientedRiemannian.l2_inner_eq_integral
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF]
    {p : ℕ} (α β : Ω p) :
    hR.ip.inner α β = hR.integrate (hR.wedge_star p α β) :=
  hR.inner_eq_integrate_wedge_star α β


/-- A predicate giving the Sobolev regularity scale $H^s$ for differential forms. -/
class HasSobolevSpaces (Ω : ℕ → Type*) (VF : Type*) [DifferentialFormSpace Ω VF] where
  IsSobolevRegular : ℕ → ∀ {p : ℕ}, Ω (p + 1) → Prop


/-- A *smoothing operator* $S$: linear and raises Sobolev regularity by at least one
order (and by two when iterated). -/
class IsSmoothing {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [sob : HasSobolevSpaces Ω VF]
    (S : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) : Prop where
  S_add : ∀ {p : ℕ} (a b : Ω (p + 1)), S (a + b) = S a + S b
  S_smul : ∀ {p : ℕ} (r : ℝ) (a : Ω (p + 1)), S (r • a) = r • S a
  sobolev_improvement : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + 1) (S α)
  compact_improvement : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + 2) (S (S α))

/-- Iterating a smoothing operator $n$ times raises Sobolev regularity by $n$ orders:
if $\alpha \in H^s$, then $S^n \alpha \in H^{s+n}$. -/
theorem IsSmoothing.iterate_improvement
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [sob : HasSobolevSpaces Ω VF]
    {S : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)}
    [hS : IsSmoothing (inst := inst) S] :
    ∀ (n s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + n) (S^[n] α) := by
  intro n
  induction n with
  | zero => intro s p α h; simpa using h
  | succ n ih =>
    intro s p α hs
    rw [Function.iterate_succ', Function.comp]
    have h1 := ih s α hs
    have h2 := hS.sobolev_improvement (s + n) (S^[n] α) h1
    rwa [show s + (n + 1) = s + n + 1 from by omega]


/-- A smoothing operator $S: E \to E$ on an abstract topological vector space, characterized
by raising the Sobolev regularity by one order. -/
structure IsSmoothingOp {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    (S : E →L[ℝ] E)
    (IsSobReg : ℕ → E → Prop) : Prop where
  sobolev_improvement : ∀ (s : ℕ) (α : E),
    IsSobReg s α → IsSobReg (s + 1) (S α)

/-- A parametrix (pseudo-inverse) for a continuous linear operator $L: E \to F$:
a continuous linear $P: F \to E$ with $PL = \mathrm{id} + S_{\text{left}}$ and
$LP = \mathrm{id} + S_{\text{right}}$, where $S_{\text{left}}$ and $S_{\text{right}}$
are smoothing operators. -/
structure HasParametrix
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    (L : E →L[ℝ] F) where
  P : F →L[ℝ] E
  S_left : E →L[ℝ] E
  S_right : F →L[ℝ] F
  PL_eq : ∀ (α : E), P (L α) = α + S_left α
  LP_eq : ∀ (β : F), L (P β) = β + S_right β
  IsSobRegE : ℕ → E → Prop
  IsSobRegF : ℕ → F → Prop
  isSmoothingOp_S_left : IsSmoothingOp S_left IsSobRegE
  isSmoothingOp_S_right : IsSmoothingOp S_right IsSobRegF

/-- The left smoothing remainder $S_{\text{left}}$ of a parametrix as an $\mathbb{R}$-linear map. -/
def HasParametrix.sLeftLinearMap
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    {L : E →L[ℝ] F}
    (h : HasParametrix L) : E →ₗ[ℝ] E :=
  h.S_left.toLinearMap

/-- The right smoothing remainder $S_{\text{right}}$ of a parametrix as an $\mathbb{R}$-linear map. -/
def HasParametrix.sRightLinearMap
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    {L : E →L[ℝ] F}
    (h : HasParametrix L) : F →ₗ[ℝ] F :=
  h.S_right.toLinearMap

/-- A parametrix (pseudo-inverse) for an operator $L$ on the differential form spaces:
$PL = \mathrm{id} + S_{\text{left}}$ and $LP = \mathrm{id} + S_{\text{right}}$ with
smoothing remainders. -/
structure HasParametrixDFS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasSobolevSpaces Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  P : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_left : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_right : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  PL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (P α) = α + S_right α
  S_left_isSmoothing : IsSmoothing (inst := inst) S_left
  S_right_isSmoothing : IsSmoothing (inst := inst) S_right


/-- A Fredholm operator on differential forms: linear, with a parametrix, having finite
dimensional kernel and cokernel and complemented (closed) range. -/
structure IsFredholm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  P : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_left : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_right : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  PL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (P α) = α + S_right α
  ker_contained : ∀ {p : ℕ} (α : Ω (p + 1)),
    L α = 0 → α + S_left α = P (0 : Ω (p + 1))
  L_add : ∀ {p : ℕ} (α β : Ω (p + 1)), L (α + β) = L α + L β
  L_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), L (r • α) = r • L α
  kernel_finiteDim : ∀ (p : ℕ),
    FiniteDimensional ℝ ↥(LinearMap.ker
      ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
         map_add' := L_add
         map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)))
  cokernel_finiteDim : ∀ (p : ℕ),
    FiniteDimensional ℝ (Ω (p + 1) ⧸ LinearMap.range
      ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
         map_add' := L_add
         map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)))
  range_complemented : ∀ (p : ℕ),
    ∃ (C : Submodule ℝ (Ω (p + 1))),
      LinearMap.range
        ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
           map_add' := L_add
           map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)) ⊔ C = ⊤ ∧
      LinearMap.range
        ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
           map_add' := L_add
           map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)) ⊓ C = ⊥

/-- Packages a Fredholm operator on $\Omega^{p+1}$ as an $\mathbb{R}$-linear map. -/
def IsFredholm.toLinearMap
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)}
    (hF : IsFredholm (inst := inst) L) (p : ℕ) : Ω (p + 1) →ₗ[ℝ] Ω (p + 1) :=
  { toFun := L
    map_add' := hF.L_add
    map_smul' := hF.L_smul }


/-- A Green-operator decomposition $\mathrm{id} = LG + H$ where $H$ is the harmonic
projection (with $LH = 0$) and $G$ is the Green operator (inverse of $L$ on
$(\ker L)^\perp$). Asserts the orthogonality $\langle H\alpha, LG\alpha\rangle = 0$. -/
structure HasGreenOperatorDecomp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  G : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  H : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  H_maps_to_ker : ∀ {p : ℕ} (α : Ω (p + 1)), L (H α) = 0
  LG_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (G α) = α + -(H α)
  GL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), G (L α) = α + -(H α)
  H_idem : ∀ {p : ℕ} (α : Ω (p + 1)), H (H α) = H α
  G_add : ∀ {p : ℕ} (α β : Ω (p + 1)), G (α + β) = G α + G β
  H_add : ∀ {p : ℕ} (α β : Ω (p + 1)), H (α + β) = H α + H β
  G_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), G (r • α) = r • G α
  H_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), H (r • α) = r • H α
  G_preserves_regularity : ∀ [sob : HasSobolevSpaces Ω VF] (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular s (G α)
  H_preserves_regularity : ∀ [sob : HasSobolevSpaces Ω VF] (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular s (H α)
  orth_decomp : ∀ (cod : Codifferential (inst := inst))
      (ip : @L2InnerProduct Ω VF inst cod)
      {p : ℕ} (α : Ω (p + 1)),
      ip.inner (H α) (L (G α)) = 0
  G_H_eq_zero : ∀ {p : ℕ} (α : Ω (p + 1)), G (H α) = 0
  H_G_eq_zero : ∀ {p : ℕ} (α : Ω (p + 1)), H (G α) = 0


/-- The formal adjoint $\bar\partial^*: \Omega^{p+1} \to \Omega^p$ of the Dolbeault
operator $\bar\partial$. -/
structure DelbarStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) where
  delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  delbar_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The formal adjoint $\partial^*: \Omega^{p+1} \to \Omega^p$ of the Dolbeault
operator $\partial$. -/
structure DelStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) where
  del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  del_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    del_star (α + β) = del_star α + del_star β
  del_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    del_star (r • α) = r • del_star α






/-- **Elliptic regularity.** If $L$ is an elliptic operator with parametrix $P$ and
$\xi$ is a Sobolev section with $L\xi$ smooth, then $\xi$ itself is smooth:
$L\xi \in C^\infty \Rightarrow \xi \in C^\infty$. -/
theorem elliptic_regularity
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF] [HasSobolevSpaces Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
    (param : HasParametrixDFS (inst := inst) L)
    (IsSmoothSection : ∀ {p : ℕ}, Ω (p + 1) → Prop)
    (IsSobolevRegular : ℕ → ∀ {p : ℕ}, Ω (p + 1) → Prop)

    (P_preserves_smooth : ∀ {p : ℕ} (β : Ω (p + 1)), IsSmoothSection β → IsSmoothSection (param.P β))


    (S_left_maps_sobolev_to_smooth : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
      IsSobolevRegular s α → IsSmoothSection (param.S_left α))

    (smooth_sub : ∀ {p : ℕ} (a b : Ω (p + 1)),
      IsSmoothSection a → IsSmoothSection b → IsSmoothSection (a - b))
    {p : ℕ} {ξ : Ω (p + 1)}
    (s : ℕ) (hξ_sob : IsSobolevRegular s ξ)
    (hLξ_smooth : IsSmoothSection (L ξ)) :
    IsSmoothSection ξ := by

  have hid := param.PL_eq ξ

  have hP_smooth : IsSmoothSection (param.P (L ξ)) :=
    P_preserves_smooth (L ξ) hLξ_smooth

  have hS_smooth : IsSmoothSection (param.S_left ξ) :=
    S_left_maps_sobolev_to_smooth s ξ hξ_sob

  have h_eq : ξ = param.P (L ξ) - param.S_left ξ := by
    rw [hid]; simp [sub_eq_add_neg, add_assoc, add_neg_cancel]
  rw [h_eq]
  exact smooth_sub _ _ hP_smooth hS_smooth
















/-- The $L^2$ inner product is additive in its second argument:
$\langle \alpha, \beta + \gamma\rangle = \langle \alpha, \beta\rangle + \langle \alpha, \gamma\rangle$. -/
lemma L2InnerProduct.inner_add_right
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    (ip : L2InnerProduct cod) {p : ℕ} (α β γ : Ω p) :
    ip.inner α (β + γ) = ip.inner α β + ip.inner α γ := by
  rw [ip.inner_symm α (β + γ), ip.inner_add_left, ip.inner_symm β α, ip.inner_symm γ α]

/-- The Hodge Laplacian is self-adjoint with respect to the $L^2$ inner product:
$\langle \Delta\alpha, \beta\rangle = \langle \alpha, \Delta\beta\rangle$. -/
theorem laplacian_self_adjoint
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    (ip : L2InnerProduct cod)
    {p : ℕ} (α β : Ω (p + 1)) :
    ip.inner (laplacian cod α) β = ip.inner α (laplacian cod β) := by
  unfold laplacian

  rw [ip.inner_add_left]

  rw [ip.inner_add_right]

  have h1 : ip.inner (inst.d (cod.dstar α)) β = ip.inner (cod.dstar α) (cod.dstar β) :=
    ip.adjoint_d (cod.dstar α) β
  have h2 : ip.inner α (inst.d (cod.dstar β)) = ip.inner (cod.dstar α) (cod.dstar β) := by
    rw [ip.inner_symm, ip.adjoint_d (cod.dstar β) α, ip.inner_symm]
  have h3 : ip.inner (cod.dstar (inst.d α)) β = ip.inner (inst.d α) (inst.d β) := by
    rw [ip.inner_symm (cod.dstar (inst.d α)) β]


    rw [← ip.adjoint_d β (inst.d α), ip.inner_symm (inst.d β) (inst.d α)]
  have h4 : ip.inner α (cod.dstar (inst.d β)) = ip.inner (inst.d α) (inst.d β) :=
    (ip.adjoint_d α (inst.d β)).symm
  linarith


/-- The image of the Green operator $G \circ \Delta$ is exactly the orthogonal complement
of the harmonic forms: $\alpha \in \mathrm{Im}(G \circ \Delta) \iff \alpha \perp \mathcal{H}^k$. -/
theorem green_operator_image_orthogonal
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactOrientedRiemannian Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    (gd : @HasGreenOperatorDecomp Ω VF inst (fun α => laplacian cod α))
    {p : ℕ} (α : Ω (p + 1)) :
    (∃ β, gd.G (laplacian cod β) = α) ↔
      (∀ h : Ω (p + 1), IsHarmonic cod h → ip.inner h α = 0) := by
  constructor
  ·
    rintro ⟨β, hβ⟩ h hh

    have hGL : gd.G (laplacian cod β) = β + -(gd.H β) := gd.GL_eq β
    have hLG : laplacian cod (gd.G β) = β + -(gd.H β) := gd.LG_eq β

    have hα_eq : α = laplacian cod (gd.G β) := by
      have : α = β + -(gd.H β) := by rw [← hGL, hβ]
      rw [this, ← hLG]

    rw [hα_eq, ip.inner_symm, laplacian_self_adjoint cod ip (gd.G β) h]
    rw [show laplacian cod h = 0 from hh]

    rw [ip.inner_symm]; exact ip.inner_zero_left (gd.G β)
  ·
    intro horth

    use α

    have hGL : gd.G (laplacian cod α) = α + -(gd.H α) := gd.GL_eq α

    suffices hH0 : gd.H α = 0 by rw [hGL, hH0, neg_zero, add_zero]

    have hH_harm : IsHarmonic cod (gd.H α) := gd.H_maps_to_ker α

    have horth_Hα : ip.inner (gd.H α) α = 0 := horth (gd.H α) hH_harm

    have hLG : laplacian cod (gd.G α) = α + -(gd.H α) := gd.LG_eq α

    have hα_decomp : α = gd.H α + laplacian cod (gd.G α) := by
      have : gd.H α + laplacian cod (gd.G α) = gd.H α + (α + -(gd.H α)) := by
        rw [hLG]
      rw [this]; abel


    have horth_decomp : ip.inner (gd.H α) (laplacian cod (gd.G α)) = 0 :=
      gd.orth_decomp cod ip α

    have hHα_self : ip.inner (gd.H α) (gd.H α) = 0 := by

      have expand : ip.inner (gd.H α) α =
          ip.inner (gd.H α) (gd.H α) + ip.inner (gd.H α) (laplacian cod (gd.G α)) := by
        have h_eq : ip.inner (gd.H α) α =
            ip.inner (gd.H α) (gd.H α + laplacian cod (gd.G α)) := by
          congr 1

        rw [h_eq, ip.inner_add_right]
      linarith

    exact ip.inner_self_eq_zero (gd.H α) hHα_self




/-- **Hodge decomposition (three-way version).** Every form $\alpha \in \Omega^k$
on a compact oriented Riemannian manifold can be written as
$\alpha = h + d\beta + d^*\gamma$ with $h$ harmonic. -/
theorem hodge_decomposition_three_way
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactOrientedRiemannian Ω VF]
    (cod : @Codifferential Ω VF inst)


    (h_green : Nonempty (@HasGreenOperatorDecomp Ω VF inst (fun α => laplacian cod α)))
    {p : ℕ} (α : Ω (p + 1)) :
    ∃ (h : Ω (p + 1)) (β : Ω p) (γ : Ω (p + 2)),
      IsHarmonic cod h ∧ α = h + inst.d β + cod.dstar γ := by

  obtain ⟨gd⟩ := h_green

  refine ⟨gd.H α, cod.dstar (gd.G α), inst.d (gd.G α), ?_, ?_⟩
  ·

    exact gd.H_maps_to_ker α
  ·


    have hLG := gd.LG_eq α

    show α = gd.H α + inst.d (cod.dstar (gd.G α)) + cod.dstar (inst.d (gd.G α))


    have hLG' : inst.d (cod.dstar (gd.G α)) + cod.dstar (inst.d (gd.G α)) = α + -gd.H α := hLG

    have step : gd.H α + (inst.d (cod.dstar (gd.G α)) + cod.dstar (inst.d (gd.G α))) = α := by
      rw [hLG']; abel
    rw [← add_assoc] at step
    exact step.symm


/-- Harmonic forms are $L^2$-orthogonal to exact forms:
$\langle h, d\beta\rangle = 0$ when $h$ is harmonic. -/
theorem orthog_harmonic_exact
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    {p : ℕ} (h : Ω (p + 1)) (hh : IsHarmonic cod h) (β : Ω p) :
    ip.inner h (inst.d β) = 0 := by
  rw [ip.inner_symm]

  rw [ip.adjoint_d]

  rw [(harmonic_iff_closed_coclosed cod ip h).mp hh |>.2]

  rw [ip.inner_symm]
  exact ip.inner_zero_left β

/-- Harmonic forms are $L^2$-orthogonal to coexact forms:
$\langle h, d^*\gamma\rangle = 0$ when $h$ is harmonic. -/
theorem orthog_harmonic_coexact
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    {p : ℕ} (h : Ω (p + 1)) (hh : IsHarmonic cod h) (γ : Ω (p + 2)) :
    ip.inner h (cod.dstar γ) = 0 := by

  rw [← ip.adjoint_d]

  rw [(harmonic_iff_closed_coclosed cod ip h).mp hh |>.1]
  exact ip.inner_zero_left γ

/-- Exact and coexact forms are $L^2$-orthogonal: $\langle d\beta, d^*\gamma\rangle = 0$,
since $\langle d\beta, d^*\gamma\rangle = \langle d^2\beta, \gamma\rangle = 0$. -/
theorem orthog_exact_coexact
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    {p : ℕ} (β : Ω p) (γ : Ω (p + 2)) :
    ip.inner (inst.d β) (cod.dstar γ) = 0 := by

  rw [← ip.adjoint_d]

  rw [inst.d_squared]
  exact ip.inner_zero_left γ


/-- Typeclass packaging the existence of a Green-operator decomposition for the
Hodge Laplacian. -/
class HasLaplacianGreenDecomp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst) where
  green_decomp : Nonempty (@HasGreenOperatorDecomp Ω VF inst (fun α => laplacian cod α))


/-- **Hodge decomposition theorem (orthogonal form).** On a compact oriented Riemannian
manifold, every $(k+1)$-form $\alpha$ has an orthogonal Hodge decomposition
$\alpha = h + d\beta + d^*\gamma$ with the three summands pairwise $L^2$-orthogonal,
and the harmonic part $h$ is unique. -/
theorem hodge_decomposition_orthogonal
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactOrientedRiemannian Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    [h_green : HasLaplacianGreenDecomp cod]

    {p : ℕ} (α : Ω (p + 1)) :

    (∃ (h : Ω (p + 1)) (β : Ω p) (γ : Ω (p + 2)),
      IsHarmonic cod h ∧
      α = h + inst.d β + cod.dstar γ ∧

      ip.inner h (inst.d β) = 0 ∧
      ip.inner h (cod.dstar γ) = 0 ∧
      ip.inner (inst.d β) (cod.dstar γ) = 0) ∧

    (∀ (h₁ h₂ : Ω (p + 1)) (β₁ β₂ : Ω p) (γ₁ γ₂ : Ω (p + 2)),
      IsHarmonic cod h₁ → IsHarmonic cod h₂ →
      α = h₁ + inst.d β₁ + cod.dstar γ₁ →
      α = h₂ + inst.d β₂ + cod.dstar γ₂ →
      h₁ = h₂) := by
  constructor
  ·
    obtain ⟨h, β, γ, hh, hdecomp⟩ := hodge_decomposition_three_way cod h_green.green_decomp α
    exact ⟨h, β, γ, hh, hdecomp,
      orthog_harmonic_exact cod ip h hh β,
      orthog_harmonic_coexact cod ip h hh γ,
      orthog_exact_coexact cod ip β γ⟩
  ·
    intro h₁ h₂ β₁ β₂ γ₁ γ₂ hHarm₁ hHarm₂ hdecomp₁ hdecomp₂


    have dstar_neg_local : ∀ {q : ℕ} (ω : Ω (q + 1)),
        cod.dstar (-ω) = -cod.dstar ω := by
      intro q ω; have := cod.dstar_smul (-1 : ℝ) ω; simp at this; exact this
    have hdiff : h₁ - h₂ = inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁) := by
      have heq : h₁ + inst.d β₁ + cod.dstar γ₁ = h₂ + inst.d β₂ + cod.dstar γ₂ :=
        hdecomp₁.symm.trans hdecomp₂
      have hd_sub : inst.d (β₂ - β₁) = inst.d β₂ - inst.d β₁ := by
        rw [show β₂ - β₁ = β₂ + (-β₁) from sub_eq_add_neg β₂ β₁, inst.d_add, d_neg]; abel
      have hds_sub : cod.dstar (γ₂ - γ₁) = cod.dstar γ₂ - cod.dstar γ₁ := by
        rw [show γ₂ - γ₁ = γ₂ + (-γ₁) from sub_eq_add_neg γ₂ γ₁,
            cod.dstar_add, dstar_neg_local]; abel
      rw [hd_sub, hds_sub]
      have h1 : h₁ = α - inst.d β₁ - cod.dstar γ₁ := by rw [hdecomp₁]; abel
      have h2 : h₂ = α - inst.d β₂ - cod.dstar γ₂ := by rw [hdecomp₂]; abel
      rw [h1, h2]; abel

    have hHarm_diff : IsHarmonic cod (h₁ - h₂) := by
      unfold IsHarmonic laplacian
      rw [show h₁ - h₂ = h₁ + (-h₂) from sub_eq_add_neg h₁ h₂]
      rw [cod.dstar_add, inst.d_add, inst.d_add, cod.dstar_add]
      rw [d_neg, dstar_neg_local, d_neg, dstar_neg_local]
      have hΔ₁ : inst.d (cod.dstar h₁) + cod.dstar (inst.d h₁) = 0 := hHarm₁
      have hΔ₂ : inst.d (cod.dstar h₂) + cod.dstar (inst.d h₂) = 0 := hHarm₂

      have h1a : inst.d (cod.dstar h₁) = -(cod.dstar (inst.d h₁)) :=
        eq_neg_of_add_eq_zero_left hΔ₁
      have h2a : inst.d (cod.dstar h₂) = -(cod.dstar (inst.d h₂)) :=
        eq_neg_of_add_eq_zero_left hΔ₂
      rw [h1a, h2a]; abel

    have inner_zero : ip.inner (h₁ - h₂) (h₁ - h₂) = 0 := by
      have hrw : ip.inner (h₁ - h₂) (h₁ - h₂) =
          ip.inner (h₁ - h₂) (inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁)) := by
        rw [show (h₁ - h₂ : Ω (p + 1)) = inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁) from hdiff]
      rw [hrw]
      rw [ip.inner_symm (h₁ - h₂) (inst.d (β₂ - β₁) + cod.dstar (γ₂ - γ₁)),
          ip.inner_add_left,
          ip.inner_symm (inst.d (β₂ - β₁)), ip.inner_symm (cod.dstar (γ₂ - γ₁))]
      have h_exact : ip.inner (h₁ - h₂) (inst.d (β₂ - β₁)) = 0 :=
        orthog_harmonic_exact cod ip (h₁ - h₂) hHarm_diff (β₂ - β₁)
      have h_coexact : ip.inner (h₁ - h₂) (cod.dstar (γ₂ - γ₁)) = 0 :=
        orthog_harmonic_coexact cod ip (h₁ - h₂) hHarm_diff (γ₂ - γ₁)
      linarith
    exact sub_eq_zero.mp (ip.inner_self_eq_zero _ inner_zero)


/-- **Hodge representative (existence).** Every closed form $\alpha$ on a compact oriented
Riemannian manifold can be written as $\alpha = h + d\beta$ with $h$ harmonic. -/
theorem hodge_representative
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactOrientedRiemannian Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)


    (h_green : Nonempty (HasGreenOperatorDecomp (inst := inst) (fun α => laplacian cod α)))
    {p : ℕ} (α : Ω (p + 1)) (hclosed : inst.d α = 0) :
    ∃ (h : Ω (p + 1)) (β : Ω p),
      IsHarmonic cod h ∧ α = h + inst.d β := by

  obtain ⟨h, β, γ, hHarm, hDecomp⟩ := hodge_decomposition_three_way cod h_green α


  have hclosed_h : inst.d h = 0 :=
    ((harmonic_iff_closed_coclosed cod ip h).mp hHarm).1


  have hd_dstar_gamma : inst.d (cod.dstar γ) = 0 := by
    have := congr_arg inst.d hDecomp
    rw [inst.d_add, inst.d_add, hclosed, hclosed_h, inst.d_squared] at this

    simp only [zero_add, add_zero] at this
    exact this.symm

  have adj : ip.inner (inst.d (cod.dstar γ)) γ =
      ip.inner (cod.dstar γ) (cod.dstar γ) :=
    ip.adjoint_d (cod.dstar γ) γ

  have inner_zero : ip.inner (cod.dstar γ) (cod.dstar γ) = 0 := by
    rw [← adj, hd_dstar_gamma]; exact ip.inner_zero_left γ

  have hvanish : cod.dstar γ = 0 := ip.inner_self_eq_zero _ inner_zero

  exact ⟨h, β, hHarm, by rw [hDecomp, hvanish, add_zero]⟩


/-- An exact harmonic form is zero: if $h = d\gamma$ is harmonic, then $h = 0$.
Proof: $\langle h, h\rangle = \langle d\gamma, h\rangle = \langle \gamma, d^* h\rangle = 0$. -/
theorem harmonic_exact_is_zero
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    {p : ℕ} (h : Ω (p + 1)) (hHarm : IsHarmonic cod h)
    (γ : Ω p) (hExact : h = inst.d γ) :
    h = 0 := by

  have hcoclosed : cod.dstar h = 0 :=
    ((harmonic_iff_closed_coclosed cod ip h).mp hHarm).2

  have inner_hh : ip.inner h h = 0 := by

    have : ip.inner h h = ip.inner (inst.d γ) h := by rw [hExact]
    rw [this, ip.adjoint_d γ h, hcoclosed]

    rw [ip.inner_symm γ (0 : Ω p)]
    exact ip.inner_zero_left γ


  exact ip.inner_self_eq_zero h inner_hh

/-- The codifferential commutes with negation: $d^*(-\alpha) = -d^*\alpha$. -/
lemma Codifferential.dstar_neg
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) :
    cod.dstar (-α) = -cod.dstar α := by
  have := cod.dstar_smul (-1 : ℝ) α; simp at this; exact this

/-- The Laplacian is additive under subtraction: $\Delta(\alpha - \beta) = \Delta\alpha - \Delta\beta$. -/
lemma laplacian_sub
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α β : Ω (p + 1)) :
    laplacian cod (α - β) = laplacian cod α - laplacian cod β := by
  unfold laplacian
  rw [show α - β = α + (-β) from sub_eq_add_neg α β]
  rw [cod.dstar_add, inst.d_add, inst.d_add, cod.dstar_add]
  rw [d_neg, cod.dstar_neg, d_neg, cod.dstar_neg]
  abel

/-- **Hodge representative uniqueness.** If $h_1, h_2$ are harmonic and differ by an
exact form, $h_1 - h_2 = d\gamma$, then $h_1 = h_2$. -/
theorem hodge_representative_unique
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    {p : ℕ} (h₁ h₂ : Ω (p + 1))
    (hHarm₁ : IsHarmonic cod h₁) (hHarm₂ : IsHarmonic cod h₂)
    (γ : Ω p) (hDiff : h₁ - h₂ = inst.d γ) :
    h₁ = h₂ := by

  have hHarm_diff : IsHarmonic cod (h₁ - h₂) := by
    unfold IsHarmonic
    rw [laplacian_sub]

    rw [show laplacian cod h₁ = 0 from hHarm₁, show laplacian cod h₂ = 0 from hHarm₂]
    simp

  have hzero : h₁ - h₂ = 0 := harmonic_exact_is_zero cod ip (h₁ - h₂) hHarm_diff γ hDiff
  exact sub_eq_zero.mp hzero

/-- The exterior derivative is additive under subtraction: $d(\alpha - \beta) = d\alpha - d\beta$. -/
lemma d_sub
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {p : ℕ} (α β : Ω p) :
    inst.d (α - β) = inst.d α - inst.d β := by
  rw [show α - β = α + (-β) from sub_eq_add_neg α β, inst.d_add, d_neg]
  abel


/-- **Hodge theorem.** Every de Rham cohomology class on a compact oriented Riemannian
manifold has a unique harmonic representative: for any closed $\alpha$, there is a unique
harmonic $h$ with $\alpha = h + d\beta$ for some $\beta$. -/
theorem hodge_representative_exists_unique
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF]


    (h_green : Nonempty (@HasGreenOperatorDecomp Ω VF inst (fun α => laplacian hR.cod α)))
    {p : ℕ} (α : Ω (p + 1)) (hclosed : inst.d α = 0) :
    ∃! (h : Ω (p + 1)), IsHarmonic hR.cod h ∧ ∃ (β : Ω p), α = h + inst.d β := by

  let cod := hR.cod
  let ip := hR.ip

  obtain ⟨h, β, hHarm, hDecomp⟩ := hodge_representative cod ip h_green α hclosed

  refine ⟨h, ⟨hHarm, β, hDecomp⟩, ?_⟩

  intro h' ⟨hHarm', β', hDecomp'⟩

  have hdiff : h - h' = inst.d (β' - β) := by
    have heq : h + inst.d β = h' + inst.d β' := hDecomp.symm.trans hDecomp'
    rw [d_sub]


    have step : h = h' + inst.d β' + -(inst.d β) := by
      calc h = (h + inst.d β) + -(inst.d β) := by abel
        _ = (h' + inst.d β') + -(inst.d β) := by rw [heq]

    calc h - h' = (h' + inst.d β' + -(inst.d β)) - h' := by rw [step]
      _ = inst.d β' - inst.d β := by abel

  exact (hodge_representative_unique cod ip h h' hHarm hHarm' (β' - β) hdiff).symm

/-- Two forms $\alpha_1, \alpha_2$ are de Rham cohomologous if they differ by an exact form:
$\alpha_1 - \alpha_2 = d\gamma$ for some $\gamma$. -/
def IsDRCohomologous
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {k : ℕ} (α₁ α₂ : Ω (k + 1)) : Prop :=
  ∃ (γ : Ω k), α₁ - α₂ = inst.d γ


/-- **Hodge decomposition of de Rham cohomology on Kähler manifolds.**
Cohomologous closed forms on a compact Kähler manifold share the same harmonic
representative, which further decomposes into $(p,q)$-components, each
$\bar\partial$-harmonic: this yields $H^k_{dR}(M, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}_{\bar\partial}(M)$. -/
theorem kahler_hodge_decomposition_cohomology
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    (cod : Codifferential (inst := inst))

    (ip : L2InnerProduct cod)
    (dol : DolbeaultOps (inst := inst))
    {n : ℕ} (bg : HasBigrading J n)
    (dol_lap : DolbeaultLaplacian dol cod)


    (h_harmonic_bigrading :
      ∀ {k : ℕ} (h_form : Ω (k + 1)) (_h_harmonic : laplacian cod h_form = 0),
        ∃ (component : Fin (k + 2) → Ω (k + 1)),
          (∀ (j : Fin (k + 2)),
            ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)),
              cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt)))
                (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧
          (∀ j, dol.del (component j) = 0) ∧
          (∀ j, dol.delbar (component j) = 0) ∧
          (∀ j, laplacian cod (component j) = 0) ∧
          h_form = Finset.univ.sum component)

    (h_hodge_rep : ∀ {p : ℕ} (α' : Ω (p + 1)), inst.d α' = 0 →
      ∃ (h : Ω (p + 1)) (β : Ω p),
        laplacian cod h = 0 ∧ α' = h + inst.d β)

    (h_dolbeault_id : ∀ {k' : ℕ} (α' : Ω (k' + 1)),
      laplacian cod α' = 0 ↔ dol_lap.box_bar α' = 0)

    {k : ℕ}

    (α₁ α₂ : Ω (k + 1))
    (hclosed₁ : inst.d α₁ = 0)
    (hclosed₂ : inst.d α₂ = 0)
    (hcohom : IsDRCohomologous (inst := inst) (k := k) α₁ α₂) :


    (∀ (h₁ h₂ : Ω (k + 1)) (β₁ β₂ : Ω k),
      IsHarmonic cod h₁ → α₁ = h₁ + inst.d β₁ →
      IsHarmonic cod h₂ → α₂ = h₂ + inst.d β₂ →
      h₁ = h₂) ∧


    (∃ (component : Fin (k + 2) → Ω (k + 1)) (β : Ω k),

      (∀ (j : Fin (k + 2)),
        ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)),
          cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt)))
            (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧

      (∀ j, dol.del (component j) = 0) ∧

      (∀ j, dol.delbar (component j) = 0) ∧

      (∀ j, laplacian cod (component j) = 0) ∧

      (∀ j, dol_lap.box_bar (component j) = 0) ∧


      (α₁ = (Finset.univ.sum component) + inst.d β) ∧
      (∃ (β' : Ω k), α₂ = (Finset.univ.sum component) + inst.d β')) := by
  obtain ⟨γ, hγ⟩ := hcohom
  constructor

  · intro h₁ h₂ β₁ β₂ hHarm₁ hDecomp₁ hHarm₂ hDecomp₂


    have hdiff : h₁ - h₂ = inst.d (γ - β₁ + β₂) := by
      have h₁_eq : h₁ = α₁ - inst.d β₁ := by rw [hDecomp₁]; abel
      have h₂_eq : h₂ = α₂ - inst.d β₂ := by rw [hDecomp₂]; abel
      rw [h₁_eq, h₂_eq]
      rw [show α₁ - inst.d β₁ - (α₂ - inst.d β₂) = (α₁ - α₂) - (inst.d β₁ - inst.d β₂)
        from by abel]
      rw [hγ, ← d_sub, show inst.d γ - inst.d (β₁ - β₂) = inst.d (γ - (β₁ - β₂))
        from (d_sub γ (β₁ - β₂)).symm]
      congr 1; abel
    exact hodge_representative_unique cod ip h₁ h₂ hHarm₁ hHarm₂ (γ - β₁ + β₂) hdiff


  ·
    obtain ⟨h₁, β₁, hHarm₁, hDecomp₁⟩ := h_hodge_rep α₁ hclosed₁
    obtain ⟨h₂, β₂, hHarm₂, hDecomp₂⟩ := h_hodge_rep α₂ hclosed₂

    have heq_harm : h₁ = h₂ := by
      have hdiff : h₁ - h₂ = inst.d (γ - β₁ + β₂) := by
        have h₁_eq : h₁ = α₁ - inst.d β₁ := by rw [hDecomp₁]; abel
        have h₂_eq : h₂ = α₂ - inst.d β₂ := by rw [hDecomp₂]; abel
        rw [h₁_eq, h₂_eq]
        rw [show α₁ - inst.d β₁ - (α₂ - inst.d β₂) = (α₁ - α₂) - (inst.d β₁ - inst.d β₂)
          from by abel]
        rw [hγ, ← d_sub, show inst.d γ - inst.d (β₁ - β₂) = inst.d (γ - (β₁ - β₂))
          from (d_sub γ (β₁ - β₂)).symm]
        congr 1; abel
      exact hodge_representative_unique cod ip h₁ h₂ hHarm₁ hHarm₂ (γ - β₁ + β₂) hdiff

    obtain ⟨component, h_bideg, h_del, h_delbar, h_laplacian, h_sum⟩ :=
      h_harmonic_bigrading h₁ hHarm₁


    have h_box_bar : ∀ j, dol_lap.box_bar (component j) = 0 := by
      intro j
      exact (h_dolbeault_id (component j)).mp (h_laplacian j)


    have hDecomp₂' : α₂ = Finset.univ.sum component + inst.d β₂ := by
      rw [← heq_harm] at hDecomp₂
      rw [hDecomp₂, h_sum]
    exact ⟨component, β₁,
      h_bideg, h_del, h_delbar, h_laplacian, h_box_bar,
      by rw [hDecomp₁, h_sum],
      β₂, hDecomp₂'⟩


set_option maxHeartbeats 400000 in
/-- **Corollary 4 (Kähler Hodge corollary).** Combines:
(a) the Laplacian preserves the bigrading on a Kähler manifold;
(b) every de Rham cohomology class has a unique harmonic representative whose
$(p,q)$-components are $\bar\partial$-harmonic, providing the Hodge decomposition
$H^k_{dR}(M, \mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}_{\bar\partial}(M)$. -/
theorem corollary4_kahler_hodge
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    (cod : @Codifferential Ω VF inst)
    (ip : L2InnerProduct cod)
    (dol : DolbeaultOps (inst := inst))
    {n : ℕ} (bg : HasBigrading J n)
    (dol_lap : DolbeaultLaplacian dol cod)
    (wells : KahlerWellsIdentities S J hK dol_lap)


    (h_box_bar_pres : ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)))


    (h_harmonic_bigrading :
      ∀ {k : ℕ} (h_form : Ω (k + 1)) (_h_harmonic : laplacian cod h_form = 0),
        ∃ (component : Fin (k + 2) → Ω (k + 1)),
          (∀ (j : Fin (k + 2)),
            ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)),
              cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt)))
                (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧
          (∀ j, dol.del (component j) = 0) ∧
          (∀ j, dol.delbar (component j) = 0) ∧
          (∀ j, laplacian cod (component j) = 0) ∧
          h_form = Finset.univ.sum component)

    (_hC : @HasComplexStructure Ω VF inst)

    (h_hodge_rep : ∀ {p : ℕ} (α' : Ω (p + 1)), inst.d α' = 0 →
      ∃ (h : Ω (p + 1)) (β : Ω p),
        laplacian cod h = 0 ∧ α' = h + inst.d β) :


    (∀ (k : ℕ) (p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω))) ∧


    (∀ {k : ℕ} (α₁ α₂ : Ω (k + 1))
      (hclosed₁ : inst.d α₁ = 0) (hclosed₂ : inst.d α₂ = 0)
      (hcohom : IsDRCohomologous (inst := inst) (k := k) α₁ α₂),


      (∀ (h₁ h₂ : Ω (k + 1)) (β₁ β₂ : Ω k),
        IsHarmonic cod h₁ → α₁ = h₁ + inst.d β₁ →
        IsHarmonic cod h₂ → α₂ = h₂ + inst.d β₂ →
        h₁ = h₂) ∧


      (∃ (component : Fin (k + 2) → Ω (k + 1)) (β : Ω k),
        (∀ (j : Fin (k + 2)),
          ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)),
            cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt)))
              (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧
        (∀ j, dol.del (component j) = 0) ∧
        (∀ j, dol.delbar (component j) = 0) ∧
        (∀ j, laplacian cod (component j) = 0) ∧
        (∀ j, dol_lap.box_bar (component j) = 0) ∧
        (α₁ = (Finset.univ.sum component) + inst.d β) ∧
        (∃ (β' : Ω k), α₂ = (Finset.univ.sum component) + inst.d β'))) := by

  have h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
    fun α => kahler_two_box_bar_blocker S J hK dol_lap wells α

  have h_dolbeault_id : ∀ {k' : ℕ} (α' : Ω (k' + 1)),
      laplacian cod α' = 0 ↔ dol_lap.box_bar α' = 0 :=
    fun α' => dolbeault_identification S J hK cod dol dol_lap h_two_box_bar α'
  constructor


  · exact fun k p' q' h ω =>
      laplacian_preserves_bidegree S J hK cod dol dol_lap bg h_box_bar_pres
        (h_two_box_bar := h_two_box_bar) k p' q' h ω

  · intro k α₁ α₂ hclosed₁ hclosed₂ hcohom
    exact kahler_hodge_decomposition_cohomology S J hK cod ip dol bg dol_lap
      h_harmonic_bigrading h_hodge_rep h_dolbeault_id α₁ α₂ hclosed₁ hclosed₂ hcohom


/-- A form $\alpha \in \Omega^{p+q}$ is a pure $(p,q)$-form if it lies in the image of
the inclusion $\Omega^{p,q} \hookrightarrow \Omega^{p+q}$. -/
def HasBigrading.is_pq_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n) (p q : ℕ) (α : Ω (p + q)) : Prop :=
  ∃ β : bg.Ω_pq p q, bg.incl p q β = α


/-- The Hodge star respects the Hodge bigrading: $*: \Omega^{p,q} \to \Omega^{n-q, n-p}$. -/
theorem HasBigrading.star_bigraded
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n) (β : bg.Ω_pq p q) :
    ∃ γ : bg.Ω_pq (n - q) (n - p),
      bg.incl (n - q) (n - p) γ =
        cast (congrArg Ω (by omega))
          (bg.star_total (by omega : p + q ≤ 2 * n) (bg.incl p q β)) := by

  obtain ⟨a, b, c, ha, hb, habc, γ, hγ⟩ := bg.star_abc_decomp hp hq β


  have h_nq : a + (n - a - b - c) = n - q := by omega
  have h_np : b + (n - a - b - c) = n - p := by omega

  exact ⟨cast (by rw [h_nq, h_np]) γ, by
    rw [bg.incl_cast h_nq h_np γ, hγ, cast_cast]⟩

/-- The Hodge star restricted to the bigraded piece $\Omega^{p,q}$, with image in
$\Omega^{n-q, n-p}$. -/
noncomputable def HasBigrading.star_pq
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (β : bg.Ω_pq p q) : bg.Ω_pq (n - q) (n - p) :=
  (bg.star_bigraded hp hq β).choose

/-- Defining identity for `star_pq`: its inclusion into $\Omega^{2n-(p+q)}$ matches the
total Hodge star applied to the inclusion of $\beta$. -/
theorem HasBigrading.star_pq_spec
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (β : bg.Ω_pq p q) :
    bg.incl (n - q) (n - p) (bg.star_pq hp hq β) =
      cast (congrArg Ω (by omega))
        (bg.star_total (by omega : p + q ≤ 2 * n) (bg.incl p q β)) :=
  (bg.star_bigraded hp hq β).choose_spec


/-- If $\alpha$ is a pure $(p,q)$-form, then $*\alpha$ is a pure $(n-q, n-p)$-form,
reflecting that the Hodge star preserves the bigrading. -/
theorem hodge_star_pq_type
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    {n : ℕ} (bg : HasBigrading J n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (α : Ω (p + q)) (hα : bg.is_pq_form p q α) :
    bg.is_pq_form (n - q) (n - p)
      (cast (congrArg Ω (by omega)) (bg.star_total (by omega : p + q ≤ 2 * n) α)) := by

  obtain ⟨β, hβ⟩ := hα


  obtain ⟨γ, hγ⟩ := bg.star_bigraded hp hq β


  exact ⟨γ, by subst hβ; exact hγ⟩


/-- An $L^2$ inner product compatible with the Dolbeault $\bar\partial$ operator:
the formal adjoint $\bar\partial^*$ is the $L^2$-adjoint of $\bar\partial$,
witnessed via Stokes-type integration formulas. -/
structure ComplexL2InnerProduct
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dbs : DelbarStar dol)
    extends L2InnerProduct cod where
  integrate_delbar_top : ∀ {p : ℕ}, Ω p → Ω (p + 1) → ℝ
  stokes_delbar_leibniz : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (dol.delbar α) β = (-1 : ℝ)^(p + 1) • integrate_delbar_top α β
  h_delbar_star_sign : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    (-1 : ℝ)^(p + 1) • integrate_delbar_top α β = inner α (dbs.delbar_star β)


/-- Stokes-derived adjointness: $\langle \bar\partial \alpha, \beta\rangle = \langle \alpha, \bar\partial^* \beta\rangle$,
obtained by combining the Stokes-Leibniz expansion with the sign-tracking formula
for $\bar\partial^*$. -/
theorem delbar_adjoint_from_stokes
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dbs : DelbarStar dol)
    (cip : ComplexL2InnerProduct cod dol dbs)
    {p : ℕ} (α : Ω p) (β : Ω (p + 1)) :
    cip.inner (dol.delbar α) β = cip.inner α (dbs.delbar_star β) := by

  rw [cip.stokes_delbar_leibniz α β]

  exact cip.h_delbar_star_sign α β

/-- $\bar\partial^*$ is the $L^2$-adjoint of $\bar\partial$ on a compact symplectic manifold:
$\langle \bar\partial \alpha, \beta\rangle = \langle \alpha, \bar\partial^* \beta\rangle$. -/
theorem delbar_star_L2_adjoint
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dbs : DelbarStar dol)
    (cip : ComplexL2InnerProduct cod dol dbs)
    {p : ℕ} (α : Ω p) (β : Ω (p + 1)) :
    cip.inner (dol.delbar α) β = cip.inner α (dbs.delbar_star β) :=
  delbar_adjoint_from_stokes cod dol dbs cip α β


/-- The $\partial$-counterpart of `ComplexL2InnerProduct`: an $L^2$ inner product
compatible with the Dolbeault $\partial$ operator and its formal adjoint $\partial^*$. -/
structure ComplexL2InnerProductDel
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (ds : DelStar dol)
    extends L2InnerProduct cod where
  integrate_del_top : ∀ {p : ℕ}, Ω p → Ω (p + 1) → ℝ
  stokes_del_leibniz : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (dol.del α) β = (-1 : ℝ)^(p + 1) • integrate_del_top α β
  h_del_star_sign : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    (-1 : ℝ)^(p + 1) • integrate_del_top α β = inner α (ds.del_star β)

/-- Stokes-derived adjointness: $\langle \partial \alpha, \beta\rangle = \langle \alpha, \partial^* \beta\rangle$. -/
theorem del_adjoint_from_stokes
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (ds : DelStar dol)
    (cip : ComplexL2InnerProductDel cod dol ds)
    {p : ℕ} (α : Ω p) (β : Ω (p + 1)) :
    cip.inner (dol.del α) β = cip.inner α (ds.del_star β) := by
  rw [cip.stokes_del_leibniz α β]
  exact cip.h_del_star_sign α β


/-- $\partial^*$ is the $L^2$-adjoint of $\partial$ on a compact symplectic manifold:
$\langle \partial \alpha, \beta\rangle = \langle \alpha, \partial^* \beta\rangle$. -/
theorem del_star_L2_adjoint
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (ds : DelStar dol)
    (cip : ComplexL2InnerProductDel cod dol ds)
    {p : ℕ} (α : Ω p) (β : Ω (p + 1)) :
    cip.inner (dol.del α) β = cip.inner α (ds.del_star β) :=
  del_adjoint_from_stokes cod dol ds cip α β


/-- **$L^2$-adjointness of Dolbeault operators (Lemma 2).** Both $\partial^*$ and
$\bar\partial^*$ are $L^2$-adjoints of $\partial$ and $\bar\partial$ respectively. -/
theorem lemma2_L2_adjointness
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dbs : DelbarStar dol)
    (ds : DelStar dol)
    (cip_delbar : ComplexL2InnerProduct cod dol dbs)
    (cip_del : ComplexL2InnerProductDel cod dol ds) :

    (∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
      cip_delbar.inner (dol.delbar α) β = cip_delbar.inner α (dbs.delbar_star β)) ∧

    (∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
      cip_del.inner (dol.del α) β = cip_del.inner α (ds.del_star β)) :=
  ⟨fun α β => delbar_star_L2_adjoint cod dol dbs cip_delbar α β,
   fun α β => del_star_L2_adjoint cod dol ds cip_del α β⟩


/-- A $\bar\square$-harmonic form is both $\bar\partial$-closed and $\bar\partial$-coclosed:
$\bar\square \alpha = 0 \iff \bar\partial \alpha = 0 \text{ and } \bar\partial^* \alpha = 0$
(direct $\Rightarrow$ implication shown). -/
theorem box_bar_harmonic_implies_delbar_closed_coclosed
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    (ip : L2InnerProduct cod)


    (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
      ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
    {p : ℕ} (α : Ω (p + 1))
    (hBox : dol_lap.box_bar α = 0) :
    dol.delbar α = 0 ∧ dol_lap.delbar_star α = 0 := by


  have eq1 : ip.inner (dol.delbar (dol_lap.delbar_star α)) α =
      ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) :=
    h_adj_delbar (dol_lap.delbar_star α) α

  have eq2 : ip.inner (dol_lap.delbar_star (dol.delbar α)) α =
      ip.inner (dol.delbar α) (dol.delbar α) := by
    rw [ip.inner_symm (dol_lap.delbar_star (dol.delbar α)) α,
        h_adj_delbar α (dol.delbar α), ip.inner_symm]


  have sum_eq : ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) +
      ip.inner (dol.delbar α) (dol.delbar α) = 0 := by
    have step : ip.inner (dol.delbar (dol_lap.delbar_star α) +
        dol_lap.delbar_star (dol.delbar α)) α =
        ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) +
        ip.inner (dol.delbar α) (dol.delbar α) := by
      rw [ip.inner_add_left, eq1, eq2]

    have hbox_def : dol.delbar (dol_lap.delbar_star α) +
        dol_lap.delbar_star (dol.delbar α) = dol_lap.box_bar α := rfl
    rw [hbox_def, hBox, ip.inner_zero_left] at step
    linarith

  have h_delbar_star : ip.inner (dol_lap.delbar_star α) (dol_lap.delbar_star α) = 0 := by
    linarith [ip.inner_self_nonneg (dol_lap.delbar_star α),
              ip.inner_self_nonneg (dol.delbar α)]
  have h_delbar : ip.inner (dol.delbar α) (dol.delbar α) = 0 := by linarith

  exact ⟨ip.inner_self_eq_zero _ h_delbar, ip.inner_self_eq_zero _ h_delbar_star⟩

/-- A $\bar\square$-harmonic form that is $\bar\partial$-exact is zero:
if $h = \bar\partial \gamma$ is $\bar\square$-harmonic, then $h = 0$. -/
theorem box_bar_harmonic_delbar_exact_is_zero
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    (ip : L2InnerProduct cod)
    (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
      ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
    {p : ℕ} (h : Ω (p + 1)) (hBox : dol_lap.box_bar h = 0)
    (γ : Ω p) (hExact : h = dol.delbar γ) :
    h = 0 := by

  have hcoclosed : dol_lap.delbar_star h = 0 :=
    (box_bar_harmonic_implies_delbar_closed_coclosed cod dol dol_lap ip h_adj_delbar h hBox).2

  have inner_hh : ip.inner h h = 0 := by
    have : ip.inner h h = ip.inner (dol.delbar γ) h := by rw [hExact]
    rw [this, h_adj_delbar γ h, hcoclosed]
    rw [ip.inner_symm γ (0 : Ω p)]
    exact ip.inner_zero_left γ

  exact ip.inner_self_eq_zero h inner_hh


/-- $\bar\partial^*$ commutes with negation: $\bar\partial^*(-\alpha) = -\bar\partial^*\alpha$. -/
lemma delbar_star_neg
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    {dol : DolbeaultOps (inst := inst)}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α : Ω (p + 1)) :
    dol_lap.delbar_star (-α) = -dol_lap.delbar_star α := by
  have := dol_lap.delbar_star_smul (-1 : ℝ) α; simp at this; exact this

/-- $\bar\partial$ commutes with negation: $\bar\partial(-\alpha) = -\bar\partial\alpha$. -/
lemma delbar_neg
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    {p : ℕ} (α : Ω p) :
    dol.delbar (-α) = -dol.delbar α := by
  have := dol.delbar_smul (-1 : ℝ) α; simp at this; exact this

/-- The $\bar\square$ Laplacian is linear under subtraction:
$\bar\square(\alpha - \beta) = \bar\square \alpha - \bar\square \beta$. -/
lemma box_bar_sub
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    {dol : DolbeaultOps (inst := inst)}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α β : Ω (p + 1)) :
    dol_lap.box_bar (α - β) = dol_lap.box_bar α - dol_lap.box_bar β := by
  unfold DolbeaultLaplacian.box_bar
  rw [show α - β = α + (-β) from sub_eq_add_neg α β]
  rw [dol_lap.delbar_star_add, dol.delbar_add, dol.delbar_add, dol_lap.delbar_star_add]
  rw [delbar_neg, delbar_star_neg dol_lap,
      delbar_neg, delbar_star_neg dol_lap]
  abel

/-- Uniqueness of the $\bar\square$-harmonic representative: two $\bar\square$-harmonic
forms whose $\bar\partial$-cohomology classes coincide must be equal. -/
theorem box_bar_harmonic_unique
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    (ip : L2InnerProduct cod)
    (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
      ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
    {p' : ℕ} (h₁ h₂ : Ω (p' + 1))
    (hHarm₁ : dol_lap.box_bar h₁ = 0)
    (hHarm₂ : dol_lap.box_bar h₂ = 0)
    (a b : Ω p')
    (hcohom : h₁ + dol.delbar a = h₂ + dol.delbar b) :
    h₁ = h₂ := by

  have hExact : h₁ - h₂ = dol.delbar (b - a) := by
    have hsub : h₁ - h₂ = dol.delbar b - dol.delbar a := by
      have : h₁ = h₂ + dol.delbar b - dol.delbar a := by rw [← hcohom]; abel
      rw [this]; abel
    rw [hsub]
    rw [show b - a = b + (-a) from sub_eq_add_neg b a, dol.delbar_add, delbar_neg]
    abel

  have hHarm_diff : dol_lap.box_bar (h₁ - h₂) = 0 := by
    rw [box_bar_sub dol_lap]
    rw [hHarm₁, hHarm₂]
    simp

  have hzero : h₁ - h₂ = 0 :=
    box_bar_harmonic_delbar_exact_is_zero cod dol dol_lap ip h_adj_delbar
      (h₁ - h₂) hHarm_diff (b - a) hExact
  exact sub_eq_zero.mp hzero








/-- A $\bar\square$-harmonic form is automatically $\bar\partial$-closed:
$\bar\square h = 0 \Rightarrow \bar\partial h = 0$. -/
theorem harmonic_is_delbar_closed
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    (ip : L2InnerProduct cod)
    (h_adj_delbar : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
      ip.inner (dol.delbar α) β = ip.inner α (dol_lap.delbar_star β))
    {p' : ℕ} (h : Ω (p' + 1))
    (hBox : dol_lap.box_bar h = 0) :
    dol.delbar h = 0 :=
  (box_bar_harmonic_implies_delbar_closed_coclosed cod dol dol_lap ip h_adj_delbar h hBox).1





/-- The twisted differential $d_C = -J d J$ as a method on `JActsOnForms`. -/
def JActsOnForms.d_C
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) : Ω (p + 1) :=
  -(Jf.J_form (inst.d (Jf.J_form α)))

/-- The twisted differential squares to zero: $d_C \circ d_C = 0$.
This follows from $d^2 = 0$ and $J^2 = -\mathrm{id}$. -/
theorem JActsOnForms.d_C_sq_zero
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) :
    Jf.d_C (Jf.d_C α) = 0 := by
  unfold JActsOnForms.d_C

  rw [Jf.J_form_neg]

  rw [Jf.J_form_sq]

  rw [neg_neg]

  rw [inst.d_squared]

  rw [Jf.J_form_zero]

  exact neg_zero


/-- The twisted Laplacian $\Delta_C = -J \Delta J$ associated to the $J$-action on forms. -/
def JActsOnForms.laplacian_C
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  -(Jf.J_form (laplacian cod (Jf.J_form α)))

/-- Compatibility data witnessing that $J$ commutes with each of $\partial, \bar\partial,
\partial^*, \bar\partial^*$ on a Kähler manifold. -/
structure KahlerJDolbeaultComm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    (dol_lap : DolbeaultLaplacian dol cod) where
  J_commutes_del : ∀ {p : ℕ} (α : Ω p), dol.del (Jf.J_form α) = Jf.J_form (dol.del α)
  J_commutes_delbar : ∀ {p : ℕ} (α : Ω p), dol.delbar (Jf.J_form α) = Jf.J_form (dol.delbar α)
  J_commutes_del_star : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol_lap.del_star (Jf.J_form α) = Jf.J_form (dol_lap.del_star α)
  J_commutes_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol_lap.delbar_star (Jf.J_form α) = Jf.J_form (dol_lap.delbar_star α)

/-- On a Kähler manifold, $d$ commutes with the action of $J$ on forms:
$d(J\alpha) = J(d\alpha)$. Deduced from $d = \partial + \bar\partial$ and the commutation
of each Dolbeault component with $J$. -/
theorem kahler_d_commutes_J
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    (Jf : JActsOnForms J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    {dol_lap : DolbeaultLaplacian dol cod}
    (hJD : KahlerJDolbeaultComm dol Jf cod dol_lap) :
    ∀ {p : ℕ} (α : Ω p), inst.d (Jf.J_form α) = Jf.J_form (inst.d α) := by
  intro p α
  rw [dol.decomp (Jf.J_form α), hJD.J_commutes_del, hJD.J_commutes_delbar,
      ← Jf.J_form_add, ← dol.decomp]

/-- On a Kähler manifold, $d^*$ commutes with the action of $J$:
$d^*(J\alpha) = J(d^*\alpha)$. Deduced from $d^* = \partial^* + \bar\partial^*$. -/
theorem kahler_dstar_commutes_J
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {dol : DolbeaultOps (inst := inst)}
    {dol_lap : DolbeaultLaplacian dol cod}
    (hJD : KahlerJDolbeaultComm dol Jf cod dol_lap) :
    ∀ {p : ℕ} (α : Ω (p + 1)),
      cod.dstar (Jf.J_form α) = Jf.J_form (cod.dstar α) := by
  intro p α
  rw [dol_lap.dstar_decomp (Jf.J_form α), hJD.J_commutes_del_star,
      hJD.J_commutes_delbar_star, ← Jf.J_form_add, ← dol_lap.dstar_decomp]

/-- On a Kähler manifold, the twisted Laplacian equals the ordinary one:
$\Delta_C = -J \Delta J = \Delta$, since $J$ commutes with $\Delta$ and $J^2 = -\mathrm{id}$. -/
theorem JActsOnForms.laplacian_C_eq_laplacian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J)
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {dol : DolbeaultOps (inst := inst)}
    {dol_lap : DolbeaultLaplacian dol cod}
    (hJD : KahlerJDolbeaultComm dol Jf cod dol_lap)
    {p : ℕ} (α : Ω (p + 1)) :
    Jf.laplacian_C cod α = laplacian cod α := by
  unfold JActsOnForms.laplacian_C


  rw [laplacian_J_invariant S J hK Jf cod
    (kahler_d_commutes_J S J hK Jf hJD)
    (kahler_dstar_commutes_J S J hK Jf cod hJD) α]


  rw [Jf.J_form_sq]

  exact neg_neg _


/-- The twisted codifferential $d_C^* = -J d^* J$ as a method on `JActsOnForms`. -/
def JActsOnForms.d_C_star
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) : Ω p :=
  -(Jf.J_form (cod.dstar (Jf.J_form α)))

/-- The twisted Laplacian decomposes as $\Delta_C = d_C d_C^* + d_C^* d_C$ in analogy
with the standard formula for $\Delta$. -/
theorem JActsOnForms.laplacian_C_eq_dC_decomp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) :
    Jf.laplacian_C cod α =
      Jf.d_C (Jf.d_C_star cod α) + Jf.d_C_star cod (Jf.d_C α) := by

  unfold JActsOnForms.laplacian_C laplacian JActsOnForms.d_C_star JActsOnForms.d_C


  conv_rhs => rw [show Jf.J_form (-(Jf.J_form (cod.dstar (Jf.J_form α))))
    = cod.dstar (Jf.J_form α) from by rw [Jf.J_form_neg, Jf.J_form_sq, neg_neg]]

  conv_rhs => rw [show Jf.J_form (-(Jf.J_form (inst.d (Jf.J_form α))))
    = inst.d (Jf.J_form α) from by rw [Jf.J_form_neg, Jf.J_form_sq, neg_neg]]


  rw [← neg_add]


  rw [← Jf.J_form_add]


/-- A form is *smooth via Sobolev* if it lies in every Sobolev space $H^s$:
$\alpha \in C^\infty \iff \alpha \in \bigcap_s H^s$. -/
def IsSmoothViaSobolev
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [sob : HasSobolevSpaces Ω VF]
    {p : ℕ} (α : Ω (p + 1)) : Prop :=
  ∀ s : ℕ, sob.IsSobolevRegular s α



