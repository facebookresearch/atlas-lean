/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

/-- Structure capturing the residue-field surjection at each place. For each
place $p \in P$, `degPlace p` is the $k$-degree of the residue field
$\mathcal{O}_p / \mathfrak{m}_p$, and `φ D p₀` is a surjective $k$-linear map
from $A(D+p_0)$ onto $\mathcal{O}_{p_0}/\mathfrak{m}_{p_0}$ whose kernel is
exactly $A(D)$ — packaging the ingredient needed for Lemma 22.8. -/
class HasResidueFieldSurjection (P : Type*) (F : Type*) (k : Type*)
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    (O : P → ValuationSubring F)
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] where
  degPlace : P → ℕ
  degPlace_pos : ∀ p, 0 < degPlace p
  φ : ∀ (D : P → ℤ) (p₀ : P),
    ↥(adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))) →ₗ[k]
    (Fin (degPlace p₀) → k)
  φ_surj : ∀ (D : P → ℤ) (p₀ : P), Function.Surjective (φ D p₀)
  φ_ker : ∀ (D : P → ℤ) (p₀ : P),
    LinearMap.ker (φ D p₀) =
      Submodule.comap
        (adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))).subtype
        (adeleSpace (F := F) (O := O) k D)


/-- A uniformizer exists at every place: an element $t \in F$ with
$\mathrm{ord}_p(t) = 1$. Wrapper around the corresponding axiom in the
`DiscreteValuationFamily` interface. -/
theorem uniformizer_exists {P : Type*} {F : Type*} {k : Type*}
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    {_O : P → ValuationSubring F}
    [DiscreteValuationFamily P F k] (p : P) :
    ∃ t : F, DiscreteValuationFamily.ord (k := k) p t = (1 : ℤ) :=
  DiscreteValuationFamily.uniformizer_exists (k := k) p

/-- The residue field $\mathcal{O}_p/\mathfrak{m}_p$ at a place $p$ is a
$k$-algebra via the composition $k \to \mathcal{O}_p \twoheadrightarrow
\mathcal{O}_p/\mathfrak{m}_p$. -/
noncomputable instance residueFieldAlgebra {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)] (p : P) :
    Algebra k (IsLocalRing.ResidueField ↥(O p)) :=
  letI : Algebra k ↥(O p) :=
    ((algebraMap k F).codRestrict (O p).toSubring
      (fun c => ConstantField.algebraMap_mem (k := k) (O := O) p c)).toAlgebra
  (IsLocalRing.residue ↥(O p) |>.comp (algebraMap k ↥(O p))).toAlgebra

/-- For a function field over its constant subfield $k$, the residue field at
any place $p$ is finite-dimensional over $k$. -/
theorem residueField_finiteDimensional {P : Type*} {F : Type*} {k : Type*}
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] (p : P) :
    FiniteDimensional k (IsLocalRing.ResidueField ↥(O p)) :=
  ConstantField.residueField_finiteDimensional p

/-- The *degree* $\deg p = [\mathcal{O}_p / \mathfrak{m}_p : k]$ of a place
$p$, defined as the $k$-dimension of the residue field. -/
noncomputable def placeDegree {P : Type*} {F : Type*} {k : Type*}
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] : P → ℕ := fun p =>
  Module.finrank k (IsLocalRing.ResidueField ↥(O p))

/-- The degree of any place is strictly positive: $\deg p \ge 1$. -/
theorem placeDegree_pos {P : Type*} {F : Type*} {k : Type*}
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k] (p : P) :
    0 < placeDegree (F := F) (k := k) (O := O) p := by
  unfold placeDegree
  haveI := residueField_finiteDimensional (F := F) (k := k) (O := O) p
  exact Module.finrank_pos






/-- Normalization: $\mathrm{ord}_p(1) = 0$. -/
lemma dvr_ord_one {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    [DiscreteValuationFamily P F k] (p : P) :
    DiscreteValuationFamily.ord (k := k) p (1 : F) = (0 : ℤ) := by
  have := DiscreteValuationFamily.ord_algebraMap (k := k) (F := F) p (1 : k) one_ne_zero
  rwa [map_one] at this

/-- Order of an integer power of a uniformizer: $\mathrm{ord}_p(t^m) = m$
whenever $\mathrm{ord}_p(t) = 1$ and $t \neq 0$. -/
lemma dvr_ord_zpow {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    [DiscreteValuationFamily P F k]
    (p : P) (t : F) (ht : DiscreteValuationFamily.ord (k := k) p t = (1 : ℤ))
    (ht_ne : t ≠ 0) (m : ℤ) :
    DiscreteValuationFamily.ord (k := k) p (t ^ m) = (m : ℤ) := by

  have ht_inv : DiscreteValuationFamily.ord (k := k) p t⁻¹ = (-1 : ℤ) := by
    have hmul := DiscreteValuationFamily.ord_mul (k := k) p t t⁻¹
    rw [mul_inv_cancel₀ ht_ne, dvr_ord_one, ht] at hmul
    cases hv : DiscreteValuationFamily.ord (k := k) p t⁻¹ with
    | top => rw [hv] at hmul; simp at hmul
    | coe v =>
      rw [hv, ← WithTop.coe_add] at hmul
      have : (1 : ℤ) + v = 0 := by exact_mod_cast hmul.symm
      norm_cast; omega
  induction m using Int.induction_on with
  | zero => simp [zpow_zero, dvr_ord_one]
  | succ n ih =>
    rw [zpow_add_one₀ ht_ne, DiscreteValuationFamily.ord_mul, ih, ht,
        ← WithTop.coe_add]
  | pred n ih =>
    rw [zpow_sub_one₀ ht_ne, DiscreteValuationFamily.ord_mul, ih, ht_inv,
        ← WithTop.coe_add]; congr 1


/-- Construction of an adele supported at a single place: given $x \in F$ with
$\mathrm{ord}_{p_0}(x) \ge -(D(p_0) + 1)$, there is an adele $\alpha \in A(D')$
(where $D' = D + p_0$) whose $p_0$-th component is $x$ and all other
components are $0$. -/
theorem adeleFromSingleComponent {P : Type*} {F : Type*} {k : Type*}
    [DecidableEq P] [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    (D : P → ℤ) (p₀ : P) (x : F)
    (hx : DiscreteValuationFamily.ord (k := k) p₀ x ≥ ↑(-(D p₀ + 1))) :
    ∃ α : ↥(adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1))),
      (α : FunctionFieldAdeleRing F P O) p₀ = x := by

  set f : P → F := Function.update (fun _ => (0 : F)) p₀ x with hf_def

  have h_cofin : ∀ᶠ p in Filter.cofinite, f p ∈ O p := by
    rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (Set.finite_singleton p₀)
    intro q hq
    simp only [Set.mem_setOf_eq] at hq
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hq (by rw [hf_def, Function.update_of_ne h]; exact (O q).toSubring.zero_mem)

  set α : FunctionFieldAdeleRing F P O := ⟨f, h_cofin⟩ with hα_def

  have h_mem : α ∈ adeleSpace (F := F) (O := O) k (Function.update D p₀ (D p₀ + 1)) := by
    intro q
    show DiscreteValuationFamily.ord (k := k) q (f q) ≥
      ↑(-(Function.update D p₀ (D p₀ + 1) q))
    by_cases hq : q = p₀
    · subst hq
      simp only [hf_def, Function.update_self, Function.update_self]
      exact hx
    · simp only [hf_def, Function.update_of_ne hq]
      simp only [DiscreteValuationFamily.ord_zero]
      exact le_top
  refine ⟨⟨α, h_mem⟩, ?_⟩
  show α p₀ = x
  simp only [hα_def, hf_def]
  change (Function.update (fun _ => (0 : F)) p₀ x) p₀ = x
  exact Function.update_self p₀ x (fun _ => (0 : F))

/-- $k$-linear projection of an adele onto its $p_0$-component: the map
$\alpha \mapsto \alpha(p_0)$ from the adele ring to $F$. -/
noncomputable def adeleComponentMap {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)]
    (p₀ : P) : FunctionFieldAdeleRing F P O →ₗ[k] F where
  toFun α := α p₀
  map_add' α β := by
    show (α + β) p₀ = α p₀ + β p₀
    rfl
  map_smul' c α := by
    show (c • α) p₀ = c • (α p₀)
    rw [FunctionFieldAdeleRing.smul_apply]
    simp only [Algebra.smul_def]





/-- Degree of a divisor $D = \sum n_p \cdot p$ as
$\deg D = \sum_p n_p \cdot \deg p$. -/
noncomputable def adeleDivisorDeg {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F}
    [DiscreteValuationFamily P F k]
    [DecidableEq P] [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [HasResidueFieldSurjection P F k O] (D : P →₀ ℤ) : ℤ :=
  D.sum (fun p n => n * (HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p : ℤ))

section ChainFormula

variable {R : Type*} [DivisionRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Chain formula for finrank of quotients of submodules: for $S \le T \le U$
in $M$, $$\dim_R(U/S) = \dim_R(T/S) + \dim_R(U/T),$$ and the left side is
finite-dimensional when both summands are. -/
theorem finrank_comap_chain (S T U : Submodule R M) (hST : S ≤ T) (hTU : T ≤ U)
    [FiniteDimensional R (↥U ⧸ Submodule.comap U.subtype T)]
    [FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype S)] :
    FiniteDimensional R (↥U ⧸ Submodule.comap U.subtype S) ∧
    Module.finrank R (↥U ⧸ Submodule.comap U.subtype S) =
    Module.finrank R (↥T ⧸ Submodule.comap T.subtype S) +
    Module.finrank R (↥U ⧸ Submodule.comap U.subtype T) := by
  set S' := Submodule.comap U.subtype S with hS'_def
  set T' := Submodule.comap U.subtype T with hT'_def
  have hS'T' : S' ≤ T' := Submodule.comap_mono hST
  let e := Submodule.comapSubtypeEquivOfLe hTU
  have hmap : Submodule.map e.toLinearMap (Submodule.comap T'.subtype S') =
      Submodule.comap T.subtype S := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy_mem, hy_eq⟩
      rw [← show (↑(e y) : M) = x from congr_arg Subtype.val hy_eq,
          Submodule.comapSubtypeEquivOfLe_apply_coe]
      exact hy_mem
    · intro hxS
      exact ⟨⟨⟨x, hTU hx⟩, hx⟩, hxS,
        Subtype.ext (Submodule.comapSubtypeEquivOfLe_apply_coe hTU _)⟩
  let qe := Submodule.Quotient.equiv _ _ e hmap
  haveI : FiniteDimensional R (↥T' ⧸ Submodule.comap T'.subtype S') :=
    Module.Finite.equiv qe.symm
  let f : ↥T' →ₗ[R] ↥U ⧸ S' := S'.mkQ.comp T'.subtype
  have hker_f : LinearMap.ker f = Submodule.comap T'.subtype S' := by
    ext ⟨x, hx⟩
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
               Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  have hrange_f : LinearMap.range f = Submodule.map S'.mkQ T' := by
    ext y; simp only [f, LinearMap.mem_range, LinearMap.comp_apply, Submodule.subtype_apply]
    exact ⟨fun ⟨⟨x, hx⟩, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩
  have h_re : (↥T' ⧸ Submodule.comap T'.subtype S') ≃ₗ[R] ↥(Submodule.map S'.mkQ T') := by
    rw [← hker_f, ← hrange_f]; exact f.quotKerEquivRange
  haveI : FiniteDimensional R ↥(Submodule.map S'.mkQ T') := Module.Finite.equiv h_re
  have h_iso := Submodule.quotientQuotientEquivQuotient S' T' hS'T'
  haveI : FiniteDimensional R ((↥U ⧸ S') ⧸ Submodule.map S'.mkQ T') :=
    Module.Finite.equiv h_iso.symm
  haveI : FiniteDimensional R (↥U ⧸ S') :=
    Module.Finite.of_submodule_quotient (Submodule.map S'.mkQ T')
  refine ⟨inferInstance, ?_⟩
  have h1 := Submodule.finrank_quotient_add_finrank (Submodule.map S'.mkQ T')
  rw [LinearEquiv.finrank_eq h_iso] at h1
  have h2 : Module.finrank R ↥(Submodule.map S'.mkQ T') =
    Module.finrank R (↥T' ⧸ Submodule.comap T'.subtype S') := (LinearEquiv.finrank_eq h_re).symm
  have h3 : Module.finrank R (↥T' ⧸ Submodule.comap T'.subtype S') =
    Module.finrank R (↥T ⧸ Submodule.comap T.subtype S) := LinearEquiv.finrank_eq qe
  omega

end ChainFormula

section Lemma22_8

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]

/-- Monotonicity of adele spaces in the divisor: $A \le B$ pointwise implies
$A(A) \subseteq A(B)$. -/
theorem adeleSpace_mono {A B : P → ℤ} (hAB : ∀ p, A p ≤ B p) :
    adeleSpace (F := F) (O := O) k A ≤ adeleSpace (F := F) (O := O) k B := by
  intro α hα
  simp only [adeleSpace, Submodule.mem_mk] at *
  intro p
  exact le_trans (by exact_mod_cast neg_le_neg_iff.mpr (hAB p)) (hα p)

variable [HasResidueFieldSurjection P F k O]

/-- Pullback of $A(A)$ to $A(B)$ as a $k$-submodule: the comap of $A(A)$
along the inclusion $A(B) \hookrightarrow $ adeles. -/
noncomputable abbrev adeleComap (A B : P → ℤ) :
    Submodule k (↥(adeleSpace (F := F) (O := O) k B)) :=
  Submodule.comap (adeleSpace (F := F) (O := O) k B).subtype
    (adeleSpace (F := F) (O := O) k A)

/-- Single-step dimension: incrementing $D$ by one at the place $p_0$
enlarges $A(D)$ by exactly $\deg p_0$ many $k$-dimensions, i.e.
$\dim_k A(D + p_0) / A(D) = \deg p_0$. -/
theorem adeleSpace_singleStep_finrank (D : P → ℤ) (p₀ : P) :
    let D' := Function.update D p₀ (D p₀ + 1)
    FiniteDimensional k
      (adeleSpace (F := F) (O := O) k D' ⧸
        Submodule.comap
          (adeleSpace (F := F) (O := O) k D').subtype
          (adeleSpace (F := F) (O := O) k D)) ∧
    Module.finrank k
      (adeleSpace (F := F) (O := O) k D' ⧸
        Submodule.comap
          (adeleSpace (F := F) (O := O) k D').subtype
          (adeleSpace (F := F) (O := O) k D)) =
      HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p₀ := by
  intro D'

  set φ := HasResidueFieldSurjection.φ (F := F) (O := O) (k := k) D p₀
  have hφ_surj := HasResidueFieldSurjection.φ_surj (F := F) (O := O) (k := k) D p₀
  have hφ_ker := HasResidueFieldSurjection.φ_ker (F := F) (O := O) (k := k) D p₀


  have h_equiv : (adeleSpace (F := F) (O := O) k D' ⧸ LinearMap.ker φ) ≃ₗ[k]
      LinearMap.range φ := φ.quotKerEquivRange

  have h_range_top : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj

  have h_equiv' : (adeleSpace (F := F) (O := O) k D' ⧸ LinearMap.ker φ) ≃ₗ[k]
      (Fin (HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p₀) → k) := by
    exact h_equiv.trans (LinearEquiv.ofTop _ h_range_top)

  rw [hφ_ker] at h_equiv'

  constructor
  ·
    exact Module.Finite.equiv h_equiv'.symm
  ·
    rw [LinearEquiv.finrank_eq h_equiv']
    simp

/-- Combinatorial distance between divisors: $\sum_p (B - A)(p)$, truncated to
$\mathbb{N}$. Used as a strong-induction measure in the proof of Lemma 22.8. -/
noncomputable def divisorDistance (A B : P →₀ ℤ) : ℕ :=
  ((B - A).sum (fun _ n => n)).toNat


/-- Strict decrease of the induction measure: subtracting one at any place
$p$ in the support of $B - A$ strictly decreases `divisorDistance A B`. -/
lemma divisorDistance_sub_single_lt {A B : P →₀ ℤ}
    (hAB : ∀ p, A p ≤ B p) (_h_ne : B - A ≠ 0)
    {p : P} (hp : p ∈ (B - A).support) :
    divisorDistance A (B - Finsupp.single p 1) < divisorDistance A B := by
  simp only [divisorDistance]
  have hBA_nonneg : ∀ q, 0 ≤ (B - A) q := fun q => by
    simp only [Finsupp.coe_sub, Pi.sub_apply]; linarith [hAB q]
  have hBAp_pos : (B - A) p ≥ 1 := by
    rw [Finsupp.mem_support_iff] at hp; have := hBA_nonneg p; omega
  have h_diff : (B - Finsupp.single p 1) - A = (B - A) - Finsupp.single p 1 := by
    ext q; simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]; ring
  rw [h_diff]
  have h_sub : ((B - A) - Finsupp.single p 1).sum (fun _ n => n) =
      (B - A).sum (fun _ n => n) - 1 := by
    rw [Finsupp.sum_sub_index (fun _ b₁ b₂ => by ring)]
    rw [Finsupp.sum_single_index rfl]
  rw [h_sub]
  have h_sum_nonneg : (B - A).sum (fun _ n => n) ≥ 0 :=
    Finsupp.sum_nonneg (fun q _ => hBA_nonneg q)
  have h_sum_pos : (B - A).sum (fun _ n => n) ≥ 1 := by
    unfold Finsupp.sum
    calc ∑ x ∈ (B - A).support, (B - A) x ≥ (B - A) p :=
          Finset.single_le_sum (fun q _ => hBA_nonneg q) hp
        _ ≥ 1 := hBAp_pos
  omega

/-- The comap of $A(D)$ in itself is the top submodule. -/
lemma adeleComap_top_of_eq (D : P → ℤ) :
    adeleComap (F := F) (O := O) k D D = ⊤ := by
  ext ⟨x, hx⟩
  simp only [adeleComap, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.mem_top, iff_true]
  exact hx

/-- The quotient $M / \top$ is the zero module, hence has $R$-rank $0$. -/
lemma finrank_quotient_top_eq_zero' {R M : Type*}
    [DivisionRing R] [AddCommGroup M] [Module R M] :
    Module.finrank R (M ⧸ (⊤ : Submodule R M)) = 0 := by
  haveI : Subsingleton (M ⧸ (⊤ : Submodule R M)) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/-- Behavior of divisor degree under addition of a single place:
$\deg(D + p) = \deg D + \deg p$. -/
lemma adeleDivisorDeg_add_single (D : P →₀ ℤ) (p : P) :
    adeleDivisorDeg (F := F) (k := k) (O := O) (D + Finsupp.single p 1) =
    adeleDivisorDeg (F := F) (k := k) (O := O) D +
    (HasResidueFieldSurjection.degPlace (F := F) (k := k) (O := O) p : ℤ) := by
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_add_index (fun a _ => by simp) (fun a _ n₁ n₂ => by ring)]
  rw [Finsupp.sum_single_index (by simp)]
  ring

/-- Lemma 22.8. For divisors $A \le B$, the quotient $A(B) / A(A)$ is
finite-dimensional over $k$ and $$\dim_k \big(A(B) / A(A)\big) = \deg(B - A).$$
Proved by strong induction on `divisorDistance`, peeling off one place at a
time and combining `adeleSpace_singleStep_finrank` with the chain formula
`finrank_comap_chain`. -/
theorem adeleSpace_quotient_finrank_eq (A B : P →₀ ℤ) (hAB : ∀ p, A p ≤ B p) :
    FiniteDimensional k
      (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⧸
        adeleComap k (A : P → ℤ) (B : P → ℤ)) ∧
    (Module.finrank k
      (adeleSpace (F := F) (O := O) k (B : P → ℤ) ⧸
        adeleComap k (A : P → ℤ) (B : P → ℤ)) : ℤ) =
      adeleDivisorDeg (F := F) (k := k) (O := O) (B - A) := by

  induction h : divisorDistance A B using Nat.strongRecOn generalizing A B with
  | _ n ih =>
  by_cases h_eq : B - A = 0
  ·
    have hAeqB : (A : P → ℤ) = (B : P → ℤ) := by
      ext p
      have := Finsupp.ext_iff.mp h_eq p
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    rw [show adeleComap (F := F) (O := O) k (A : P → ℤ) (B : P → ℤ) = ⊤ from by
      rw [← hAeqB]; exact adeleComap_top_of_eq k _]
    rw [h_eq]
    refine ⟨inferInstance, ?_⟩
    simp only [adeleDivisorDeg, Finsupp.sum_zero_index]
    rw [finrank_quotient_top_eq_zero']
    simp
  ·
    obtain ⟨p₀, hp₀⟩ := Finsupp.support_nonempty_iff.mpr h_eq
    set B' : P →₀ ℤ := B - Finsupp.single p₀ 1 with hB'_def
    have hBA_pos : B p₀ - A p₀ ≥ 1 := by
      rw [Finsupp.mem_support_iff] at hp₀
      have h0 := hAB p₀
      have : (B - A) p₀ ≠ 0 := hp₀
      simp only [Finsupp.coe_sub, Pi.sub_apply] at this
      omega
    have hAB' : ∀ q, A q ≤ B' q := by
      intro q
      simp only [hB'_def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hq
      · subst hq; linarith [hBA_pos]
      · simp only [sub_zero]; exact hAB q
    have hB'B : ∀ q, B' q ≤ B q := by
      intro q
      simp only [hB'_def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs <;> linarith
    have hB'p₀ : B' p₀ = B p₀ - 1 := by
      simp [hB'_def, Finsupp.coe_sub, Pi.sub_apply]
    have hB_update : (B : P → ℤ) = Function.update (B' : P → ℤ) p₀ (B' p₀ + 1) := by
      funext q
      by_cases hq : q = p₀
      · subst hq; simp [Function.update, hB'p₀]
      · simp only [Function.update, dif_neg hq]
        simp only [hB'_def, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply,
          if_neg (Ne.symm hq), sub_zero]
    have h_dist_lt : divisorDistance A B' < n := by
      rw [← h]; exact divisorDistance_sub_single_lt hAB h_eq hp₀
    have h_ind := ih _ h_dist_lt A B' hAB' rfl
    obtain ⟨hfd_ind, hrank_ind⟩ := h_ind

    have h_single := adeleSpace_singleStep_finrank (F := F) (O := O) k (B' : P → ℤ) p₀
    dsimp only at h_single
    rw [show Function.update (↑B' : P → ℤ) p₀ ((B' : P → ℤ) p₀ + 1) = (B : P → ℤ)
      from hB_update.symm] at h_single
    obtain ⟨h_single_fd, h_single_rank⟩ := h_single
    haveI := hfd_ind
    haveI := h_single_fd
    have h_chain := finrank_comap_chain
      (adeleSpace (F := F) (O := O) k (A : P → ℤ))
      (adeleSpace (F := F) (O := O) k (B' : P → ℤ))
      (adeleSpace (F := F) (O := O) k (B : P → ℤ))
      (adeleSpace_mono k hAB')
      (adeleSpace_mono k hB'B)
    obtain ⟨hfd_result, hrank_result⟩ := h_chain
    refine ⟨hfd_result, ?_⟩
    push_cast [hrank_result]
    rw [hrank_ind, h_single_rank]
    have h_BA : B - A = (B' - A) + Finsupp.single p₀ 1 := by
      ext q; simp [hB'_def]; ring
    rw [h_BA, adeleDivisorDeg_add_single]

end Lemma22_8
