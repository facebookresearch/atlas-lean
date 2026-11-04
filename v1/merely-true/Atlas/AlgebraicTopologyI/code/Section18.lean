/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.Torsion
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Atlas.AlgebraicTopologyI.code.Section14
import Atlas.AlgebraicTopologyI.code.Section1
import Atlas.AlgebraicTopologyI.code.Section16
import Atlas.AlgebraicTopologyI.code.ContractibleHomology

open Topology BigOperators AlgebraicTopology CategoryTheory

namespace EulerCharacteristic

/-- The rank of an abelian group $A$, defined as
$\dim_{\mathbb{Q}} (A \otimes_{\mathbb{Z}} \mathbb{Q})$.

For a finitely generated abelian group $A \cong \mathbb{Z}^r \oplus T$ (with
$T$ torsion), this returns $r$, the number of $\mathbb{Z}$-summands. -/
noncomputable def abelianGroupRank (A : Type*) [AddCommGroup A] : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ A)

/-- **Lemma 18.2** (rank is additive on short exact sequences). Given a SES
$0 \to A \to B \to C \to 0$ of finitely generated abelian groups,
$\operatorname{rank} B = \operatorname{rank} A + \operatorname{rank} C$.

Proof: Tensoring with $\mathbb{Q}$ over $\mathbb{Z}$ is exact (since $\mathbb{Q}$
is $\mathbb{Z}$-flat), so the rationalized sequence is also short exact, and
the result follows from rank-nullity for $\mathbb{Q}$-vector spaces. -/
theorem abelianGroupRank_additive
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module.Finite ℤ A] [Module.Finite ℤ B] [Module.Finite ℤ C]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f = LinearMap.ker g) :
    abelianGroupRank B = abelianGroupRank A + abelianGroupRank C := by
  unfold abelianGroupRank
  let f' := LinearMap.baseChange ℚ f
  let g' := LinearMap.baseChange ℚ g
  have hf'_inj : Function.Injective f' :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hg'_surj : Function.Surjective g' :=
    LinearMap.lTensor_surjective _ hg
  have hexact_fg : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have : y ∈ LinearMap.ker g := LinearMap.mem_ker.mpr hy
      rw [← hfg] at this
      exact LinearMap.mem_range.mp this
    · intro ⟨x, hx⟩
      have : y ∈ LinearMap.range f := ⟨x, hx⟩
      rw [hfg] at this
      exact LinearMap.mem_ker.mp this
  have hexact' : Function.Exact (LinearMap.lTensor ℚ f) (LinearMap.lTensor ℚ g) :=
    Module.Flat.lTensor_exact ℚ hexact_fg
  have hfg' : f'.range = g'.ker := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      rw [LinearMap.mem_ker]
      have := (hexact' (f' a)).mpr ⟨a, rfl⟩
      rw [ha] at this
      exact this
    · intro hx
      rw [LinearMap.mem_ker] at hx
      exact (hexact' x).mp hx
  have h1 : Module.finrank ℚ (TensorProduct ℤ ℚ B) =
      Module.finrank ℚ (LinearMap.ker g') + Module.finrank ℚ (LinearMap.range g') := by
    have := LinearMap.finrank_range_add_finrank_ker g'
    omega
  have h2 : Module.finrank ℚ (LinearMap.range g') = Module.finrank ℚ (TensorProduct ℤ ℚ C) := by
    have htop : LinearMap.range g' = ⊤ := LinearMap.range_eq_top.mpr hg'_surj
    rw [htop, finrank_top]
  have h3 : Module.finrank ℚ (LinearMap.ker g') = Module.finrank ℚ (TensorProduct ℤ ℚ A) := by
    rw [← hfg']
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective f' hf'_inj)).symm
  linarith

/-- The rank of an abelian group is an isomorphism invariant: if $A \cong B$
as abelian groups, then $\operatorname{rank} A = \operatorname{rank} B$. -/
lemma abelianGroupRank_eq_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) : abelianGroupRank A = abelianGroupRank B := by
  unfold abelianGroupRank
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ℚ ℚ) e.toIntLinearEquiv).finrank_eq

/-- The number $a_n$ of $n$-cells in a CW-structure on $X$, i.e. the cardinality
of the indexing set of $n$-dimensional cells. -/
noncomputable def numCells (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : ℕ :=
  Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n)

/-- The **Euler characteristic** of a CW-complex $X$ of dimension $< N$,
defined as the alternating sum
$$\chi(X) = \sum_{k=0}^{N-1} (-1)^k a_k$$
where $a_k$ is the number of $k$-cells. -/
noncomputable def eulerCharacteristic (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * (numCells X k : ℤ)

/-- The $n$th Betti number of $X$: the $\mathbb{Z}$-rank of the singular
homology group $H_n(X; \mathbb{Z})$. -/
noncomputable def singularHomologyRank (X : Type) [TopologicalSpace X] (n : ℕ) : ℕ :=
  abelianGroupRank
    (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

/-- Homotopy-invariance of Betti numbers: a homotopy equivalence
$X \simeq Y$ induces $\operatorname{rank} H_k(X) = \operatorname{rank} H_k(Y)$
for every $k$. -/
lemma singularHomologyRank_eq_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (k : ℕ) :
    singularHomologyRank X k = singularHomologyRank Y k :=
  abelianGroupRank_eq_of_addEquiv
    (ContractibleHomology.singularHomologyIsoOfHomotopyEquiv e k).addCommGroupIsoToAddEquiv

/-- Telescoping identity for alternating sums: for any sequence $b$,
$$\sum_{k=0}^{N-1} (-1)^k b_k + \sum_{k=0}^{N-1} (-1)^k b_{k+1} = b_0 - (-1)^N b_N.$$
Used in the proof that $\chi(X)$ equals the alternating sum of Betti numbers. -/
lemma telescoping_general (N : ℕ) (b : ℕ → ℤ) :
    ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * b k +
    ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * b (k + 1) = b 0 - (-1 : ℤ) ^ N * b N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : (-1 : ℤ) ^ (n + 1) = -(-1 : ℤ) ^ n := by ring
    rw [h1]
    linarith [ih]

/-- Algebraic backbone of Theorem 18.3: if a chain sequence $c_k$ decomposes
as $c_k = h_k + b_k + b_{k+1}$ with $b_0 = b_N = 0$, then the alternating sums
$\sum (-1)^k c_k$ and $\sum (-1)^k h_k$ agree. Applied with $c_k$ = number of
$k$-cells, $h_k$ = $k$th Betti number, $b_k$ = rank of $k$-boundaries. -/
theorem alternating_sum_chain_eq_homology (N : ℕ)
    (c h b : ℕ → ℤ)
    (hb0 : b 0 = 0) (hbN : b N = 0)
    (hdecomp : ∀ k, k < N → c k = h k + b k + b (k + 1)) :
    ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * c k =
    ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * h k := by
  have hrewrite : ∀ k ∈ Finset.range N, (-1 : ℤ) ^ k * c k =
      (-1 : ℤ) ^ k * h k + (-1 : ℤ) ^ k * b k + (-1 : ℤ) ^ k * b (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hdecomp k hk]
    ring
  rw [Finset.sum_congr rfl hrewrite]
  simp only [Finset.sum_add_distrib]
  have htelescope := telescoping_general N b
  rw [hb0, hbN] at htelescope
  simp only [mul_zero, sub_zero] at htelescope
  linarith


/-- The rank of the free abelian group on a finite set $S$ equals $|S|$. -/
theorem abelianGroupRank_freeAbelianGroup
    (S : Type*) [Finite S] :
    abelianGroupRank (FreeAbelianGroup S) = Nat.card S := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  rw [show abelianGroupRank (FreeAbelianGroup S) =
      abelianGroupRank (S →₀ ℤ) from
    abelianGroupRank_eq_of_addEquiv (FreeAbelianGroup.equivFinsupp S)]
  unfold abelianGroupRank
  have : Module.finrank ℚ (TensorProduct ℤ ℚ (S →₀ ℤ)) =
      Module.finrank ℚ (S →₀ ℚ) :=
    (TensorProduct.finsuppScalarRight ℤ ℚ ℚ S).finrank_eq
  rw [this, Module.finrank_finsupp_self]
  exact (Nat.card_eq_fintype_card).symm


/-- The differential $d_{k+1} : C_{k+1} \to C_k$ of a chain complex of abelian
groups, packaged as a $\mathbb{Z}$-linear map. -/
noncomputable def chainDifferentialLinearMap
    (C : ChainComplex AddCommGrpCat ℕ) (k : ℕ) : (C.X (k + 1)) →ₗ[ℤ] (C.X k) :=
  AddMonoidHom.toIntLinearMap (C.d (k + 1) k).hom

/-- Rank-nullity for $\mathbb{Z}$-linear maps between finitely generated abelian
groups: $\operatorname{rank} A = \operatorname{rank}(\ker f) +
\operatorname{rank}(\operatorname{im} f)$. -/
lemma abelianGroupRank_ker_add_range
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] [Module.Finite ℤ B]
    (f : A →ₗ[ℤ] B) :
    abelianGroupRank A = abelianGroupRank (LinearMap.ker f) +
      abelianGroupRank (LinearMap.range f) :=
  abelianGroupRank_additive
    (LinearMap.ker f).subtype
    f.rangeRestrict
    (Subtype.val_injective)
    (LinearMap.surjective_rangeRestrict f)
    (by rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict])


/-- Rank decomposition of cycles at degree $k+1$: for a chain complex with
finitely generated pieces,
$$\operatorname{rank} Z_k = \operatorname{rank} B_{k+1} +
  \operatorname{rank} H_{k+1}$$
i.e. the cycles in degree $k$ split via the short exact sequence
$0 \to B_{k+1} \to Z_k \to H_{k+1} \to 0$. -/
theorem chain_complex_kernel_image_homology_rank
    (C : ChainComplex AddCommGrpCat ℕ)
    (hC_fin : ∀ k, Module.Finite ℤ (C.X k))
    (k : ℕ) :
    abelianGroupRank (LinearMap.ker (chainDifferentialLinearMap C k)) =
      abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C (k + 1))) +
        abelianGroupRank (C.homology (k + 1)) := by

  let S := C.sc' (k + 2) (k + 1) k


  have hprev : (ComplexShape.down ℕ).prev (k + 1) = k + 2 := ChainComplex.prev ℕ (k + 1)
  have hnext : (ComplexShape.down ℕ).next (k + 1) = k := ChainComplex.next_nat_succ k
  let compIso := (CategoryTheory.ShortComplex.homologyMapIso
    (C.isoSc' (k + 2) (k + 1) k hprev hnext)) ≪≫ S.abHomologyIso


  have hHomRank : abelianGroupRank (C.homology (k + 1)) =
      abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) :=
    abelianGroupRank_eq_of_addEquiv compIso.addCommGroupIsoToAddEquiv


  haveI hfin1 : Module.Finite ℤ (C.X (k + 1)) := hC_fin (k + 1)
  haveI : Module.Finite ℤ (AddMonoidHom.ker S.g.hom) := by
    have : Module.Finite ℤ (LinearMap.ker (chainDifferentialLinearMap C k)) := inferInstance
    convert this using 1
  haveI hfin2 : Module.Finite ℤ (C.X (k + 2)) := hC_fin (k + 2)
  haveI : Module.Finite ℤ (↑S.X₁) := hfin2
  let tcLM := S.abToCycles.toIntLinearMap
  haveI : Module.Finite ℤ (LinearMap.range tcLM) := inferInstance
  haveI : Module.Finite ℤ (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    Module.Finite.quotient ℤ _
  have hKerSES : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
      abelianGroupRank (LinearMap.range tcLM) +
        abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    abelianGroupRank_additive (LinearMap.range tcLM).subtype (LinearMap.range tcLM).mkQ
      Subtype.val_injective (Submodule.Quotient.mk_surjective _)
      (by rw [Submodule.range_subtype]; exact (Submodule.ker_mkQ _).symm)
  have hQuotEq : abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) =
      abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) := by
    congr 1
  have hKerEq : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
      abelianGroupRank (LinearMap.ker (chainDifferentialLinearMap C k)) := by
    congr 1
  have hRangeEq : abelianGroupRank (LinearMap.range tcLM) =
      abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C (k + 1))) := by
    apply abelianGroupRank_eq_of_addEquiv
    have hval : ∀ y : C.X (k + 2),
        (S.abToCycles y : AddMonoidHom.ker S.g.hom).1 =
        chainDifferentialLinearMap C (k + 1) y := by
      intro y; rfl
    refine {
      toFun := fun ⟨a, ha⟩ => ⟨a.1, by
        rw [LinearMap.mem_range] at ha ⊢; obtain ⟨y, hy⟩ := ha
        exact ⟨y, by rw [← hval]; exact congr_arg Subtype.val hy⟩⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, by
        rw [LinearMap.mem_range] at hx; obtain ⟨y, hy⟩ := hx
        rw [← hy, ← hval]; exact (S.abToCycles y).2⟩, by
        rw [LinearMap.mem_range] at hx ⊢; obtain ⟨y, hy⟩ := hx
        exact ⟨y, Subtype.ext (by show (S.abToCycles y).1 = x; rw [hval, hy])⟩⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl
      map_add' := fun _ _ => rfl
    }
  linarith [hKerEq, hKerSES, hQuotEq, hHomRank, hRangeEq]


/-- Rank decomposition at degree $0$: since there is no differential into
$C_0$, all of $C_0$ consists of $0$-cycles, giving
$\operatorname{rank} C_0 = \operatorname{rank} B_0 + \operatorname{rank} H_0$. -/
theorem chain_complex_rank_decomposition_zero
    (C : ChainComplex AddCommGrpCat ℕ)
    (hC_fin : ∀ k, Module.Finite ℤ (C.X k)) :
    abelianGroupRank (C.X 0) =
      abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C 0)) +
        abelianGroupRank (C.homology 0) := by

  let S := C.sc' 1 0 0

  have hg_zero : S.g = 0 := C.shape 0 0 (by decide)

  have hker_top : AddMonoidHom.ker S.g.hom = ⊤ := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_top, iff_true]
    show S.g.hom x = 0
    rw [hg_zero]
    simp

  have hprev : (ComplexShape.down ℕ).prev 0 = 1 := ChainComplex.prev ℕ 0
  have hnext : (ComplexShape.down ℕ).next 0 = 0 := ChainComplex.next_nat_zero
  let compIso := (CategoryTheory.ShortComplex.homologyMapIso
    (C.isoSc' 1 0 0 hprev hnext)) ≪≫ S.abHomologyIso
  have hHomRank : abelianGroupRank (C.homology 0) =
      abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) :=
    abelianGroupRank_eq_of_addEquiv compIso.addCommGroupIsoToAddEquiv


  let kerEquiv : AddMonoidHom.ker S.g.hom ≃+ (C.X 0) := {
    toFun := fun ⟨x, _⟩ => x
    invFun := fun x => ⟨x, by rw [hker_top]; trivial⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
  }

  haveI hfin0 : Module.Finite ℤ (C.X 0) := hC_fin 0
  haveI hfin1 : Module.Finite ℤ (C.X 1) := hC_fin 1
  haveI : Module.Finite ℤ (AddMonoidHom.ker S.g.hom) :=
    Module.Finite.equiv kerEquiv.symm.toIntLinearEquiv
  haveI : Module.Finite ℤ (↑S.X₁) := hfin1
  let tcLM := S.abToCycles.toIntLinearMap
  haveI : Module.Finite ℤ (LinearMap.range tcLM) := inferInstance
  haveI : Module.Finite ℤ (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    Module.Finite.quotient ℤ _

  have hKerSES : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
      abelianGroupRank (LinearMap.range tcLM) +
        abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    abelianGroupRank_additive (LinearMap.range tcLM).subtype (LinearMap.range tcLM).mkQ
      Subtype.val_injective (Submodule.Quotient.mk_surjective _)
      (by rw [Submodule.range_subtype]; exact (Submodule.ker_mkQ _).symm)

  have hQuotEq : abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) =
      abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) := by
    congr 1

  have hKerEq : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
      abelianGroupRank (C.X 0) :=
    abelianGroupRank_eq_of_addEquiv kerEquiv

  have hRangeEq : abelianGroupRank (LinearMap.range tcLM) =
      abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C 0)) := by
    apply abelianGroupRank_eq_of_addEquiv
    have hval : ∀ y : C.X 1,
        (S.abToCycles y : AddMonoidHom.ker S.g.hom).1 =
        chainDifferentialLinearMap C 0 y := by
      intro y; rfl
    refine {
      toFun := fun ⟨a, ha⟩ => ⟨a.1, by
        rw [LinearMap.mem_range] at ha ⊢; obtain ⟨y, hy⟩ := ha
        exact ⟨y, by rw [← hval]; exact congr_arg Subtype.val hy⟩⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, by
        rw [LinearMap.mem_range] at hx; obtain ⟨y, hy⟩ := hx
        rw [← hy, ← hval]; exact (S.abToCycles y).2⟩, by
        rw [LinearMap.mem_range] at hx ⊢; obtain ⟨y, hy⟩ := hx
        exact ⟨y, Subtype.ext (by show (S.abToCycles y).1 = x; rw [hval, hy])⟩⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl
      map_add' := fun _ _ => rfl
    }
  linarith [hKerEq, hKerSES, hQuotEq, hHomRank, hRangeEq]

/-- The trivial submodule $\{0\}$ has rank $0$. -/
lemma abelianGroupRank_bot {A : Type*} [AddCommGroup A] :
    abelianGroupRank (⊥ : Submodule ℤ A) = 0 := by
  have heq : abelianGroupRank (⊥ : Submodule ℤ A) =
      abelianGroupRank (Fin 0 → ℤ) := by
    apply abelianGroupRank_eq_of_addEquiv
    exact {
      toFun := fun _ => Fin.elim0
      invFun := fun _ => 0
      left_inv := fun ⟨x, hx⟩ => by
        simp only [Submodule.mem_bot] at hx; subst hx; rfl
      right_inv := fun f => funext (fun i => Fin.elim0 i)
      map_add' := fun _ _ => by ext i; exact Fin.elim0 i
    }
  rw [heq]
  simp [abelianGroupRank]

open CategoryTheory.Limits in
/-- Combined rank decomposition of a bounded chain complex of finitely
generated abelian groups: there exist sequences $z_k = \operatorname{rank}
Z_k$ and $b_k = \operatorname{rank} B_k$ satisfying
$\operatorname{rank} C_k = z_k + b_{k-1}$ and $z_k = b_k +
\operatorname{rank} H_k$, with $b_k = 0$ above the dimension bound. This
provides the structural identity used to prove $\chi(X) = \sum (-1)^k
\operatorname{rank} H_k(X)$. -/
theorem chain_complex_rank_decomposition
    (C : ChainComplex AddCommGrpCat ℕ)
    (N : ℕ)
    (hC_fin : ∀ k, Module.Finite ℤ (C.X k))
    (hC_zero : ∀ m, N ≤ m → IsZero (C.X m)) :
    ∃ (rankZ rankB : ℕ → ℕ),
      (abelianGroupRank (C.X 0) = rankZ 0) ∧
      (∀ k, 0 < k → k < N → abelianGroupRank (C.X k) = rankZ k + rankB (k - 1)) ∧
      (∀ k, k < N → rankZ k = rankB k + abelianGroupRank (C.homology k)) ∧
      (∀ k, N ≤ k + 1 → rankB k = 0) := by

  let dk (m : ℕ) : (C.X (m + 1)) →ₗ[ℤ] (C.X m) := chainDifferentialLinearMap C m

  let rB : ℕ → ℕ := fun k => abelianGroupRank (LinearMap.range (dk k))


  let rZ : ℕ → ℕ := fun k =>
    match k with
    | 0 => abelianGroupRank (C.X 0)
    | m + 1 => abelianGroupRank (LinearMap.ker (dk m))
  refine ⟨rZ, rB, rfl, ?_, ?_, ?_⟩
  ·
    intro k hk0 hkN
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [rZ, rB]
    exact abelianGroupRank_ker_add_range (dk m)
  ·
    intro k hkN
    match k with
    | 0 =>
      simp only [rZ, rB]
      exact chain_complex_rank_decomposition_zero C hC_fin
    | m + 1 =>


      simp only [rZ, rB]
      exact chain_complex_kernel_image_homology_rank C hC_fin m
  ·
    intro k hk
    show abelianGroupRank (LinearMap.range (dk k)) = 0

    have hzero := hC_zero (k + 1) hk

    have hmorphzero : C.d (k + 1) k = 0 := hzero.eq_of_src _ _

    have hdkzero : dk k = 0 := by
      ext x
      change AddMonoidHom.toIntLinearMap (C.d (k + 1) k).hom x = 0
      rw [hmorphzero]
      simp
    rw [hdkzero, LinearMap.range_zero]
    exact abelianGroupRank_bot



/-- The rank of the cellular $k$-chain group equals the number $a_k$ of
$k$-cells, since $C_k(X) = \mathbb{Z}[A_k]$ is free abelian on the indexing set
of $k$-cells. -/
lemma abelianGroupRank_cellularChains
    (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (hfin : ∀ n, Finite (Topology.CWComplex.cell (Set.univ : Set X) n))
    (k : ℕ) :
    abelianGroupRank (CWComplex.cellularChains X k) = numCells X k := by
  unfold CWComplex.cellularChains numCells
  exact abelianGroupRank_freeAbelianGroup _







end EulerCharacteristic

namespace CWComplex

/-- The number of torsion coefficients of an abelian group $A$: the minimum
number of generators needed for its torsion subgroup. For a finitely generated
abelian group $A \cong \mathbb{Z}^r \oplus \bigoplus_i \mathbb{Z}/d_i$ this is
the number of cyclic torsion summands. -/
noncomputable def numTorsionCoeffs (A : Type*) [AddCommGroup A] : ℕ :=
  sInf {n : ℕ | ∃ (S : Finset (AddCommGroup.torsion A)),
    S.card = n ∧ AddSubgroup.closure (Subtype.val '' (S : Set (AddCommGroup.torsion A))) =
      AddCommGroup.torsion A}

/-- The minimal number of $k$-cells predicted by Wall's theorem:
$r(k) + t(k) + t(k - 1)$, where $r(k) = \operatorname{rank} H_k(X)$ is the
$k$th Betti number and $t(k)$ is the number of torsion coefficients of
$H_k(X)$. (For $k = 0$ the term $t(k - 1)$ is omitted.) -/
noncomputable def minimalCellCount (X : Type) [TopologicalSpace X] (k : ℕ) : ℕ :=
  let Hk : AddCommGrpCat :=
    ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)
  EulerCharacteristic.abelianGroupRank Hk +
  numTorsionCoeffs Hk +
  (if k = 0 then 0
   else
    let Hk₁ : AddCommGrpCat :=
      ((singularHomologyFunctor AddCommGrpCat (k - 1)).obj
        (AddCommGrpCat.of ℤ)).obj (TopCat.of X)
    numTorsionCoeffs Hk₁)



/-- A **Moore space** $M(A, k)$ is a path-connected CW-complex whose only
nontrivial reduced homology group is $H_k(M) \cong A$. -/
structure IsMooreSpace (M : Type) (tM : TopologicalSpace M)
    (cwM : @Topology.CWComplex M tM Set.univ) (A : AddCommGrpCat) (k : ℕ) : Prop where
  pathConnected : @PathConnectedSpace M tM
  homology_iso : Nonempty (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj (@TopCat.of M tM) ≅ A)
  homology_vanish : ∀ q, 0 < q → q ≠ k →
    @Limits.IsZero AddCommGrpCat _ (((singularHomologyFunctor AddCommGrpCat q).obj
      (AddCommGrpCat.of ℤ)).obj (@TopCat.of M tM))








end CWComplex
