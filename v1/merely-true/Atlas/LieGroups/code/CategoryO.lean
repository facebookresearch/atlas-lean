/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules
import Atlas.LieGroups.code.HarishChandraIsomorphism
import Atlas.LieGroups.code.HilbertNoether
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def HasWeightDecomposition (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] : Prop :=
  ∀ m : M, ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)) (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ),
    m = ∑ μ ∈ S, (v μ : M)

structure IsCategoryO (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  finitely_generated : ∃ (S : Finset M), LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤
  weight_decomp : HasWeightDecomposition Δ M
  weight_bound : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
    ∀ μ ∈ weights Δ M, ∃ wt ∈ bds, rd.IsInQPlus (wt - μ)

theorem PositiveRootData.IsInQPlus_zero
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) :
    rd.IsInQPlus 0 :=
  ⟨fun _ => 0, by simp⟩

theorem PositiveRootData.IsInQPlus_trans
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wt0 μ ν : Δ.𝔥 →ₗ[R] R)
    (h1 : rd.IsInQPlus (wt0 - μ))
    (h2 : rd.IsInQPlus (μ - ν)) :
    rd.IsInQPlus (wt0 - ν) := by
  have heq : wt0 - ν = (wt0 - μ) + (μ - ν) := by abel
  rw [heq]
  obtain ⟨c₁, hc₁⟩ := h1
  obtain ⟨c₂, hc₂⟩ := h2
  refine ⟨fun α => c₁ α + c₂ α, ?_⟩
  simp only [hc₁, hc₂, ← Finset.sum_add_distrib, add_nsmul]

def WeightLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  rd.IsInQPlus (wt - μ)

def ReflectionLT {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (α : Δ.𝔥 →ₗ[R] R) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  α ∈ rd.posRoots ∧ ∃ (n : ℕ), 0 < n ∧ rd.corootPairing wt α = (n : R) ∧ μ = wt - n • α

def BruhatLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ α, ReflectionLT rd α a b) μ wt

section CategoryOResults

variable {Δ : TriangularDecomposition R 𝔤}
variable {rd : PositiveRootData Δ}
variable {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]




theorem hilbert_noether_commRing
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {G : Type*} [Group G] [Fintype G]
    (algAct : G →* (A ≃ₐ[R] A))
    (hA_fg : Subalgebra.FG (⊤ : Subalgebra R A)) :
    (Subalgebra.invariants G algAct).FG := by

  letI : MulSemiringAction G A := MulSemiringAction.compHom A algAct
  letI : SMulCommClass G R A := ⟨fun g r a => by
    show (algAct g) (r • a) = r • (algAct g) a
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, Algebra.smul_def]⟩

  haveI : Algebra.FiniteType R A := ⟨hA_fg⟩

  have hfg := hilbert_noether_fg (R := R) (A := A) (G := G)

  have hfg_sub : (FixedPoints.subalgebra R A G).FG :=
    (Subalgebra.fg_iff_finiteType _).mpr hfg

  have heq : FixedPoints.subalgebra R A G = Subalgebra.invariants G algAct := by
    ext a
    simp only [FixedPoints.subalgebra, Subalgebra.invariants, Subalgebra.mem_mk,
      Subsemiring.mem_mk, Submonoid.mem_mk]
    constructor
    · intro ha g; exact ha g
    · intro ha g; exact ha g
  rw [← heq]
  exact hfg_sub

theorem symmetric_algebra_fg_top (R : Type*) [CommRing R]
    (L : Type*) [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    [Module.Free R L] [Module.Finite R L] :
    Subalgebra.FG (⊤ : Subalgebra R (SymmetricAlgebra R L)) := by
  by_cases hR : Nontrivial R
  · have hb := Module.Free.chooseBasis R L
    haveI : Finite (Module.Free.ChooseBasisIndex R L) := Module.Finite.finite_basis hb
    haveI : Algebra.FiniteType R (MvPolynomial (Module.Free.ChooseBasisIndex R L) R) :=
      Algebra.FiniteType.instMvPolynomialOfFinite
    haveI : Algebra.FiniteType R (SymmetricAlgebra R L) :=
      Algebra.FiniteType.equiv ‹Algebra.FiniteType R (MvPolynomial _ R)›
        (SymmetricAlgebra.equivMvPolynomial hb).symm
    exact Algebra.FiniteType.out
  · rw [not_nontrivial_iff_subsingleton] at hR
    haveI := hR
    refine ⟨∅, ?_⟩
    have : Subsingleton (SymmetricAlgebra R L) := by
      have h01 : (0 : R) = 1 := Subsingleton.elim _ _
      constructor; intro a b
      have : ∀ (x : SymmetricAlgebra R L), x = 0 := by
        intro x
        calc x = (1 : R) • x := by simp
          _ = (0 : R) • x := by rw [h01]
          _ = 0 := by simp
      rw [this a, this b]
    ext x
    simp [Subsingleton.elim x (algebraMap R _ 0)]








def GeneralizedEigenspaceCenter
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    Submodule R M where
  carrier := {m : M | ∀ (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
    ∃ (n : ℕ), ((ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
      chi z • (LinearMap.id : Module.End R M)) ^ n : Module.End R M) m = 0}
  add_mem' := by

    intro a b ha hb z
    obtain ⟨na, hna⟩ := ha z
    obtain ⟨nb, hnb⟩ := hb z
    set T : Module.End R M := ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
      chi z • (LinearMap.id : Module.End R M) with hT_def
    use na + nb

    have hlin := (T ^ (na + nb)).map_add a b
    rw [hlin]

    have ha0 : (T ^ (na + nb)) a = 0 := by
      have h1 : T ^ (na + nb) = T ^ nb * T ^ na := by
        rw [show na + nb = nb + na from Nat.add_comm na nb]; exact pow_add T nb na
      change (T ^ (na + nb)) a = 0
      rw [h1]; show (T ^ nb) ((T ^ na) a) = 0; rw [hna]; exact map_zero _

    have hb0 : (T ^ (na + nb)) b = 0 := by
      have h1 : T ^ (na + nb) = T ^ na * T ^ nb := pow_add T na nb
      change (T ^ (na + nb)) b = 0
      rw [h1]; show (T ^ na) ((T ^ nb) b) = 0; rw [hnb]; exact map_zero _

    rw [ha0, hb0, add_zero]

  zero_mem' := by
    intro z; exact ⟨0, by simp [pow_zero]⟩

  smul_mem' := by
    intro r m hm z
    obtain ⟨n, hn⟩ := hm z
    exact ⟨n, by simp [map_smul, hn]⟩

def IsInCategoryOChi
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) : Prop :=
  IsCategoryO Δ rd M ∧
  GeneralizedEigenspaceCenter M ueaAct chi = ⊤

def GeneralizedEigenspaceCenter.toLieSubmodule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    LieSubmodule R 𝔤 M :=
  { GeneralizedEigenspaceCenter M ueaAct chi with
    lie_mem := by
      intro x m hm z


      obtain ⟨n, hn⟩ := hm z
      use n

      have hcomm_uea : (z : UniversalEnvelopingAlgebra R 𝔤) *
        UniversalEnvelopingAlgebra.ι R x =
        UniversalEnvelopingAlgebra.ι R x * (z : UniversalEnvelopingAlgebra R 𝔤) := by
        have hz := z.property
        rw [Subalgebra.mem_center_iff] at hz
        exact (hz _).symm

      have hcomm_end : ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) *
        ueaAct (UniversalEnvelopingAlgebra.ι R x) =
        ueaAct (UniversalEnvelopingAlgebra.ι R x) *
        ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) := by
        rw [← map_mul, ← map_mul, hcomm_uea]

      set T : Module.End R M := ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) -
        chi z • (LinearMap.id : Module.End R M) with hT_def
      set X : Module.End R M := ueaAct (UniversalEnvelopingAlgebra.ι R x)

      have hTX : T * X = X * T := by
        simp only [hT_def, sub_mul, mul_sub, hcomm_end]
        congr 1
        ext m₀
        simp [LinearMap.smul_apply, LinearMap.id_apply]

      have hTnX : T ^ n * X = X * T ^ n := Commute.pow_left hTX n

      have hxm : ⁅x, m⁆ = X m := (hcompat x m).symm
      rw [hxm]
      show (T ^ n) (X m) = 0
      have : (T ^ n) (X m) = (T ^ n * X) m := rfl
      rw [this, hTnX]
      show X ((T ^ n) m) = 0
      rw [hn, map_zero] }

lemma GeneralizedEigenspaceCenter.toLieSubmodule_coe
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    (GeneralizedEigenspaceCenter.toLieSubmodule M ueaAct hcompat chi : Submodule R M) =
    GeneralizedEigenspaceCenter M ueaAct chi := rfl

lemma commute_pow_sub_smul_id {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g : Module.End R M) (hcomm : g * f = f * g)
    (c : R) (k : ℕ) (x : M) :
    ((f - c • (LinearMap.id : Module.End R M)) ^ k) (g x) =
    g (((f - c • (LinearMap.id : Module.End R M)) ^ k) x) := by
  have h1 : Commute g (f - c • (LinearMap.id : Module.End R M)) := by
    rw [Commute, SemiconjBy, mul_sub, sub_mul, hcomm]
    congr 1; ext y; simp
  exact congr_fun (congr_arg DFunLike.coe (h1.pow_right k).symm) x





noncomputable def idealStepFilt
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) (N : Submodule R M) : Submodule R M :=
  ⨆ z : ι, Submodule.map (T z) N

noncomputable def idealChainFilt
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) : ℕ → Submodule R M
  | 0 => ⊤
  | n + 1 => idealStepFilt T (idealChainFilt T n)


lemma idealChainFilt_antitone
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) :
    ∀ n : ℕ, idealChainFilt T (n + 1) ≤ idealChainFilt T n := by
  intro n; induction n with
  | zero => exact le_top
  | succ n ih => exact iSup_mono (fun z => Submodule.map_mono ih)

lemma mem_idealChainFilt_succ
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} (T : ι → Module.End R M) (n : ℕ) (z : ι) (m : M)
    (hm : m ∈ idealChainFilt T n) : T z m ∈ idealChainFilt T (n + 1) :=
  Submodule.mem_iSup_of_mem z (Submodule.mem_map.mpr ⟨m, hm, rfl⟩)

lemma idealChainFilt_lie_stable
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {ι : Type*}
    (T : ι → Module.End R M)
    (hcomm : ∀ (x : 𝔤) (z : ι) (m : M), ⁅x, T z m⁆ = T z ⁅x, m⁆)
    (n : ℕ) : ∀ (x : 𝔤) (m : M),
    m ∈ idealChainFilt T n → ⁅x, m⁆ ∈ idealChainFilt T n := by
  induction n with
  | zero => intros; trivial
  | succ k ih =>
    intro xl m hm
    change m ∈ idealStepFilt T (idealChainFilt T k) at hm
    change ⁅xl, m⁆ ∈ idealStepFilt T (idealChainFilt T k)
    simp only [idealStepFilt] at hm ⊢
    apply Submodule.iSup_induction
      (motive := fun y => ⁅xl, y⁆ ∈ ⨆ z, Submodule.map (T z) (idealChainFilt T k))
      (fun z => Submodule.map (T z) (idealChainFilt T k)) hm
    · intro z y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨m₀, hm₀, rfl⟩ := hy
      rw [hcomm]
      apply Submodule.mem_iSup_of_mem z
      exact Submodule.mem_map.mpr ⟨⁅xl, m₀⁆, ih xl m₀ hm₀, rfl⟩
    · simp [lie_zero]
    · intro y₁ y₂ hy₁ hy₂
      rw [lie_add]
      exact Submodule.add_mem _ hy₁ hy₂


theorem CategoryO.detecting_submodule_gives_chain_bound
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (E : Submodule R M)
    (hdetect : ∀ (N₁ N₂ : LieSubmodule R 𝔤 M), N₁ < N₂ →
      ∃ x, x ∈ (N₂ : Submodule R M) ⊓ E ∧ x ∉ (N₁ : Submodule R M))
    (n : ℕ)
    (hE_bound : ∀ (chain : Fin (n + 2) → Submodule R M),
      (∀ i, chain i ≤ E) → StrictMono chain → False) :
    ∀ (chain : Fin (n + 2) → LieSubmodule R 𝔤 M), StrictMono chain → False := by
  intro chain hchain

  let chain' : Fin (n + 2) → Submodule R M := fun i => (chain i : Submodule R M) ⊓ E

  have hchain' : StrictMono chain' := by
    intro i j hij
    have hlt := hchain hij
    obtain ⟨x, hx_mem, hx_not⟩ := hdetect (chain i) (chain j) hlt
    apply lt_of_le_of_ne
    · intro y hy
      exact ⟨(hchain.monotone hij.le) hy.1, hy.2⟩
    · intro heq
      have hxi : x ∈ chain' i := by rw [heq]; exact hx_mem
      exact hx_not (Submodule.mem_inf.mp hxi).1

  have hle : ∀ i, chain' i ≤ E := fun i => inf_le_right

  exact hE_bound chain' hle hchain'

theorem section4_weightSpace_iSupIndep
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    iSupIndep fun μ : Δ.𝔥 →ₗ[R] R => (WeightSpace Δ M μ : Submodule R M) := by
  haveI : IsLieAbelian Δ.𝔥 := Δ.h_abelian
  simp_rw [fun μ => weightSpace_eq_mathlib_weightSpace (Δ := Δ) (M := M) μ]
  exact ((LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace R Δ.𝔥 M)).comp
    DFunLike.coe_injective).mono
    fun χ => LieModule.weightSpace_le_genWeightSpace M (χ ·)

theorem weightSpace_iSupIndep
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    iSupIndep fun μ : Δ.𝔥 →ₗ[R] R => (WeightSpace Δ M μ : Submodule R M) :=
  section4_weightSpace_iSupIndep

theorem weightSpace_sum_eq_zero_components
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ)
    (hsum : ∑ μ ∈ S, (v μ : M) = 0)
    (μ : Δ.𝔥 →ₗ[R] R) (hμ : μ ∈ S) :
    (v μ : M) = 0 := by
  have hindep := @weightSpace_iSupIndep R _ 𝔤 _ _ Δ M _ _ _ _
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero] at hindep
  exact hindep S (fun σ => (v σ : M)) (fun σ _ => (v σ).property) hsum μ hμ

theorem lieSubmodule_weight_decomp
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hwd : HasWeightDecomposition Δ M)
    (N : LieSubmodule R 𝔤 M)
    (m : M) (hm : m ∈ N) :
    ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)) (w : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ),
      m = ∑ μ ∈ T, (w μ : M) ∧ ∀ μ ∈ T, (w μ : M) ∈ N := by

  obtain ⟨S, v, hdecomp⟩ := hwd m


  refine ⟨S, v, hdecomp, fun ν hν => ?_⟩


  have mk_weight : ∀ σ : Δ.𝔥 →ₗ[R] R,
      (LieSubmodule.Quotient.mk' N (v σ : M)) ∈ WeightSpace Δ (M ⧸ N) σ := by
    intro σ h


    rw [show ⁅(h : 𝔤), LieSubmodule.Quotient.mk' N (v σ : M)⁆ =
        LieSubmodule.Quotient.mk' N ⁅(h : 𝔤), (v σ : M)⁆ from rfl]

    rw [(v σ).property h]


    exact map_smul (LieSubmodule.Quotient.mk' N).toLinearMap (σ h) (v σ : M)

  let qv : (σ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ (M ⧸ N) σ :=
    fun σ => ⟨LieSubmodule.Quotient.mk' N (v σ : M), mk_weight σ⟩

  have hsum : ∑ σ ∈ S, (qv σ : M ⧸ N) = 0 := by
    simp only [qv]

    rw [show ∑ σ ∈ S, (LieSubmodule.Quotient.mk' N (v σ : M) : M ⧸ N) =
        LieSubmodule.Quotient.mk' N (∑ σ ∈ S, (v σ : M)) from
      (map_sum (LieSubmodule.Quotient.mk' N).toLinearMap (fun σ => (v σ : M)) S).symm]
    rw [← hdecomp]
    exact (LieSubmodule.Quotient.mk_eq_zero (N := N)).mpr hm

  have hν_zero := weightSpace_sum_eq_zero_components S qv hsum ν hν

  simp only [qv] at hν_zero
  rwa [LieSubmodule.Quotient.mk_eq_zero (N := N)] at hν_zero

theorem weightDecomp_component_mem_lieSubmodule
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hwd : HasWeightDecomposition Δ M)
    (N : LieSubmodule R 𝔤 M)
    (m : M) (hm : m ∈ N)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ)
    (hdecomp : m = ∑ μ ∈ S, (v μ : M))
    (μ : Δ.𝔥 →ₗ[R] R) (hμ : μ ∈ S) :
    (v μ : M) ∈ N := by
  classical

  obtain ⟨T, w, hdecomp_w, hw_mem⟩ := lieSubmodule_weight_decomp hwd N m hm

  let d : (ν : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M ν := fun ν =>
    ⟨(if ν ∈ S then (v ν : M) else 0) - (if ν ∈ T then (w ν : M) else 0),
     (WeightSpace Δ M ν).sub_mem
       (by split_ifs with h; exact (v ν).property; exact (WeightSpace Δ M ν).zero_mem)
       (by split_ifs with h; exact (w ν).property; exact (WeightSpace Δ M ν).zero_mem)⟩

  have hdsum : ∑ ν ∈ S ∪ T, (d ν : M) = 0 := by
    simp only [d, sub_eq_add_neg]
    rw [Finset.sum_add_distrib]

    have hv_sum : ∑ ν ∈ S ∪ T, (if ν ∈ S then (v ν : M) else 0) = ∑ ν ∈ S, (v ν : M) := by
      rw [← Finset.sum_filter]
      congr 1; ext ν; simp [Finset.mem_filter, Finset.mem_union]; tauto

    have hw_sum : ∑ ν ∈ S ∪ T, (-(if ν ∈ T then (w ν : M) else 0)) = -(∑ ν ∈ T, (w ν : M)) := by
      conv_lhs => arg 2; ext ν; rw [apply_ite Neg.neg, neg_zero]

      rw [← Finset.sum_filter]
      have hfilt : Finset.filter (fun a => a ∈ T) (S ∪ T) = T := by
        ext ν; simp [Finset.mem_filter, Finset.mem_union]; tauto
      rw [hfilt, Finset.sum_neg_distrib]
    rw [hv_sum, hw_sum, ← hdecomp, ← hdecomp_w, add_neg_cancel]

  have hd_zero := weightSpace_sum_eq_zero_components (S ∪ T) d hdsum μ
    (Finset.mem_union_left T hμ)

  simp only [d] at hd_zero

  rw [if_pos hμ] at hd_zero
  rw [sub_eq_zero] at hd_zero
  rw [hd_zero]
  split_ifs with h
  · exact hw_mem μ h
  · exact N.zero_mem




theorem IsCategoryO_quotient
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (Z : LieSubmodule R 𝔤 X) :
    IsCategoryO Δ rd (X ⧸ Z) where
  finitely_generated := by
    classical
    obtain ⟨S, hS⟩ := hXO.finitely_generated
    refine ⟨S.image (LieSubmodule.Quotient.mk' Z), ?_⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z q
    have hx : x ∈ (LieSubmodule.lieSpan R 𝔤 (S : Set X) : LieSubmodule R 𝔤 X) := by
      rw [hS]; trivial
    suffices LieSubmodule.map (LieSubmodule.Quotient.mk' Z)
        (LieSubmodule.lieSpan R 𝔤 (S : Set X)) ≤
        LieSubmodule.lieSpan R 𝔤
          (↑(S.image (LieSubmodule.Quotient.mk' Z)) : Set (X ⧸ Z)) by
      exact this ⟨x, hx, rfl⟩
    rw [LieSubmodule.map_le_iff_le_comap, LieSubmodule.lieSpan_le]
    intro s hs
    apply LieSubmodule.mem_comap.mpr
    apply LieSubmodule.subset_lieSpan
    simp only [Finset.coe_image]
    exact Set.mem_image_of_mem _ hs
  weight_decomp := by
    intro m_bar
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z m_bar
    obtain ⟨S, v, hm⟩ := hXO.weight_decomp m
    refine ⟨S, fun μ => ⟨(LieSubmodule.Quotient.mk' Z) (v μ : X), fun h => ?_⟩, ?_⟩
    · rw [← LieModuleHom.map_lie]
      rw [(v μ).prop h]
      exact map_smul (LieSubmodule.Quotient.mk' Z).toLinearMap (μ h) (v μ : X)
    · conv_lhs => rw [hm]
      rw [map_sum]
  weight_bound := by
    obtain ⟨bds, hbds⟩ := hXO.weight_bound
    refine ⟨bds, fun μ hμ => hbds μ ?_⟩
    rw [weights, Set.mem_setOf_eq] at hμ ⊢
    intro hbot
    apply hμ; clear hμ
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z q
    obtain ⟨S, v, hm⟩ := hXO.weight_decomp m
    have mk_wt : ∀ ν, (LieSubmodule.Quotient.mk' Z (v ν : X)) ∈
        WeightSpace Δ (X ⧸ Z) ν := by
      intro ν h
      rw [← LieModuleHom.map_lie, (v ν).prop h]
      exact map_smul (LieSubmodule.Quotient.mk' Z).toLinearMap (ν h) (v ν : X)
    classical
    let S' := {μ} ∪ S
    let w : (ν : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ (X ⧸ Z) ν := fun ν =>
      ⟨(if ν ∈ S then (LieSubmodule.Quotient.mk' Z (v ν : X)) else 0) -
       (if ν = μ then LieSubmodule.Quotient.mk' Z m else 0),
       (WeightSpace Δ (X ⧸ Z) ν).sub_mem
         (by split_ifs with h
             · exact mk_wt ν
             · exact (WeightSpace Δ (X ⧸ Z) ν).zero_mem)
         (by split_ifs with h
             · exact h ▸ hq
             · exact (WeightSpace Δ (X ⧸ Z) ν).zero_mem)⟩
    have hsum : ∑ ν ∈ S', (w ν : X ⧸ Z) = 0 := by
      simp only [w, S']
      rw [Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have hlhs : (∑ x ∈ {μ} ∪ S, (if x ∈ S then
            (LieSubmodule.Quotient.mk' Z) ↑(v x) else 0)) =
          ∑ x ∈ S, (LieSubmodule.Quotient.mk' Z) ↑(v x) := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp [Finset.mem_filter]
        tauto
      have hrhs : (∑ x ∈ {μ} ∪ S, (if x = μ then
            (LieSubmodule.Quotient.mk' Z) m else 0)) =
          (LieSubmodule.Quotient.mk' Z) m := by
        rw [Finset.sum_ite_eq']
        simp
      rw [hlhs, hrhs]
      conv_rhs => rw [hm]
      rw [map_sum]
    have hwμ := weightSpace_sum_eq_zero_components S' w hsum μ
      (Finset.mem_union_left S (Finset.mem_singleton_self μ))
    simp only [w] at hwμ
    simp only [if_true] at hwμ
    rw [sub_eq_zero] at hwμ


    split_ifs at hwμ with h
    ·

      have hv_zero : (v μ : X) = 0 := by
        rw [eq_bot_iff] at hbot
        exact hbot (v μ).property
      rw [hv_zero, map_zero] at hwμ
      exact hwμ.symm
    ·
      exact hwμ.symm

lemma CategoryO.subquotient_has_weight_vector
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (N₁ N₂ : LieSubmodule R 𝔤 M) (hlt : N₁ < N₂) :
    ∃ γ, ∃ x, x ∈ (N₂ : Submodule R M) ⊓ WeightSpace Δ M γ ∧
      x ∉ (N₁ : Submodule R M) := by

  obtain ⟨x, hx_N2, hx_N1⟩ := SetLike.exists_of_lt hlt

  obtain ⟨S, v, hdecomp⟩ := hM.weight_decomp x


  by_contra h_all
  push Not at h_all

  apply hx_N1

  rw [hdecomp]
  apply (N₁ : Submodule R M).sum_mem
  intro μ hμS

  have hv_N2 : (v μ : M) ∈ N₂ :=
    weightDecomp_component_mem_lieSubmodule hM.weight_decomp N₂ x hx_N2 S v hdecomp μ hμS

  have hv_wt : (v μ : M) ∈ WeightSpace Δ M μ := (v μ).property

  exact h_all μ (v μ : M) ⟨hv_N2, hv_wt⟩





lemma strictMono_fin_le_val {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) :
    ∀ i : Fin n, i.val ≤ f i := by
  intro ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hj : j < n := by omega
    have h1 : f ⟨j, hj⟩ < f ⟨j + 1, hi⟩ := hf (Fin.mk_lt_mk.mpr (by omega))
    have h2 : j ≤ f ⟨j, hj⟩ := ih hj
    show j + 1 ≤ f ⟨j + 1, hi⟩; omega

theorem findim_submodule_chain_bound
    {K : Type*} [DivisionRing K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (E : Submodule K V) [FiniteDimensional K E] :
    ∀ (chain : Fin (Module.finrank K E + 2) → Submodule K V),
      (∀ i, chain i ≤ E) → StrictMono chain → False := by
  intro chain hle hmon
  have hfd : ∀ i, FiniteDimensional K ↥(chain i) :=
    fun i => Submodule.finiteDimensional_of_le (hle i)
  have hbound : ∀ i, Module.finrank K ↥(chain i) ≤ Module.finrank K E :=
    fun i => Submodule.finrank_mono (hle i)
  have hfm : StrictMono (fun i => Module.finrank K ↥(chain i)) := by
    intro a b hab; exact Submodule.finrank_lt_finrank_of_lt (hmon hab)
  have hge := strictMono_fin_le_val hfm ⟨Module.finrank K E + 1, by omega⟩
  have hle' := hbound ⟨Module.finrank K E + 1, by omega⟩
  simp at hge; omega





end CategoryOResults

lemma lie_hom_commutes_uea_act
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    (f : M →ₗ⁅R, L⁆ N) (u : UniversalEnvelopingAlgebra R L) (m : M) :
    f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)) u) m) =
    ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N)) u) (f m) := by

  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u


  suffices h : ∀ m' : M,
      f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
           ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)) m') =
      ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
        ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)) (f m') from h m
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro m'
    simp only [Algebra.algebraMap_eq_smul_one]
    simp
  | ι x =>
    intro m'
    rw [show (UniversalEnvelopingAlgebra.mkAlgHom R L) ((TensorAlgebra.ι R) x) =
            (UniversalEnvelopingAlgebra.ι R) x from rfl]
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
    simp only [LieModule.toEnd_apply_apply]
    exact f.map_lie x m'
  | mul a b ha hb =>
    intro m'
    rw [map_mul, map_mul, map_mul]
    show f (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
             ((UniversalEnvelopingAlgebra.mkAlgHom R L) a))
            (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M))
               ((UniversalEnvelopingAlgebra.mkAlgHom R L) b)) m')) =
         ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
           ((UniversalEnvelopingAlgebra.mkAlgHom R L) a))
          (((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L N))
             ((UniversalEnvelopingAlgebra.mkAlgHom R L) b)) (f m'))
    rw [ha]
    congr 1
    exact hb m'
  | add a b ha hb =>
    intro m'
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add]
    congr 1
    · exact ha m'
    · exact hb m'






universe u_vm in
theorem IsVermaModule.universal_map'
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type u_vm} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    {V : Type u_vm} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (v : V)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v)
    (hv_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) :
    ∃ (η : M →ₗ⁅R, 𝔤⁆ V), η hM.highestWeightVec = v :=
  hM.universal_map V v hv_wt hv_npos

universe u_vhsw in
theorem verma_hom_same_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {Mmu : Type u_vhsw} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    {Mlam : Type u_vhsw} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hMmu : IsVermaModule Δ Mmu wt)
    (hMlam : IsVermaModule Δ Mlam wt) :
    ∃ (eta : Mmu →ₗ⁅R, 𝔤⁆ Mlam), eta ≠ 0 := by


  obtain ⟨η, hη⟩ := hMmu.universal_map' hMlam.highestWeightVec
    hMlam.cartan_action hMlam.npos_action

  exact ⟨η, fun h => hMlam.hwv_ne_zero (by rw [← hη]; simp [h])⟩








lemma IsInQPlus_antisymm_catO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hpos : rd.IsInQPlus μ)
    (hneg : rd.IsInQPlus (-μ)) :
    μ = 0 := by
  classical
  obtain ⟨c, hc⟩ := hpos

  obtain ⟨d, hd⟩ := hneg
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hμ (by rw [hc]; exact Finset.sum_eq_zero fun β hβ => by simp [hall β hβ])
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _; rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [Finset.ne_of_mem_erase hγ]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ; omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩


lemma root_vec_raises_weight_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
    (μ : Δ.𝔥 →ₗ[R] R) (w : M)
    (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), w⁆ = μ h • w) :
    ∀ (h : Δ.𝔥), ⁅(h : 𝔤), (⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ : M)⁆ =
      (α + μ) h • ⁅(↑(rd.posRootVec α hα) : 𝔤), w⁆ := by
  intro h
  have hleibniz := leibniz_lie (h : 𝔤) (↑(rd.posRootVec α hα) : 𝔤) w
  have hroot := rd.posRootVec_weight α hα h
  have hwt := hw_wt h
  rw [hroot, hwt] at hleibniz
  rw [smul_lie, LieModule.lie_smul] at hleibniz
  rw [hleibniz]
  simp only [LinearMap.add_apply]
  rw [← add_smul]



def WeylStabilizerModQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w : wg.W | ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    wg.dualAction w x - x = ∑ α ∈ rd.posRoots, c α • α}

def WeylStabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w : wg.W | wg.dualAction w x = x}

lemma WeylStabilizer_mul_closed
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (x : Δ.𝔥 →ₗ[R] R)
    {w₁ w₂ : wg.W}
    (h₁ : w₁ ∈ WeylStabilizer rd wg x)
    (h₂ : w₂ ∈ WeylStabilizer rd wg x) :
    w₁ * w₂ ∈ WeylStabilizer rd wg x := by
  show wg.dualAction (w₁ * w₂) x = x
  rw [wg.dualAction_mul, h₂, h₁]

structure RootSystemWithReflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  allRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_sub : ∀ α ∈ rd.posRoots, α ∈ allRoots
  roots_pos_or_neg : ∀ α ∈ allRoots, α ∈ rd.posRoots ∨ -α ∈ rd.posRoots
  reflection : (Δ.𝔥 →ₗ[R] R) → wg.W
  coroot : (Δ.𝔥 →ₗ[R] R) → Δ.𝔥
  corootPairing_eq_eval : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    rd.corootPairing μ α = μ (coroot α)
  reflection_formula : ∀ α ∈ allRoots, ∀ μ : Δ.𝔥 →ₗ[R] R,
    wg.dualAction (reflection α) μ = μ - (μ (coroot α)) • α
  reflection_order_two : ∀ α ∈ allRoots, reflection α * reflection α = 1
  allRoots_neg_closed : ∀ α ∈ allRoots, -α ∈ allRoots
  reflection_neg : ∀ α ∈ allRoots, reflection (-α) = reflection α
  reflection_conjugation : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    reflection α * reflection β * reflection α =
    reflection (wg.dualAction (reflection α) β)
  allRoots_reflection_closed : ∀ α ∈ allRoots, ∀ β ∈ allRoots,
    wg.dualAction (reflection α) β ∈ allRoots
  dualAction_sub : ∀ (w : wg.W) (μ ν : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (μ - ν) = wg.dualAction w μ - wg.dualAction w ν
  dualAction_zsmul : ∀ (w : wg.W) (n : ℤ) (μ : Δ.𝔥 →ₗ[R] R),
    wg.dualAction w (n • μ) = n • wg.dualAction w μ
  dualAction_rootLattice : ∀ (w : wg.W) (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    ∃ (c' : (Δ.𝔥 →ₗ[R] R) → ℤ),
      wg.dualAction w (∑ α ∈ rd.posRoots, c α • α) = ∑ α ∈ rd.posRoots, c' α • α
  pairing_integral : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ allRoots →
    ∀ (μ : Δ.𝔥 →ₗ[R] R),
    (∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
      -(μ (coroot α)) • α = ∑ γ ∈ rd.posRoots, c γ • γ) →
    ∃ (n : ℤ), μ (coroot α) = (n : R)
  generated_by_reflections : ∀ w : wg.W, ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
    (∀ i, αs i ∈ allRoots) ∧
    w = (List.ofFn (fun i => reflection (αs i))).prod
  ρ_eq_half_sum : (2 : R) • wg.ρ = rd.sumPosRoots


theorem RootSystemWithReflections.dualAction_mul
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (_rs : RootSystemWithReflections rd wg)
    (w₁ w₂ : wg.W) (μ : Δ.𝔥 →ₗ[R] R) :
    wg.dualAction (w₁ * w₂) μ = wg.dualAction w₁ (wg.dualAction w₂ μ) :=
  wg.dualAction_mul w₁ w₂ μ

def rootsOfStabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) : Set (Δ.𝔥 →ₗ[R] R) :=
  {α | α ∈ rs.allRoots ∧ rs.reflection α ∈ WeylStabilizerModQ rd wg x}

def IsRootSubsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=

  (∀ α ∈ S, α ∈ rs.allRoots) ∧

  ((0 : Δ.𝔥 →ₗ[R] R) ∉ S) ∧

  (∀ α ∈ S, -α ∈ S) ∧

  (∀ α ∈ S, ∀ β ∈ S, wg.dualAction (rs.reflection α) β ∈ S)

def corootsOf
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Set Δ.𝔥 :=
  {h : Δ.𝔥 | ∃ α ∈ S, h = rs.coroot α}

lemma WeylStabilizerModQ_mul_closed
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R)
    {w₁ w₂ : wg.W}
    (h₁ : w₁ ∈ WeylStabilizerModQ rd wg x)
    (h₂ : w₂ ∈ WeylStabilizerModQ rd wg x) :
    w₁ * w₂ ∈ WeylStabilizerModQ rd wg x := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c₂', hc₂'⟩ := rs.dualAction_rootLattice w₁ c₂
  refine ⟨fun α => c₁ α + c₂' α, ?_⟩


  have hmul := rs.dualAction_mul w₁ w₂ x
  have hsub := rs.dualAction_sub w₁ (wg.dualAction w₂ x) x

  have hkey : wg.dualAction w₁ (wg.dualAction w₂ x - x) =
    wg.dualAction w₁ (wg.dualAction w₂ x) - wg.dualAction w₁ x := hsub

  rw [hc₂] at hkey

  rw [hc₂'] at hkey


  have : wg.dualAction (w₁ * w₂) x - x =
    (wg.dualAction w₁ (wg.dualAction w₂ x) - wg.dualAction w₁ x) +
    (wg.dualAction w₁ x - x) := by
    rw [hmul]
    abel
  rw [this, ← hkey, hc₁, ← Finset.sum_add_distrib]
  congr 1
  funext α
  show c₂' α • α + c₁ α • α = (c₁ α + c₂' α) • α
  rw [add_comm (c₁ α) (c₂' α), add_zsmul]

theorem weyl_generated_by_root_reflections
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg) :
    ∀ w : wg.W, ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
      (∀ i, αs i ∈ rs.allRoots) ∧
      w = (List.ofFn (fun i => rs.reflection (αs i))).prod :=
  fun w => rs.generated_by_reflections w







theorem Wx_roots_form_root_system
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :
    IsRootSubsystem rd wg rs (rootsOfStabilizer rd wg rs x) := by


  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro α hα
    exact hα.1
  ·

    intro h0
    have h0_in : (0 : Δ.𝔥 →ₗ[R] R) ∈ rs.allRoots := h0.1
    rcases rs.roots_pos_or_neg 0 h0_in with hp | hn
    · exact absurd rfl (rd.posRoots_ne_zero 0 hp)
    · simp at hn
      exact absurd rfl (rd.posRoots_ne_zero 0 hn)
  ·


    intro α hα
    refine ⟨rs.allRoots_neg_closed α hα.1, ?_⟩
    rw [rs.reflection_neg α hα.1]
    exact hα.2
  ·


    intro α hα β hβ

    have h_root : wg.dualAction (rs.reflection α) β ∈ rs.allRoots :=
      rs.allRoots_reflection_closed α hα.1 β hβ.1
    refine ⟨h_root, ?_⟩


    rw [← rs.reflection_conjugation α hα.1 β hβ.1]
    exact WeylStabilizerModQ_mul_closed rd wg rs x
      (WeylStabilizerModQ_mul_closed rd wg rs x hα.2 hβ.2)
      hα.2


theorem Rx_dual_is_root_subsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :


    ∀ h : Δ.𝔥,
      h ∈ corootsOf rs (rootsOfStabilizer rd wg rs x) ↔
        (h ∈ Submodule.span ℤ (corootsOf rs (rootsOfStabilizer rd wg rs x)) ∧
         h ∈ corootsOf rs (↑rs.allRoots : Set (Δ.𝔥 →ₗ[R] R))) := by
  intro h
  constructor
  ·


    intro hh
    constructor
    · exact Submodule.subset_span hh
    · obtain ⟨α, hα_mem, hα_eq⟩ := hh
      refine ⟨α, ?_, hα_eq⟩
      simp only [Finset.mem_coe]
      exact hα_mem.1
  ·


    intro ⟨h_span, h_all⟩

    obtain ⟨β, hβ_all, hβ_eq⟩ := h_all
    simp only [Finset.mem_coe] at hβ_all

    refine ⟨β, ⟨hβ_all, ?_⟩, hβ_eq⟩


    have h_int_stab : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ rootsOfStabilizer rd wg rs x →
        ∃ (n : ℤ), x (rs.coroot α) = (n : R) := by
      intro α hα
      apply rs.pairing_integral α hα.1 x

      obtain ⟨c, hc⟩ := hα.2

      have hrefl := rs.reflection_formula α hα.1 x


      have : wg.dualAction (rs.reflection α) x - x = -(x (rs.coroot α)) • α := by
        rw [hrefl]
        simp [sub_sub_cancel_left]
      rw [← this]
      exact ⟨c, hc⟩


    have h_int_beta : ∃ (N : ℤ), x (rs.coroot β) = (N : R) := by

      let S : Submodule ℤ Δ.𝔥 :=
        { carrier := {v : Δ.𝔥 | ∃ (n : ℤ), x v = (n : R)}
          add_mem' := by
            intro a b ⟨na, ha⟩ ⟨nb, hb⟩
            exact ⟨na + nb, by rw [map_add, ha, hb, Int.cast_add]⟩
          zero_mem' := ⟨0, by simp⟩
          smul_mem' := by
            intro m v ⟨n, hn⟩
            refine ⟨m * n, ?_⟩
            show x ((m : ℤ) • v) = ((m * n : ℤ) : R)
            rw [← Int.cast_smul_eq_zsmul R m v, map_smul, hn, Int.cast_mul, smul_eq_mul] }

      have h_sub : corootsOf rs (rootsOfStabilizer rd wg rs x) ⊆ S := by
        intro v hv
        obtain ⟨α, hα_mem, hα_eq⟩ := hv
        rw [hα_eq]
        exact h_int_stab α hα_mem

      rw [hβ_eq] at h_span

      exact Submodule.span_le.mpr h_sub h_span


    obtain ⟨N, hN⟩ := h_int_beta
    show rs.reflection β ∈ WeylStabilizerModQ rd wg x

    rw [WeylStabilizerModQ]
    simp only [Set.mem_setOf_eq]

    have hreflβ := rs.reflection_formula β hβ_all x

    have hdiff : wg.dualAction (rs.reflection β) x - x = -(x (rs.coroot β)) • β := by
      rw [hreflβ]
      simp [sub_sub_cancel_left]
    rw [hdiff, hN]


    have h_zsmul : -((N : R)) • β = (-N : ℤ) • β := by
      rw [← Int.cast_neg, Int.cast_smul_eq_zsmul R]
    rw [h_zsmul]
    rcases rs.roots_pos_or_neg β hβ_all with h_pos | h_neg
    ·
      classical
      refine ⟨fun γ => if γ = β then -N else 0, ?_⟩
      rw [Finset.sum_eq_single β
        (fun γ _ hγ => by simp [hγ])
        (fun hβ => absurd h_pos hβ)]
      simp
    ·
      classical
      refine ⟨fun γ => if γ = -β then N else 0, ?_⟩
      rw [Finset.sum_eq_single (-β)
        (fun γ _ hγ => by simp [hγ])
        (fun hβ => absurd h_neg hβ)]
      simp

end
