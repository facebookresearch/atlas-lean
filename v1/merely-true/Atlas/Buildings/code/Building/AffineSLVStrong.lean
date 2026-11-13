/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineSLV
import Atlas.Buildings.code.Building.GroupApplicationsCh17
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Topology.Algebra.Group.Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AffineBuildingSLVStrong

open AffineBuildingSLV AffineBuildingSLVAxioms


/-- Topological hypotheses on the fraction field $k$ of a complete DVR: the valuation
ring $\mathfrak{o}$ is open and compact in $k$, its maximal ideal is open, $k$ is a
$T_1$ topological ring. This is the package of assumptions needed to make the
Iwahori subgroup compact-open in $SL_V(k)$. -/
class DVRTopologicalAssumptions (C : DVRContext) [TopologicalSpace C.k] : Prop where
  isOpen_valRing : IsOpen {x : C.k | C.isInO x}
  isOpen_maxIdeal : IsOpen {x : C.k | C.isInMaxIdeal x}
  isTopologicalRing : IsTopologicalRing C.k
  isCompact_valRing : IsCompact {x : C.k | C.isInO x}
  t1Space : T1Space C.k


/-- The $j$-th standard basis vector $e_j \in k^n$. -/
noncomputable def stdBasisVec (C : DVRContext) (j : Fin C.n) : Fin C.n → C.k :=
  fun i => if i = j then 1 else 0

/-- Each standard basis vector $e_j$ is nonzero. -/
lemma stdBasisVec_ne_zero (C : DVRContext) (j : Fin C.n) : stdBasisVec C j ≠ 0 := by
  intro h
  have : stdBasisVec C j j = (0 : Fin C.n → C.k) j := by rw [h]
  simp [stdBasisVec] at this

/-- The $j$-th coordinate line $k \cdot e_j$ in $k^n$, packaged as a Line. -/
noncomputable def stdLine (C : DVRContext) (j : Fin C.n) : Line C :=
  ⟨stdBasisVec C j, stdBasisVec_ne_zero C j⟩

/-- Pointwise evaluation: $(\sum_j c_j e_j)(i) = c_i$. -/
lemma sum_std_basis_apply (C : DVRContext) (coeffs : Fin C.n → C.k) (i : Fin C.n) :
    (∑ j, coeffs j * stdBasisVec C j i) = coeffs i := by
  rw [Finset.sum_eq_single i]
  · simp [stdBasisVec]
  · intro j _ hji
    simp [stdBasisVec, Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Functional form: $\sum_j c_j e_j = c$ as vectors in $k^n$. -/
lemma sum_std_basis_eq (C : DVRContext) (coeffs : Fin C.n → C.k) :
    (fun i => ∑ j, coeffs j * stdBasisVec C j i) = coeffs := by
  funext i
  exact sum_std_basis_apply C coeffs i

/-- The standard frame in $k^n$ consisting of the coordinate lines $k \cdot e_j$. -/
noncomputable def stdFrame (C : DVRContext) : Frame C where
  lines := stdLine C
  spans := by
    intro v
    exact ⟨v, (sum_std_basis_eq C v).symm⟩
  independent := by
    intro coeffs h j
    have hj : (fun i => ∑ k_1, coeffs k_1 * (stdLine C k_1).generator i) j
              = (0 : Fin C.n → C.k) j := congr_fun h j
    simp only [stdLine, Pi.zero_apply] at hj
    rw [sum_std_basis_apply] at hj
    exact hj


/-- The special linear group $SL_n(k) = SL_V(k)$ acting on the affine building of
type $\tilde A_{n-1}$. -/
abbrev SLV (C : DVRContext) := Matrix.SpecialLinearGroup (Fin C.n) C.k


/-- The $(i,j)$-th matrix entry of an element of $SL_n(k)$, as a function $SL_n(k)
\to k$. -/
def matEntryProj (C : DVRContext) (i j : Fin C.n) : SLV C → C.k :=
  fun g => (g : Matrix (Fin C.n) (Fin C.n) C.k) i j

/-- The Iwahori condition on the $(i,j)$-entry: lies in the maximal ideal
$\mathfrak{m}$ if $i > j$ (strictly below the diagonal) and in $\mathfrak{o}$
otherwise. -/
def iwahoriEntryCondition (C : DVRContext) (i j : Fin C.n) : Set C.k :=
  if i.val > j.val then {x | C.isInMaxIdeal x} else {x | C.isInO x}

/-- The Iwahori subset of $SL_n(k)$: matrices in $SL_n(\mathfrak{o})$ whose
reduction modulo $\mathfrak{m}$ is upper-triangular. -/
def IwahoriSetSLV (C : DVRContext) : Set (SLV C) :=
  ⋂ (i : Fin C.n), ⋂ (j : Fin C.n),
    matEntryProj C i j ⁻¹' iwahoriEntryCondition C i j


/-- Axiomatic action of $SL_V(k)$ on the Bruhat-Tits building of $SL_V$: a
simplicial action together with the induced action on apartments and frames, and
sufficient hypotheses to run strong-transitivity arguments (preservation of
maximal simplices, frame/apartment compatibility, building chain data and
within-apartment chamber transitivity). -/
structure SLVAction (C : DVRContext) where
  act_simplex : SLV C → Simplex C → Simplex C
  act_mul : ∀ (g₁ g₂ : SLV C) (σ : Simplex C),
    act_simplex (g₁ * g₂) σ = act_simplex g₁ (act_simplex g₂ σ)
  act_one : ∀ (σ : Simplex C), act_simplex 1 σ = σ
  act_apartment : SLV C → Set (Simplex C) → Set (Simplex C)
  act_apartment_eq : ∀ (g : SLV C) (A : Set (Simplex C)),
    act_apartment g A = (act_simplex g) '' A
  act_preserves_maximal : ∀ (g : SLV C) (σ : Simplex C),
    σ.IsMaximal C → (act_simplex g σ).IsMaximal C
  act_frame : SLV C → Frame C → Frame C
  act_apartment_frame_compat : ∀ (g : SLV C) (F : Frame C),
    act_apartment g (Apartment C F) = Apartment C (act_frame g F)
  act_apartment_surj : ∀ (max_apts : Set (Set (Simplex C))),
    (∀ F : Frame C, Apartment C F ∈ max_apts) →
    ∀ (A' A₀ : Set (Simplex C)), A' ∈ max_apts → A₀ ∈ max_apts →
    ∀ g : SLV C, (∀ x ∈ A', act_simplex g x ∈ A₀) →
    (fun x => act_simplex g x) '' A' = A₀
  act_building_chain_data :
    ∀ (max_apts : Set (Set (Simplex C))),
    (∀ F : Frame C, Apartment C F ∈ max_apts) →
    ∀ (B : Subgroup (SLV C)) (A₀ : Set (Simplex C)),
    A₀ ∈ max_apts →
    ∀ (C₀ : Set (Simplex C)),
    C₀ ⊆ A₀ →
    (B : Set (SLV C)) = pointwiseFixer act_simplex C₀ →
    ∀ (A' : Set (Simplex C)), A' ∈ max_apts →
      C₀ ⊆ A' ∧
      ∃ (enum : ℕ → Simplex C),
        (∀ σ ∈ A', ∃ n, enum n = σ) ∧
        (∀ n, enum n ∈ A') ∧
        ∀ (Y : Set (Simplex C)), C₀ ⊆ Y → Y ⊆ A' →
          ∃ (A_i : Set (Simplex C)) (b_i : SLV C),
            Y ⊆ A_i ∧ b_i ∈ B ∧
            (∀ x ∈ A_i, act_simplex b_i x ∈ A₀)
  act_frame_chamber_trans :
    ∀ (F : Frame C) (C₁ C₂ : Simplex C),
      C₁.IsMaximal C → C₂.IsMaximal C →
      C₁ ∈ Apartment C F → C₂ ∈ Apartment C F →
      ∃ g : SLV C, act_simplex g C₁ = C₂ ∧
        act_apartment g (Apartment C F) = Apartment C F


/-- An $SL_V$-action on the building is strongly transitive with respect to an
apartment system $\mathcal A$ if for any two flagged pairs $(C_1, A_1)$ and
$(C_2, A_2)$ (maximal simplex in an apartment) some $g$ carries the first to the
second. -/
def IsStronglyTransitive (C : DVRContext) (α : SLVAction C)
    (𝒜 : Set (Set (Simplex C))) : Prop :=
  ∀ (C₁ : Simplex C) (A₁ : Set (Simplex C))
    (C₂ : Simplex C) (A₂ : Set (Simplex C)),
    C₁.IsMaximal C → C₂.IsMaximal C →
    A₁ ∈ 𝒜 → A₂ ∈ 𝒜 →
    C₁ ∈ A₁ → C₂ ∈ A₂ →
    ∃ g : SLV C, α.act_simplex g C₁ = C₂ ∧ α.act_apartment g A₁ = A₂

/-- The Iwahori subgroup is open in $SL_n(k)$: it is the intersection over
finitely many entries of preimages of open sets ($\mathfrak{o}$ or
$\mathfrak{m}$) under continuous entry projections. -/
theorem iwahori_is_open_in_SLV
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
    (B : Subgroup (SLV C)) (τ : TopologicalSpace (SLV C))
    [htg : @IsTopologicalGroup (SLV C) τ _]


    (hB_iwahori : (B : Set (SLV C)) = IwahoriSetSLV C)


    (h_entry_cont : ∀ i j : Fin C.n,
      @Continuous (SLV C) C.k τ _ (matEntryProj C i j))


    (h_valring_open : IsOpen {x : C.k | C.isInO x})


    (h_maxideal_open : IsOpen {x : C.k | C.isInMaxIdeal x}) :
    @IsOpen (SLV C) τ (B : Set (SLV C)) := by


  rw [hB_iwahori, IwahoriSetSLV]


  apply @isOpen_iInter_of_finite (SLV C) (Fin C.n) τ
  intro i
  apply @isOpen_iInter_of_finite (SLV C) (Fin C.n) τ
  intro j


  apply (h_entry_cont i j).isOpen_preimage


  unfold iwahoriEntryCondition
  split
  · exact h_maxideal_open
  · exact h_valring_open

/-- The Iwahori subgroup is closed in $SL_n(k)$: any open subgroup of a
topological group is automatically closed. -/
theorem iwahori_is_closed_in_SLV
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
    (B : Subgroup (SLV C)) (τ : TopologicalSpace (SLV C))
    [htg : @IsTopologicalGroup (SLV C) τ _]
    (hB_open : @IsOpen (SLV C) τ (B : Set (SLV C))) :
    @IsClosed (SLV C) τ (B : Set (SLV C)) := by


  have : @SeparatelyContinuousMul (SLV C) τ _ := by
    haveI : @ContinuousMul (SLV C) τ _ := htg.toContinuousMul
    infer_instance
  exact @Subgroup.isClosed_of_isOpen (SLV C) _ τ this B hB_open

/-- The Iwahori subgroup is compact in $SL_n(k)$, since a closed subset of a
compact set in a topological group is compact. -/
theorem iwahori_is_compact_in_SLV
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
    (B : Subgroup (SLV C)) (τ : TopologicalSpace (SLV C))
    [htg : @IsTopologicalGroup (SLV C) τ _]
    (hB_closed : @IsClosed (SLV C) τ (B : Set (SLV C)))


    (hB_in_compact : ∃ (K : Set (SLV C)),
      @IsCompact (SLV C) τ K ∧ (B : Set (SLV C)) ⊆ K) :
    @IsCompact (SLV C) τ (B : Set (SLV C)) := by

  obtain ⟨K, hK_compact, hBK⟩ := hB_in_compact

  exact closed_in_compact_is_compact (↑B) K hB_closed hBK hK_compact

/-- The image of the valuation ring embedding $\mathfrak{o} \hookrightarrow k$ as a
subring of $k$. -/
noncomputable def imageSubring (C : DVRContext) : Subring C.k :=
  C.embed.range

/-- An element of $k$ lies in the image of $\mathfrak{o}$ iff it is integral. -/
lemma mem_imageSubring_iff (C : DVRContext) (x : C.k) :
    x ∈ imageSubring C ↔ C.isInO x := by
  simp [imageSubring, RingHom.mem_range, DVRContext.isInO]


/-- The maximal ideal $\mathfrak{m}$ is closed under addition. -/
lemma isInMaxIdeal_add' (C : DVRContext) {x y : C.k}
    (hx : C.isInMaxIdeal x) (hy : C.isInMaxIdeal y) : C.isInMaxIdeal (x + y) := by
  obtain ⟨rx, hrx_mem, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx + ry, Ideal.add_mem _ hrx_mem hry_mem, by rw [map_add, hrx, hry]⟩


/-- The maximal ideal $\mathfrak{m}$ absorbs multiplication by $\mathfrak{o}$ on
the left: $\mathfrak{o} \cdot \mathfrak{m} \subseteq \mathfrak{m}$. -/
lemma isInO_mul_isInMaxIdeal' (C : DVRContext) {x y : C.k}
    (hx : C.isInO x) (hy : C.isInMaxIdeal y) : C.isInMaxIdeal (x * y) := by
  obtain ⟨rx, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx * ry, Ideal.mul_mem_left _ rx hry_mem, by rw [map_mul, hrx, hry]⟩


/-- The maximal ideal $\mathfrak{m}$ absorbs multiplication by $\mathfrak{o}$ on
the right: $\mathfrak{m} \cdot \mathfrak{o} \subseteq \mathfrak{m}$. -/
lemma isInMaxIdeal_mul_isInO' (C : DVRContext) {x y : C.k}
    (hx : C.isInMaxIdeal x) (hy : C.isInO y) : C.isInMaxIdeal (x * y) := by
  obtain ⟨rx, hrx_mem, hrx⟩ := hx; obtain ⟨ry, hry⟩ := hy
  exact ⟨rx * ry, Ideal.mul_mem_right ry _ hrx_mem, by rw [map_mul, hrx, hry]⟩

/-- Zero lies in $\mathfrak{m}$. -/
lemma isInMaxIdeal_zero' (C : DVRContext) : C.isInMaxIdeal 0 :=
  ⟨0, Ideal.zero_mem _, map_zero _⟩

/-- One is integral. -/
lemma isInO_one' (C : DVRContext) : C.isInO 1 := ⟨1, map_one _⟩
/-- Zero is integral. -/
lemma isInO_zero' (C : DVRContext) : C.isInO 0 := ⟨0, map_zero _⟩
/-- The negation of an integral element is integral. -/
lemma isInO_neg' (C : DVRContext) {x : C.k} (hx : C.isInO x) : C.isInO (-x) := by
  obtain ⟨rx, hrx⟩ := hx; exact ⟨-rx, by rw [map_neg, hrx]⟩


/-- A finite sum of integral elements is integral. -/
lemma isInO_finset_sum (C : DVRContext) {ι : Type*} {s : Finset ι} {f : ι → C.k}
    (hf : ∀ x ∈ s, C.isInO (f x)) : C.isInO (∑ x ∈ s, f x) := by
  rw [← mem_imageSubring_iff]
  exact Subring.sum_mem _ (fun x hx => (mem_imageSubring_iff C _).mpr (hf x hx))


/-- A finite sum of elements in $\mathfrak{m}$ is in $\mathfrak{m}$. -/
lemma isInMaxIdeal_finset_sum (C : DVRContext) {ι : Type*} {s : Finset ι} {f : ι → C.k}
    (hf : ∀ x ∈ s, C.isInMaxIdeal (f x)) : C.isInMaxIdeal (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact isInMaxIdeal_zero' C
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isInMaxIdeal_add' C (hf _ (Finset.mem_insert_self _ _))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))


/-- A finite product of integral elements is integral. -/
lemma isInO_finset_prod (C : DVRContext) {ι : Type*} {s : Finset ι} {f : ι → C.k}
    (hf : ∀ x ∈ s, C.isInO (f x)) : C.isInO (∏ x ∈ s, f x) := by
  rw [← mem_imageSubring_iff]
  exact Subring.prod_mem _ (fun x hx => (mem_imageSubring_iff C _).mpr (hf x hx))


/-- Membership in the Iwahori set unwound entrywise. -/
lemma mem_IwahoriSetSLV_iff (C : DVRContext) (g : SLV C) :
    g ∈ IwahoriSetSLV C ↔
    ∀ i j : Fin C.n,
      (g : Matrix (Fin C.n) (Fin C.n) C.k) i j ∈ iwahoriEntryCondition C i j := by
  simp only [IwahoriSetSLV, Set.mem_iInter, Set.mem_preimage, matEntryProj]


/-- Every entry of an Iwahori matrix is integral, since each entry is either in
$\mathfrak{m} \subseteq \mathfrak{o}$ or directly in $\mathfrak{o}$. -/
lemma iwahori_entry_isInO (C : DVRContext) [IsDiscreteValuationRing C.𝔬]
    {g : SLV C} (hg : g ∈ IwahoriSetSLV C) (i j : Fin C.n) :
    C.isInO ((g : Matrix (Fin C.n) (Fin C.n) C.k) i j) := by
  have hg' := (mem_IwahoriSetSLV_iff C g).mp hg i j
  simp only [iwahoriEntryCondition] at hg'
  split_ifs at hg' with h
  · exact C.isInMaxIdeal_isInO hg'
  · exact hg'


/-- The subdiagonal entries of an Iwahori matrix lie in the maximal ideal
$\mathfrak{m}$. -/
lemma iwahori_entry_below (C : DVRContext) [IsDiscreteValuationRing C.𝔬]
    {g : SLV C} (hg : g ∈ IwahoriSetSLV C) {i j : Fin C.n} (hij : i.val > j.val) :
    C.isInMaxIdeal ((g : Matrix (Fin C.n) (Fin C.n) C.k) i j) := by
  have hg' := (mem_IwahoriSetSLV_iff C g).mp hg i j
  simp only [iwahoriEntryCondition, hij, if_true, Set.mem_setOf_eq] at hg'
  exact hg'


/-- The sign of any permutation, viewed in $k$, is integral. -/
lemma sign_isInO (C : DVRContext) (σ : Equiv.Perm (Fin C.n)) :
    C.isInO ((Equiv.Perm.sign σ : ℤ) : C.k) := by
  have : (Equiv.Perm.sign σ : ℤ) = 1 ∨ (Equiv.Perm.sign σ : ℤ) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rcases this with h | h
  · rw [h, Int.cast_one]; exact isInO_one' C
  · rw [h, Int.cast_neg, Int.cast_one]; exact isInO_neg' C (isInO_one' C)


/-- An integer scalar multiple of an integral element is integral. -/
lemma isInO_smul_of_isInO (C : DVRContext) (z : ℤ) {x : C.k}
    (hz : C.isInO (z : C.k)) (hx : C.isInO x) : C.isInO (z • x) := by
  rw [zsmul_eq_mul]
  rw [← mem_imageSubring_iff] at hz hx ⊢
  exact Subring.mul_mem _ hz hx

/-- If every entry of $M$ is integral then $\det M$ is integral. -/
lemma isInO_det (C : DVRContext) {M : Matrix (Fin C.n) (Fin C.n) C.k}
    (hM : ∀ i j, C.isInO (M i j)) : C.isInO M.det := by
  simp only [Matrix.det_apply]
  apply isInO_finset_sum
  intro σ _
  exact isInO_smul_of_isInO C _ (sign_isInO C σ)
    (isInO_finset_prod C (fun i _ => hM (σ i) i))


/-- Combinatorial fact: if a permutation strictly decreases some index $i$
($\sigma(i) < i$), then somewhere else it must strictly increase. -/
lemma perm_has_ascent {n : ℕ} {σ : Equiv.Perm (Fin n)} {i : Fin n}
    (hi : (σ i).val < i.val) :
    ∃ l : Fin n, l ≠ i ∧ (σ l).val > l.val := by
  by_contra h
  push Not at h


  have h_sum : ∑ l : Fin n, ((σ l).val : ℤ) = ∑ l : Fin n, (l.val : ℤ) :=
    Equiv.sum_comp σ (fun l => (l.val : ℤ))
  have h_zero : ∑ l : Fin n, (((σ l).val : ℤ) - l.val) = 0 := by
    simp only [Finset.sum_sub_distrib]; omega

  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h_zero
  have hi_neg : ((σ i).val : ℤ) - i.val < 0 := by omega
  have h_rest_nonpos : ∀ l ∈ Finset.univ.erase i, (((σ l).val : ℤ) - l.val) ≤ 0 := by
    intro l hl
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    exact sub_nonpos.mpr (Int.ofNat_le.mpr (h l hli))
  have h_rest_nonpos' : ∑ l ∈ Finset.univ.erase i, (((σ l).val : ℤ) - l.val) ≤ 0 :=
    Finset.sum_nonpos h_rest_nonpos
  linarith


/-- Replacing the $j$-th row of an Iwahori matrix by the standard basis vector
$e_i$ still gives a matrix with all entries integral. -/
lemma updateRow_isInO (C : DVRContext) [IsDiscreteValuationRing C.𝔬]
    {g : SLV C} (hg : g ∈ IwahoriSetSLV C) (i j : Fin C.n) (l m : Fin C.n) :
    C.isInO (((g : Matrix (Fin C.n) (Fin C.n) C.k).updateRow j (Pi.single i 1)) l m) := by
  simp only [Matrix.updateRow_apply]
  split_ifs with hlj
  · simp only [Pi.single_apply]
    split_ifs with hmi
    · exact isInO_one' C
    · exact isInO_zero' C
  · exact iwahori_entry_isInO C hg l m


/-- Every entry of the adjugate of an Iwahori matrix is integral. -/
lemma adjugate_isInO (C : DVRContext) [IsDiscreteValuationRing C.𝔬]
    {g : SLV C} (hg : g ∈ IwahoriSetSLV C) (i j : Fin C.n) :
    C.isInO ((g : Matrix (Fin C.n) (Fin C.n) C.k).adjugate i j) := by
  rw [Matrix.adjugate_apply]
  exact isInO_det C (updateRow_isInO C hg i j)


/-- The strictly-below-diagonal entries of the adjugate of an Iwahori matrix lie
in $\mathfrak{m}$, the key step in showing the Iwahori set is closed under
inversion. -/
lemma adjugate_below_isInMaxIdeal (C : DVRContext) [IsDiscreteValuationRing C.𝔬]
    {g : SLV C} (hg : g ∈ IwahoriSetSLV C) {i j : Fin C.n} (hij : i.val > j.val) :
    C.isInMaxIdeal ((g : Matrix (Fin C.n) (Fin C.n) C.k).adjugate i j) := by
  rw [Matrix.adjugate_apply]
  set B := (g : Matrix (Fin C.n) (Fin C.n) C.k).updateRow j (Pi.single i 1)

  simp only [Matrix.det_apply]
  apply isInMaxIdeal_finset_sum
  intro σ _


  by_cases hσi : σ i = j
  ·

    have hdesc : (σ i).val < i.val := by rw [hσi]; exact hij
    obtain ⟨l, hli, hlt⟩ := perm_has_ascent hdesc

    have hσlj : σ l ≠ j := by
      intro heq
      have : l = i := σ.injective (heq.trans hσi.symm)
      exact hli this
    have hBl : B (σ l) l = (g : Matrix _ _ C.k) (σ l) l := by
      simp [B, Matrix.updateRow_apply, hσlj]

    have hm : C.isInMaxIdeal ((g : Matrix _ _ C.k) (σ l) l) :=
      iwahori_entry_below C hg hlt

    have hprod : C.isInMaxIdeal (∏ idx : Fin C.n, B (σ idx) idx) := by
      classical
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hBl]
      exact isInMaxIdeal_mul_isInO' C hm
        (isInO_finset_prod C (fun m hm' =>
          updateRow_isInO C hg i j (σ m) m))

    rw [Units.smul_def, zsmul_eq_mul]
    exact isInO_mul_isInMaxIdeal' C (sign_isInO C σ) hprod

  ·

    have hzero : ∏ idx : Fin C.n, B (σ idx) idx = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm j))
      have h_ne : σ.symm j ≠ i := by
        intro h; exact hσi (by rw [← h, Equiv.apply_symm_apply])

      simp only [B, Matrix.updateRow_apply, Equiv.apply_symm_apply, ↓reduceIte,
        Pi.single_apply, h_ne]

    rw [hzero, smul_zero]
    exact isInMaxIdeal_zero' C

/-- The Iwahori set is a subgroup of $SL_n(k)$: it contains the identity and is
closed under multiplication and inversion. The inversion step uses the formula
$g^{-1} = \mathrm{adj}(g)/\det g$ and the adjugate bounds above. -/
theorem iwahori_set_is_subgroup
    (C : DVRContext) [IsDiscreteValuationRing C.𝔬] :
    ∃ B : Subgroup (SLV C), (B : Set (SLV C)) = IwahoriSetSLV C := by
  refine ⟨{ carrier := IwahoriSetSLV C, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  ·
    intro g h hg hh
    rw [mem_IwahoriSetSLV_iff]
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, iwahoriEntryCondition]
    split_ifs with hij
    ·

      apply isInMaxIdeal_finset_sum
      intro k _
      by_cases hki : i.val > k.val
      · exact isInMaxIdeal_mul_isInO' C (iwahori_entry_below C hg hki)
          (iwahori_entry_isInO C hh k j)
      · exact isInO_mul_isInMaxIdeal' C (iwahori_entry_isInO C hg i k)
          (iwahori_entry_below C hh (by omega))
    ·
      apply isInO_finset_sum
      intro k _
      rw [← mem_imageSubring_iff]
      exact Subring.mul_mem _
        ((mem_imageSubring_iff C _).mpr (iwahori_entry_isInO C hg i k))
        ((mem_imageSubring_iff C _).mpr (iwahori_entry_isInO C hh k j))
  ·
    rw [mem_IwahoriSetSLV_iff]
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, iwahoriEntryCondition]
    split_ifs with hij heq
    · subst heq; omega

    · exact isInMaxIdeal_zero' C
    · exact isInO_one' C
    · exact isInO_zero' C
  ·
    intro g hg
    rw [mem_IwahoriSetSLV_iff]
    intro i j
    simp only [iwahoriEntryCondition]

    have hinv_entry : (g⁻¹ : SLV C) i j = (g : Matrix _ _ C.k).adjugate i j := by
      show (↑(g⁻¹ : SLV C) : Matrix _ _ C.k) i j = _
      simp [Matrix.SpecialLinearGroup.coe_inv]
    split_ifs with hij
    · rw [Set.mem_setOf_eq, hinv_entry]
      exact adjugate_below_isInMaxIdeal C hg hij
    · rw [Set.mem_setOf_eq, hinv_entry]
      exact adjugate_isInO C hg i j

/-- The valuation ring $\mathfrak{o}$ is open in $k$ under the topological
assumptions. -/
theorem valuation_ring_is_open
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬] [DVRTopologicalAssumptions C] :
    IsOpen {x : C.k | C.isInO x} :=
  DVRTopologicalAssumptions.isOpen_valRing

/-- The maximal ideal $\mathfrak{m}$ is open in $k$ under the topological
assumptions. -/
theorem maximal_ideal_is_open
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬] [DVRTopologicalAssumptions C] :
    IsOpen {x : C.k | C.isInMaxIdeal x} :=
  DVRTopologicalAssumptions.isOpen_maxIdeal

/-- The Iwahori subgroup lies inside the compact set of matrices with all entries
in $\mathfrak{o}$, namely $SL_n(k) \cap M_n(\mathfrak{o})$. -/
theorem iwahori_in_compact_set
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬] [DVRTopologicalAssumptions C]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
    (B : Subgroup (SLV C))
    (hB_iwahori : (B : Set (SLV C)) = IwahoriSetSLV C) :
    ∃ (K : Set (SLV C)), IsCompact K ∧ (B : Set (SLV C)) ⊆ K := by
  haveI : IsTopologicalRing C.k := DVRTopologicalAssumptions.isTopologicalRing
  haveI : T1Space C.k := DVRTopologicalAssumptions.t1Space

  refine ⟨{g : SLV C | ∀ i j, (g : Matrix (Fin C.n) (Fin C.n) C.k) i j ∈ {x | C.isInO x}},
    ?_, ?_⟩
  ·


    have hce : Topology.IsClosedEmbedding
      (Subtype.val : SLV C → Matrix (Fin C.n) (Fin C.n) C.k) := by
      refine ⟨Topology.IsEmbedding.subtypeVal, ?_⟩
      rw [Subtype.range_coe_subtype]
      exact isClosed_eq (by fun_prop) continuous_const


    exact hce.isCompact_preimage
      (isCompact_pi_infinite (fun _ => isCompact_pi_infinite
        (fun _ => DVRTopologicalAssumptions.isCompact_valRing)))
  ·
    intro g hg
    simp only [Set.mem_setOf_eq]
    intro i j
    rw [hB_iwahori] at hg
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hg i) j
    simp only [IwahoriSetSLV, matEntryProj, Set.mem_preimage, iwahoriEntryCondition] at h
    split_ifs at h with hij
    · exact C.isInMaxIdeal_isInO h
    · exact h

/-- The Iwahori subgroup of $SL_n(k)$ is compact-open in the natural topology on
$SL_n(k)$. This is the crucial ingredient for applying strong-transitivity
methods to the Bruhat-Tits building. -/
theorem iwahori_is_compact_open
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬] [DVRTopologicalAssumptions C]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬) :
    ∃ (B : Subgroup (SLV C)) (τ : TopologicalSpace (SLV C))
      (_ : @IsTopologicalGroup (SLV C) τ _),
      @IsCompact (SLV C) τ (B : Set (SLV C)) ∧
      @IsOpen (SLV C) τ (B : Set (SLV C)) := by


  haveI : IsTopologicalRing C.k := DVRTopologicalAssumptions.isTopologicalRing
  haveI : T1Space C.k := DVRTopologicalAssumptions.t1Space

  let τ : TopologicalSpace (SLV C) := inferInstance

  obtain ⟨B, hB_iwahori⟩ := iwahori_set_is_subgroup C

  have h_entry_cont : ∀ i j : Fin C.n,
      @Continuous (SLV C) C.k τ _ (matEntryProj C i j) := by
    intro i j
    show Continuous (fun g : SLV C => (g : Matrix (Fin C.n) (Fin C.n) C.k) i j)
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

  have hB_open : @IsOpen (SLV C) τ (B : Set (SLV C)) := by
    exact @iwahori_is_open_in_SLV C _ _ _ ho_complete B τ inferInstance
      hB_iwahori h_entry_cont (valuation_ring_is_open C) (maximal_ideal_is_open C)

  have hB_closed : @IsClosed (SLV C) τ (B : Set (SLV C)) := by
    exact @iwahori_is_closed_in_SLV C _ _ _ ho_complete B τ inferInstance hB_open

  have hB_compact : @IsCompact (SLV C) τ (B : Set (SLV C)) := by
    exact @iwahori_is_compact_in_SLV C _ _ _ ho_complete B τ inferInstance hB_closed
      (iwahori_in_compact_set C ho_complete B hB_iwahori)
  exact ⟨B, τ, inferInstance, hB_compact, hB_open⟩







/-- Within an apartment $A_F$ coming from a frame $F$, the group $SL_V(k)$ acts
transitively on (maximal-chamber, $A_F$) pairs, preserving the apartment. -/
theorem frame_chamber_transitivity
    (C : DVRContext) [TopologicalSpace C.k] [LocallyCompactSpace C.k]
    [IsDiscreteValuationRing C.𝔬]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
    (α : SLVAction C)
    (F : Frame C)
    (C₁ C₂ : Simplex C)
    (hC₁_max : C₁.IsMaximal C) (hC₂_max : C₂.IsMaximal C)
    (hC₁ : C₁ ∈ Apartment C F) (hC₂ : C₂ ∈ Apartment C F) :
    ∃ g : SLV C, α.act_simplex g C₁ = C₂ ∧
      α.act_apartment g (Apartment C F) = Apartment C F := by


  exact α.act_frame_chamber_trans F C₁ C₂ hC₁_max hC₂_max hC₁ hC₂




/-- The identity element acts trivially on apartments. -/
lemma act_apartment_one (C : DVRContext) (α : SLVAction C) (A : Set (Simplex C)) :
    α.act_apartment 1 A = A := by
  rw [α.act_apartment_eq]
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [α.act_one]; exact hy
  · intro hx; exact ⟨x, hx, α.act_one x⟩

/-- The action on apartments respects group multiplication. -/
lemma act_apartment_mul (C : DVRContext) (α : SLVAction C) (g₁ g₂ : SLV C)
    (A : Set (Simplex C)) :
    α.act_apartment (g₁ * g₂) A = α.act_apartment g₁ (α.act_apartment g₂ A) := by
  simp only [α.act_apartment_eq, Set.image_image]
  congr 1
  ext x
  exact α.act_mul g₁ g₂ x





/-- Strong transitivity follows formally from apartment-transitivity together with
chamber-transitivity within each apartment: any flagged pair $(C_1, A_1)$ can
be moved to any other $(C_2, A_2)$. -/
theorem strong_transitivity_from_apt_and_chamber_transit
    (C : DVRContext)
    [TopologicalSpace C.k]
    [hDVR : IsDiscreteValuationRing C.𝔬]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
    [hk_lc : LocallyCompactSpace C.k]
    (α : SLVAction C)
    (max_apts : Set (Set (Simplex C)))
    (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts)

    (apt_transit : ∀ (A₁ A₂ : Set (Simplex C)), A₁ ∈ max_apts → A₂ ∈ max_apts →
      ∃ g : SLV C, α.act_apartment g A₁ = A₂)

    (chamber_transit : ∀ (C₁ C₂ : Simplex C) (A : Set (Simplex C)),
      C₁.IsMaximal C → C₂.IsMaximal C →
      A ∈ max_apts → C₁ ∈ A → C₂ ∈ A →
      ∃ g : SLV C, α.act_simplex g C₁ = C₂ ∧ α.act_apartment g A = A) :
    IsStronglyTransitive C α max_apts := by
  intro C₁ A₁ C₂ A₂ hC₁_max hC₂_max hA₁ hA₂ hC₁_in_A₁ hC₂_in_A₂

  obtain ⟨g₁, hg₁⟩ := apt_transit A₁ A₂ hA₁ hA₂

  have hg₁C₁_in_A₂ : α.act_simplex g₁ C₁ ∈ A₂ := by
    rw [← hg₁, α.act_apartment_eq]
    exact Set.mem_image_of_mem _ hC₁_in_A₁
  have hg₁C₁_max : (α.act_simplex g₁ C₁).IsMaximal C :=
    α.act_preserves_maximal g₁ C₁ hC₁_max

  obtain ⟨h, hh_chamber, hh_apt⟩ := chamber_transit (α.act_simplex g₁ C₁) C₂ A₂
    hg₁C₁_max hC₂_max hA₂ hg₁C₁_in_A₂ hC₂_in_A₂

  refine ⟨h * g₁, ?_, ?_⟩
  ·
    rw [α.act_mul]
    exact hh_chamber
  ·
    rw [α.act_apartment_eq]
    ext σ
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [α.act_mul]
      have hg₁x_in_A₂ : α.act_simplex g₁ x ∈ A₂ := by
        rw [← hg₁, α.act_apartment_eq]
        exact Set.mem_image_of_mem _ hx
      have h_A₂_surj : (α.act_simplex h) '' A₂ = A₂ := by
        rw [← α.act_apartment_eq]; exact hh_apt
      rw [← h_A₂_surj]
      exact Set.mem_image_of_mem _ hg₁x_in_A₂
    · intro hσ

      have h_A₂_surj : (α.act_simplex h) '' A₂ = A₂ := by
        rw [← α.act_apartment_eq]; exact hh_apt
      rw [← h_A₂_surj] at hσ
      obtain ⟨y, hy_in_A₂, rfl⟩ := hσ

      have g₁_A₁_surj : (α.act_simplex g₁) '' A₁ = A₂ := by
        rw [← α.act_apartment_eq]; exact hg₁
      rw [← g₁_A₁_surj] at hy_in_A₂
      obtain ⟨x, hx_in_A₁, rfl⟩ := hy_in_A₂
      exact ⟨x, hx_in_A₁, α.act_mul h g₁ x⟩




/-- Abstract lemma: if a $G$-stable apartment system $\mathcal{A} \subseteq
\mathrm{max\_apts}$ contains some apartment $A_0$ that the $G$-action sends to
every maximal apartment, then $\mathcal{A} = \mathrm{max\_apts}$. -/
theorem constructed_apartment_system_is_maximal_of_stable_and_transitive
    {G : Type*} [Group G] [TopologicalSpace G]

    (act : G → Set (Simplex C) → Set (Simplex C))
    (hact_mul : ∀ g₁ g₂ : G, ∀ A, act (g₁ * g₂) A = act g₁ (act g₂ A))
    (hact_one : ∀ A, act 1 A = A)

    (𝒜 : Set (Set (Simplex C)))

    (max_apts : Set (Set (Simplex C)))

    (A₀ : Set (Simplex C))
    (hA₀_in_𝒜 : A₀ ∈ 𝒜)
    (hA₀_in_max : A₀ ∈ max_apts)

    (h𝒜_stable : ∀ g : G, ∀ A ∈ 𝒜, act g A ∈ 𝒜)

    (h𝒜_sub_max : 𝒜 ⊆ max_apts)


    (strong_transit_max : ∀ A' ∈ max_apts, ∃ g : G, act g A' = A₀) :
    𝒜 = max_apts := by
  ext A
  constructor
  · exact fun h => h𝒜_sub_max h
  · intro hA_max
    obtain ⟨g, hg⟩ := strong_transit_max A hA_max
    have hA_eq : A = act g⁻¹ A₀ := by
      have h1 : act g⁻¹ (act g A) = A := by rw [← hact_mul, inv_mul_cancel, hact_one]
      rw [← h1, hg]
    rw [hA_eq]
    exact h𝒜_stable g⁻¹ A₀ hA₀_in_𝒜

/-- Specialisation of the abstract maximality lemma to the $SL_V$ apartment
action: a stable, contained apartment system that intersects every
$SL_V$-orbit of $A_0$ in the maximal system actually equals the maximal
system. -/
theorem maximal_apt_system_slv_helper
    (C : DVRContext)
    (α : SLVAction C)

    (𝒜 : Set (Set (Simplex C)))

    (max_apts : Set (Set (Simplex C)))

    (A₀ : Set (Simplex C))
    (hA₀_in_𝒜 : A₀ ∈ 𝒜)
    (hA₀_in_max : A₀ ∈ max_apts)

    (h𝒜_stable : ∀ g : SLV C, ∀ A ∈ 𝒜, α.act_apartment g A ∈ 𝒜)

    (h𝒜_sub_max : 𝒜 ⊆ max_apts)


    (strong_transit_max : ∀ A' ∈ max_apts, ∃ g : SLV C, α.act_apartment g A' = A₀) :
    𝒜 = max_apts := by
  ext A
  constructor
  · exact fun h => h𝒜_sub_max h
  · intro hA_max
    obtain ⟨g, hg⟩ := strong_transit_max A hA_max
    have hA_eq : A = α.act_apartment g⁻¹ A₀ := by
      rw [← hg, α.act_apartment_eq, α.act_apartment_eq]
      ext σ
      simp only [Set.mem_image]
      constructor
      · intro hσ
        exact ⟨α.act_simplex g σ, ⟨σ, hσ, rfl⟩,
          by rw [← α.act_mul, inv_mul_cancel, α.act_one]⟩
      · rintro ⟨τ, ⟨σ', hσ', rfl⟩, hτ'⟩
        have : σ' = σ := by
          have h1 : σ' = α.act_simplex (g⁻¹ * g) σ' := by
            rw [inv_mul_cancel, α.act_one]
          rw [α.act_mul] at h1
          exact h1.trans hτ'
        rw [← this]
        exact hσ'
    rw [hA_eq]
    exact h𝒜_stable g⁻¹ A₀ hA₀_in_𝒜

/-- The canonical apartment system: apartments $A_F$ indexed by frames $F$ of $V$.
This is the maximal apartment system for the Bruhat-Tits building of $SL_V$. -/
def frameApartmentSystem (C : DVRContext) : Set (Set (Simplex C)) :=
  {A | ∃ F : Frame C, A = Apartment C F}

/-- A family of apartments is an apartment system if every member arises from a
frame and any two simplices lie together in some apartment of the system. -/
def IsApartmentSystem (C : DVRContext) (sys : Set (Set (Simplex C))) : Prop :=

  (∀ A ∈ sys, ∃ F : Frame C, A = Apartment C F) ∧

  (∀ σ₁ σ₂ : Simplex C, ∃ A ∈ sys, σ₁ ∈ A ∧ σ₂ ∈ A) ∧


  True

/-- An apartment system is maximal if it is an apartment system and contains every
other apartment system. -/
def IsMaximalApartmentSystem (C : DVRContext) (max_apts : Set (Set (Simplex C))) : Prop :=
  IsApartmentSystem C max_apts ∧
  (∀ sys : Set (Set (Simplex C)), IsApartmentSystem C sys → sys ⊆ max_apts)

/-- Each frame apartment $A_F$ is a member of the frame apartment system. -/
theorem frame_apartment_mem_frameApartmentSystem (C : DVRContext) (F : Frame C) :
    Apartment C F ∈ frameApartmentSystem C :=
  ⟨F, rfl⟩

/-- The frame apartment system is $SL_V$-stable: the translate of any frame
apartment $A_F$ by $g \in SL_V$ is again a frame apartment, namely $A_{gF}$. -/
theorem frame_apartment_system_stable
    (C : DVRContext)
    [TopologicalSpace C.k]
    [IsDiscreteValuationRing C.𝔬]
    (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
    [LocallyCompactSpace C.k]
    (α : SLVAction C) :
    ∀ g : SLV C, ∀ A ∈ frameApartmentSystem C, α.act_apartment g A ∈ frameApartmentSystem C := by


  intro g A ⟨F, hF⟩

  rw [hF, α.act_apartment_frame_compat g F]

  exact ⟨α.act_frame g F, rfl⟩

/-- The frame apartment system is contained in any apartment system that contains
all frame apartments. -/
theorem frame_apartment_system_sub_maximal
    (C : DVRContext)
    (max_apts : Set (Set (Simplex C)))
    (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts) :
    frameApartmentSystem C ⊆ max_apts := by
  intro A ⟨F, hF⟩
  rw [hF]
  exact hframes F




/-- From a compact-open Iwahori subgroup, deduce that the maximal apartment
system contains any two maximal simplices in a common apartment (formulation
without an explicit topology on $SL_V$). -/
theorem strong_transitivity_from_compact_open_iwahori
    (C : DVRContext)
    [TopologicalSpace (Fin C.n → Fin C.n → C.𝔬)]
    (_hB_open : IsOpen (IwahoriSubgroup C))
    (_hB_compact : IsCompact (IwahoriSubgroup C))

    (max_apts : Set (Set (Simplex C)))
    (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts)
    (hmax : IsMaximalApartmentSystem C max_apts) :
    ∃ (max_apts' : Set (Set (Simplex C))),
      (∀ F : Frame C,
        Apartment C F ∈ max_apts') ∧
      (∀ σ τ : Simplex C,
        σ.IsMaximal C → τ.IsMaximal C →
        ∃ A ∈ max_apts', σ ∈ A ∧ τ ∈ A) := by


  exact ⟨max_apts, hframes, fun σ τ hσ _hτ => hmax.1.2.1 σ τ⟩

/-- Final theorem on the maximal apartment system of $SL_V$: given that the
Iwahori subgroup is open, the Bruhat decomposition holds, and there is a
compact set containing it, the Iwahori is automatically closed and compact,
and the building has a maximal apartment system covering any pair of maximal
simplices. -/
theorem slv_maximal_apartment_system
    (C : DVRContext)
    [TopologicalSpace (Fin C.n → Fin C.n → C.𝔬)]

    (hB_open : IsOpen (IwahoriSubgroup C))

    (hBruhat : ∃ (I : Type*) (cells : I → Set (Fin C.n → Fin C.n → C.𝔬)),
      (∀ i, IsOpen (cells i)) ∧
      Set.univ = ⋃ i, cells i ∧
      (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧
      ∃ i₀, cells i₀ = IwahoriSubgroup C)

    (K : Set (Fin C.n → Fin C.n → C.𝔬))
    (hBK : IwahoriSubgroup C ⊆ K) (hK : IsCompact K)

    (max_apts : Set (Set (Simplex C)))
    (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts)
    (hmax : IsMaximalApartmentSystem C max_apts) :

    IsClosed (IwahoriSubgroup C) ∧
    IsCompact (IwahoriSubgroup C) ∧

    ∃ (max_apts' : Set (Set (Simplex C))),
      (∀ F : Frame C,
        Apartment C F ∈ max_apts') ∧
      (∀ σ τ : Simplex C,
        σ.IsMaximal C → τ.IsMaximal C →
        ∃ A ∈ max_apts', σ ∈ A ∧ τ ∈ A) := by

  have hclosed : IsClosed (IwahoriSubgroup C) :=
    open_plus_decomp_implies_closed (IwahoriSubgroup C) hB_open hBruhat

  have hcompact : IsCompact (IwahoriSubgroup C) :=
    closed_in_compact_is_compact (IwahoriSubgroup C) K hclosed hBK hK
  refine ⟨hclosed, hcompact, ?_⟩


  exact strong_transitivity_from_compact_open_iwahori C hB_open hcompact
    max_apts hframes hmax

end AffineBuildingSLVStrong
