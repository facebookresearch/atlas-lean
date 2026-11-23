/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section6

open Finset BigOperators

namespace AlgebraicTopologyI

noncomputable section

/-- The standard $n$-simplex is contractible: it is a convex subset of $\mathbf{R}^{n+1}$ and
hence has the homotopy type of a point (used to verify acyclicity of star-shaped chain complexes,
Proposition 5.13). -/
instance stdSimplex_contractible (n : ℕ) :
    ContractibleSpace ↥(stdSimplex ℝ (Fin (n + 1))) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩

/-- Any two singular $n$-simplices in the one-point space `PUnit` are equal, because all maps
into a subsingleton agree. -/
lemma singularSimplex_punit_unique (n : ℕ) (σ τ : SingularSimplex n PUnit) : σ = τ :=
  ContinuousMap.ext fun _ => Subsingleton.elim _ _

/-- Every singular $n$-chain on `PUnit` is an integer multiple of a fixed generating
$n$-simplex, since all singular simplices in `PUnit` coincide. -/
lemma singularChains_punit_multiple (n : ℕ) (σ₀ : SingularSimplex n PUnit)
    (c : SingularChains n PUnit) :
    ∃ m : ℤ, c = m • FreeAbelianGroup.of σ₀ := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => exact ⟨0, by simp⟩
  | of a => exact ⟨1, by rw [one_smul, singularSimplex_punit_unique n a σ₀]⟩
  | neg a => exact ⟨-1, by simp [singularSimplex_punit_unique n a σ₀]⟩
  | add a b ha hb =>
    obtain ⟨m, rfl⟩ := ha; obtain ⟨k, rfl⟩ := hb
    exact ⟨m + k, by rw [add_smul]⟩

/-- If an integer multiple `m • FreeAbelianGroup.of a` vanishes in a free abelian group, then the
scalar `m` itself must be zero (since the generator `a` is non-torsion). -/
lemma freeAbelianGroup_smul_of_eq_zero {T : Type*} (a : T) (m : ℤ)
    (h : m • FreeAbelianGroup.of a = (0 : FreeAbelianGroup T)) : m = 0 := by
  have : (FreeAbelianGroup.lift (fun _ => (1 : ℤ))) (m • FreeAbelianGroup.of a) = 0 := by
    rw [h, map_zero]
  rw [map_zsmul, FreeAbelianGroup.lift_apply_of] at this
  simpa using this

/-- The alternating sum $\sum_{i<N} (-1)^i$ equals $1$ when $N$ is odd and $0$ otherwise. -/
lemma alternating_sum_range_parity (N : ℕ) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i = if Odd N then 1 else 0 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]; simp only [Nat.odd_add_one]
    by_cases hk : Odd k
    · simp only [hk, not_true_eq_false, ite_true, ite_false]; rw [hk.neg_one_pow]; ring
    · simp only [hk, not_false_eq_true, ite_false, ite_true]
      rw [(Nat.not_odd_iff_even.mp hk).neg_one_pow]; ring

/-- The alternating sum over `Fin (n + 2)` evaluates to $1$ if $n$ is odd and $0$ otherwise;
the version of `alternating_sum_range_parity` indexed by face indices of an $(n+1)$-simplex. -/
lemma alternating_sum_fin_parity (n : ℕ) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) = if Odd n then 1 else 0 := by
  rw [Fin.sum_univ_eq_sum_range, alternating_sum_range_parity]
  simp only [show Odd (n + 2) ↔ Odd n from
    ⟨fun ⟨k, hk⟩ => ⟨k - 1, by omega⟩, fun ⟨k, hk⟩ => ⟨k + 1, by omega⟩⟩]

/-- The boundary of a singular $(n+1)$-simplex on `PUnit` equals the alternating sum
$\sum_i (-1)^i$ times a fixed $n$-simplex generator, since all face simplices in `PUnit` agree. -/
lemma boundaryMap_punit_gen (n : ℕ) (σ : SingularSimplex (n + 1) PUnit)
    (σ₀ : SingularSimplex n PUnit) :
    boundaryMap n PUnit (FreeAbelianGroup.of σ) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀ := by
  show (FreeAbelianGroup.lift (fun σ =>
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (SingularSimplex.face i σ)))
    (FreeAbelianGroup.of σ) = _
  erw [FreeAbelianGroup.lift_apply_of]
  conv_rhs => rw [show (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀ =
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • FreeAbelianGroup.of σ₀
    from by rw [← Finset.sum_smul]]
  simp_rw [singularSimplex_punit_unique n _ σ₀]

/-- Given a point $t$ in the standard $(n+1)$-simplex, drop its first coordinate and rescale the
remaining coordinates by $1/(1-t_0)$ to land in the standard $n$-simplex; this is the inverse to
the front-face inclusion away from the apex $t_0 = 1$. -/
noncomputable def rescaleTail (n : ℕ) (t : ↥(stdSimplex ℝ (Fin (n + 2)))) :
    ↥(stdSimplex ℝ (Fin (n + 1))) := by
  by_cases h : t.1 0 = 1
  · exact ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  · have ht0_lt : t.1 0 < 1 := by
      have h1 : t.1 0 ≤ ∑ i : Fin (n + 2), t.1 i :=
        Finset.single_le_sum (fun i _ => t.2.1 i) (Finset.mem_univ 0)
      exact lt_of_le_of_ne (by linarith [t.2.2]) h
    have h_pos : (1 : ℝ) - t.1 0 > 0 := by linarith
    have htail : ∑ i : Fin (n + 1), t.1 (Fin.succ i) = 1 - t.1 0 := by
      have := t.2.2; rw [Fin.sum_univ_succ] at this; linarith
    refine ⟨fun i => t.1 (Fin.succ i) / (1 - t.1 0), fun i => ?_, ?_⟩
    · exact div_nonneg (t.2.1 (Fin.succ i)) (le_of_lt h_pos)
    · rw [show ∑ i : Fin (n+1), t.1 (Fin.succ i) / (1 - t.1 0) =
          (∑ i : Fin (n+1), t.1 (Fin.succ i)) / (1 - t.1 0) from by
          simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]]
      rw [htail, div_self (ne_of_gt h_pos)]

/-- The set-theoretic (pre-continuity) cone map: for a base point $b$ and an $(n+1)$-simplex
$\sigma$ in the standard $m$-simplex, send $t \in \Delta^{n+1}$ to the convex combination
$t_0 \cdot b + (1 - t_0) \cdot \sigma(\text{rescaleTail}(t))$. -/
noncomputable def coneRawSimplex (m n : ℕ) (b : ↥(stdSimplex ℝ (Fin m)))
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin m))))
    (t : ↥(stdSimplex ℝ (Fin (n + 2)))) : ↥(stdSimplex ℝ (Fin m)) :=
  let s := rescaleTail n t
  let σs := σ s
  ⟨fun j => t.1 0 * b.1 j + (1 - t.1 0) * σs.1 j,
   (convex_stdSimplex ℝ (Fin m)) b.2 σs.2 (t.2.1 0)
     (by have h1 : t.1 0 ≤ ∑ i : Fin (n+2), t.1 i :=
            Finset.single_le_sum (fun i _ => t.2.1 i) (Finset.mem_univ 0)
         linarith [t.2.2])
     (by linarith)⟩


/-- Every coordinate of a point in the standard $m$-simplex is at most $1$, because the
coordinates are nonnegative and sum to $1$. -/
lemma stdSimplex_coord_le_one {m : ℕ} (x : ↥(stdSimplex ℝ (Fin m))) (i : Fin m) :
    x.1 i ≤ 1 := by
  have hi : x.1 i ≤ ∑ j : Fin m, x.1 j :=
    Finset.single_le_sum (fun j _ => x.2.1 j) (Finset.mem_univ i)
  linarith [x.2.2]

/-- The raw cone map `coneRawSimplex` is continuous on the standard $(n+1)$-simplex; the apex
$t_0 = 1$ is handled separately since the factor $(1 - t_0)$ kills the discontinuity of the
`rescaleTail` map there. -/
theorem coneSimplex_continuous (m n : ℕ) (b : ↥(stdSimplex ℝ (Fin m)))
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin m)))) :
    Continuous (coneRawSimplex m n b σ) := by

  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro j
  show Continuous (fun t => (coneRawSimplex m n b σ t).1 j)
  rw [continuous_iff_continuousAt]
  intro t

  have hfun_eq : ∀ s : ↥(stdSimplex ℝ (Fin (n + 2))),
      (coneRawSimplex m n b σ s).1 j =
        s.1 0 * b.1 j + (1 - s.1 0) * (σ (rescaleTail n s)).1 j := fun _ => rfl
  by_cases ht : t.1 0 = 1
  ·
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have h_coord : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) => s.1 0) t :=
      ((continuous_apply 0).comp continuous_subtype_val).continuousAt
    rw [ContinuousAt, ht, Metric.tendsto_nhds] at h_coord
    filter_upwards [h_coord ε hε] with s hs
    rw [Real.dist_eq] at hs

    have hvalt : (coneRawSimplex m n b σ t).1 j = b.1 j := by
      simp [coneRawSimplex, ht]
    rw [Real.dist_eq, show (coneRawSimplex m n b σ s).1 j - (coneRawSimplex m n b σ t).1 j =
        (1 - s.1 0) * ((σ (rescaleTail n s)).1 j - b.1 j) from by
      rw [hfun_eq, hvalt]; ring, abs_mul]
    have hbnd : |(σ (rescaleTail n s)).1 j - b.1 j| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [(σ (rescaleTail n s)).2.1 j, stdSimplex_coord_le_one b j],
             by linarith [b.2.1 j, stdSimplex_coord_le_one (σ (rescaleTail n s)) j]⟩
    calc |1 - s.1 0| * |(σ (rescaleTail n s)).1 j - b.1 j|
        ≤ |1 - s.1 0| * 1 := mul_le_mul_of_nonneg_left hbnd (abs_nonneg _)
      _ = |1 - s.1 0| := mul_one _
      _ = |s.1 0 - 1| := abs_sub_comm _ _
      _ < ε := hs
  ·
    have hopen : IsOpen {s : ↥(stdSimplex ℝ (Fin (n + 2))) | s.1 0 ≠ 1} :=
      (isOpen_ne.preimage (continuous_apply 0)).preimage continuous_subtype_val

    have h_rescale_at : ContinuousAt (rescaleTail n) t := by
      rw [Topology.IsInducing.subtypeVal.continuousAt_iff]


      have h_loc : ∀ᶠ s in nhds t, (Subtype.val ∘ rescaleTail n) s =
          (fun s : ↥(stdSimplex ℝ (Fin (n+2))) =>
            (fun i : Fin (n+1) => s.1 (Fin.succ i) / (1 - s.1 0))) s := by
        filter_upwards [hopen.mem_nhds ht] with s hs
        simp [Function.comp, rescaleTail, dif_neg hs]

      have h_div : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) =>
          (fun i : Fin (n+1) => s.1 (Fin.succ i) / (1 - s.1 0))) t := by
        apply continuousAt_pi.mpr
        intro i
        exact ((continuous_apply (Fin.succ i)).comp continuous_subtype_val).continuousAt.div
          ((continuous_const.sub ((continuous_apply 0).comp continuous_subtype_val)).continuousAt)
          (by linarith [stdSimplex_coord_le_one t 0,
              lt_of_le_of_ne (stdSimplex_coord_le_one t 0) ht])
      exact h_div.congr (h_loc.mono (fun s hs => hs.symm))

    have hg : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) =>
        (σ (rescaleTail n s)).1 j) t :=
      ((continuous_apply j).comp continuous_subtype_val).continuousAt.comp
        (σ.continuous.continuousAt.comp h_rescale_at)
    have ht0 : ContinuousAt (fun s : ↥(stdSimplex ℝ (Fin (n+2))) => s.1 0) t :=
      ((continuous_apply 0).comp continuous_subtype_val).continuousAt
    exact (ht0.mul continuousAt_const).add
      ((continuousAt_const.sub ht0).mul hg) |>.congr
        (Filter.Eventually.of_forall (fun s => (hfun_eq s).symm))

/-- The cone (as a continuous map) on a singular $(n+1)$-simplex `σ` with apex `b` in a single
standard simplex; bundles `coneRawSimplex` with its continuity proof. -/
noncomputable def coneSimplex₁ (m n : ℕ) (b : ↥(stdSimplex ℝ (Fin m)))
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin m)))) :
    C(↥(stdSimplex ℝ (Fin (n + 2))), ↥(stdSimplex ℝ (Fin m))) :=
  ⟨coneRawSimplex m n b σ, coneSimplex_continuous m n b σ⟩

/-- Cone construction on a singular $n$-simplex valued in the product of two standard simplices
$\Delta^p \times \Delta^q$, with apex the pair of base vertices; this produces an $(n+1)$-simplex
used to witness acyclicity of the product chain complex. -/
noncomputable def coneSimplex (p q n : ℕ)
    (σ : SingularSimplex n
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    SingularSimplex (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) :=
  let b₁ : ↥(stdSimplex ℝ (Fin (p+1))) := ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  let b₂ : ↥(stdSimplex ℝ (Fin (q+1))) := ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  let σ₁ : C(↥(stdSimplex ℝ (Fin (n+1))), ↥(stdSimplex ℝ (Fin (p+1)))) :=
    ContinuousMap.fst.comp σ
  let σ₂ : C(↥(stdSimplex ℝ (Fin (n+1))), ↥(stdSimplex ℝ (Fin (q+1)))) :=
    ContinuousMap.snd.comp σ
  (coneSimplex₁ (p+1) n b₁ σ₁).prodMk (coneSimplex₁ (q+1) n b₂ σ₂)

/-- The chain-level cone operator $h: S_n(\Delta^p \times \Delta^q) \to S_{n+1}(\Delta^p \times
\Delta^q)$ obtained by extending `coneSimplex` linearly; it serves as the chain homotopy from the
identity to the augmentation map. -/
noncomputable def coneChain (p q n : ℕ) :
    SingularChains n (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) →+
    SingularChains (n + 1) (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) :=
  FreeAbelianGroup.map (coneSimplex p q n)


/-- The zeroth face of the cone $c(\sigma)$ on a simplex $\sigma$ recovers $\sigma$ itself,
because the $0$-th face of $\Delta^{n+2}$ corresponds to the bottom face $t_0 = 0$ of the cone. -/
theorem coneSimplex_face_zero (p q n : ℕ)
    (σ : SingularSimplex (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    SingularSimplex.face 0 (coneSimplex p q (n + 1) σ) = σ := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, ContinuousMap.comp_apply, coneSimplex, ContinuousMap.prodMk,
    coneSimplex₁, ContinuousMap.coe_mk, coneRawSimplex]

  have h0 : (faceInclusion (n + 1) 0 t).1 0 = 0 := by
    simp [faceInclusion]

  have hne : (faceInclusion (n + 1) 0 t).1 0 ≠ 1 := by rw [h0]; exact one_ne_zero.symm

  have h_rescale : rescaleTail (n + 1) (faceInclusion (n + 1) 0 t) = t := by
    simp only [rescaleTail, dif_neg hne]
    ext i
    simp only [h0, sub_zero, div_one]
    simp [faceInclusion]
  simp only [h0, zero_mul, zero_add, sub_zero, one_mul, h_rescale]
  simp

/-- Inserting a value at position `i.succ` in a tuple leaves the first coordinate unchanged,
since the insertion position is strictly positive. -/
lemma insertNth_succ_zero' (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → ℝ) :
    @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 f 0 = f 0 := by
  conv_lhs => rw [show (0 : Fin (n + 3)) = i.succ.succAbove 0 from
    (Fin.succ_succAbove_zero i).symm]
  exact @Fin.insertNth_apply_succAbove (n + 2) (fun _ => ℝ) i.succ 0 f 0

/-- Compatibility of `Fin.insertNth` with the successor map: inserting at `i.succ` on the
`succ`-shifted index equals inserting at `i` on the shifted tail. -/
lemma insertNth_succ_succ' (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → ℝ)
    (j : Fin (n + 2)) :
    @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 f (Fin.succ j) =
    @Fin.insertNth (n + 1) (fun _ => ℝ) i 0 (fun k : Fin (n + 1) => f (Fin.succ k)) j := by
  by_cases hji : j = i
  · subst hji
    rw [@Fin.insertNth_apply_same (n + 1) (fun _ => ℝ)]
    exact @Fin.insertNth_apply_same (n + 2) (fun _ => ℝ) j.succ 0 f
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (y := i) hji
    subst hk
    rw [@Fin.insertNth_apply_succAbove (n + 1) (fun _ => ℝ) i 0 _ k]
    conv_lhs => rw [show Fin.succ (i.succAbove k) = i.succ.succAbove (Fin.succ k) from
      (Fin.succ_succAbove_succ i k).symm]
    exact @Fin.insertNth_apply_succAbove (n + 2) (fun _ => ℝ) i.succ 0 f (Fin.succ k)

/-- Compatibility of `rescaleTail` with the $i$-th face inclusion (for $i > 0$): rescaling after
inclusion equals inclusion after rescaling. This is the key combinatorial identity behind
`coneSimplex_face_succ`. -/
lemma rescaleTail_faceInclusion_succ (n : ℕ) (i : Fin (n + 2))
    (t : ↥(stdSimplex ℝ (Fin (n + 2)))) (ht : t.1 0 ≠ 1) :
    rescaleTail (n + 1) ⟨Fin.insertNth i.succ 0 t.1,
      faceMap_mem_stdSimplex (n + 1) i.succ t.1 t.2⟩ =
    ⟨Fin.insertNth i 0 (rescaleTail n t).1,
      faceMap_mem_stdSimplex n i (rescaleTail n t).1 (rescaleTail n t).2⟩ := by
  have ht0_eq : @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 t.1 0 = t.1 0 :=
    insertNth_succ_zero' n i t.1
  have h1 : @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 t.1 0 ≠ 1 := by rw [ht0_eq]; exact ht
  apply Subtype.ext
  funext k
  simp only [rescaleTail, dif_neg h1, dif_neg ht]
  rw [insertNth_succ_succ' n i t.1 k, ht0_eq]
  by_cases hki : k = i
  · subst hki
    simp
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (y := i) hki
    subst hj
    simp [@Fin.insertNth_apply_succAbove (n + 1) (fun _ => ℝ)]

/-- For positive face indices `i.succ`, the face of the cone equals the cone of the face:
$d_{i+1}(c(\sigma)) = c(d_i \sigma)$. This together with `coneSimplex_face_zero` is what makes
`coneChain` a chain homotopy. -/
theorem coneSimplex_face_succ (p q n : ℕ) (i : Fin (n + 2))
    (σ : SingularSimplex (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    SingularSimplex.face i.succ (coneSimplex p q (n + 1) σ) =
      coneSimplex p q n (SingularSimplex.face i σ) := by
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, ContinuousMap.comp_apply, coneSimplex, coneSimplex₁,
    ContinuousMap.prod_eval, faceInclusion, ContinuousMap.coe_mk]
  have ht0_eq : @Fin.insertNth (n + 2) (fun _ => ℝ) i.succ 0 t.1 0 = t.1 0 :=
    insertNth_succ_zero' n i t.1

  by_cases ht : t.1 0 = 1
  ·
    apply Prod.ext <;> apply Subtype.ext <;> funext j <;>
      simp only [coneRawSimplex, ContinuousMap.comp_apply, ContinuousMap.coe_mk, ht0_eq, ht] <;>
      ring
  ·
    have h_rescale := rescaleTail_faceInclusion_succ n i t ht
    apply Prod.ext <;> apply Subtype.ext <;> funext j <;>
      simp only [coneRawSimplex, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ht0_eq, h_rescale]


/-- The chain-level cone formula $d \circ h + h \circ d = \mathrm{id}$ on chains in
$\Delta^p \times \Delta^q$: the boundary of the cone of $c$ equals $c$ minus the cone of its
boundary. This realises `coneChain` as a chain contraction. -/
theorem coneSimplex_boundary (p q n : ℕ)
    (c : SingularChains (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))) :
    boundaryMap (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1))))
      (coneChain p q (n + 1) c) =
    c - coneChain p q n (boundaryMap n
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) c) := by

  induction c using FreeAbelianGroup.induction_on with
  | zero =>
    show (boundaryMap _ _) ((coneChain p q (n + 1)) 0) =
      0 - (coneChain p q n) ((boundaryMap _ _) 0)
    simp only [AddMonoidHom.map_zero, sub_zero]
  | of σ =>

    change boundaryMap (n + 1) _ ((FreeAbelianGroup.map (coneSimplex p q (n + 1)))
      (FreeAbelianGroup.of σ)) = _
    rw [FreeAbelianGroup.map_of_apply]

    change (FreeAbelianGroup.lift (fun τ =>
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (SingularSimplex.face i τ)))
      (FreeAbelianGroup.of (coneSimplex p q (n + 1) σ)) = _
    erw [FreeAbelianGroup.lift_apply_of]

    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul]

    rw [coneSimplex_face_zero]

    simp_rw [coneSimplex_face_succ p q n _ σ]

    simp_rw [show ∀ j : Fin (n + 2), (j.succ : ℕ) = (j : ℕ) + 1 from fun _ => rfl,
      pow_succ, mul_neg_one, neg_smul]

    rw [Finset.sum_neg_distrib]


    rw [sub_eq_add_neg]
    congr 1

    congr 1

    symm
    change (FreeAbelianGroup.map (coneSimplex p q n))
      ((FreeAbelianGroup.lift (fun τ =>
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          FreeAbelianGroup.of (SingularSimplex.face i τ)))
        (FreeAbelianGroup.of σ)) = _
    erw [FreeAbelianGroup.lift_apply_of]
    rw [map_sum]
    congr 1; ext j
    rw [map_zsmul, FreeAbelianGroup.map_of_apply]
  | neg σ ih =>
    have h1 : (coneChain p q (n + 1)) (-FreeAbelianGroup.of σ) =
      -((coneChain p q (n + 1)) (FreeAbelianGroup.of σ)) := map_neg _ _
    have h2 : (boundaryMap n _) (-FreeAbelianGroup.of σ) =
      -((boundaryMap n _) (FreeAbelianGroup.of σ)) := map_neg _ _
    have h3 : (coneChain p q n) (-(boundaryMap n _ (FreeAbelianGroup.of σ))) =
      -((coneChain p q n) ((boundaryMap n _) (FreeAbelianGroup.of σ))) := map_neg _ _
    rw [h1, map_neg, ih, h2, h3]
    simp only [sub_eq_add_neg, neg_neg, neg_add_rev]
    abel
  | add a b iha ihb =>
    have h1 : (coneChain p q (n + 1)) (a + b) =
      (coneChain p q (n + 1)) a + (coneChain p q (n + 1)) b := map_add _ _ _
    have h2 : (boundaryMap n _) (a + b) =
      (boundaryMap n _) a + (boundaryMap n _) b := map_add _ _ _
    have h3 : (coneChain p q n) ((boundaryMap n _) a + (boundaryMap n _) b) =
      (coneChain p q n) ((boundaryMap n _) a) +
      (coneChain p q n) ((boundaryMap n _) b) := map_add _ _ _
    rw [h1, map_add, iha, ihb, h2, h3]
    simp only [sub_eq_add_neg, neg_add_rev]
    abel

/-- Acyclicity of the singular chain complex on a product of standard simplices in positive
degrees: every $(n+1)$-cycle in $\Delta^p \times \Delta^q$ is a boundary. This is the technical
heart of Proposition 5.13 ($S_*(X) \to \mathbf{Z}$ is a chain homotopy equivalence for star-shaped
$X$) for the case of products of simplices. -/
theorem stdSimplex_prod_acyclic (p q n : ℕ)
    (c : SingularChains (n + 1)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))))
    (hc : boundaryMap n
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) c = 0) :
    ∃ d : SingularChains (n + 2)
      (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))),
      boundaryMap (n + 1)
        (↥(stdSimplex ℝ (Fin (p+1))) × ↥(stdSimplex ℝ (Fin (q+1)))) d = c := by
  refine ⟨coneChain p q (n + 1) c, ?_⟩
  rw [coneSimplex_boundary p q n c, hc, map_zero, sub_zero]

end

end AlgebraicTopologyI
