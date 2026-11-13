/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Topology.Metrizable.Urysohn

open Set MeasureTheory Filter Topology

namespace MeasureTheory

/-- The collection of measurable sets in a measurable space forms a set algebra:
it contains the empty set, is closed under complements, and closed under finite unions.
This is the algebra-of-sets part of the σ-algebra structure. -/
theorem measurableSpace_isSetAlgebra (α : Type*) [m : MeasurableSpace α] :
    IsSetAlgebra {s : Set α | MeasurableSet s} where
  empty_mem := MeasurableSet.empty
  compl_mem := fun {s} (hs : MeasurableSet s) => hs.compl
  union_mem := fun {s t} (hs : MeasurableSet s) (ht : MeasurableSet t) => hs.union ht

/-- If sets $E_1, \dots, E_n$ are measurable, then $\bigcup_{k=1}^n E_k$ is measurable.
Stated for an arbitrary finite indexing `Finset`. -/
theorem sigmaAlgebra_finite_union_mem {α : Type*} [MeasurableSpace α]
    {ι : Type*} {f : ι → Set α} (S : Finset ι)
    (hf : ∀ i ∈ S, MeasurableSet (f i)) : MeasurableSet (⋃ i ∈ S, f i) :=
  S.measurableSet_biUnion hf

/-- Let $\mathcal{A}$ be an algebra (here, a σ-algebra), and let $\{E_n\}$ be a countable
collection of measurable sets. Then there exists a pairwise disjoint countable
collection $\{F_n\}$ of measurable sets such that $\bigcup_n E_n = \bigcup_n F_n$. -/
theorem exists_disjoint_seq_with_same_union {α : Type*} [MeasurableSpace α]
    (E : ℕ → Set α) (hE : ∀ n, MeasurableSet (E n)) :
    ∃ F : ℕ → Set α,
      (∀ n, MeasurableSet (F n)) ∧
      Pairwise (Function.onFun Disjoint F) ∧
      (⋃ n, F n) = (⋃ n, E n) :=
  ⟨disjointed E,
   fun n => MeasurableSet.disjointed hE n,
   disjoint_disjointed E,
   iUnion_disjointed⟩

/-- The Lebesgue (null-)measurable subsets of $\mathbb{R}$ form a σ-algebra:
the empty set is measurable, complements of measurable sets are measurable,
and countable unions of measurable sets are measurable. -/
theorem lebesgue_measurableSet_sigmaAlgebra :

    (NullMeasurableSet (∅ : Set ℝ) volume) ∧

    (∀ s : Set ℝ, NullMeasurableSet s volume →
      NullMeasurableSet sᶜ volume) ∧

    (∀ f : ℕ → Set ℝ, (∀ n, NullMeasurableSet (f n) volume) →
      NullMeasurableSet (⋃ n, f n) volume) :=
  ⟨nullMeasurableSet_empty, fun _ hs => hs.compl, fun _ hf => .iUnion hf⟩

/-- Continuity of measure for increasing sequences: if $E_1 \subset E_2 \subset \cdots$
is an increasing sequence of measurable sets, then
$\mu\left(\bigcup_{k=1}^{\infty} E_k\right) = \lim_{n \to \infty} \mu(E_n)$. -/
theorem continuity_measure_increasing {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : ℕ → Set α} (hE : Monotone E) :
    Tendsto (fun n => μ (E n)) atTop (𝓝 (μ (⋃ n, E n))) :=
  tendsto_measure_iUnion_atTop hE

/-- The pointwise limit of measurable functions is measurable: if
$f_n : \alpha \to \overline{\mathbb{R}}$ are measurable and $f_n(x) \to g(x)$ for all $x$,
then $g$ is measurable. -/
theorem measurable_of_pointwise_limit
    {α : Type*} [MeasurableSpace α]
    {f : ℕ → α → EReal} {g : α → EReal}
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Measurable g := by
  haveI : TopologicalSpace.PseudoMetrizableSpace EReal :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology EReal
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hlim)

end MeasureTheory

namespace MeasureTheory

/-- Simple functions are closed under scalar multiplication, addition, and multiplication:
for any simple functions $f, g$ and scalar $c$, the functions $c \cdot f$, $f + g$, and
$f \cdot g$ are again simple functions. -/
theorem simpleFunc_closed_scalar_add_mul
    {α : Type*} [MeasurableSpace α]
    {β : Type*} [AddCommMonoid β] [Mul β] {K : Type*} [SMul K β] :

    (∀ (c : K) (f : SimpleFunc α β), ∃ g : SimpleFunc α β, ⇑g = c • ⇑f) ∧

    (∀ (f g : SimpleFunc α β), ∃ h : SimpleFunc α β, ⇑h = ⇑f + ⇑g) ∧

    (∀ (f g : SimpleFunc α β), ∃ h : SimpleFunc α β, ⇑h = ⇑f * ⇑g) :=
  ⟨fun c f => ⟨c • f, rfl⟩, fun f g => ⟨f + g, rfl⟩, fun f g => ⟨f * g, rfl⟩⟩

end MeasureTheory

namespace MeasureTheory.SimpleFunc

/-- For any nonnegative measurable function $f : \alpha \to [0, \infty]$, there exists a
sequence of simple functions $\{\varphi_n\}$ such that:
(a) $0 \le \varphi_0(a) \le \varphi_1(a) \le \cdots \le f(a)$ for all $a$ (pointwise
increasing and dominated by $f$);
(b) $\varphi_n(a) \to f(a)$ pointwise; and
(c) for every bound $B < \infty$ and every $\varepsilon > 0$, there is an $N$ such that
$f(a) - \varphi_n(a) < \varepsilon$ for all $n \ge N$ and all $a$ with $f(a) \le B$
(uniform convergence on sets where $f$ is bounded). -/
theorem exists_monotone_tendsto
    {α : Type*} [MeasurableSpace α] {f : α → ENNReal} (hf : Measurable f) :
    ∃ φ : ℕ → SimpleFunc α ENNReal,
      ((∀ n a, φ n a ≤ f a) ∧ (Monotone fun n => (φ n : α → ENNReal))) ∧
      (∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (f a))) ∧
      (∀ B : ENNReal, B ≠ ⊤ → ∀ ε : ENNReal, ε ≠ 0 →
        ∃ N : ℕ, ∀ n ≥ N, ∀ a, f a ≤ B → f a - φ n a < ε) := by
  refine ⟨eapprox f, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    exact fun n a => (iSup_eapprox_apply hf a ▸ le_iSup (fun n => (eapprox f n) a) n)
  ·
    exact fun _ _ h a => monotone_eapprox f h a
  ·
    exact fun a => tendsto_eapprox hf a
  ·
    intro B hB ε hε
    by_cases hε_top : ε = ⊤
    · exact ⟨0, fun n _ a ha => by
        rw [hε_top]
        exact tsub_le_self.trans_lt (lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hB ha))⟩
    have hε_pos : (0 : ENNReal) < ε := pos_iff_ne_zero.mpr hε
    have hB_lt : B < ⊤ := lt_top_iff_ne_top.mpr hB
    obtain ⟨r, hr_pos, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε_pos
    have hr_real_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast ENNReal.coe_pos.mp hr_pos
    obtain ⟨q, hq_pos_real, hqr⟩ := exists_rat_btwn hr_real_pos
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    have hq_lt_ε : ENNReal.ofReal (q : ℝ) < ε := by
      calc ENNReal.ofReal (q : ℝ) < (r : ENNReal) := by
              rw [← ENNReal.ofReal_coe_nnreal]
              exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hq_pos)).mpr hqr
        _ < ε := hrε
    set k := Nat.ceil (B.toReal / (q : ℝ))
    set N := 1 + (Finset.range (k + 1)).sup (fun i => Encodable.encode ((↑i : ℚ) * q))
    use N
    intro n hn a ha
    by_cases hfa_zero : f a = 0
    · simp [hfa_zero, hε_pos]
    have hfa_lt : f a < ⊤ := lt_of_le_of_lt ha hB_lt
    have hfa_ne_top : f a ≠ ⊤ := hfa_lt.ne
    set j := Nat.floor ((f a).toReal / (q : ℝ))
    have h_div_nn : (0 : ℝ) ≤ (f a).toReal / (q : ℝ) :=
      div_nonneg ENNReal.toReal_nonneg (le_of_lt hq_pos)
    have h_j_le : (↑j : ℝ) * (q : ℝ) ≤ (f a).toReal := by
      nlinarith [Nat.floor_le h_div_nn, div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
    have h_diff_lt : (f a).toReal - ↑j * (q : ℝ) < (q : ℝ) := by
      nlinarith [Nat.lt_floor_add_one ((f a).toReal / (q : ℝ)),
                 div_mul_cancel₀ (f a).toReal (ne_of_gt hq_pos)]
    have hj_le_k : j ≤ k :=
      (Nat.floor_le_ceil _).trans (Nat.ceil_le_ceil
        (div_le_div_of_nonneg_right ((ENNReal.toReal_le_toReal hfa_ne_top hB).mpr ha)
          (le_of_lt hq_pos)))
    have h_encode_lt : Encodable.encode ((↑j : ℚ) * q) < N := by
      have hmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have h : Encodable.encode ((↑j : ℚ) * q) ≤
          (Finset.range (k + 1)).sup (fun i => Encodable.encode ((↑i : ℚ) * q)) :=
        Finset.le_sup_of_le hmem le_rfl
      omega
    have h_embed_val : ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) =
        ENNReal.ofReal (↑j * (q : ℝ)) := by
      rw [ennrealRatEmbed_encode]; simp [ENNReal.ofReal, Rat.cast_mul, Rat.cast_natCast]
    have h_embed_le : ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤ f a := by
      rw [h_embed_val, ENNReal.ofReal_le_iff_le_toReal hfa_ne_top]; exact_mod_cast h_j_le
    have h_eapprox_ge : ENNReal.ofReal (↑j * (q : ℝ)) ≤ eapprox f n a := by
      rw [← h_embed_val]
      have h_step : ennrealRatEmbed (Encodable.encode ((↑j : ℚ) * q)) ≤
          eapprox f (Encodable.encode ((↑j : ℚ) * q) + 1) a := by
        have h := approx_apply a hf (i := ennrealRatEmbed)
          (n := Encodable.encode ((↑j : ℚ) * q) + 1)
        change ennrealRatEmbed _ ≤ (approx ennrealRatEmbed f _) a; rw [h]
        refine le_trans ?_ (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _)))
        simp [h_embed_le]
      exact h_step.trans (monotone_eapprox f (by omega) a)
    calc f a - eapprox f n a
        ≤ f a - ENNReal.ofReal (↑j * (q : ℝ)) := tsub_le_tsub_left h_eapprox_ge _
      _ < ENNReal.ofReal (q : ℝ) := by
          rw [← ENNReal.ofReal_toReal hfa_ne_top]
          rw [← ENNReal.ofReal_sub _ (show (0 : ℝ) ≤ ↑j * (q : ℝ) from by positivity)]
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr h_diff_lt
      _ < ε := hq_lt_ε

end MeasureTheory.SimpleFunc

open ENNReal

namespace MeasureTheory

/-- For all $a \in \mathbb{R}$, the open interval $(a, \infty)$ is measurable. -/
theorem measurableSet_Ioi_real (a : ℝ) : MeasurableSet (Set.Ioi a) :=
  measurableSet_Ioi

end MeasureTheory
