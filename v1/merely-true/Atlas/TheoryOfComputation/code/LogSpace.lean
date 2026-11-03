/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Atlas.TheoryOfComputation.code.SpaceComplexity
import Atlas.TheoryOfComputation.code.Complexity
open SpaceComplexity
open TuringMachine

namespace LogSpace

/-- Base-2 logarithm on `ℕ`, used as the canonical space bound for the class `L = SPACE(log n)`. -/
def log : ℕ → ℕ := Nat.log 2

/-- A log-space Turing machine configuration `(q, p_1, p_2, t)` consisting of
the current state, the input-tape head position `p_1`, the work-tape head
position `p_2`, and the contents `t` of the work tape. -/
structure LogSpaceConfig (Q : Type) (Γ : Type) where
  state : Q
  inputHeadPos : ℕ
  workHeadPos : ℕ
  workTape : ℕ → Γ

/-- The type of log-space configurations restricted so that the input head lies
in `Fin n`, the work head lies in `Fin s`, and the work tape is encoded as a
function `Fin s → Γ`. This is a finite type whenever `Q` and `Γ` are. -/
def BoundedLogSpaceConfig (Q : Type) (Γ : Type) (n s : ℕ) :=
  Q × Fin n × Fin s × (Fin s → Γ)

/-- `BoundedLogSpaceConfig Q Γ n s` is a finite type, inherited from the
product structure of its components. -/
noncomputable instance BoundedLogSpaceConfig.fintype
    (Q : Type) (Γ : Type) [Fintype Q] [Fintype Γ] (n s : ℕ) :
    Fintype (BoundedLogSpaceConfig Q Γ n s) :=
  inferInstanceAs (Fintype (Q × Fin n × Fin s × (Fin s → Γ)))

/-- Convert an ordinary Turing-machine configuration into the log-space
configuration view by taking the input head position to be `|c.headPos|`,
initializing the work head to `0`, and copying the tape as the work tape. -/
def LogSpaceConfig.ofConfig
    (c : TuringMachine.Config Q Γ) : LogSpaceConfig Q Γ where
  state := c.state
  inputHeadPos := c.headPos.natAbs
  workHeadPos := 0
  workTape := fun i => c.tape (Int.ofNat i)

/-- The complexity class `L = SPACE(log n)`: `A ∈ L` iff `A` is decided by some
deterministic TM in space `O(log n)`. -/
def InL {Γ : Type} (A : Set (List Γ)) : Prop :=
  InSPACE log A

/-- The complexity class `NL = NSPACE(log n)`: `A ∈ NL` iff `A` is decided by
some nondeterministic TM in space `O(log n)`. -/
def InNL {Γ : Type} (A : Set (List Γ)) : Prop :=
  InNSPACE log A

/-- `coNSPACE(f)`: `A ∈ coNSPACE(f)` iff the complement of `A` lies in
`NSPACE(f)`. -/
def InCoNSPACE {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  InNSPACE f Aᶜ

/-- The class `coNL = coNSPACE(log n)`: `A ∈ coNL` iff `Aᶜ ∈ NL`. -/
def InCoNL {Γ : Type} (A : Set (List Γ)) : Prop :=
  InCoNSPACE log A

/-- `IsAtLeastLog f` asserts that `f` grows at least as fast as `log₂`, i.e.
`log₂ n ≤ f n` for every `n`. This is the standard hypothesis under which
Immerman–Szelepcsényi gives `NSPACE(f) = coNSPACE(f)`. -/
def IsAtLeastLog (f : ℕ → ℕ) : Prop :=
  ∀ n, Nat.log 2 n ≤ f n




/-- `BoundedReachable G d s t` holds when `t` is reachable from `s` in the
graph `G` using at most `d` edge steps. The `weaken` constructor pads a
`d`-step path into a `(d+1)`-step path, ensuring monotonicity in `d`. -/
inductive BoundedReachable {V : Type*} (G : V → V → Prop) : ℕ → V → V → Prop where
  | refl (s : V) : BoundedReachable G 0 s s
  | step {d : ℕ} {s u t : V} : BoundedReachable G d s u → G u t →
      BoundedReachable G (d + 1) s t
  | weaken {d : ℕ} {s t : V} : BoundedReachable G d s t →
      BoundedReachable G (d + 1) s t

/-- The set of vertices reachable from `s` in `G` within at most `d` steps. -/
def reachableSet {V : Type*} (G : V → V → Prop) (d : ℕ) (s : V) : Set V :=
  {u | BoundedReachable G d s u}

/-- The count `c_d = |reachableSet G d s|` of vertices reachable from `s`
within `d` steps. In the Immerman–Szelepcsényi proof this is the quantity
computed inductively by an NL machine. -/
noncomputable def reachableCount {V : Type*} (G : V → V → Prop) (d : ℕ) (s : V) : ℕ :=
  Set.ncard (reachableSet G d s)

/-- Inductive step in the Immerman–Szelepcsényi argument: given an NL
procedure for computing `c_d`, one can build an NL procedure for deciding the
distance-`(d+1)` path predicate, from which an NL procedure for `c_{d+1}` is
obtained. This packages those two abstract steps into the successor case. -/
theorem nl_config_compute
    {NLComputes_cd NLDecides_pathd : ℕ → Prop}
    (thm_cd_to_pathd_succ : ∀ d, NLComputes_cd d → NLDecides_pathd (d + 1))
    (counting_to_cd : ∀ d, NLDecides_pathd d → NLComputes_cd d)
    (d : ℕ) (h : NLComputes_cd d) :
    NLComputes_cd (d + 1) :=
  counting_to_cd (d + 1) (thm_cd_to_pathd_succ d h)

section LSubsetP

variable {Q Γ : Type} [DecidableEq Q]

/-- If `c` is a halting configuration of `M`, then `M.step c = c`: halting
configurations are fixed points of the transition function. -/
lemma step_eq_of_isHaltConfig (M : TuringMachine.TM Q Γ) (c : TuringMachine.Config Q Γ)
    (h : M.isHaltConfig c) : M.step c = c := by
  unfold TuringMachine.TM.step
  simp only [TuringMachine.TM.isHaltConfig, TuringMachine.TM.isAcceptConfig,
    TuringMachine.TM.isRejectConfig] at h
  rcases h with h | h <;> simp [h]

/-- Once `M` has halted by step `n`, running it further does nothing:
`M.run c m = M.run c n` for every `m ≥ n`. -/
lemma run_eq_of_isHaltConfig (M : TuringMachine.TM Q Γ) (c : TuringMachine.Config Q Γ)
    {n m : ℕ} (hn : n ≤ m) (h : M.isHaltConfig (M.run c n)) :
    M.run c m = M.run c n := by
  induction m with
  | zero => simp [Nat.le_zero.mp hn]
  | succ m ih =>
    by_cases hle : n ≤ m
    · simp only [TuringMachine.TM.run]
      rw [ih hle]; exact step_eq_of_isHaltConfig M _ h
    · have : n = m + 1 := by omega
      subst this; rfl

/-- Monotonicity of halting: if `M` is in a halting configuration after `n`
steps and `n ≤ m`, then it is also in a halting configuration after `m` steps. -/
lemma isHaltConfig_mono (M : TuringMachine.TM Q Γ) (c : TuringMachine.Config Q Γ)
    {n m : ℕ} (hn : n ≤ m) (h : M.isHaltConfig (M.run c n)) :
    M.isHaltConfig (M.run c m) := by
  rw [run_eq_of_isHaltConfig M c hn h]; exact h

end LSubsetP

/-- A deterministic TM running in space `g(n)` must halt within
`O(2^{O(g(n))})` steps, since otherwise some configuration would repeat and
the machine would loop. Concretely there exist a time bound `t` and a
constant `K > 0` with `M.runsInTime t` and `t n ≤ K · 2^(K · g n)`. -/
theorem space_bounded_decider_poly_time {Q Γ : Type} [DecidableEq Q] [Fintype Q] [Fintype Γ]
    (M : TuringMachine.TM Q Γ) (g : ℕ → ℕ) (hSpace : TMRunsInSpace M g) :
    ∃ (t : ℕ → ℕ) (K : ℕ), M.runsInTime t ∧ 0 < K ∧ ∀ n, t n ≤ K * 2 ^ (K * g n) := by
  classical
  set qc := Fintype.card Q
  set gc := Fintype.card Γ
  set K := max (qc * gc) (Nat.clog 2 (2 * gc)) + 1
  have hK_pos : 0 < K := by omega
  have hK_ge_qc_gc : qc * gc < K := by omega
  have hK_ge_clog : Nat.clog 2 (2 * gc) < K := by omega

  have hgc_bound : 2 * gc ≤ 2 ^ K :=
    (Nat.le_pow_clog (by norm_num) (2 * gc)).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))

  have hgc_le : gc ≤ 2 ^ (K - 1) := by
    have h2 : K = (K - 1) + 1 := by omega
    rw [h2, pow_succ] at hgc_bound; omega

  have hexp_ge : ∀ n : ℕ, n + 2 ≤ 2 ^ (n + 1) := by
    intro n; induction n with
    | zero => norm_num
    | succ n ih =>
      calc n + 3 ≤ (n + 2) + (n + 2) := by omega
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
        _ = 2 ^ (n + 2) := by ring

  have hConfigBound : ∀ s, qc * (s + 1) * gc ^ (s + 1) ≤ K * 2 ^ (K * s) := by
    intro s
    rcases s with _ | s
    · simp; omega
    ·
      have hexp1 : s + 1 + (K - 1) * (s + 1) = K * (s + 1) := by
        have hK1 : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hK_pos
        have : s + 1 + (K - 1) * (s + 1) = (K - 1 + 1) * (s + 1) := by ring
        rw [this, hK1]

      calc qc * (s + 1 + 1) * gc ^ (s + 1 + 1)
          = qc * (s + 2) * (gc * gc ^ (s + 1)) := by ring
        _ ≤ qc * 2 ^ (s + 1) * (gc * (2 ^ (K - 1)) ^ (s + 1)) := by
            apply Nat.mul_le_mul
            · exact Nat.mul_le_mul_left _ (hexp_ge s)
            · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgc_le _)
        _ = qc * gc * (2 ^ (s + 1) * 2 ^ ((K - 1) * (s + 1))) := by ring
        _ = qc * gc * 2 ^ (s + 1 + (K - 1) * (s + 1)) := by rw [← pow_add]
        _ = qc * gc * 2 ^ (K * (s + 1)) := by rw [hexp1]
        _ ≤ K * 2 ^ (K * (s + 1)) := Nat.mul_le_mul_right _ (by omega)
  refine ⟨fun n => K * 2 ^ (K * g n), K, ?_, hK_pos, fun n => le_refl _⟩

  intro w
  set N := K * 2 ^ (K * g w.length) with hN_def
  by_contra h_not_halt

  obtain ⟨n₀, hn₀⟩ := hSpace.1 w

  have hN_lt : N < n₀ := by
    by_contra hle; push Not at hle
    exact h_not_halt (isHaltConfig_mono M (M.initConfig w) hle hn₀)

  have h_none : ∀ k, k ≤ N → ¬M.isHaltConfig (M.runOnInput w k) :=
    fun k hk hH => h_not_halt (isHaltConfig_mono M (M.initConfig w) hk hH)

  set S := TMSpaceUsed M w N
  have hS_le : S ≤ g w.length := by
    calc TMSpaceUsed M w N
        ≤ TMSpaceUsed M w n₀ := by
          unfold TMSpaceUsed
          exact Finset.card_le_card
            (Finset.image_subset_image (Finset.range_mono (by exact Nat.succ_le_succ (Nat.le_of_lt hN_lt))))

      _ ≤ g w.length := hSpace.2 w n₀ hn₀

  set visited := (Finset.range (N + 1)).image (fun k => (M.runOnInput w k).headPos)
  have hvc : visited.card = S := rfl
  have h_vis : ∀ k, k ≤ N → (M.runOnInput w k).headPos ∈ visited :=
    fun k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  set enum := visited.equivFinOfCardEq hvc

  let proj : Fin (N + 1) → Q × Fin (S + 1) × (Fin (S + 1) → Γ) := fun ⟨k, hk⟩ =>
    let c := M.runOnInput w k
    (c.state, (enum ⟨c.headPos, h_vis k (by omega)⟩).castSucc,
     fun i => if hi : i.val < S then c.tape (enum.symm ⟨i.val, hi⟩).val else c.tape 0)

  have hcard : Fintype.card (Q × Fin (S + 1) × (Fin (S + 1) → Γ)) <
      Fintype.card (Fin (N + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    show qc * ((S + 1) * gc ^ (S + 1)) < N + 1
    calc qc * ((S + 1) * gc ^ (S + 1))
        = qc * (S + 1) * gc ^ (S + 1) := by ring
      _ ≤ K * 2 ^ (K * S) := hConfigBound S
      _ ≤ K * 2 ^ (K * g w.length) := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left K hS_le)
      _ = N := rfl
      _ < N + 1 := by omega

  obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt proj hcard
  simp only [proj, Prod.mk.injEq] at heq
  obtain ⟨hSt, hHd, hTp⟩ := heq

  have hHead : (M.runOnInput w k₁).headPos = (M.runOnInput w k₂).headPos := by
    simp only [Fin.castSucc_inj] at hHd
    exact congr_arg Subtype.val (enum.injective hHd)


  have hTape_eq : (M.runOnInput w k₁).tape = (M.runOnInput w k₂).tape := by
    funext p
    by_cases hp : p ∈ visited
    ·
      set idx := enum ⟨p, hp⟩
      have htf := congr_fun hTp ⟨idx.val, by omega⟩
      simp only [idx.isLt, dite_true] at htf
      have h1 : (↑(enum.symm ⟨idx.val, idx.isLt⟩) : ↥visited).val = p := by
        show (enum.symm (enum ⟨p, hp⟩)).val = p; simp
      unfold TuringMachine.TM.runOnInput at htf ⊢; rw [h1] at htf; exact htf

    ·
      have hp' : ∀ m, m < N + 1 → (M.runOnInput w m).headPos ≠ p := by
        intro m hm heq
        exact hp (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, heq⟩)

      suffices haux : ∀ k, k ≤ N → (M.runOnInput w k).tape p = (M.initConfig w).tape p by
        rw [haux k₁ (by omega), haux k₂ (by omega)]
      intro k hk
      unfold TuringMachine.TM.runOnInput
      induction k with
      | zero => rfl
      | succ k ih =>
        show (M.step (M.run (M.initConfig w) k)).tape p = (M.initConfig w).tape p
        have hkp : (M.run (M.initConfig w) k).headPos ≠ p := hp' k (by omega)
        unfold TuringMachine.TM.step
        split_ifs with hh
        · exact ih (by omega)
        · simp only
          rw [Function.update_of_ne (Ne.symm hkp)]
          exact ih (by omega)


  have hcfg : M.runOnInput w k₁ = M.runOnInput w k₂ := by
    have : ∀ (c : Config Q Γ), c = ⟨c.state, c.headPos, c.tape⟩ := fun c => by cases c; rfl
    rw [this (M.runOnInput w k₁), this (M.runOnInput w k₂), hSt, hHead, hTape_eq]


  have hk_ne : k₁ ≠ k₂ := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hk_ne with h_lt | h_lt
  · exact (SpaceComplexity.not_halts_of_config_repeat M w k₁ k₂ h_lt hcfg
      (h_none k₁ (by omega))) (hSpace.1 w)
  · exact (SpaceComplexity.not_halts_of_config_repeat M w k₂ k₁ h_lt hcfg.symm
      (h_none k₂ (by omega))) (hSpace.1 w)



/-- **`L ⊆ P`.** Every language decidable in deterministic log-space is also
decidable in deterministic polynomial time. The proof combines
`space_bounded_decider_poly_time` (giving a time bound of `K · 2^(K · g n)`)
with the bound `g n ≤ c · log₂ n` from the log-space hypothesis, yielding a
polynomial time bound `K · n^(K · c + 1)`. -/
theorem l_subset_p {Γ : Type} [Fintype Γ] (A : Set (List Γ)) (h : InL A) :
    TuringMachine.InP A := by
  unfold InL InSPACE at h
  obtain ⟨Q, hFinQ, hDecEq, M, hLang, g, hgBound, hSpace⟩ := h
  letI := hFinQ; letI := hDecEq
  have hDecides : M.decides A := ⟨hSpace.1, hLang⟩
  obtain ⟨c_bound, n₀, hc_pos, hgBoundFn⟩ := hgBound

  obtain ⟨t, K, hRunsInTime, hK_pos, htBound⟩ :=
    space_bounded_decider_poly_time M g hSpace


  use K * c_bound + 1
  exact ⟨Q, inferInstance, hDecEq, M, t, hDecides, hRunsInTime,
    ⟨K, max n₀ 1, hK_pos, fun n hn => by
      dsimp only at hn ⊢
      have hn₀ : n₀ ≤ n := le_of_max_le_left hn
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have hn0 : n ≠ 0 := by omega
      have hg_le : g n ≤ c_bound * Nat.log 2 n := by
        have := hgBoundFn n hn₀; simp only [log] at this; exact this
      calc t n ≤ K * 2 ^ (K * g n) := htBound n
        _ ≤ K * 2 ^ (K * (c_bound * Nat.log 2 n)) := by
            apply Nat.mul_le_mul_left
            apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
            apply Nat.mul_le_mul_left
            exact hg_le
        _ = K * (2 ^ Nat.log 2 n) ^ (K * c_bound) := by
            rw [← pow_mul]; congr 1
            rw [mul_comm c_bound, ← mul_assoc, mul_comm K, mul_assoc]
        _ ≤ K * n ^ (K * c_bound) :=
            Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn0) _)
        _ ≤ K * n ^ (K * c_bound + 1) :=
            Nat.mul_le_mul_left K (Nat.pow_le_pow_right hn1 (Nat.le_succ _))⟩⟩

end LogSpace
