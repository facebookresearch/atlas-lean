/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Testing limits: finite tests and universal laws

Standalone teaching example (not a testing framework).

Clause map:
- C1: `oracle`, `passesOn` (pointwise equality on `T` only).
- C2: `badAt100`, `badAt100_passes`, `badAt100_at_100`,
  `badAt100_not_universal`.
- C3: `succ_of_base_and_law` (Nat induction), `oracle_base`,
  `oracle_law`, `oracle_is_succ`.
- C4: `lawHoldsOn`, `badAt101`, `badAt101_law_passes`,
  `badAt101_base`, `badAt101_sides_at_100`,
  `badAt101_law_fails_at_100`, `lawArgs_within_0_to_100`,
  `plusTwo`, `plusTwo_law`, `plusTwo_base_fails`,
  `plusTwo_not_succ`.
- C5: `ExtEq`, `adequateFor`, `constZero`, `onePlus`,
  `onePlus_ext`, `famMut`, `famIndex`, `selected_adequate`,
  `badAt100_not_selected`, `adequacy_says_nothing_unselected`.
- C6: `guardFn`, `branchFn`, `branch_tested_agree`,
  `branch_uncovered_false_guard` (observation only).
- C7: `check`, `runTests`, `main` (executable assertions).
-/

/-- C1: independent successor oracle on naturals. -/
private def oracle : Nat → Nat := fun n => n + 1

/-- C1: passing `T` is pointwise equality on `T` only. -/
private def passesOn (f : Nat → Nat) (T : List Nat) : Prop :=
  ∀ n ∈ T, f n = oracle n

/-- C2: mutant matching on 0-99, wrong (0) at 100. -/
private def badAt100 : Nat → Nat :=
  fun n => if n = 100 then 0 else n + 1

/-- C2: `badAt100` passes direct tests on 0 through 99. -/
private theorem badAt100_passes :
    passesOn badAt100 (List.range 100) := by
  intro n hn
  have hlt : n < 100 := List.mem_range.mp hn
  have hne : n ≠ 100 := Nat.ne_of_lt hlt
  show badAt100 n = oracle n
  simp only [badAt100, oracle]
  simp [hne]

/-- C2: at 100 the actual 0 differs from expected 101. -/
private theorem badAt100_at_100 :
    badAt100 100 = 0 ∧ oracle 100 = 101 ∧
      badAt100 100 ≠ oracle 100 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [badAt100]
  · rfl
  · simp [badAt100, oracle]

/-- C1-C2: passing finite tests is not universal equality. -/
private theorem badAt100_not_universal :
    ¬ ∀ n : Nat, badAt100 n = oracle n := by
  intro h
  have h100 := h 100
  simp [badAt100, oracle] at h100

/-- C3: base `f 0 = 1` plus UNIVERSAL law gives successor. -/
private theorem succ_of_base_and_law (f : Nat → Nat)
    (hbase : f 0 = 1)
    (hlaw : ∀ n : Nat, f (n + 1) = f n + 1) :
    ∀ n : Nat, f n = n + 1 := by
  intro n
  induction n with
  | zero =>
    simpa using hbase
  | succ k ih =>
    have h := hlaw k
    rw [h, ih]

/-- C3: the oracle meets the required base condition. -/
private theorem oracle_base : oracle 0 = 1 := rfl

/-- C3: the oracle meets the increment law everywhere. -/
private theorem oracle_law :
    ∀ n : Nat, oracle (n + 1) = oracle n + 1 :=
  fun _ => rfl

/-- C3-C7: the universal result instantiated at the oracle. -/
private theorem oracle_is_succ :
    ∀ n : Nat, oracle n = n + 1 :=
  succ_of_base_and_law oracle oracle_base oracle_law

/-- C4: the increment law checked on finite indices `I`. -/
private def lawHoldsOn (f : Nat → Nat) (I : List Nat) :
    Prop :=
  ∀ n ∈ I, f (n + 1) = f n + 1

/-- C4: second mutant, wrong (0) at 101, successor elsewhere. -/
private def badAt101 : Nat → Nat :=
  fun n => if n = 101 then 0 else n + 1

/-- C4: `badAt101` passes law checks on indices 0-99. -/
private theorem badAt101_law_passes :
    lawHoldsOn badAt101 (List.range 100) := by
  intro n hn
  have hlt : n < 100 := List.mem_range.mp hn
  have h1 : n ≠ 101 := by omega
  have h2 : n + 1 ≠ 101 := by omega
  show badAt101 (n + 1) = badAt101 n + 1
  simp only [badAt101]
  simp [h1, h2]

/-- C4: `badAt101` also passes the base check `f 0 = 1`. -/
private theorem badAt101_base : badAt101 0 = 1 := by
  decide

/-- C4: law-index-100 sides are 0 (left) and 102 (right). -/
private theorem badAt101_sides_at_100 :
    badAt101 (100 + 1) = 0 ∧ badAt101 100 + 1 = 102 := by
  constructor <;> decide

/-- C4: `badAt101` fails the increment law at index 100. -/
private theorem badAt101_law_fails_at_100 :
    badAt101 (100 + 1) ≠ badAt101 100 + 1 := by
  decide

/-- C4: law indices 0-99 observe only arguments 0-100. -/
private theorem lawArgs_within_0_to_100 :
    ∀ n ∈ List.range 100,
      n ∈ List.range 101 ∧ n + 1 ∈ List.range 101 := by
  intro n hn
  have hlt : n < 100 := List.mem_range.mp hn
  constructor
  · exact List.mem_range.mpr (by omega)
  · exact List.mem_range.mpr (by omega)

/-- C4: `n + 2` obeys the increment law but not the base. -/
private def plusTwo : Nat → Nat := fun n => n + 2

/-- C4: `plusTwo` satisfies the UNIVERSAL increment law. -/
private theorem plusTwo_law :
    ∀ n : Nat, plusTwo (n + 1) = plusTwo n + 1 :=
  fun _ => rfl

/-- C4: `plusTwo` fails the base condition (`f 0 = 2`). -/
private theorem plusTwo_base_fails :
    plusTwo 0 = 2 ∧ plusTwo 0 ≠ 1 := by
  constructor <;> decide

/-- C4: the law alone does not give the successor result. -/
private theorem plusTwo_not_succ :
    ¬ ∀ n : Nat, plusTwo n = n + 1 := by
  intro h
  have h0 := h 0
  simp [plusTwo] at h0

/-- C5: extensional equality with the oracle (all inputs). -/
private def ExtEq (f : Nat → Nat) : Prop :=
  ∀ n : Nat, f n = oracle n

/-- C5: adequacy over selected mutants; equivalents excluded. -/
private def adequateFor (T I : List Nat)
    (mutFn : Nat → (Nat → Nat)) : Prop :=
  ∀ i ∈ I, ¬ ExtEq (mutFn i) →
    ∃ t ∈ T, mutFn i t ≠ oracle t

/-- C5: selected wrong mutant, constantly zero. -/
private def constZero : Nat → Nat := fun _ => 0

/-- C5: selected mutant extensionally equal to the oracle. -/
private def onePlus : Nat → Nat := fun n => 1 + n

/-- C5: `onePlus` is extensionally equal (proved, not tested). -/
private theorem onePlus_ext : ExtEq onePlus :=
  fun n => Nat.add_comm 1 n

/-- C5: indices 0,1,2 select constZero, plusTwo, onePlus. -/
private def famMut : Nat → (Nat → Nat) :=
  fun i =>
    match i with
    | 0 => constZero
    | 1 => plusTwo
    | _ => onePlus

/-- C5: the selected finite index list. -/
private def famIndex : List Nat := [0, 1, 2]

/-- C5: the selected family is adequate on tests 0-99. -/
private theorem selected_adequate :
    adequateFor (List.range 100) famIndex famMut := by
  intro i hi
  simp only [famIndex, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact fun _ => ⟨0, List.mem_range.mpr (by omega),
      by decide⟩
  · exact fun _ => ⟨0, List.mem_range.mpr (by omega),
      by decide⟩
  · intro hne
    exact absurd onePlus_ext hne

/-- C5: `badAt100` is not among the selected mutants. -/
private theorem badAt100_not_selected :
    ∀ i ∈ famIndex, famMut i ≠ badAt100 := by
  intro i hi
  simp only [famIndex, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl
  · intro h
    have h99 := congrFun h 99
    have e1 : famMut 0 99 = 0 := rfl
    have e2 : badAt100 99 = 100 := rfl
    rw [e1, e2] at h99
    simp at h99
  · intro h
    have h0 := congrFun h 0
    have e1 : famMut 1 0 = 2 := rfl
    have e2 : badAt100 0 = 1 := rfl
    rw [e1, e2] at h0
    simp at h0
  · intro h
    have h100 := congrFun h 100
    have e1 : famMut 2 100 = 101 := rfl
    have e2 : badAt100 100 = 0 := rfl
    rw [e1, e2] at h100
    simp at h100

/-- C5: adequacy holds while unselected `badAt100` survives. -/
private theorem adequacy_says_nothing_unselected :
    adequateFor (List.range 100) famIndex famMut ∧
      passesOn badAt100 (List.range 100) ∧
      ¬ ExtEq badAt100 :=
  ⟨selected_adequate, badAt100_passes, badAt100_not_universal⟩

-- C6 observation (elementary counterexample only, not a formal
-- IMP coverage criterion, MC/DC theorem, or defect-rate claim).

/-- C6: guard `n < 2` observed as a Boolean value. -/
private def guardFn : Nat → Bool :=
  fun n => decide (n < 2)

/-- C6: both branches return 1 (outputs equal, guards differ). -/
private def branchFn : Nat → Nat :=
  fun n => if n < 2 then 1 else 1

/-- C6: on tested inputs 0,1 outputs and guards coincide. -/
private theorem branch_tested_agree :
    ∀ t ∈ ([0, 1] : List Nat),
      branchFn t = 1 ∧ guardFn t = true := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false]
    at ht
  rcases ht with rfl | rfl
  · constructor <;> decide
  · constructor <;> decide

/-- C6: input 2 takes the untested false guard, same output. -/
private theorem branch_uncovered_false_guard :
    guardFn 2 = false ∧ branchFn 2 = 1 := by
  constructor <;> decide

/-- C7: named assertion; throws (fails) unless `cond` holds. -/
private def check (name : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw (IO.userError s!"CHECK FAILED: {name}")
  IO.println s!"CHECK PASSED: {name}"

/-- C7: executable assertions for C1-C6; aborts on failure. -/
private def runTests : IO Unit := do
  check "C1 oracle 100 = 101" (oracle 100 == 101)
  check "C2 badAt100 100 = 0" (badAt100 100 == 0)
  check "C2 badAt100 99 = 100" (badAt100 99 == 100)
  check "C2 badAt100 100 differs from oracle"
    (badAt100 100 != oracle 100)
  check "C3 oracle 0 = 1" (oracle 0 == 1)
  check "C3 oracle 57 = 58" (oracle 57 == 58)
  check "C4 badAt101 101 = 0" (badAt101 101 == 0)
  check "C4 badAt101 100 = 101" (badAt101 100 == 101)
  check "C4 law index 100 lhs = 0" (badAt101 (100 + 1) == 0)
  check "C4 law index 100 rhs = 102"
    (badAt101 100 + 1 == 102)
  check "C4 plusTwo law at 50"
    (plusTwo (50 + 1) == plusTwo 50 + 1)
  check "C4 plusTwo 0 = 2" (plusTwo 0 == 2)
  check "C5 constZero killed at 0"
    (constZero 0 != oracle 0)
  check "C5 plusTwo killed at 0" (plusTwo 0 != oracle 0)
  check "C5 onePlus 57 agrees" (onePlus 57 == oracle 57)
  check "C5 badAt100 42 passes" (badAt100 42 == oracle 42)
  check "C6 branch 0 = 1" (branchFn 0 == 1)
  check "C6 branch 1 = 1" (branchFn 1 == 1)
  check "C6 guard 0" (guardFn 0 == true)
  check "C6 guard 1" (guardFn 1 == true)
  check "C6 guard 2 is false" (guardFn 2 == false)
  check "C6 branch 2 = 1" (branchFn 2 == 1)
  IO.println "ALL CHECKS PASSED"

/-- C7: entry point for `lean --run` (sole public declaration;
    a private `main` is invisible to the runner in a module). -/
public def main : IO Unit := runTests

-- Axiom audit: transitive axioms per named declaration.
#print axioms oracle
#print axioms passesOn
#print axioms badAt100
#print axioms badAt100_passes
#print axioms badAt100_at_100
#print axioms badAt100_not_universal
#print axioms succ_of_base_and_law
#print axioms oracle_base
#print axioms oracle_law
#print axioms oracle_is_succ
#print axioms lawHoldsOn
#print axioms badAt101
#print axioms badAt101_law_passes
#print axioms badAt101_base
#print axioms badAt101_sides_at_100
#print axioms badAt101_law_fails_at_100
#print axioms lawArgs_within_0_to_100
#print axioms plusTwo
#print axioms plusTwo_law
#print axioms plusTwo_base_fails
#print axioms plusTwo_not_succ
#print axioms ExtEq
#print axioms adequateFor
#print axioms constZero
#print axioms onePlus
#print axioms onePlus_ext
#print axioms famMut
#print axioms famIndex
#print axioms selected_adequate
#print axioms badAt100_not_selected
#print axioms adequacy_says_nothing_unselected
#print axioms guardFn
#print axioms branchFn
#print axioms branch_tested_agree
#print axioms branch_uncovered_false_guard
#print axioms check
#print axioms runTests
#print axioms main

#eval runTests
