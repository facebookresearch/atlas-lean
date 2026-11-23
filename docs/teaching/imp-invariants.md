# IMP invariants: a countdown transfer, proved totally

Teaching example. The Lean file
[`examples/IMPInvariants.lean`](examples/IMPInvariants.lean) is the checked
artifact; this page is its reading guide. It is a teaching consumer of the
public `Cslib.IMP` Hoare-logic APIs: it adds no library theorem, theorem-count
or accepted-spec increment, and makes no implementation, compiler or runtime
claim.

## Problem

For distinct variables `x` and `y`, starting from `x = n` and `y = 0`:

```
while x ≠ 0 do
  y := y + 1
  x := x − 1
```

Show the program terminates with `x = 0` and `y = n`, stating the invariant
and the variant separately so each obligation can fail on its own.

## Obligations, in order

1. The precondition `x = n ∧ y = 0` entails the invariant `x + y = n`.
2. One body step from an invariant state with `x ≠ 0` restores the invariant.
   The guard matters: at `x = 0` truncated subtraction gives `0 − 1 = 0`, so
   preservation fails without it.
3. The invariant plus a false guard entails `x = 0 ∧ y = n`.
4. The variant `x` strictly decreases across one body step — but only when
   `x` and `y` are distinct cells.
5. Total correctness combines 1–4; partial correctness needs only 1–3.

Positive witnesses (`n = 0` and `n = 3`) are proved by explicit runs, not by
appealing to the general theorems, so the hypotheses are seen to be
satisfiable.

## Three failing variants

- **Increment by 2.** Changing `y := y + 1` to `y := y + 2` breaks the
  invariant at `n = 1` (it survives vacuously at `n = 0`), and the whole
  end-to-end claim fails.
- **`while true do skip`.** Partial correctness holds for every postcondition,
  including `False`; total correctness fails for every postcondition. The
  difference between the two judgments is exactly termination.
- **Aliasing (`x = y`).** Partial correctness still holds, but the variant no
  longer decreases: with one cell the body is the identity at value 1, the
  loop diverges, and no variant argument exists for the same invariant. Note
  the tempting statement "the aliased total-correctness triple fails" is
  itself false — its precondition `x = n ∧ x = 0` forces `n = 0`.

## Exercises

1. Weaken obligation 2 by dropping the guard conjunct and find the
   counterexample state.
2. Compare the two assignment orders in the one-cell body at value 0:
   `x := x + 1; x := x − 1` ends at 0, while the reordered
   `x := x − 1; x := x + 1` ends at 1. Conclude that statement order is
   observable exactly at 0, where truncated subtraction loses information.
   (Both one-cell bodies already fail obligation 4 at value 1: the
   unreordered body computes `1 → 2 → 1`, the reordered body
   `1 → 0 → 1`, so the cell never decreases.)
3. Replace the variant `x` by `x + y` and identify which obligation breaks.

## Prior art in this repository

Atlas already has Hoare-logic examples. `Cslib.IMP.Examples.countdown_valid`
proves partial correctness of a two-cell transfer loop: cell 0 is
incremented while cell 1 is decremented to 0, ending with cell 0 equal to
the sum of the two starting values. `HoareTotalTests.countdown_total`
proves total correctness of a different, one-cell decrement-only loop.
`HoareGcd.gcd_total` and `HoareGcd.gcd_12_18` cover a two-variable gcd
loop with a sum variant.

The program in this lesson is a transfer of the same family: `y` starts
at 0 and ends at `n`. Its gaps, relative to the examples above, are
named teaching obligations: the invariant and variant are discharged as
separate reusable-step lemmas (including the odd aliasing case), its
total-correctness proof is assembled from them, and the `n = 0` and
`n = 3` endpoints are proved by explicit zero-step and three-step runs
rather than by quoting the general theorems. The remaining theorems in
this file exhibit ways the obligations can fail: changing the increment,
removing termination, and aliasing the variables.
