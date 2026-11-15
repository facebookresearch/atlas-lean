# Native state and exception contracts

Roadmap facet: `cs:VER-046#native-state-exception-contracts`.

This lesson follows one checked debit from a precise contract through
composition, weakest-precondition reasoning, concrete execution, and
counterexamples. The [Lean example](examples/NativeStateContracts.lean)
uses Lean's existing `EStateM`, `Std.Do.Triple`, and standard monad transformers.
It does not introduce another program logic or a production banking API.

## Model and observations

A balance and an amount are natural numbers. Success and insufficient-funds
errors both carry `Unit`; the result constructor distinguishes them.

For initial balance `b` and debit amount `a`:

- When `a ≤ b`, the program succeeds with final balance `b - a`.
- When `b < a`, it returns an error and keeps the input balance `b`.

These are mathematical natural numbers, not fixed-width machine integers.
The model has no external account, concurrency, persistence, or physical
rollback operation. IO in the executable checks belongs to the test harness,
not to the debit model.

## Compose contracts, including failure

The two-debit program really sequences debit `a` and then debit `c`. Its
three outcomes are:

| Conditions | Result | Final balance |
| --- | --- | --- |
| `a ≤ b` and `c ≤ b - a` | Success | `b - a - c` |
| `b < a` | First debit fails; the second is not executed | `b` |
| `a ≤ b` and `b - a < c` | Second debit fails | `b - a` |

For example, debiting 3 and then 4 from 5 leaves an error with balance 2.
Preserving a failing debit's input state is not the same as rolling back an
entire sequence: the second debit received 2, not 5.

Read the proof in this order:

1. The single-debit triple records separate, precise success and error
   postconditions.
2. `Std.Do.Triple.bind` composes the programs through an explicit intermediate
   assertion: the first debit was affordable and the current balance is
   `b - a`. Both ways to fail remain visible in the final postcondition.
3. `Std.Do.EStateM.of_wp_run_eq` connects the weakest-precondition proof to the
   actual native run. Its result predicate covers both result constructors.
   The run equality supplied to this rule names the actual computation; it
   does not assume the desired output.

A law about generic predicate-transformer algebra would not, by itself,
identify the behavior of this particular native program.

## Check observations and discriminate wrong programs

The concrete cases cover equality, zero amount, insufficient balance, and
both failure positions. In particular:

| Initial balance | First debit | Second debit | Expected observation |
| --- | --- | --- | --- |
| 10 | 3 | 7 | Success, balance 0 |
| 5 | 6 | 0 | Error, balance 5 |
| 5 | 3 | 4 | Error, balance 2 |
| 0 | 0 | 1 | Error, balance 0 |

The file also instantiates the universal run theorems. Executable assertions
check literal expected observations for the cases above. These are
specified deterministic fixtures, not a randomized coverage estimate.

Three private wrong implementations test the assertions themselves:

- A strict `<` guard incorrectly rejects debiting 5 from 5.
- Clearing state on error incorrectly changes 5 to 0 when debiting 6.
- Rolling back the whole pair incorrectly returns 5 rather than 2 after
  debiting 3 and then 4.

The same fixture must accept the baseline and reject its corresponding
mutant. A mutant that does not compile is a compiler control, not a runtime
mutation test. Proving that a fixture Boolean is false is useful proof
evidence, but does not replace running the assertion harness.

To replay the file's commands with the repository-pinned toolchain:

```sh
lake env lean -DwarningAsError=true docs/teaching/examples/NativeStateContracts.lean
```

CI runs this standalone teaching file explicitly. It is not a library or a
`CSLibExtTest` module: it exercises core APIs rather than a public Atlas API.
Axiom listings and executable assertion results establish different facts;
inspect both. The kernel checks the stated propositions. These finite
executions do not verify Lean's compiler or a deployed service.

## Transformer order changes the observable result

With initial balance 5, debit 3 followed by debit 4 gives:

- `ExceptT Unit (StateM Nat)`: an error together with intermediate state 2.
- `StateT Nat (Except Unit)`: an error with no returned state.

The example runs the actual standard transformer computations. The missing
state in the second result is not evidence that an external system physically
restored its old state.

## A weak error postcondition hides errors

An error postcondition equal to `True` holds even when the debit fails.
The example proves such a weak triple and also proves that the same debit
returns an error. Thus the weak triple cannot establish absence of errors.
It does not replace the main specifications' precise failure conditions.

## Exercises

1. From balance 9, debit 4 and then 6. Which assertion holds between the
   debits, and which result branch applies? The intermediate balance is 5;
   the second debit fails and returns state 5.
2. Why is `(0, 0, 1)` different from a first-debit failure? The zero debit
   succeeds; the attempt to debit 1 fails afterward.
3. Can an all-`True` error postcondition distinguish the correct debit from
   one that clears state on error? No. The precise error-state assertion can.

This is a teaching consumer of existing APIs, not a new reusable-library
theorem or completion of the broader contract-refinement topic. It does not
increase the relational-specification inventory's accepted-spec count.

## Native API references

The example uses the repository's Lean 4.35.0 pin. The relevant core sources
are [`Std.Do.Triple.bind`][bind] and the
[`EStateM` weakest-precondition instance and run bridge][wp].

[bind]: https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Do/Triple/Basic.lean#L84-L94
[wp]: https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Std/Do/WP/Basic.lean#L92-L125
