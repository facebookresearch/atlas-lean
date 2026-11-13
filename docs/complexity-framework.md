# Canonical complexity framework

## Decision and scope

Use `MetaMathlibExt.ComplexityTheory.IsPolyTime`, `P`, `NP`, and `coNP`
for general complexity-class statements. `IsPolyTimeWithEncoding` packages a
`Turing.TM2ComputableInPolyTime` witness; `IsPolyTime` selects the existing
bitstring encodings. `P` is defined through that predicate, and `NP` through
a polynomially bounded witness and a verifier satisfying it ([definitions]).

This is a documentation decision, not a new framework or a completed
migration. It adds no Lean declarations, aliases, deprecation attributes,
module moves, or simulation proofs. It does not establish any missing bridge.

## Use the existing interfaces

- **Encodings:** keep `MetaMathlibExt.BitstringEncoding`. The existing pair
  encoding frames its first component; the list encoding frames every element
  ([encodings]). Raw input words and these encodings are not interchangeable
  by a rename. A change of representation needs its own correctness and
  resource bounds.
- **Reductions:** keep `Cslib.CookLevin.PolyManyOneRed`. It already requires
  the canonical `IsPolyTime` predicate and preservation of the decision
  problem ([reductions]). It is not a competing complexity framework.
  Keep the existing CNF compatibility exports as well ([cnf-exports]).
- **Named cost annotations:** keep the declared-time predicates in
  `Cslib.TimeMComplexity`. They constrain the supplied `TimeM.time` annotation
  (and, for computed functions, output length), not a machine's running time
  ([declared]). In particular, `exists_decidesInDeclaredPolyTime` shows that
  every decision problem has an unrestricted `TimeM` decider,
  `fun x => pure (L x)`, with declared time zero ([zero-declared-time]).
  Do not define `P` or `NP` by quantifying over unrestricted host-language
  `TimeM` functions.
- **Canonical membership from a named algorithm:** use
  `mem_P_of_decides`, `mem_NP_of_verifies`, or
  `cookLevinPolyManyOneRed_of_declared` only with their independently proved
  canonical `IsPolyTime` hypothesis ([declared-bridges]). An annotation bound
  alone does not supply it. This also applies to declared-time SAT examples;
  functional correctness and a declared bound are not canonical NP evidence.

No relocation of these interfaces or new namespace aliases is required by
this decision. Deprecating *class-defining use* of declared annotations does
not remove the valid per-algorithm APIs. Preserve existing clients and names;
any future code migration needs separate justification, ownership review,
and checks of its consumers.

## Keep model-specific results distinct

The following interfaces remain useful. None is an alias for all the others.

- `Cslib.Turing.MultiTapeTM.DTIME` and `DSPACE` quantify over finite-state
  multi-tape deciders with explicit affine bounds ([multi-bounds]).
  `Cslib.Turing.MultiTapeTM.Classes.P` and `PSPACE` are their polynomial
  unions ([multi-classes]). Keep the model qualification when using them;
  do not silently substitute this `P` for the TM2-based canonical `P`.
- `Cslib.Complexity.Classes.langOf` maps a Boolean decision problem to its
  accepted set of words. Its `PSPACE`, `EXP`, `EXPSPACE`, and `LogSpace`
  definitions use multi-tape classes through that map ([language-adapter]).
  This is a language adapter, not a cost-preserving machine simulation.
  Keep the existing class definitions rather than replacing them with
  unsupported TM2 equivalents.
- `Cslib.Complexity.P_subset_singleTapeP` proves the direction from canonical
  `P` to `SingleTapeP`, with a polynomial-time single-tape decider
  ([single-tape]). Use that direction as stated. An inclusion is not an
  equality or an unrestricted interface replacement.
- `Cslib.Turing.Universal.CodeTime t` uses the exact clock bound `t` on the
  coded machine's evaluator, not an implicit big-O bound. For example,
  `codeTime_eq_empty` says it is empty when `t 0 = 0` ([code-time]). Do not
  erase constants or replace it with `DTIME t`. The diagonalization module
  explicitly distinguishes its cross-model result from a same-model time
  hierarchy theorem ([code-scope]).
- The multi-tape computability bridge erases time and space bounds
  ([multi-bridge]). A computability result, or a language adapter, is not
  evidence of polynomial simulation overhead.

Before transferring a result, identify its machine, input/output encoding,
acceptance or halting convention, resource measure, direction, and overhead
quantifiers. Cite the actual bridge that preserves what the result needs.
Neither this memo nor a common type such as `DecisionProblem` supplies one.
Cook-Levin and Karp statement-fidelity audits remain separate work; this
memo does not certify their individual reductions or proofs.

## Cost attribution and the RAM boundary

The separately pinned RAM-cost work uses `CSLibExt.Cost.CostM := TimeM Cost`,
not a replacement computation carrier. Its time and cumulative-space
annotations add, and supplied peak-memory annotations combine by maximum;
record fields remain `ret` and `time` ([cost-carrier]). Do not infer hardware
cost from those annotations.

Its instrumented RAM reuses `ramStep`, proves result erasure, and counts
in-range instruction dispatches, including `halt` and self-jumps. Its
first-halt theorem has explicit active-prefix and halted-endpoint hypotheses;
under them the count is `min budget h` ([ram-count]). Space and memory are
unmodeled zero annotations, not measured zero usage. This snapshot is linked
separately below and must not be assumed available from the main snapshot.

The underlying RAM has natural-number registers and saturating subtraction
([ram-model]). It is not a fixed-width word-RAM. A word-RAM front end and its
resource-preserving TM simulation remain separate design and proof tasks:
word width, overflow, representation, and overhead must be specified and
justified. The instruction-count result does not discharge that debt.

## Migration work that is not implemented here

1. Use the canonical names above in new general class statements. Preserve
   existing model-specific APIs and do not manufacture equivalences or thin
   aliases solely to make directory names uniform.
2. Retain the conditional `TimeMComplexity` bridges and the already canonical
   reduction interface in their current homes. This memo does not move the
   Cook-Levin or Karp files, add shims, or rewrite another contributor's code.
3. Prove any missing resource-preserving bridge as a separately reviewed
   unit, with faithful statements and concrete clients. Do not turn a
   comment naming future work into an assumption of the desired theorem.
4. Treat the following names as unresolved documentation references, not
   importable modules at the main snapshot below. The Church-Turing and RAM
   comments name the first four ([urm-references], [ram-reference]); the
   multi-tape bridge comments name the last three ([multi-bridge]).

   Under `WantedExt/TheoryOfComputation/`:
   - `PartrecToURM.lean`
   - `LambdaCalculusEquivalence.lean`
   - `CounterMachineEquivalence.lean`
   - `RAMMachineEquivalence.lean`
   - `MultiTapeBridge.lean`
   - `MultiTapeRecognizableBridge.lean`
   - `MultiTapeComplexityBridge.lean`

   None of those exact paths is present in the inspected tree. This is a
   path-inventory result, not proof that no related theorem exists elsewhere.
   Repairing references or authoring new Wanted statements requires its own
   scope and statement checks; no placeholder declarations are added here.

## Source snapshot

The main-source links pin `8d9615534e952953b234d95b73dfc5054ed662cb`.
The two RAM-cost links separately pin the reviewed #902 source
`9239b6e649f1a40be2ada4660fb3291c1aa7f82b`. These are source references,
not claims that a migration, word-RAM implementation, or program-wide
acceptance gate has been completed.

[definitions]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/MathlibExt/Computability/Complexity.lean#L166-L208
[encodings]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/MathlibExt/Computability/Complexity.lean#L134-L162
[reductions]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/CookLevin.lean#L388-L398
[cnf-exports]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/CookLevin.lean#L38-L43
[declared]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/TimeMComplexity.lean#L65-L115
[zero-declared-time]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/TimeMComplexity.lean#L129-L138
[declared-bridges]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/TimeMComplexity.lean#L274-L314
[multi-bounds]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Machines/Turing/MultiTape/TimeSpace.lean#L140-L172
[multi-classes]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Machines/Turing/MultiTape/TimeSpace.lean#L201-L211
[language-adapter]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Complexity/Classes.lean#L111-L147
[single-tape]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Machines/Turing/SingleTape/PolyTime.lean#L451-L490
[code-time]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Machines/Turing/Universal/Diagonalization.lean#L108-L169
[code-scope]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Machines/Turing/Universal/Diagonalization.lean#L15-L32
[multi-bridge]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Machines/Turing/MultiTape/Bridge.lean#L17-L39
[cost-carrier]: https://github.com/facebookresearch/atlas-lean/blob/9239b6e649f1a40be2ada4660fb3291c1aa7f82b/CSLibExt/Computability/Models/Cost/Basic.lean#L17-L108
[ram-count]: https://github.com/facebookresearch/atlas-lean/blob/9239b6e649f1a40be2ada4660fb3291c1aa7f82b/CSLibExt/Computability/Models/Cost/RAM.lean#L14-L84
[ram-model]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Decidability/RAMMachines.lean#L52-L118
[urm-references]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Decidability/ChurchTuring.lean#L17-L34
[ram-reference]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Computability/Decidability/RAMMachines.lean#L15-L24
