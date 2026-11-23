# LOGICS: program logics and verification conditions

This page lists LOGICS legs, where their declarations live, and whether one
pinned demo replay built or exercised each. The replay did not build or
exercise three of them: canonical IMP metatheory, canonical IMP VC generation
and Boole. It is a partial coverage note, not an acceptance record or an
expert review.

## Sources

- Main: atlas-lean commit [`8d96155`][main].
- MiniImp: commit [`ca4511b`][miniimp] of the branch proposed in pull request
  #904. Main at `8d96155` has no `CSLibExt/Languages/MiniImp/` directory, so
  every MiniImp link below is pinned to `ca4511b`. MiniImp names are relative
  to the namespace `CSLibExt.Languages.MiniImp`.
- CSLib: commit [`5b56df9`][cslib], the pin in both commits'
  `lake-manifest.json` (Lean `v4.35.0`, Mathlib `56a0058`).

## Replay

[`ReadCost.md`][readcost] at `ca4511b` is the replay guide: its two
`lake build` commands, the read-cost convention, the proof chain from
`execReads_ret` to `BinarySearch.verified_read_cost`, the checks, and the
trust limits. On 2026-11-04 (UTC) both commands exited 0 on a fresh clone of
`ca4511b` with no preexisting root build outputs, and every MiniImp proof and
test module they target was elaborated in that run. Main itself was not built.
The one main-linked file the replay built, `LowerBound.lean`, and the
dependency pins are byte-identical at `ca4511b`. The canonical IMP modules
`HoareTotal`, `HoareCompleteness` and `VCG` are outside the replay targets and
were not built.

In the table, "Built" means the replay compiled the module, so Lean elaborated
its theorems and its kernel checked them during the build; no separate
`leanchecker` replay was run. An "`#eval` assertion" is a finite executable
check run during the build that throws, and so fails the build, on a mismatch.

## Legs

| Leg | Declarations | Checked in the replay | Limits |
|---|---|---|---|
| Logic metatheory (canonical IMP, main) | Partial correctness: [`Cslib.IMP.derivable_iff_valid`][imp-complete]. Total correctness: [`Cslib.IMP.tderivable_iff_tvalid`][imp-tcomplete]; semantic [`Cslib.IMP.wp`][imp-wp], [`Cslib.IMP.wp.sound`][imp-sound], [`Cslib.IMP.wp.weakest`][imp-weakest] | Not built or exercised | Assertions are semantic predicates on states; completeness is relative in Cook's sense ([module docstring][imp-doc]) |
| VC generation (canonical IMP, main) | [`Cslib.IMP.ACmd`][vcg-acmd], [`Cslib.IMP.ACmd.pre`][vcg-pre], [`Cslib.IMP.ACmd.vc`][vcg-vc], [`Cslib.IMP.ACmd.vc_sound`][vcg-sound], [`Cslib.IMP.ACmd.vc_complete_of_valid`][vcg-complete] | Not built or exercised | Partial correctness only: loops carry invariants, no variants; preconditions and VCs are computed semantically ([module docstring][vcg-doc]) |
| IMP to MiniImp translation bridge | [`IMPBridge.command`][bridge-command] translates IMP commands into MiniImp; [`IMPBridge.execution_iff`][bridge-exec] relates their executions in both directions; [`IMPBridge.valid_to_hoare`][bridge-hoare] carries IMP partial-correctness validity to MiniImp Hoare triples | Built; [bridge tests][bridge-tests] check a translated factorial loop by `decide` and reflect its run to IMP `BigStep` | Partial correctness; termination is not transported; tests use a test-local injective variable renaming |
| Specification | [`Cslib.Algorithms.Lean.TimeM.lowerBound_spec`][spec] (main) | Built at `ca4511b` as a dependency; the file is byte-identical at main | Sorted arrays; index-separation property |
| Read cost (MiniImp) | [`execReads`][execreads], [`execReads_ret`][execreads-ret], [`execReads_sound`][execreads-sound], [`BinarySearch.program_reads_eq_time`][reads-eq], [`BinarySearch.program_reads_le`][reads-le] | Built; [`#eval` assertions][cost-sweep] compare 16,380 full-search and 4,494 subinterval cost/index results with the reference algorithm; a theorem proved by `decide` shows a [length-eight linear scan][scan] costs 8 reads, above `clog₂ 9 = 4` | Counts successful bounds-checked array reads only, not wall time, RAM or instruction cost; the exact count and the bound assume fuel at least `xs.size + 7` and do not assume sorted input |
| WP to proof (MiniImp) | [`wp`][mi-wp], [`wp_sound`][wp-sound], [`BinarySearch.program_vc`][program-vc], [`BinarySearch.total_correct`][total-correct] | Built; [`#eval` assertions][bs-tests] compare 8,190 results and [4,494 subintervals][bs-intervals] with the reference algorithm | `wp` is sufficient, not weakest; partial correctness, with termination proved for this program |
| Composition (MiniImp) | [`BinarySearch.verified_read_cost`][verified], private [`composed_client`][client] | Built; the client theorem yields 3 counted reads and index 1 on `#[1,3,3,7]`, key 3 | One concrete instance; sortedness is a hypothesis used only by the result specification |
| Boole VC | none | Unavailable: at the CSLib pin, `Cslib/Languages/Boole/` holds only a [README][boole] reading "Placeholder for the Boole language." | No Boole integration is claimed |

The replayed demo connects specification, read cost, WP and proof; the Boole
verification-condition step is missing at this pin.

## Assurance limits

- The replay shows that Lean accepts the theorems in the modules it built at
  `ca4511b`. It is not an expert review of whether they state the intended
  claims.
- From `#print axioms` output in the replayed tests and one diagnostic:
  `execReads`, `execReads_ret`, `execReads_sound`, `ReadSteps.erase`,
  `BigStep.exists_readSteps`, `BinarySearch.loop_reads_eq_time` and
  `BinarySearch.program_reads_eq_time` do not use `Classical.choice`;
  `BinarySearch.program_reads_le`, `BinarySearch.verified_read_cost` and
  `composed_client` do. None of the declarations whose axioms were printed
  depends on `sorryAx`.
- Finite executable checks supplement the universally quantified theorems;
  they do not replace them.

## Outside this replay

The replayed demo does not exercise relational rules, probabilistic rules,
cost rules beyond this binary-search instance, heap reasoning through the
iris-lean interface, the canonical IMP VC generator, or a Boole backend, and
it produces no verification-condition-discharge benchmark tasks. Main contains
a probabilistic cost definition,
[`Cslib.Algorithms.Lean.TimeM.expectedTime`][expected]; this page checked that
declaration only and makes no claim about other probabilistic material.

[main]: https://github.com/facebookresearch/atlas-lean/tree/8d9615534e952953b234d95b73dfc5054ed662cb
[miniimp]: https://github.com/akiezun/atlas-lean/tree/ca4511b77d80c9388143b9a2858fdbb81bffc6ef
[cslib]: https://github.com/leanprover/cslib/tree/5b56df99362532c46e1175381fbbdd755bd56030
[readcost]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/ReadCost.md
[imp-doc]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/HoareCompleteness.lean#L18-L61
[imp-complete]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/HoareCompleteness.lean#L161-L164
[imp-tcomplete]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/HoareCompleteness.lean#L392-L395
[imp-wp]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/HoareTotal.lean#L133-L135
[imp-sound]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/HoareTotal.lean#L139-L142
[imp-weakest]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/HoareTotal.lean#L144-L147
[vcg-doc]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/VCG.lean#L16-L36
[vcg-acmd]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/VCG.lean#L42-L48
[vcg-pre]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/VCG.lean#L60-L69
[vcg-vc]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/VCG.lean#L71-L82
[vcg-sound]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/VCG.lean#L84-L106
[vcg-complete]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Languages/IMP/VCG.lean#L168-L172
[spec]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Algorithms/Lean/Search/LowerBound.lean#L127-L137
[expected]: https://github.com/facebookresearch/atlas-lean/blob/8d9615534e952953b234d95b73dfc5054ed662cb/CSLibExt/Algorithms/Lean/Random/ExpectedCost.lean#L43-L51
[bridge-command]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/IMPBridge.lean#L78-L85
[bridge-exec]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/IMPBridge.lean#L217-L226
[bridge-hoare]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/IMPBridge.lean#L228-L236
[bridge-tests]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExtTest/Languages/MiniImp/IMPBridgeTests.lean#L45-L61
[execreads]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/ReadCost.lean#L30-L56
[execreads-ret]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/ReadCost.lean#L58-L77
[execreads-sound]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/ReadCost.lean#L140-L186
[reads-eq]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/BinarySearch.lean#L334-L348
[reads-le]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/BinarySearch.lean#L350-L356
[mi-wp]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/VC.lean#L31-L43
[wp-sound]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/VC.lean#L45-L60
[program-vc]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/BinarySearch.lean#L163-L171
[total-correct]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/BinarySearch.lean#L252-L261
[verified]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExt/Languages/MiniImp/BinarySearch.lean#L358-L381
[client]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExtTest/Languages/MiniImp/BinarySearchCostTests.lean#L87-L98
[scan]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExtTest/Languages/MiniImp/BinarySearchCostTests.lean#L65-L78
[cost-sweep]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExtTest/Languages/MiniImp/BinarySearchCostTests.lean#L119-L146
[bs-tests]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExtTest/Languages/MiniImp/BinarySearchTests.lean#L57-L73
[bs-intervals]: https://github.com/akiezun/atlas-lean/blob/ca4511b77d80c9388143b9a2858fdbb81bffc6ef/CSLibExtTest/Languages/MiniImp/BinarySearchTests.lean#L84-L107
[boole]: https://github.com/leanprover/cslib/blob/5b56df99362532c46e1175381fbbdd755bd56030/Cslib/Languages/Boole/README.md
