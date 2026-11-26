# Finite-alphabet TM2 with binary input and output

Take Mathlib’s `Turing.TM2ComputableInPolyTime e_in e_out F` with each stack alphabet explicitly finite. Its `FinTM2` has finitely many stacks, labels and internal states, one finite stack alphabet per stack, a designated input stack and output stack, a start label and an initial internal state. Each label has a finite statement tree. Along the selected branch it can push a state-dependent symbol, peek at a stack head (optional on empty), pop its optional head (tail of an empty stack remains empty), update the internal state, and branch on it. The branch ends with a jump to a label or halt. One charged step executes this entire statement tree, not one step per primitive within it. A halted configuration has no outgoing step.

Both designated stack alphabets have specified bijections with `Bool`. The initial stacks are empty except for the input stack, which contains `e_in(x)` converted under the inverse bijection in list order. Starting at the main label and initial state, the machine must reach the configuration with absent label, exactly `e_out(F(x))` on the output stack under its inverse bijection, all other stacks empty, and internal state equal to the initial state. The allowed bound is a single polynomial with natural coefficients evaluated at the length of the encoded input, including any seed or framing when it is part of that input. The output encoder is not a free computation performed after the halt; these exact bits must be on the stack. No conversion to a different bit model is presumed.

## Depends on

- The finite stack alphabet and labelled-block transition syntax of `Turing.FinTM2`.

## Related results

The [composition theorem for native TM2 polynomial-time functions](composition-of-multi-stack-machines/tm2-computable-in-poly-time-comp.md) uses the computability predicate; it is not part of its definition.

## Sources

- [Application of the exact predicate to binary multigraph matching](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinaryMatching.lean#L57-L73)
- [Application to the singleton-loop input and output encoders](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SingletonLoopMatching.lean#L100-L129)
- [Application to paired binary input and seeds](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianRecovery.lean#L62-L76)
- [FinTM2, binary alphabet bijections, initialization, exact halt and polynomial budget](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Computability/TuringMachine/Computable.lean#L46-L174)
- [Statement tree operations and one-block step](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Computability/TuringMachine/StackTuringMachine.lean#L125-L173)
