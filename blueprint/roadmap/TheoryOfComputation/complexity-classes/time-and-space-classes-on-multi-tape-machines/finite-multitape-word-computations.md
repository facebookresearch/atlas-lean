# Finite multitape computations with full-tape binary output

A machine has finite control with initial state 0 and finitely many two-sided tapes, at least one. Its alphabet contains 0 (blank), 1 (false), and 2 (true), and may contain further symbols. Input occupies tape zero at the nonnegative cells starting at 0, with blanks elsewhere. All heads start at 0. One transition reads the complete tuple of head symbols and the state. If no action is given, the configuration is halted, with no additional transition charged. Otherwise it changes state, writes one symbol at every current head, and moves each head independently left, right or not at all. A halted configuration is stationary. A word is output only when halted and the entire tape zero equals the binary word at the same starting position, blank everywhere else. There are no output conditions on the other tapes.

For a language, an exponential-time decider halts within $2^{c(L+1)^d}$ with the one-bit membership word on every input of length $L$. A polynomial-time many-one reduction between two languages halts with an output word within $c(L+1)^d$ and preserves membership in both directions, on every word. The natural constants can be chosen separately for each decider and reducer. Exponential-time completeness means membership in this exponential-time class and a reduction from every language of the class. Do not identify this model with a stack reset or a mere output prefix.

## Sources

- [The underlying machine, exact output and complexity predicates](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VariableWL.lean#L9-L77).
