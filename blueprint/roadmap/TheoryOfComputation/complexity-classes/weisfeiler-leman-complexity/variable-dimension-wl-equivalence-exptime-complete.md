# EXPTIME-completeness of unrestricted variable-dimension WL equivalence

An input is two consecutive graph encodings (order as a unary length prefix of the binary numeral followed by its bits, then the full row-major adjacency matrix) followed by a similarly framed binary $k\ge2$. Graphs are finite, simple and uncolored. Membership requires equality of their tuple-color histograms at every round of joint $k$-dimensional refinement: initialize by all tuple equalities and adjacencies and at each round retain the old color and the multiset over vertices $z$ of the full vectors of old colors obtained by replacing each coordinate in turn with $z$. Malformed inputs are not members. This language is EXPTIME-complete. In the source model a fixed finite-state, finite-alphabet multitape binary machine halts with a single bit in time $2^{c(L+1)^d}$ on all input words; hardness is under total polynomial-time many-one reductions in that machine model (replacing the first tape by the result word).

## Depends on

- [Finite multitape computation and full-tape binary output](../time-and-space-classes-on-multi-tape-machines/finite-multitape-word-computations.md)
- Joint tuple histogram equivalence, full binary encodings and their validity checks, and finite-alphabet local multitape EXPTIME and reduction semantics.

## Proof outline

Separate the upper bound from the hardness transformation. Prove the model bridge with the exact halt/output relation; do not identify dimension encoded in binary with any fixed-dimension bound. The connected subcubic restriction is a separate theorem.

- Exponential-time decision procedure and unconditional hardness reduction for the unrestricted language.

## Sources

- [Comparator statement: `OAI.VariableWL.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VariableWL.lean#L125-L127)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/133.md)
- [Finite multitape machine, exact full-tape halt output and complexity predicates](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VariableWL.lean#L11-L77)
