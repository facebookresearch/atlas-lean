# Deterministic approximate matching count with singleton loops

Use a binary-multiplicity loopless multigraph as in the [ordinary approximation](deterministic-binary-multigraph-matching-count.md), followed by a framed loop-record count and distinct framed pairs (vertex index, nonnegative multiplicity); missing entries have multiplicity zero. A loop covers just its own vertex. If $M$ ranges over ordinary partial matchings, $Z$ is the sum of the product of ordinary edge multiplicities on $M$ times the product of loop multiplicities at each uncovered vertex.

There exist an output function $A$ with values $(a,b)\in\mathbb N^2$ and a [finite-alphabet TM2](../turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md) polynomial-time computation of $A$ on that input encoding. Its output is the concatenation of the framed naturals $a,b$, not their unframed bits and not the result of a rational division on the tape. A separately quantified polynomial bounds the length of this entire framed output as a function of the complete input length. For every input $b>0$, $a\le bZ\le2^{18n}a$, and $a=0\iff Z=0$. The time polynomial bounds the native block transitions, while the length polynomial counts the two payloads and their two prefixes and delimiters together.

## Depends on

- [Exact finite-alphabet TM2 native computation](../turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md)
- Binary multiplicity encoding and the singleton-loop count as partial matching sum.

## Proof outline

Establish the transfer identity on the count, then its effect on the $2^{18n}$ factor and the zero case. Probe an order-one graph with and without loops; one singleton loop covers the vertex.

- Multiplicity-preserving transfer to a loopless approximation and polynomial control of the rational denominator and output encoding.

## Sources

- [Comparator statement: `OAI.LoopMatching.fullEndpoint`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SingletonLoopMatching.lean#L126-L129)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/113.md)
- [Loop records, singleton coverage, framed encoders and independent length bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SingletonLoopMatching.lean#L59-L129)
