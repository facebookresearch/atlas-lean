# Deterministic approximate counting in binary multigraphs

A graph of order $n$ is specified by a list of distinct pairs $0\le i<j<n$ with nonnegative integer multiplicities $w_{ij}$; absent pairs have multiplicity zero. Write $Z$ for the sum, over perfect matchings of the complete simple graph on these vertices, of the product of $w_{ij}$ over the chosen pairs. The input contains the order, record count, and successive triples, encoding each natural by a prefix of as many zero bits as the numeral has bits, then one bit, then its low-to-high `Nat.bits` payload.

There exist a function $A$ from these inputs to the naturals and one [finite-alphabet TM2](../turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md) polynomial-time computation of $A$, with this input encoder and **unframed** `Nat.bits` for output. Independently of the machine’s time polynomial, there is a natural-coefficient polynomial $P$ such that the length of `Nat.bits` of $A$ is at most $P$ evaluated at the full encoded input length. For all inputs $A\le Z\le2^{9n}A$ and $A=0\iff Z=0$. At order zero the empty matching contributes one.

## Depends on

- [Exact finite-alphabet TM2 input, output and charged-step semantics](../turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md)
- Perfect-matchings of labelled vertices with binary multiplicities and finite-alphabet multitape computation on framed natural numbers.

## Proof outline

Verify that the weighted sum counts the parallel choices without expanding binary multiplicities into a unary graph. Separate the multiplicative estimate, zero test and output-length bound.

- Entropy-based approximation plus bit-complexity bounds for binary weights and integral output.

## Sources

- [Comparator statement: `OAI.BinaryMatching.deterministic_approximate_counting`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinaryMatching.lean#L66-L73)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/113.md)
- [Weighted matching count, input framing and two polynomial bounds](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinaryMatching.lean#L31-L73)
