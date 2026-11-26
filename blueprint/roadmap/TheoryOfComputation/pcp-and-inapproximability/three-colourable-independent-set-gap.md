# Gap reduction to independent sets in three-colourable graphs

For each real $0<\delta<1/3$ there is a deterministic [finite-alphabet TM2](../turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md) polynomial-time reduction for Boolean CNF of clause width at most three. Its input encoder is the identity on **all** binary words, and its output is a nonempty finite simple graph in full row-major adjacency-matrix encoding. A separate natural-coefficient polynomial bounds that encoded output length on every word. Encode a natural by framing its low-to-high `Nat.bits` (each bit $b$ is emitted as $1b$, terminated by $0$). Encode a signed literal by its sign followed by its framed variable name, and prefix clause and formula lists with their framed lengths. Encode a graph by its framed order followed by all adjacency entries. For any valid encoding of a satisfiable formula the graph admits a proper three-colouring; for any valid encoding of an unsatisfiable formula its largest independent set has size strictly less than $\delta$ times its order. The computation is total on words, but those last two requirements apply only to actual encoded formulas.

## Depends on

- [Exact charged TM2 computation and encoded output](../turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md)
- Binary width-at-most-three CNF, finite-alphabet polynomial-time computation, and nonempty finite simple graph encodings.

## Proof outline

Separate the combinatorial gap gadget from the total binary transducer and its output-size certificate; compare finite tape alphabets and encodings with the library's reduction interface. Preserve strict soundness for a real threshold, rather than weakening it to a non-strict rational approximation claim.

- Gap-producing completeness/soundness maps and proof that the gadget composition emits the entire matrix within the bit budget.

## Sources

- [Comparator statement: `OAI.LargeIndependentSets.mainTheoremReal`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IndependentSets.lean#L76-L80)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/106.md)
