# Disjoint-support quantum layers with unbounded controls

Use a finite qubit register with computational basis indexed by Boolean words. A layer is a simultaneous product of gates of pairwise disjoint supports, and depth counts such layers. The permitted gates are arbitrary single-qubit unitaries and generalized Toffoli gates whose target flips when all specified controls are one. There is no fixed arity cap on the controls. The input occupies its designated qubits in the computational basis and auxiliary qubits start at zero. An output is one designated measured bit; its success probability is the squared-norm mass of all output basis strings with the correct parity on that bit.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/QACParity.lean#L10-L67)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RegularParity.lean#L10-L59)
