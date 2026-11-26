# Worst-input parity lower bound for constant-depth quantum circuits

A circuit on $N$ qubits consists of an ordered list of layers. Each layer has pairwise disjoint gate supports; allowed gates are arbitrary one-qubit unitaries and multi-controlled Toffoli gates with any control set disjoint from the target. A Toffoli flips its target exactly when all controls are one, with an empty control set allowed. The layer acts by the product of its gate matrices, and the circuit $U$ applies the layers in chronological order.

For input $x\in\{0,1\}^n$ with $n\le N$, the first $n$ qubits contain $x$ and the rest start at zero. For an output index $o$, the success probability sums $|U_{y,(x,0)}|^2$ over all basis outputs $y$ whose bit $y_o$ is the sum of input bits modulo two; no condition is imposed on the other outputs. For every fixed natural depth bound $d$, real $c\ge1$, and $0<\varepsilon\le1/2$, there exists $n_0$ such that for every $n\ge n_0$, $n\le N\le n^c$, every circuit with at most $d$ layers, and each $o$, some input has success probability strictly less than $1/2+\varepsilon$.

**Conventions.** Use the computational-basis tensor register, arbitrary one-qubit unitaries, a gate with an unbounded control set, disjoint-support layers and the Born probability of one measured output. A fixed finite gate set on bounded-size supports would be a different circuit model.

## Depends on

- [Disjoint-support quantum layers with unbounded controls](unbounded-control-quantum-circuits.md)

## Proof depends on

Product-projection localization for this gate model and a bound controlling the influence of the remaining input coordinates on one output at fixed depth and polynomial register width.

## Expansion

Identify each physical gate's matrix and each layer's schedule with the native circuit semantics, including ancilla initialization and disposal of garbage. Separate the localization estimate from the parity contradiction. Do not replace worst-input failure by an assumption that all outputs are clean or by a restriction on auxiliary entanglement beyond the stated initial state.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/QACParity.lean#L71-L73)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/274.md)
- [Accompanying manuscript: Product-projection localization and the $\mathrm{QAC}^0$ parity lower bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Product-projection-localization-and-the-QAC0-parity-lower-bound-September-24-2026/paper.pdf)
