# A 4.6362n frontier lower bound for U2 circuits

Let $S_n\subseteq\{0,1\}^n$ satisfy the hypotheses of the unconditional frontier theorem ($K_n$-rectangle-free with $\log K_n=o(n)$ and $|S_n|\ge2^{n-o(n)}$). Then for every $\varepsilon>0$ and all large $n$, every circuit over a $U_2$ basis (binary gates are polarized conjunctions; XOR-type gates excluded) deciding $S_n$, deterministically or nondeterministically, has more than $(4.6362-\varepsilon)n$ binary gates; the same coefficient holds for average-case agreement on sets of small rectangle bias. In particular this applies to De Morgan circuits.

## Proof sketch

For $U_2$ circuits, matched pairs of AND-type gates can be compressed into $3$-state branching-program steps (a transfer-matrix analysis of matched gate pairs), and saturated compressions of the circuit graph are sparse cubic multigraphs; combining this with a weighted matching theorem and Gaussian two-cap layout bounds improves the effective layout coefficient beyond the spanning-tree value.

## Depends on

- [The full binary basis B2 and the basis U2](../circuit-models-and-complexity-measures/full-binary-basis-b2-and-u2.md)
- [Rectangle-free sets and rectangle bias](../frontier-method/rectangle-free-sets-and-rectangle-bias.md)

## Proof depends on

- [Unconditional frontier lower bounds of (2 - ε)n](../frontier-method/unconditional-frontier-lower-bounds.md)
- [Cutwidth and bisection bounds for cubic graphs via median-switched Gaussian sweeps](cubic-cutwidth-via-gaussian-sweeps.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
