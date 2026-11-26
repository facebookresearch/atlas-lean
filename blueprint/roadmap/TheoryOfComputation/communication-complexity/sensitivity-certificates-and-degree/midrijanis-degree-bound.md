# Midrijanis: D(f) ≤ deg(f)·bs(f) ≤ 2 deg(f)³

For every total Boolean function $f$,

$$D(f) \le \deg(f) \cdot bs(f) \le 2 \deg(f)^3.$$

## Proof sketch

Choose a set $S$ with $|S| = \deg(f)$ and $\hat f(S) \ne 0$ (maximal Fourier support). Every face parallel to $S$ is nonconstant, so every input has a sensitive block inside $S$. Query all of $S$; after fixing these answers, the block inside $S$ is disjoint from all remaining sensitive blocks, so block sensitivity drops by at least one, while the degree does not increase. Induct on $bs$; finish with Nisan–Szegedy $bs \le 2\deg^2$.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Nisan–Szegedy: block sensitivity is at most quadratic in degree and approximate degree](nisan-szegedy-bounds.md)
- [Faces parallel to a maximal Fourier support are nonconstant](faces-parallel-to-maximal-fourier-support.md)

## Sources

- G. Midrijanis, "Exact Quantum Query Complexity for Total Boolean Functions", arXiv:quant-ph/0403168, 2004.
- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
