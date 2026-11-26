# Exponentially small correlation of small circuits with quadratic forms

Let $Q$ be a quadratic form over $\mathbb{F}_2$ in $n$ variables whose polar matrix $Q+Q^{T}$ has cut rank at least $\lfloor n/2\rfloor-\tau n$ across every set of $\lfloor n/2\rfloor$ coordinates. Then for every $A$ for which the layout hypothesis $\mathrm{LB}(3,A)$ holds, every fan-in-two circuit with fewer than $(1+1/(2A))n$ multiary gates (up to lower-order terms) has correlation $2^{-\Omega(n)}$ with $(-1)^{Q}$. Using real-rank communication bounds, $U_2$ circuits with fewer than $2.8006n$ binary gates have exponentially small correlation with such quadratic forms.

## Proof sketch

A narrow layout partitions the inputs, at the widest step, into few combinatorial rectangles on which the circuit is constant; by Lindsey's lemma, a bilinear form of high rank is nearly balanced on every large rectangle, so the total correlation is exponentially small. The real-rank version replaces rectangle counts by the rank of the sign matrix of the circuit's cut function.

## Depends on

- [Layouts of multigraphs, cycle rank and the layout hypothesis](../frontier-method/layouts-and-the-layout-hypothesis.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Proof depends on

- [From small circuits to wide constraint networks](../frontier-method/from-circuits-to-constraint-networks.md)
- [Lindsey's lemma over GF(2)](../../../LinearAlgebra/matrix-algebra/rank-bounds-for-complexity/lindsey-lemma-over-gf2.md)
- [Real-rank Lindsey lemma](../../../LinearAlgebra/matrix-algebra/rank-bounds-for-complexity/real-rank-lindsey-lemma.md)

## Sources

- Stasys Jukna, "Extremal Combinatorics: With Applications in Computer Science", Springer, 2011.
- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
- Samuel Fiorini, Serge Massar, Sebastian Pokutta et al., "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM, 2015.
