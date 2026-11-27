# Affine sources, affine extractors and sumset extractors

An *$(n, k)$ affine source* is the uniform distribution on an affine subspace of $\mathbb{F}_2^n$ of dimension $k$; it has min-entropy exactly $k$, and its image under an affine map is an affine source whose dimension is the rank of the linear part on its direction. A function $f : \{0,1\}^n \to \{0,1\}^m$ is a *$(k, \varepsilon)$ affine extractor* if $f(X)$ is $\varepsilon$-close to uniform for every affine source of dimension at least $k$, and a *$(k_1, k_2, \varepsilon)$ sumset extractor* if $f(A + B)$ is $\varepsilon$-close to uniform for all independent sources $A, B$ on $\{0,1\}^n$ of min-entropies at least $k_1, k_2$ (sum is bitwise XOR). A sumset extractor for $(k_1, k_2)$ yields an affine extractor and hence an affine disperser at dimension $k_1 + k_2$, and is a two-source extractor after zero-padding the two inputs into disjoint coordinates.

## Depends on

- [k-sources, (k, ε)-sources and flat sources](../weak-random-sources.md)
- [Affine dispersers](../../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/gate-elimination-and-explicit-lower-bounds/affine-dispersers.md)
- [Two-source extractors](../two-source-extractors.md)

## Sources

- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023 (numbering of arXiv:2303.06802), Definitions 3.1 and 7.8.
- E. Chattopadhyay and J.-J. Liao, "Extractors for Sum of Two Sources", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC 2022), 2022, Definitions 1.2 and 1.8 (arXiv:2110.12652).
- X. Li and Y. Zhong, "Explicit Directional Affine Extractors and Improved Hardness for Linear Branching Programs", 39th Computational Complexity Conference (CCC 2024), 2024.
