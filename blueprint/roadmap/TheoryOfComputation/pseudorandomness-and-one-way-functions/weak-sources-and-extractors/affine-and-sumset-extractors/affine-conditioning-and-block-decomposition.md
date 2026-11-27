# Affine conditioning and block decomposition

(Affine conditioning.) Let $X$ be an affine source on $\mathbb{F}_2^n$ and $L$ an affine map. Then $X = A + B$ for independent affine sources $A$ and $B$ such that $L$ is constant on the support of $B$, $A$ is an affine function of $L(A)$, and conditioning $X$ on $L(X) = \ell$ yields a translate of $B$.

(Block decomposition.) If $\mathbb{F}_2^n$ is partitioned into blocks and $X$ is an affine source of codimension at most $r$, then $X$ is a mixture of product distributions of independent affine sources on the blocks, each of codimension at most $r$ in its block.

## Proof sketch

Write the direction $V$ of $X$ as $(V \cap \ker L_0) \oplus W$ for a complement $W$, where $L_0$ is the linear part of $L$; then $A$ is uniform on a translate of $W$, $B$ uniform on $V \cap \ker L_0$, and $L_0$ is injective on $W$. For blocks, condition successively on the projections to earlier blocks, applying the conditioning lemma.

## Depends on

- [Affine sources, affine extractors and sumset extractors](affine-sources-and-sumset-extractors.md)

## Sources

- X. Li, "Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science, 2023.
- X. Li and Y. Zhong, "Explicit Directional Affine Extractors and Improved Hardness for Linear Branching Programs", 39th Computational Complexity Conference (CCC 2024), 2024.
