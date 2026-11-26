# Thin-product preprocessing and queries below the decimal threshold

For every real $\varepsilon<0.1204$ and $q>0$, some $\gamma>0$ gives the following: for each natural $c$, there is one data structure with time and final-memory radius $O(N^2/D^\gamma)$ for preprocessing and persistent per-query time $O(D^q)$, for all $1\le N$, $1\le D\le N^\varepsilon$ and $U=N^c$. This is the second part of Theorem 3; the first is the separate fixed-saving preprocessing bound.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)

## Proof depends on

- [Fixed-saving thin-product preprocessing](thin-product-preprocessing-with-fixed-saving.md)
- [Entropy-tuned query bounds](entropy-tuned-thin-product-queries.md)

## Proof outline

Formalize preprocessing and its final memory bound separately from the query invariant. Prove the stated bounds at all admissible widths.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4018-L4032); [ThreeSumApsp.wordRam_theorem_3](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L256-L258).
