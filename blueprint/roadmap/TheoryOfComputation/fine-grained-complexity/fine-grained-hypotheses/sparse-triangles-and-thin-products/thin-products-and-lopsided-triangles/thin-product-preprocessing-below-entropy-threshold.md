# Thin-product preprocessing below the entropy threshold

For every real $\varepsilon<\varepsilon_*$ and every $q>0$ there is $\gamma>0$ such that, for each natural $c$, the query model has preprocessing time and final-memory radius $O(N^2\log^2 D/D^\gamma)$ and query time $O(D^q\log D)$. A pair of programs, three query cells, a word-width slope and a common constant serve all thin inputs with $1\le N$, $2\le D\le N^\varepsilon$ and $U=N^c$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof outline

Formalize preprocessing and its final memory bound separately from the query invariant. Prove the stated bounds at all admissible widths.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3932-L3947); [ThreeSumApsp.wordRam_theorem_24](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L189-L191).
