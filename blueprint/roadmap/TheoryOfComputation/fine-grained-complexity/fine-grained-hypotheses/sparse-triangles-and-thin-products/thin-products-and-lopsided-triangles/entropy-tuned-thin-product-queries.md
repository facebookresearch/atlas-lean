# Entropy-tuned thin-product query bounds

For reals $c>10$, $0<\theta<0.9$ and $\varepsilon<R_c(\gamma)$, use the stated entropy parameters $\gamma,q$. For each natural $c_0$, the input satisfies $1\le N$, $2\le D\le N^\varepsilon$ and $U=N^{c_0}$. One preprocessing and query pair, slope, three query cells and a common constant give preprocessing time and final-memory radius $O(N^2\log^2 D/D^\gamma)$ and query time $O(D^q\log D)$ over the entire input domain.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof outline

Formalize preprocessing and its final memory bound separately from the query invariant. Prove the stated bounds at all admissible widths.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4008-L4016); [ThreeSumApsp.wordRam_corollary_31](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L213-L215).
