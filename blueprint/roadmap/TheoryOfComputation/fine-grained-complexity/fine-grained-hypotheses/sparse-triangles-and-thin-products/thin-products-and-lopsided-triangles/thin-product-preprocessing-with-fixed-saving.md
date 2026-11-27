# Thin-product preprocessing and query bounds for $N\ge D^{18}$

Let $1\le D$ and $D^{18}\le N$. For each natural $c$, one pair of preprocessing and query programs, three query cells, one slope and one common constant work for every thin input with $U=N^c$, at all admissible word widths. The preprocessing time and final-memory radius are $O(N^2/D^{0.063})$; any online query costs $O(D^{0.437})$ steps with the persistent query convention.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)

## Proof outline

Formalize preprocessing and its final memory bound separately from the query invariant. Prove the stated bounds at all admissible widths.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3959-L3971); [ThreeSumApsp.wordRam_corollary_26](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L197-L199).
- Anthropic, [ThreeSumApsp.wordRam_theorem_3](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L256-L258) (first conjunct).
