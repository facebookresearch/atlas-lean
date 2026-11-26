# Parameterized thin-product preprocessing and queries

Let $m,L,t\in\mathbb N$ obey $m\ge1$, $L\ge10m$, $t\le m$ and impose $D=4^m$, $N\ge\sqrt K N_0$, $U=N^c$. Set $B=Lm\rho^tN^2/(1-\rho)+N10^L/(\sqrt K N_0)$ and $J=L\sum_{d=0}^t\alpha_d$. For each natural $c$, there are programs, three query cells, slope and one constant chosen before $m,L,t$ that give preprocessing time and final-memory radius $O(B)$ and persistent query time $O(J)$. Preprocessing receives $m,L,t$ after $N,D$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof outline

Formalize preprocessing and its final memory bound separately from the query invariant. Prove the stated bounds at all admissible widths.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3987-L4007); [ThreeSumApsp.wordRam_theorem_30](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L205-L207).
