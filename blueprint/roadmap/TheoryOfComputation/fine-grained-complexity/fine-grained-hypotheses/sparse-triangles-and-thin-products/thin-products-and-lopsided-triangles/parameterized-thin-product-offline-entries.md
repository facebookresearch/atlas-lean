# Parameterized thin-product offline entries

Let $m,L,t\in\mathbb N$ obey $m\ge1$, $L\ge10m$, $t\le m$ and impose $D=4^m$, $N\ge\sqrt K N_0$, $U=N^c$. Set $B=Lm\rho^tN^2/(1-\rho)+N10^L/(\sqrt K N_0)$ and $J=L\sum_{d=0}^t\alpha_d$. For each natural $c$ there is one program, slope and constant chosen before $m,L,t$, which outputs all requested entries in $O(|W|J+B)$ time. It receives $m,L,t$ after $N,D,|W|$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof outline

Formalize the encoding, box counts and entry-recovery cost; verify uniformity of the program and of its constants over the allowed matrix dimensions.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3987-L4007); [ThreeSumApsp.wordRam_theorem_30_wanted](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L209-L211).
