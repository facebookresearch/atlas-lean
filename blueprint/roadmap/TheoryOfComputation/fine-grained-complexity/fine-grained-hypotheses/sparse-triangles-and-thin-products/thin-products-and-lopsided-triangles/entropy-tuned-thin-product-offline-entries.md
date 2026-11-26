# Entropy-tuned offline thin-product entry bound

For reals $c>10$, $0<\theta<0.9$ and $\varepsilon<R_c(\gamma)$, use the stated entropy parameters $\gamma,q$. For each natural $c_0$, the input satisfies $1\le N$, $2\le D\le N^\varepsilon$ and $U=N^{c_0}$. For each $\kappa>0$ and $|W|\le N^2/D^\kappa$, one program, slope and constant give running time $O(N^2\log^2 D(D^{-\gamma}+D^{q-\kappa}))$. The program and constants are chosen before the matrices and list of positions.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof depends on

- [Entropy-tuned thin-product query bounds](entropy-tuned-thin-product-queries.md)

## Proof outline

Formalize the encoding, box counts and entry-recovery cost; verify uniformity of the program and of its constants over the allowed matrix dimensions.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4034-L4045); [ThreeSumApsp.wordRam_corollary_32](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L217-L219).
