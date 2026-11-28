# Offline thin-product entry bound below the entropy threshold

For every real $\varepsilon<\varepsilon_*$ and $\kappa>0$ there is $\gamma>0$ such that, for each natural $c$, one deterministic program computes the given entries in $O(N^2\log^2 D/D^\gamma)$ time for all $1\le N$, $2\le D\le N^\varepsilon$, $U=N^c$ and $|W|\le N^2/D^\kappa$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof outline

Formalize the encoding, box counts and entry-recovery cost; verify uniformity of the program and of its constants over the allowed matrix dimensions.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3949-L3958); [ThreeSumApsp.wordRam_theorem_25](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L193-L195).
