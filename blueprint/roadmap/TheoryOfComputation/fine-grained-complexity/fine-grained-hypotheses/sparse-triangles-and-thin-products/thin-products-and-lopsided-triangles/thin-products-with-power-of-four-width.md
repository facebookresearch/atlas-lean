# Offline thin-product bound for a power-of-four width

For each natural $c$, one program, slope and constant suffice whenever $D$ is a power of four, $4\le D$, $D^{18}\le N$, $U=N^c$, and $|W|\le N^2/\sqrt D$. The requested entries are computed within $O(N^2\log^2 D/D^{1/18})$ steps at every allowed word width.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)

## Proof depends on

- [Reusable stronger sparse-entry bound](thin-product-sparse-entry-time.md)

## Proof outline

Formalize the encoding, box counts and entry-recovery cost; verify uniformity of the program and of its constants over the allowed matrix dimensions.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3828-L3843); [ThreeSumApsp.wordRam_theorem_5](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L160-L162).
