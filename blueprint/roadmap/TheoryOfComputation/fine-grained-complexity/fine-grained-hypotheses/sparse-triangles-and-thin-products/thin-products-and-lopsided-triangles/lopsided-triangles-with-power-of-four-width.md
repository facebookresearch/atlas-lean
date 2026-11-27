# Lopsided triangle counting and detection at power-of-four widths

For all thin lopsided inputs with 0–1 entries, $U=1$, and $D$ a power of four with $4\le D$ and $D^{18}\le N$, there are separate deterministic programs for counting and detection at all requested pairs. One common slope and time constant work for both programs; each runs in $O((N^2+|W|\sqrt D)\log^2 D/D^{1/18})$ time at every admissible word width.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)

## Proof depends on

- [Offline thin-product bound](thin-product-sparse-entry-time.md)

## Proof outline

Formalize the encoding, box counts and entry-recovery cost; verify uniformity of the program and of its constants over the allowed matrix dimensions.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3845-L3876); [ThreeSumApsp.wordRam_corollary_15](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L164-L166).
