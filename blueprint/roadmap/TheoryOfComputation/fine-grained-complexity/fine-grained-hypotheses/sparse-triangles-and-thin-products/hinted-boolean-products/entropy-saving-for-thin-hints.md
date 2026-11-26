# Phased running times up to the thin-hint entropy threshold

For every $0<\tau<\varepsilon_*$ some $\gamma>0$ gives both the vector-hinted and matrix-vector-hinted problems phase 2 time $O(n^{2-\gamma\tau})$ and phase 3 time $O(n^{1+\tau/2})$. For every $0<\tau_1<\varepsilon_*\tau_2$ with $\tau_2<1$, some $\gamma>0$ gives the vector-matrix-vector variant phase times $O(n^{\tau_1})$, $O(n^{1+\tau_2-\gamma\tau_1})$ and $O(n^{\tau_2+\tau_1/2})$ after polynomial phase 1. The bounds use the fixed programs and input conventions of the phased model.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Phased Boolean products](../machine-and-inputs/three-hinted-boolean-products.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof outline

Formalize the matrix block construction and its correctness across phases; verify time in each phase without using input supplied later.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4094-L4109); [ThreeSumApsp.wordRam_corollary_40_general_times](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L233-L236).
