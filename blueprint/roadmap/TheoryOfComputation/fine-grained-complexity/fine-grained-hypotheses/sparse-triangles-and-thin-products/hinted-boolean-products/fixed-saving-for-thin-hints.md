# Phased running times for thin Boolean hints

For both the vector-hinted and matrix-vector-hinted problems, for every $0<\tau<1/18$, phase 2 takes $O(n^{2-0.063\tau})$ and phase 3 takes $O(n^{1+0.437\tau})$. For the vector-matrix-vector variant, for every $0<\tau_1<\tau_2/18$ with $\tau_2<1$, phases 2, 3 and 4 take respectively $O(n^{\tau_1})$, $O(n^{1+\tau_2-0.063\tau_1})$, and $O(n^{\tau_2+0.437\tau_1})$. In every case phase 1 is polynomial. The programs and exponents are chosen before the input and valid word width.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Phased Boolean products](../machine-and-inputs/three-hinted-boolean-products.md)
- [Decay and entropy parameters](../machine-and-inputs/thin-product-decay-parameters.md)

## Proof depends on

- [Thin-product preprocessing](../thin-products-and-lopsided-triangles/thin-product-preprocessing-with-fixed-saving.md)

## Proof outline

Formalize the matrix block construction and its correctness across phases; verify time in each phase without using input supplied later.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4080-L4092); [ThreeSumApsp.wordRam_corollary_40_times](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L229-L231), [ThreeSumApsp.wordRam_theorem_4](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L260-L262).
