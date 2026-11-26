# Two additional time bounds for tripartite integer Exact Triangle

For each natural $\kappa$, tripartite Exact Triangle with bound $n^\kappa$ on the weights admits deterministic word-RAM programs in $O(n^{3-1/648}\log^2 n)$ and $O(n^{3-0.00175}\log n)$ time. These are existential statements about programs; they do not require that the corresponding proofs use different algorithms.

The source’s third clause is the separately stated [rounded $O(n^{3-0.0017})$ bound](exact-triangle-tripartite-time.md).

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Offline thin-product bound](../thin-products-and-lopsided-triangles/thin-product-sparse-entry-time.md)

## Proof outline

Formalize the reduction on the exact instance domain and show its running time in the restricted word RAM, including padding and all terminal outcomes.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3878-L3887); [ThreeSumApsp.wordRam_theorem_19](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L172-L174).
