# Additional rounded time bounds for integer APSP and min-plus product

For each natural $\kappa$, on integer inputs of absolute value at most $n^\kappa$, there are deterministic programs on the restricted machine for directed APSP without negative closed walks and for the square min-plus product, each in $O(n^{2.9995})$ time. These are the rounded bounds; the other two clauses of the source result are the [tripartite Exact Triangle $O(n^{2.9983})$ bound](exact-triangle-tripartite-time.md) and the [3SUM $O(n^{1.9992})$ bound](three-sum-time.md). These are the deterministic integer bounds only.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Integer min-plus time](min-plus-product-time.md)
- [Directed integer APSP time](all-pairs-shortest-paths-time.md)

## Proof outline

Formalize the reduction on the exact instance domain and show its running time in the restricted word RAM, including padding and all terminal outcomes.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4145-L4158); [ThreeSumApsp.wordRam_theorem_2](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L248-L250).
