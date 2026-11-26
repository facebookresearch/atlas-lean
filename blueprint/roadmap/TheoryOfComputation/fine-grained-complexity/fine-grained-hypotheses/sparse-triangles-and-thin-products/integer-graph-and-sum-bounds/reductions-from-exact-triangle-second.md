# Polylogarithmic bounds for integer min-plus product and directed APSP

For each $\kappa\in\mathbb N$, the min-plus product and directed APSP (with no negative closed walks) each have a $\widetilde O(n^{3-0.00175/3})$ bound. Each bound quantifies its own uniform deterministic program, with the absolute input bound $n^\kappa$; the log exponent may depend on $\kappa$. The other clauses of the same source endpoint are the [rounded 3SUM bound](three-sum-time.md), the [rounded min-plus product bound](min-plus-product-time.md), and the [rounded directed APSP bound](all-pairs-shortest-paths-time.md).

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Two additional time bounds for tripartite integer Exact Triangle](exact-triangle-three-time-bounds.md)

## Proof outline

Use the uniform Exact Triangle bound with saving $0.00175$ and one logarithmic factor. In the min-plus reduction the saving is divided by three, and APSP uses that min-plus bound with additional polylogarithmic overhead. Track the padding, weight bounds and layouts of the composed programs. The rounded Triangle bound with saving $0.0017$ does not give the displayed polylogarithmic exponent by this route.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3888-L3910); [ThreeSumApsp.wordRam_theorem_22_second](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L180-L182).
- Anthropic, [the implemented reduction and its time loss](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean#L80-L113).
