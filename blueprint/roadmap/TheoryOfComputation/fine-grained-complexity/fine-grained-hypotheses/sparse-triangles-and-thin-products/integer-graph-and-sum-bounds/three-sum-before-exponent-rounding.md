# Integer 3SUM before rounding the exponents

For each natural $\kappa$ the two bounds $n^{2-1/1296+o(1)}$ and $n^{2-0.00175/2+o(1)}$ both hold for deterministic 3SUM on lists of $n$ integers bounded by $n^\kappa$. In each bound use a possibly different program, slope, constant and real sequence $e_n\to0$, with time bounded by a constant times $n^{a+e_n}+1$ for the displayed base exponent $a$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Two additional time bounds for tripartite integer Exact Triangle](exact-triangle-three-time-bounds.md)

## Proof outline

Reduce through Convolution-3SUM. The two Triangle bounds with savings $1/648$ and $0.00175$ give 3SUM savings $1/1296$ and $0.00175/2$, respectively, up to fixed polylogarithmic factors. Convert those factors to an exponent loss tending to zero while keeping the original distinct-position and input-size conventions.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3912-L3920); [ThreeSumApsp.wordRam_theorem_22_threeSum](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L184-L187).
- Anthropic, [the implemented reduction and its time loss](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean#L130-L148).
