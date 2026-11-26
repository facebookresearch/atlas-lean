# Integer min-plus product in time $O(n^{2.99942})$

For every natural $\kappa$, the min-plus product of two square integer matrices can be solved deterministically on the restricted word RAM in $O(n^{2.99942})$ time for size $n$ and absolute input bound $n^\kappa$, with the specified input and output conventions. The program and slope may depend on $\kappa$ and must work for every admissible word width.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Two additional time bounds for tripartite integer Exact Triangle](exact-triangle-three-time-bounds.md)

## Proof outline

Use the stronger Exact Triangle bound with saving $\delta=0.00175$ and one logarithmic factor. The reduction goes through Negative Triangle and gives min-plus product time $n^{3-\delta/3}$ times a polylogarithmic factor, including input and output layout. The weaker rounded Triangle saving $0.0017$ would give $3-0.0017/3>2.99942$. With the stronger saving, $3-0.00175/3<2.99942$, so the polylogarithmic factor can be absorbed for the stated exponent.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean#L98-L107); [endStatement_theorem_22_MinPlus](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/EndStatement.lean#L66-L69).
- Anthropic, [the implemented reduction and its time loss](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/ThreeSumApsp/RunningTimes/Sec3/Theorem22.lean#L61-L85).
