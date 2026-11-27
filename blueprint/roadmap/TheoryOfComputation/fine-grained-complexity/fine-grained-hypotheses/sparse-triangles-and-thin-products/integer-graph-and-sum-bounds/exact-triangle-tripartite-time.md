# Tripartite integer Exact Triangle in time $O(n^{2.9983})$

For every natural $\kappa$, tripartite Exact Triangle on three parts of size $n$ can be solved deterministically on the restricted word RAM in $O(n^{3-0.0017})$ time for size $n$ and absolute input bound $n^\kappa$, with the specified input and output conventions. The program and slope may depend on $\kappa$ and must work for every admissible word width.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof outline

Formalize the reduction on the exact instance domain and show its running time in the restricted word RAM, including padding and all terminal outcomes.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean#L72-L86); [endStatement_theorem_19](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/EndStatement.lean#L56-L59).
