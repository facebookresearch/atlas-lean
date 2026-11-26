# Minimum- and maximum-weight multipartite clique

For every fixed $k\ge3$ and every natural $\kappa$, one deterministic program each for minimization and maximization (with their own bounds and slopes) finds, rather than merely tests for, an extremal weight clique in a complete $k$-partite graph with $n\ge1$ vertices per part. The time is $O(n^{k-0.0017\lfloor k/3\rfloor})$. The output is one vertex index per part; all input blocks satisfy the bound $n^\kappa$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Headline zero-weight clique time](zero-weight-multipartite-clique-time.md)

## Proof outline

Formalize the reduction on the exact instance domain and show its running time in the restricted word RAM, including padding and all terminal outcomes.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4069-L4076); [ThreeSumApsp.wordRam_corollary_39_min_max](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L225-L227).
