# Zero-weight multipartite clique with a triangle saving

For every natural $\kappa$, for each fixed $k\ge3$, zero-weight $k$-clique on $k$ parts of size $n$ can be solved deterministically on the restricted word RAM in $O(n^{k-0.0017\lfloor k/3\rfloor})$ time for size $n$ and absolute input bound $n^\kappa$, with the specified input and output conventions. The program and slope may depend on $\kappa$ and must work for every admissible word width.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Tripartite exact triangle time](exact-triangle-tripartite-time.md)

## Proof outline

Formalize the reduction on the exact instance domain and show its running time in the restricted word RAM, including padding and all terminal outcomes.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/EndStatement.lean#L123-L137); [endStatement_corollary_39_zeroWeight](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/EndStatement.lean#L76-L80).
- The real-valued time-bound formulation of the same result: Anthropic, [Corollary 39 and agreement of time models](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3771-L3776), [zero-weight clause](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4060-L4067).
