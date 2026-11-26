# Integer Exact Triangle on simple undirected graphs

For every natural $\kappa$, one deterministic program decides whether three pairwise adjacent vertices of an $n$-vertex simple undirected graph have total weight zero, with weights given by a symmetric integer matrix, in $O(n^{2.9983})$ time. The input bound $n^\kappa$ applies to the adjacency bits and the weights supplied (zero for absent edges).

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Tripartite exact triangle time](exact-triangle-tripartite-time.md)

## Proof outline

Formalize the reduction on the exact instance domain and show its running time in the restricted word RAM, including padding and all terminal outcomes.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4160-L4163); [ThreeSumApsp.wordRam_theorem_2_graphs](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L252-L254).
