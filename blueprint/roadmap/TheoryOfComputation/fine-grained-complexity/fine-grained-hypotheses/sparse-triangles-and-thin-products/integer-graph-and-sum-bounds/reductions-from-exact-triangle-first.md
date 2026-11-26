# The first group of integer 3SUM and shortest-path time bounds

For each $\kappa\in\mathbb N$ the restricted machine solves 3SUM in $O(n^{1.99923})$. Separately the min-plus product and directed APSP (with no negative closed walks) each have a $\widetilde O(n^{3-1/1944})$ bound and an $O(n^{2.99949})$ bound. Each bound quantifies its own uniform deterministic program, with the absolute input bound $n^\kappa$; in the tilde bounds the log exponent may depend on $\kappa$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Integer problem and layout definitions](../machine-and-inputs/integer-word-ram-problems.md)

## Proof depends on

- [Tripartite exact triangle time](exact-triangle-tripartite-time.md)

## Proof outline

Formalize the reduction on the exact instance domain and show its running time in the restricted word RAM, including padding and all terminal outcomes.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [unfolded definitions and proposition](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L3888-L3910); [ThreeSumApsp.wordRam_theorem_22_first](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L176-L178).
