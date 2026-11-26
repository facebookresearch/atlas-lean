# Two offline thin-product bounds without logarithmic loss

First, for each natural $c$, one program and slope suffice for every $1\le D$, $D^{18}\le N$, $U=N^c$, and $|W|\le N^2/\sqrt D$ to output the requested entries in $O(N^2/D^{0.063})$ time. Second, for all reals $\varepsilon<0.1204$ and $\kappa>0$, there exists $\gamma>0$ such that for each natural $c$, one program and slope suffice for all $1\le N$, $1\le D\le N^\varepsilon$, $U=N^c$ and $|W|\le N^2/D^\kappa$ with time $O(N^2/D^\gamma)$.

## Depends on

- [The restricted integer word RAM](../machine-and-inputs/restricted-integer-word-ram.md)
- [Thin products and query semantics](../machine-and-inputs/thin-matrix-query-model.md)

## Proof depends on

- [Offline thin-product bound with fixed saving](thin-product-sparse-entry-time.md)
- [Offline thin-product entry bound below the entropy threshold](thin-product-offline-below-entropy-threshold.md)

## Proof outline

For the first clause, apply the requested-entry estimate and use $|W|\le N^2/\sqrt D$ to bound the query contribution by the same preprocessing order. For the second, use $0.1204<\varepsilon_*$, absorb logarithms into a smaller positive saving for $D\ge2$, and deal separately with $D=1$, where the requested products can be computed directly.

## Sources

- Josh Alman and Virginia Vassilevska Williams, [*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).
- Anthropic, [Theorem 1 with both clauses](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4129-L4143); [the general requested-position bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/PaperStatements.lean#L4046-L4057); [ThreeSumApsp.wordRam_theorem_1](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/Challenge/PaperStatements.lean#L244-L246).
- Anthropic, [the two proof routes and logarithm removal](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/3sum-apsp/ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean#L37-L44).
