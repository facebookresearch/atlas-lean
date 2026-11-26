# Goemans–Linial gap for uniform sparsest cut

For a symmetric nonnegative real capacity matrix $C$ of order $n\ge2$ with zero diagonal, define $\operatorname{OPT}(C)$ to be the infimum over nonempty proper subsets $S$ of the sum of capacities crossing the cut divided by $|S|(n-|S|)$. Let $\operatorname{GL}(C)$ be the infimum of $\sum_{i<j} C_{ij}d_{ij}$ over $d_{ij}=\|x_i-x_j\|_2^2$ for $x_i\in\mathbb R^n$, satisfying all triangle inequalities and $\sum_{i<j}d_{ij}=1$. There exist $c>0$ and capacities $C_j$ of orders $n_j\ge2$ with $n_j\to\infty$ and $\operatorname{GL}(C_j)>0$ for every $j$, such that eventually $\operatorname{OPT}(C_j)/\operatorname{GL}(C_j)\ge c\sqrt{\log n_j}/(\log\log n_j)^3$.

## Depends on

- Uniform unit-demand cut values, normalized squared-Euclidean metrics satisfying triangle inequalities, and positive relaxation value.

## Proof outline

Write the negative-type metric and relaxation separately and prove the denominator is positive on the constructed sequence. Preserve the eventual quantifier along that sequence rather than an all-orders bound.

- Construction of the capacity sequence and simultaneous lower bound on integral cuts, feasible low SDP objective and positivity of the relaxation.

## Sources

- [Comparator statement: `OAI.UniformSparsestCut.mainGap`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformSparsestCut.lean#L40-L50)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/117.md)
