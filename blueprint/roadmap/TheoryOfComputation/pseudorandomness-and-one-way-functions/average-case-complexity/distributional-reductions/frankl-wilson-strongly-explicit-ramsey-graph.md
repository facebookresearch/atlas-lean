# The Frankl–Wilson Ramsey graph is strongly explicit

For a prime $p$, let $G_p$ be the graph whose vertices are the $(p^{2}-1)$-element subsets of $[p^{3}]$, two subsets being adjacent iff their intersection size is $\not\equiv -1\pmod p$. Then $G_p$ has $\binom{p^{3}}{p^{2}-1}$ vertices but no clique and no independent set of more than $\binom{p^{3}}{p-1}$ vertices, giving a superpolynomial explicit Ramsey bound. Moreover $G_p$ is **strongly explicit**: vertices are named by strictly increasing lists, and adjacency of two named vertices is decidable in time polynomial in the name length.

## Proof sketch

Frankl–Wilson modular intersection theorem bounds families with restricted intersections modulo $p$ by $\binom{p^{3}}{p-1}$ via linear independence of polynomials over $\mathbb{F}_p$. Explicitness: decide adjacency by merging the two sorted lists and counting the common elements.

## Depends on

- [Polynomial-time computable functions](../../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- Peter Frankl and Richard M. Wilson, "Intersection Theorems with Geometric Consequences", Combinatorica 1(4), 1981.
