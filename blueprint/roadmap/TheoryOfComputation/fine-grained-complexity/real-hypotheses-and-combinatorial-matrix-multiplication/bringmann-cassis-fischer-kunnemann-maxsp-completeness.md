# Bringmann–Cassis–Fischer–Künnemann: Maximum/Minimum Inner Product is complete for MaxSP/MinSP

For fixed $k,\ell$ and a quantifier-free first-order formula $\phi$ over a relational signature, the **MaxSP** problem defined by $\phi$ asks, given a relational structure with $m$ tuples, for

$$
\max_{x_1,\dots,x_k}\ \#\{(y_1,\dots,y_\ell):\ \phi(x_1,\dots,x_k,y_1,\dots,y_\ell)\},
$$

and MinSP is defined with min; each is solvable in time $O(m^{k+\ell-1})$. MaxSP contains Maximum Inner Product, nearest-neighbour variants and optimization versions of $k$-XOR. Theorem: a sparse variant of Maximum (resp. Minimum) Inner Product is complete for MaxSP (resp. MinSP) under deterministic fine-grained reductions: a strongly subquadratic algorithm for it gives an $O(m^{k+\ell-1-\delta})$ algorithm for every MaxSP (MinSP) problem. The completeness transfers to approximation: a strongly subquadratic $c$-approximation yields $(c+\varepsilon)$-approximations for all problems in the class in time $O(m^{k+\ell-1-\delta})$. Combined with Chen–Williams, refuting the OV hypothesis is equivalent to an $O(1)$-approximation for all MinSP problems faster than $O(m^{k+\ell-1})$.

## Proof sketch

Following the completeness paradigm for first-order model checking in P, the formula is put in a normal form where the inner count is a sum over $\ell$-tuples of products of indicator relations; by a sparse "combinatorial" encoding, each candidate $\bar x$ becomes a sparse vector and each $\bar y$-constraint a coordinate, so the count equals an inner product, while self-reducibility arguments handle $k > 2$ and the quantifier-free structure.

## Depends on

- [Fine-grained reductions](../fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [SETH implies the Orthogonal Vectors hypothesis](../fine-grained-hypotheses/seth-implies-the-orthogonal-vectors-hypothesis.md)

## Sources

- Karl Bringmann, Alejandro Cassis, Nick Fischer and Marvin Künnemann, "Fine-Grained Completeness for Optimization in P", APPROX (2021), arXiv:2107.01721.
