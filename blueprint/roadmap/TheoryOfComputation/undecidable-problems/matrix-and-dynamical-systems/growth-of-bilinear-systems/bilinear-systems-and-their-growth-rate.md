# Bilinear systems and their growth rate

A bilinear system is a bilinear map on $\mathbb R^d$ with a starting vector; combining $n$ copies of the vector by $n-1$ applications of the map in all bracketings gives finitely many vectors, and the growth rate is the limit superior of the $n$-th root of their largest entry.

A *bilinear system* $(*,s)$ consists of a bilinear map $*:\mathbb R^d\times\mathbb R^d\to\mathbb R^d$, given by its coefficients $(x*y)_k=\sum_{i,j}c_{ijk}\,x_iy_j$, and a *starting vector* $s\in\mathbb R^d$. A *combination of $n$ instances of $s$* is any vector obtained from $n$ copies of $s$ by $n-1$ applications of $*$ under some bracketing; for $n=4$ these are $s*(s*(s*s))$, $s*((s*s)*s)$, $(s*s)*(s*s)$, $(s*(s*s))*s$ and $((s*s)*s)*s$. Let $g(n)$ be the largest entry over all combinations of $n$ instances of $s$.

In the *nonnegative setting* the coefficients $c_{ijk}$ and the entries of $s$ are nonnegative, and the *growth rate* of the system is

$$
\lambda=\limsup_{n\to\infty}\sqrt[n]{g(n)} .
$$

In the *positive setting*, where moreover $s$ is strictly positive, the limit superior is a limit. In algorithmic questions the coefficients and the entries of $s$ are rational. The system *can produce a zero vector* if some combination of instances of $s$ is the zero vector.

## Depends on

None.

## Proof depends on

None.

## Expansion

Matrix products are a special case: embedding $d\times d$ matrices in $\mathbb R^{d^2}$, the bilinear map $(C,C')\mapsto CC'$ turns questions about products of a finite set of matrices, such as the joint spectral radius, into questions about bilinear systems. The growth rate counts, for instance, the maximum number of minimal dominating sets in trees with $n$ leaves (Rote). In the nonnegative setting the growth rate is computable, and deciding $\lambda\le1$ is Turing equivalent to the halting problem.

## Sources

- Vuong Bui, "Growth of bilinear maps III: Decidability", *Theoretical Computer Science* 1056, 2025, article 115515, doi:[10.1016/j.tcs.2025.115515](https://doi.org/10.1016/j.tcs.2025.115515); read in arXiv:2201.09850v3 ([arXiv](https://arxiv.org/abs/2201.09850v3)), whose numbering is used: Section 1 (the growth rate, the positive and nonnegative settings, and the questions of Rosenfeld).
