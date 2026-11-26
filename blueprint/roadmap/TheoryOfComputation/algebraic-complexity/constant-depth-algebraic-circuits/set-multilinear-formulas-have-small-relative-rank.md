# Small set-multilinear formulas have small relative rank

Fix $k$ and a word $w\in\mathbb{Z}^d$ whose letters are $\lfloor k/\sqrt2\rfloor$ and $-k$ (in a suitable arrangement), with $k\ge10d$ and $\Delta\ge1$. Every set-multilinear formula of product-depth at most $\Delta$ with $s$ nodes computes a polynomial $f$ with

$$
\mathrm{relrk}_w(f)\le s\cdot 2^{-k\left(d^{1/(4^\Delta-1)}/20-1/2\right)} .
$$

## Proof sketch

Induct on product-depth: at a product gate with children on disjoint block sets the relative rank is multiplicative, and the imbalance between positive and negative weights in each child accumulates; a combinatorial lemma on sums of the word's letters over many factors shows that most product gates have large imbalance, which yields the exponentially small bound.

## Depends on

- [Relative rank of set-multilinear polynomials](relative-rank-of-set-multilinear-polynomials.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", Electronic Colloquium on Computational Complexity, 2021.
