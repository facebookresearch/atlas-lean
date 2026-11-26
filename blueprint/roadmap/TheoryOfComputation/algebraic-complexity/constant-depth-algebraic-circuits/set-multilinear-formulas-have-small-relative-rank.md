# Small set-multilinear formulas have small relative rank

Let $\alpha=1/\sqrt2$, let $d,k,\Delta\ge1$ be integers with $k\ge10d$, and let $w\in\mathbb{Z}^d$ be any word each of whose letters is $\lfloor\alpha k\rfloor$ or $-k$, in any order. Every set-multilinear formula of product-depth at most $\Delta$ with at most $s$ nodes computes a polynomial $f$ with

$$
\mathrm{relrk}_w(f)\le s\cdot 2^{-k\,d^{1/(2^\Delta-1)}/20} .
$$

The lower bound for iterated matrix multiplication applies this to the $k$-unbiased word built greedily: $w_{i+1}=\lfloor\alpha k\rfloor$ if $w_1+\dots+w_i\le0$ and $w_{i+1}=-k$ otherwise.

## Proof sketch

Induct on product-depth: at a product gate with children on disjoint block sets the relative rank is multiplicative, and the imbalance between positive and negative weights in each child accumulates; a combinatorial lemma on sums of the word's letters over many factors shows that most product gates have large imbalance, which yields the exponentially small bound.

## Depends on

- [Relative rank of set-multilinear polynomials](relative-rank-of-set-multilinear-polynomials.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", full version of the FOCS 2021 paper, Electronic Colloquium on Computational Complexity TR21-081, revision 1, 2021, Claim 16 (in the proof of Lemma 15).
