# LST lower bound for set-multilinear formulas computing IMM

In the setting of the relative-rank upper bound, every set-multilinear formula of product-depth at most $\Delta$ computing a word polynomial $P_w$ (in particular, after projection, $\mathrm{IMM}_{n,d}$ with $2^k\le n$) has at least $2^{k(d^{1/(2^\Delta-1)}/20-1/2)}$ nodes.

## Proof sketch

$P_w$ has relative rank at least $2^{-k/2}$ for the $k$-unbiased word $w$ (its matrix has full rank and $|w_1+\dots+w_d|\le k$), while a set-multilinear formula of product-depth at most $\Delta$ with $s$ nodes computes a polynomial of relative rank at most $s\,2^{-k\,d^{1/(2^\Delta-1)}/20}$; comparing the two gives the bound.

## Depends on

- [Iterated matrix multiplication and word polynomials](iterated-matrix-multiplication-polynomial.md)
- [Relative rank of set-multilinear polynomials](relative-rank-of-set-multilinear-polynomials.md)

## Proof depends on

- [Small set-multilinear formulas have small relative rank](set-multilinear-formulas-have-small-relative-rank.md)

## Sources

- Nutan Limaye, Srikanth Srinivasan, Sébastien Tavenas, "Superpolynomial Lower Bounds Against Low-Depth Algebraic Circuits", 62nd IEEE Symposium on Foundations of Computer Science (FOCS 2021), 2021.
