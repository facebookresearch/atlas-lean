# Waring rank lower bound for the product of variables

Over a field of characteristic zero, if $x_1x_2\cdots x_d=\sum_{t=1}^{s}c_t\,\ell_t(x)^d$ with linear forms $\ell_t$ and scalars $c_t$, then $s\ge\binom dk$ for every $0\le k\le d$; in particular $s\ge\binom{d}{\lfloor d/2\rfloor}$, and at degree $2n$ the bound is the central binomial coefficient $\binom{2n}{n}$. The same lower bound holds for circuits adding dictionary terms that are scaled $d$-th powers of linear forms, each shared term charged once.

## Proof sketch

Consider the coefficient (partial-derivative) matrix with rows indexed by squarefree monomials of degree $k$ and columns by complementary monomials; a $d$-th power of a linear form contributes a rank-one matrix, while $x_1\cdots x_d$ contributes a permutation matrix of size $\binom dk$.

## Depends on

- [The partial-derivative measure](partial-derivative-measure.md)

## Sources

- Neeraj Kayal, Ramprasad Saptharishi, "A Selection of Lower Bounds for Arithmetic Circuits", Perspectives in Computational Complexity: The Somenath Biswas Anniversary Volume, 2014.
