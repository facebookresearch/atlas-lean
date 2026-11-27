# Waring rank lower bound for the product of variables

Over a field of characteristic zero, if $x_1x_2\cdots x_d=\sum_{t=1}^{s}c_t\,\ell_t(x)^d$ with linear forms $\ell_t$ and scalars $c_t$, then $s\ge\binom dk$ for every $0\le k\le d$; in particular $s\ge\binom{d}{\lfloor d/2\rfloor}$, and at degree $2n$ the bound is the central binomial coefficient $\binom{2n}{n}$.

## Proof sketch

Use $\mu_k$: every $k$-th order partial derivative of $\ell^d$ is a scalar multiple of $\ell^{d-k}$, so $\mu_k(c\,\ell^d)\le1$ and subadditivity gives $\mu_k(x_1\cdots x_d)\le s$, while the $k$-th order partial derivatives of $x_1\cdots x_d$ include the $\binom dk$ distinct squarefree monomials of degree $d-k$, so $\mu_k(x_1\cdots x_d)\ge\binom dk$.

## Proof depends on

- [The partial-derivative measure](partial-derivative-measure.md)

## Sources

- Neeraj Kayal, Ramprasad Saptharishi, "A Selection of Lower Bounds for Arithmetic Circuits", Perspectives in Computational Complexity: The Somenath Biswas Anniversary Volume, 2014.
