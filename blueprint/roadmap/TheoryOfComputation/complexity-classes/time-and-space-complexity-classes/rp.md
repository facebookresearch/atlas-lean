# The class RP

A decision problem $L$ is in $\mathsf{RP}$ when there are a polynomial
$p$ with natural-number coefficients and a polynomial-time computable Boolean function $R$
on pairs of bitstrings such that for every bitstring $x$: if $L(x)$ is true, then $R(x, r)$
is true for at least half of the $2^{p(|x|)}$ bitstrings $r$ of length $p(|x|)$; and if
$L(x)$ is false, then $R(x, r)$ is false for every bitstring $r$ of length $p(|x|)$.

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Definition 7.2; M. Sipser, Introduction to the Theory of Computation, 3rd ed., 2013, Definition 10.8.
