# Gupta–Kamath–Kayal–Saptharishi: depth-four lower bound for the permanent with bottom fan-in sqrt(n)

Any homogeneous $\Sigma\Pi\Sigma\Pi^{[\sqrt{n}]}$ circuit computing the $n \times n$ determinant or permanent over a field of characteristic $0$ has size $2^{\Omega(\sqrt{n})}$. Since the determinant has homogeneous depth-four circuits of size $2^{O(\sqrt{n}\log n)}$ with bottom fan-in $\sqrt{n}$, the bound is tight up to the logarithmic factor in the exponent.

## Proof sketch

Take $k = \varepsilon\sqrt{n}$ and $\ell = n^{3/2}/\varepsilon'$. Every $k$-th order derivative of $\det_n$ or $\mathrm{perm}_n$ is (up to sign) an $(n-k)$-minor, and distinct minors are linearly independent; shifting by degree-$\ell$ monomials one shows $\mathrm{SP}_{k,\ell}$ is at least a $2^{-O(\sqrt{n})}$ fraction of the trivial bound by a leading-monomial argument. Comparing with the product upper bound for bottom fan-in $\sqrt{n}$ forces $2^{\Omega(\sqrt{n})}$ product gates.

## Depends on

- [Homogeneous depth-four circuits with bounded bottom fan-in](../depth-reduction-and-chasms/homogeneous-depth-four.md)

## Proof depends on

- [Shifted partials of a product of low-degree polynomials](spd-product-upper-bound.md)

## Sources

- A. Gupta, P. Kamath, N. Kayal, R. Saptharishi, "Approaching the chasm at depth four", Journal of the ACM 61 (2014); CCC (2013).
