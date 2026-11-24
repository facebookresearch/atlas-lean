# Hilbert's Nullstellensatz

Let $k$ be a field, let $K$ be an algebraically closed field extension of $k$, and let $x_1, \dots, x_n$ be finitely many indeterminates. For an ideal $J$ of $k[x_1, \dots, x_n]$, let $Z(J) = \{a \in K^n : g(a) = 0 \text{ for all } g \in J\}$ be its zero set in $K^n$. Then a polynomial $f \in k[x_1, \dots, x_n]$ vanishes at every point of $Z(J)$ if and only if $f^m \in J$ for some integer $m \ge 1$, that is, if and only if $f$ lies in the radical of $J$. In particular, this holds for $K = k$ when $k$ is algebraically closed.

## Sources

- David Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, Graduate Texts in Mathematics 150, Springer-Verlag, 1995.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the zero set in $K^n$ of an ideal of polynomials over $k$: `MvPolynomial.zeroLocus`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Nullstellensatz.lean#L38-L40.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the ideal of polynomials vanishing on a set: `MvPolynomial.vanishingIdeal`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/RingTheory/Nullstellensatz.lean#L60-L62.
