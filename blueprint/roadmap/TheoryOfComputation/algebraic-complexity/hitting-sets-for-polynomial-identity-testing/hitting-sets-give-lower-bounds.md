# Hitting sets give lower bounds (Heintz–Schnorr)

Over a field $K$, if $H\subseteq K^n$ is finite and $T$ is a finite set of monomials with $|T|>|H|$, then there is a nonzero polynomial supported on $T$ that vanishes on all of $H$. Consequently, if $H$ is a hitting set for a class $\mathcal{C}$, some nonzero polynomial with monomials in $T$ is not in $\mathcal{C}$; small explicit hitting sets for a circuit class yield explicit polynomials (in exponential time) outside the class.

## Proof sketch

Vanishing at the points of $H$ imposes $|H|$ homogeneous linear conditions on the $|T|$ unknown coefficients, which has a nontrivial solution.

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)

## Sources

- Joos Heintz, Claus-Peter Schnorr, "Testing Polynomials which Are Easy to Compute (Extended Abstract)", Proceedings of the 12th Annual ACM Symposium on Theory of Computing (STOC 1980), 1980.
- Manindra Agrawal, "Proving Lower Bounds Via Pseudo-random Generators", Proceedings of the 25th International Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2005), 2005.
