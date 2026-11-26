# Hitting sets for classes of polynomials

Let $\mathcal{C}$ be a class of polynomials in $K[x_1,\dots,x_n]$. A finite set $H\subseteq K^n$ is a *hitting set* for $\mathcal{C}$ if every nonzero $f\in\mathcal{C}$ satisfies $f(a)\ne0$ for some $a\in H$. A hitting set yields a deterministic black-box polynomial identity test for $\mathcal{C}$ that evaluates the input at the $|H|$ points. For non-commutative polynomials one uses tuples of matrices: $f\in K\langle x_1,\dots,x_n\rangle$ is hit by $(P_1,\dots,P_n)\in(K^{e\times e})^n$ if $f(P_1,\dots,P_n)\neq0$.

## Depends on

- [Deterministic polynomial identity testing](../../randomized-and-quantum-complexity/deterministic-polynomial-identity-testing.md)
- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Joos Heintz, Claus-Peter Schnorr, "Testing Polynomials which Are Easy to Compute (Extended Abstract)", Proceedings of the 12th Annual ACM Symposium on Theory of Computing (STOC 1980), 1980.
- Manindra Agrawal, "Proving Lower Bounds Via Pseudo-random Generators", Proceedings of the 25th International Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2005), 2005.
- Amir Shpilka, "Polynomial-size hitting sets for multilinear any-order read-once algebraic branching programs and for set-multilinear depth-3 circuits with constant-size variable sets", Electronic Colloquium on Computational Complexity, 2026.
