# Support-concentrating shifts for multilinear polynomials of small split rank

Over a field of characteristic zero, with $\ell=\lfloor\log_2w\rfloor+1$, there is an explicit set of at most $\bigl(n^2 2^{25\ell}+1\bigr)\bigl(n2^{\ell}+1\bigr)$ points $u\in F^n$ such that every nonzero multilinear polynomial $f$ in $n$ variables of split rank at most $w$ across every set of $\ell$ variables has, after the shift $x\mapsto x+u$ for some $u$ in the set, a monomial involving at most $\lfloor\log_2w\rfloor$ variables.

## Proof sketch

For a set $Y$ of $\ell$ variables with $w<2^\ell$, low split rank means the $2^\ell$ partial evaluations on $Y$ are linearly dependent, so after a generic shift some monomial of small support survives. A perfect hash family of colourings reduces the choice of $Y$ to polynomially many cases, and the shifts are taken along explicit curves.

## Depends on

- [Split rank of a polynomial across a variable partition](split-rank-across-a-partition.md)
- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)

## Sources

- Michael A. Forbes, Ramprasad Saptharishi, Amir Shpilka, "Hitting Sets for Multilinear Read-Once Algebraic Branching Programs, in any Order", Proceedings of the 46th Annual ACM Symposium on Theory of Computing, 2014.
- Amir Shpilka, "Polynomial-size hitting sets for multilinear any-order read-once algebraic branching programs and for set-multilinear depth-3 circuits with constant-size variable sets", Electronic Colloquium on Computational Complexity, 2026.
