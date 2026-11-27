# Modular evaluation and size bounds for integer terms

Let $t$ be a term of binary encoding length $\ell$. The polynomial it denotes has total degree at most $\ell$ and coefficients of absolute value at most $2^{O(\ell^2)}$; for every positive modulus $M$ and integer point $a$, the residue of $t(a)$ modulo $M$ can be computed in time polynomial in $\ell$ and the bit lengths of $a$ and $M$ by evaluating the term bottom-up (or by a stack machine reading the encoding right to left) and reducing every intermediate value modulo $M$.

## Proof sketch

Induction on the term: degrees add under multiplication and take the maximum under addition, and coefficient norms multiply; modular reduction commutes with ring operations.

## Depends on

- [Integer polynomial formulas over the reals](integer-polynomial-formulas-over-the-reals.md)

## Sources

- S. Basu, R. Pollack and M.-F. Roy, Algorithms in Real Algebraic Geometry, 2nd ed., Springer, 2006.
