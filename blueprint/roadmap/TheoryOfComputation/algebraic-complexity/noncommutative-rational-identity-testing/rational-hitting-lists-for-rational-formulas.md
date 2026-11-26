# Polynomial-time rational hitting lists for noncommutative rational formulas

There is a deterministic polynomial-time algorithm that, given $n$ and $s$ in unary, outputs a list of $n$-tuples of square rational matrices such that every admissible nonzero noncommutative rational formula in $n$ variables with at most $s$ nodes is defined and has an invertible (in particular nonzero) value at some tuple of the list. Consequently identity testing of noncommutative rational formulas is in deterministic polynomial time in the black-box model.

## Proof sketch

Certificate determinants of the formula's pencils, evaluated at polynomial deformations of quantum Fourier lifts, are nonzero polynomials of bounded degree in three auxiliary parameters; scanning an integer grid of polynomial size finds a point avoiding all their zeros, at which normalized integer matrices are emitted. All arithmetic is performed with division-free integer determinants and cyclotomic regular representations of polynomial bit length.

## Depends on

- [Noncommutative rational formulas and their matrix evaluations](noncommutative-rational-formulas.md)
- [Hitting sets for classes of polynomials](../hitting-sets-for-polynomial-identity-testing/hitting-sets-for-polynomials.md)

## Proof depends on

- [Linear realizations of rational formulas](linear-realizations-of-rational-formulas.md)
- [Weyl matrices and the quantum Fourier lift](weyl-matrices-and-quantum-fourier-lift.md)
- [Bird's division-free determinant algorithm](../../../LinearAlgebra/determinants-and-matrix-identities/determinant-identities-for-complexity/bird-division-free-determinant-algorithm.md)

## Sources

- OpenAI, "Rational matrix hitting lists for noncommutative rational formulas", 2026.
