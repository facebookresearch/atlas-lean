# Linear realizations of rational formulas

Every noncommutative rational formula $f$ with $s$ nodes has a *linear realization*: a square matrix $L_f(x)$ of affine forms in the variables, of size $s+1$, together with a rational row vector $u$ and column vector $v$, such that wherever $f$ is defined at a matrix substitution $X$, the evaluated pencil $L_f(X)$ is invertible and $f(X)=u\,L_f(X)^{-1}v$ (with the obvious Kronecker interpretation). Conversely $f$ is defined with an invertible value at $X$ iff the pencils of its inverse nodes and its augmented pencil are invertible at $X$.

## Proof sketch

Build the pencil recursively: sums and products of realizations are realized by block-triangular pencils, and inversion by a bordered pencil, as in Cohn's and Higman's linearization trick; correctness follows from Schur complement identities.

## Depends on

- [Noncommutative rational formulas and their matrix evaluations](noncommutative-rational-formulas.md)

## Sources

- OpenAI, "Rational matrix hitting lists for noncommutative rational formulas", 2026.
