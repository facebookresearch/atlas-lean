# Polynomial-size hitting sets for affine orbits of sparse polynomials

Over a field of characteristic zero, there is an explicit set of at most $(n^2+1)\bigl(2d(ns^2+s)+1\bigr)$ points of $F^n$ hitting every nonzero polynomial of the form $p(Ax+b)$ of degree at most $d$, where $A$ is an invertible $n\times n$ matrix, $b\in F^n$, and $p$ has at most $s$ monomials.

## Proof sketch

Key lemma: if all coordinates of $u$ are nonzero, the partial derivatives of the lowest nonzero homogeneous component of $p(x+u)$ span a space of dimension at most the number of monomials of $p$; this property is invariant under invertible linear maps. Shift by one of $n^2+1$ explicit points to make the relevant coordinates nonzero and apply the derivative-closed-space hitting set.

## Depends on

- [Hitting sets for classes of polynomials](hitting-sets-for-polynomials.md)
- [The partial-derivative measure](../algebraic-circuit-lower-bound-methods/partial-derivative-measure.md)

## Proof depends on

- [Hitting sets for polynomials in small derivative-closed spaces](hitting-sets-for-derivative-closed-spaces.md)

## Sources

- Vishwas Bhargava, Akash Kumar Sengupta, "Polynomial Identity Testing and Lower Bounds for Sparse Affine Orbits", Electronic Colloquium on Computational Complexity, 2026.
