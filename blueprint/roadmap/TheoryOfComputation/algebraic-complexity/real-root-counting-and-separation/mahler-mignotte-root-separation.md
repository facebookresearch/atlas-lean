# Mahler–Mignotte root separation bound

Let $p\in\mathbb{Z}[X]$ be separable of degree $d\ge2$, and let $\|p\|_2^2$ be the sum of squares of its coefficients. Then any two distinct complex roots $\alpha\neq\beta$ of $p$ satisfy

$$
3\le|\alpha-\beta|^2\,d^{\,d+2}\,\|p\|_2^{2(d-1)} ,
$$

i.e. $|\alpha-\beta|\ge\sqrt3\,d^{-(d+2)/2}\|p\|_2^{-(d-1)}$. The same holds for rational polynomials after clearing denominators.

## Proof sketch

Mahler's inequality bounds $|\alpha-\beta|$ below in terms of the discriminant and the Mahler measure, via Hadamard's determinant inequality applied to a Vandermonde-type matrix; for integer separable polynomials $|\mathrm{disc}(p)|\ge1$, and Landau's inequality bounds the Mahler measure by $\|p\|_2$.

## Depends on

- [Hadamard's determinant inequality](../../../LinearAlgebra/positive-definite-matrices/hadamard-s-inequality-and-determinant-bounds-for/hadamard-s-determinant-inequality/hadamard-determinant-inequality.md)
- [Mahler measure of an integer polynomial](../../../NumberTheory/heights-mahler-measure/lehmer-s-mahler-measure-problem/int-mahler-measure.md)

## Sources

- Kurt Mahler, "An inequality for the discriminant of a polynomial", Michigan Mathematical Journal, 1964.
- Maurice Mignotte, "Some Useful Bounds", Computer Algebra: Symbolic and Algebraic Computation, 1982.
- Saugata Basu, Richard Pollack, Marie-Françoise Roy, "Algorithms in Real Algebraic Geometry", Springer, 2006.
