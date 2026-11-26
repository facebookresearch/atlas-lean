# Affine circuits compute affine maps

Let $F$ be a commutative semiring and consider circuits whose gates compute affine functions $\sum_i a_i y_i+b$ of their arguments. Then every wire of such a circuit on inputs $x\in F^n$ carries an affine function of $x$; consequently every output map is affine, $x\mapsto Ax+c$, and a linear circuit (all $b=0$) computes a linear map $x\mapsto Ax$.

## Proof sketch

Induction along the gates: affine combinations of affine functions are affine.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
