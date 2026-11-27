# Adjugate circuits from determinant circuits

The partial derivative of the generic determinant with respect to the entry $(a,b)$ is the $(b,a)$ entry of the adjugate: $\partial\det X/\partial x_{ab}=\operatorname{adj}(X)_{ba}$. Consequently an arithmetic circuit with $s$ gates computing $\det_n$ yields a circuit with at most $5s+O(1)$ gates, and at most three times as many multiplications, computing all $n^2$ entries of the adjugate; with division-free determinant circuits, each entry family of the adjugate is in $\mathsf{VP}$ over every commutative ring.

## Proof sketch

Laplace expansion along row $a$ shows the cofactors of row $a$ do not involve variables of that row, giving the derivative formula; reverse-mode differentiation (Baur–Strassen) computes all first partials at constant-factor cost.

## Depends on

- [Jacobi's formula](../../../LinearAlgebra/determinants-and-matrix-identities/jacobi-s-formula/jacobi-det-derivative.md)
- [Valiant's class VP](../valiant-classes-vp-and-vnp/valiants-class-vp.md)

## Proof depends on

- [Baur–Strassen: all partial derivatives at constant-factor cost](../algebraic-circuit-lower-bound-methods/baur-strassen-derivative-theorem.md)
- [The determinant is in VP over every commutative ring](../valiant-classes-vp-and-vnp/determinant-is-in-vp.md)

## Sources

- Walter Baur, Volker Strassen, "The Complexity of Partial Derivatives", Theoretical Computer Science, 1983.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
