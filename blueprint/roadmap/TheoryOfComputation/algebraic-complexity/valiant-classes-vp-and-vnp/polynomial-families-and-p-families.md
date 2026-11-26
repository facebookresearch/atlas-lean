# Polynomial families and p-families

Let $K$ be a commutative ring. A *family of polynomials* $f=(f_n)_{n\ge1}$ over $K$ assigns to each $n$ a polynomial $f_n\in K[x_1,\dots,x_{v(n)}]$. It is a *p-family* if the number of variables $v(n)$ and the total degree $\deg f_n$ are bounded by a polynomial in $n$. The *circuit size* $L(f_n)$ is the least number of gates of an arithmetic circuit (addition and multiplication of fan-in two, and a constant gate for each element of $K$) computing $f_n$ as a formal polynomial.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Peter Bürgisser, "Completeness and Reduction in Algebraic Complexity Theory", Springer, 2000.
