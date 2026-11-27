# The determinant is in VP over every commutative ring

For every commutative ring $K$ and every $n$, the generic $n\times n$ determinant $\det(x_{ij})$ is computed as a formal polynomial by an arithmetic circuit (without division) with $O(n^4)$ gates whose constants are integers. Hence $(\det_n)\in\mathsf{VP}_K$ over every commutative ring.

## Proof sketch

Implement Bird's division-free algorithm: with $A=(x_{ij})$ and starting from $X=A$, perform $n-1$ rounds $X\leftarrow\mu(X)\,A$, where $\mu(X)$ keeps the strictly upper-triangular part of $X$, zeroes the part below the diagonal, and has $-\sum_{j>i}X_{jj}$ as its $i$-th diagonal entry; each round costs $O(n^3)$ ring operations, and the determinant is read off, up to the sign $(-1)^{n-1}$, from the final $(1,1)$ entry.

## Depends on

- [Valiant's class VP](valiants-class-vp.md)
- [Leibniz formula for the determinant](../../../LinearAlgebra/determinants-and-matrix-identities/determinants-of-matrices/leibniz-formula/det-apply.md)

## Proof depends on

- [Bird's division-free determinant algorithm](../../../LinearAlgebra/determinants-and-matrix-identities/determinant-identities-for-complexity/bird-division-free-determinant-algorithm.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Richard S. Bird, "A Simple Division-Free Algorithm for Computing Determinants", Information Processing Letters, 2011.
