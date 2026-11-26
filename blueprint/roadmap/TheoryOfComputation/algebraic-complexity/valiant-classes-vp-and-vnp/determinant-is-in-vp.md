# The determinant is in VP over every commutative ring

For every commutative ring $K$ and every $n$, the generic $n\times n$ determinant $\det(x_{ij})$ is computed as a formal polynomial by an arithmetic circuit (without division) with at most $3n^4+4$ gates. Hence $(\det_n)\in\mathsf{VP}_K$ over every commutative ring.

## Proof sketch

Implement Bird's division-free algorithm: $n-1$ rounds, each multiplying by the input matrix after replacing a running matrix by a strictly upper-triangular modification of its diagonal partial sums; each round costs $O(n^3)$ ring operations.

## Depends on

- [Valiant's class VP](valiants-class-vp.md)
- [Leibniz formula for the determinant](../../../LinearAlgebra/determinants-and-matrix-identities/determinants-of-matrices/leibniz-formula/det-apply.md)

## Proof depends on

- [Bird's division-free determinant algorithm](../../../LinearAlgebra/determinants-and-matrix-identities/determinant-identities-for-complexity/bird-division-free-determinant-algorithm.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Richard S. Bird, "A Simple Division-Free Algorithm for Computing Determinants", Information Processing Letters, 2011.
