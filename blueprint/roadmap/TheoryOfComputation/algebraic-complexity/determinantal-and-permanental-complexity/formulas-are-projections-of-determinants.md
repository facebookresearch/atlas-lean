# Valiant: arithmetic formulas are projections of linear-size determinants

Over every commutative ring $K$, if a polynomial is computed by an arithmetic formula with $s$ nodes (additions, multiplications and constants counted, input leaves free), then it is a projection (variables and constants substituted, no outer scalar) of the generic $(s+1)\times(s+1)$ determinant. Hence $\mathrm{dc}(f)\le s+1$.

## Proof sketch

Convert the formula into an algebraic branching program (series composition for products, parallel composition for sums) whose weighted adjacency matrix is strictly upper triangular after a topological ordering; the path-sum of such a program is, up to sign, a minor of $1-N$, i.e. the determinant of a specialization matrix of size (number of vertices minus one).

## Depends on

- [Specialization matrices and determinantal representations](specialization-matrices-and-determinantal-representations.md)

## Proof depends on

- [Algebraic branching programs as determinants](../../../LinearAlgebra/determinants-and-matrix-identities/determinant-identities-for-complexity/branching-programs-as-determinants.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Ian Orzel, Srikanth Srinivasan, Sébastien Tavenas, Amir Yehudayoff, "The Algebraic Cost of a Boolean Sum", 45th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science, 2025.
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", 2026.
