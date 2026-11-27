# Valiant: arithmetic formulas are projections of linear-size determinants

Over every field $F$, if a polynomial is computed by an arithmetic formula (fan-in two) with $s$ addition and multiplication gates (input leaves, variables and constants, free), then it is a projection (variables and constants substituted, no outer scalar) of the generic $(s+1)\times(s+1)$ determinant: it equals $\det(A)$ for a matrix $A$ of side $s+1$ with entries in $F \cup X$, where $X$ is the set of variables. Hence $\mathrm{dc}(f)\le s+1$.

## Proof sketch

Convert the formula into an algebraic branching program with at most $s+2$ vertices and $s+1$ edges (series composition for products, parallel composition for sums). Identify source and sink and add loops of weight $1$ at the other vertices: source-to-sink paths then correspond bijectively to cycle covers, so the determinant of the resulting adjacency matrix, of size at most $s+1$, is the path sum up to a global sign, which is removed by exchanging two columns. The same holds for weakly-skew circuits of size $s$.

## Depends on

- [Specialization matrices and determinantal representations](specialization-matrices-and-determinantal-representations.md)

## Proof depends on

- [Algebraic branching programs as determinants](../../../LinearAlgebra/determinants-and-matrix-identities/determinant-identities-for-complexity/branching-programs-as-determinants.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Ian Orzel, Srikanth Srinivasan, Sébastien Tavenas, Amir Yehudayoff, "The Algebraic Cost of a Boolean Sum", 45th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science, 2025.
- Peter Bürgisser, "Completeness and Reduction in Algebraic Complexity Theory", Springer, 2000.
- Peter Bürgisser, "Completeness classes in algebraic complexity theory", in Foundations of Computation and Machine Learning: The Work of Leslie Valiant, ACM; arXiv:2406.06217, 2024, Proposition 2.21, Remark 2.22 and Proposition 2.23 (over a field $F$).
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021, Theorem 3.6.
