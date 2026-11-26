# Arithmetic formulas are projections of the permanent

Over every commutative ring $K$, a polynomial computed by an arithmetic formula with $s$ nodes is a projection of the generic $(s+1)\times(s+1)$ permanent. Moreover, if $2$ is invertible in $K$, a Boolean selector variable occurring in a single entry of the $d\times d$ generic permanent can be summed out, $\sum_{b\in\{0,1\}}\mathrm{per}(M|_{b})$, as a projection of the $(d+1)\times(d+1)$ generic permanent.

## Proof sketch

The branching program of the formula has a DAG whose path sum equals the permanent of a cycle-cover matrix with self-loops of weight one (no cancellation is needed since a DAG plus the return edge has only the intended cycle covers). For the selector, an extra row and column with entries $\tfrac12$ and $1$ realize the sum over $b$.

## Depends on

- [Specialization matrices and determinantal representations](specialization-matrices-and-determinantal-representations.md)
- [Permanent of an encoded 0-1 matrix](../../counting-complexity/complexity-of-the-permanent/perm-fun.md)

## Proof depends on

- [Valiant: arithmetic formulas are projections of linear-size determinants](formulas-are-projections-of-determinants.md)

## Sources

- Leslie G. Valiant, "Completeness Classes in Algebra", Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing, 1979.
- Ian Orzel, Srikanth Srinivasan, Sébastien Tavenas, Amir Yehudayoff, "The Algebraic Cost of a Boolean Sum", 45th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science, 2025.
