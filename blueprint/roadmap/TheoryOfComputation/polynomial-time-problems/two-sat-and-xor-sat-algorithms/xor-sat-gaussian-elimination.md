# XOR-SAT is solvable by Gaussian elimination over GF(2)

A system of linear equations over $\mathbb{F}_2$ (equivalently a conjunction of XOR clauses) with $m$ equations in $n$ variables is decidable, and a solution computable, in time $O(mn\min(m,n))$ by Gaussian elimination: for each column pick a not yet used row with a $1$ in that column (skip the column if there is none), add it to every other row with a $1$ in that column, and mark it as a pivot row; the system is unsatisfiable iff an equation $0=1$ appears.

## Proof sketch

Row additions preserve the solution set; after all columns are eliminated only constant equations remain, which are all $0=0$ iff the system is consistent, and back-substitution through the pivot rows yields a solution.

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- Hubie Chen, "A Rendezvous of Logic, Complexity, and Algebra", ACM Computing Surveys 42(1), Article 2, 2009 (arXiv:cs/0611018), Theorem 4.3.
- Thomas J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
