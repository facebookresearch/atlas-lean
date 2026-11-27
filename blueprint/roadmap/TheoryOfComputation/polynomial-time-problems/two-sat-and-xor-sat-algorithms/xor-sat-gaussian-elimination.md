# XOR-SAT is solvable by Gaussian elimination over GF(2)

A system of linear equations over $\mathbb{F}_2$ (equivalently a conjunction of XOR clauses) is decidable, and a solution computable, in polynomial time by Gaussian elimination: repeatedly take an equation; if it contains no variable, check whether it is true and either remove it or report unsatisfiability; otherwise solve it for one of its variables $a_1$, substitute the resulting expression for $a_1$ in every other equation, simplify (two occurrences of a variable cancel, constants are added), and remove it. The system is unsatisfiable iff an equation $0=1$ appears; back-substitution through the removed equations yields a solution.

## Proof sketch

Each substitution preserves the solution set, and after simplification every equation has at most $2n$ variable instances ($n$ the number of variables), so each of the at most $m$ elimination steps costs polynomial time. Back-substitution in reverse order assigns each eliminated variable consistently.

Derived (explicit bound not stated in the cited sources): organised column by column on an $m\times n$ coefficient matrix (pick an unused row with a $1$ in the current column, add it to every other row with a $1$ there, mark it as a pivot), elimination performs at most $\min(m,n)$ pivot steps of $O(mn)$ bit operations each, so it runs in time $O(mn\min(m,n))$.

## Depends on

- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- Hubie Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (arXiv:cs/0611018; extended version ACM Computing Surveys 42(1), Article 2, 2009), Section 4, Theorem 4.3 and the paragraph after it ("The resulting conjunction of linear equations can be solved by the well-known Gaussian elimination algorithm").
- Thomas J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
