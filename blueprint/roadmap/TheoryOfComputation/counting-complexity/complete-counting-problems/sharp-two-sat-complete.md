# Valiant: #2SAT is #P-complete under counting Turing reductions

Counting satisfying assignments of 2-CNF formulas is in $\#\mathsf{P}$ and is $\#\mathsf{P}$-hard under polynomial-time Turing reductions, already for monotone 2-CNF formulas (no negated literals), although 2-SAT is in $\mathsf{P}$. Consequently $\#2\mathrm{SAT}\in\mathsf{FP}$ would imply $\mathsf{P}=\mathsf{NP}$.

## Proof sketch

Valiant's chain of reductions: counting perfect matchings of a bipartite graph $G$ (equivalently the $0/1$ permanent, $\#\mathsf{P}$-complete) reduces to counting all matchings of $G$, by attaching $k$ pendant vertices to every vertex of one side for $k=1,\dots,n+1$ and interpolating the polynomial $\sum_r A_r (k+1)^r$, where $A_r$ is the number of matchings of size $n-r$; counting matchings is counting satisfying assignments of the monotone 2-CNF with one variable per edge (true meaning "absent") and one clause per pair of edges sharing a vertex.

## Depends on

- [Counting satisfying assignments of a CNF formula](../counting-satisfiability-sat/count-sat-fun.md)
- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [2-SAT as a decision problem](../../polynomial-time-problems/2-satisfiability/two-sat-dec.md)

## Proof depends on

- [The permanent is #P-complete (Valiant)](../complexity-of-the-permanent/permanent-sharp-p-complete.md)

## Sources

- Leslie G. Valiant, "The Complexity of Enumeration and Reliability Problems", SIAM Journal on Computing 8(3), 410–421, 1979, Theorem 1 (reductions 2, 6 and 7, problem MONOTONE 2-SAT).
