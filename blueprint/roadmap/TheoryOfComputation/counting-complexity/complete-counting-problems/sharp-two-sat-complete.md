# Valiant: #2SAT is #P-complete under counting Turing reductions

Counting satisfying assignments of 2-CNF formulas (literals of either sign) is in $\#\mathsf{P}$ and is $\#\mathsf{P}$-hard under polynomial-time counting Turing reductions, although 2-SAT is in $\mathsf{P}$. Consequently $\#2\mathrm{SAT}\in\mathsf{FP}$ would imply $\mathsf{P}=\mathsf{NP}$.

## Proof sketch

For a CNF $\varphi$ with $m$ clauses, build for each $r$ a 2-CNF whose model count is $\sum_\sigma(r+1)^{u(\sigma)}$, where $u(\sigma)$ is the number of clauses falsified by $\sigma$ (each clause gets a weighted 2-CNF gadget). Querying $m+1$ values of $r$ and interpolating the polynomial recovers the number of $\sigma$ with $u(\sigma)=0$, i.e. $\#\varphi$.

## Depends on

- [Counting satisfying assignments of a CNF formula](../counting-satisfiability-sat/count-sat-fun.md)
- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [2-SAT as a decision problem](../../polynomial-time-problems/2-satisfiability/two-sat-dec.md)

## Proof depends on

- [Counting SAT is #P-complete](../counting-satisfiability-sat/count-sat-sharp-p-complete.md)

## Sources

- Leslie G. Valiant, "The Complexity of Enumeration and Reliability Problems", SIAM Journal on Computing 8(3), 1979.
