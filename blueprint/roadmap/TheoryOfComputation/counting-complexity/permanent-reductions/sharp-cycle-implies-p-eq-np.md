# If #CYCLE is in FP then P = NP

Let $\#\mathrm{CYCLE}$ be the function counting the simple directed cycles of a digraph. If $\#\mathrm{CYCLE}$ is computable in polynomial time, then $\mathsf{P}=\mathsf{NP}$, although deciding whether a digraph has a cycle is in $\mathsf{P}$.

## Proof sketch

Replace every arc of an $n$-vertex digraph by a gadget of $L=\mathrm{poly}(n)$ layers with $2^{L}$ paths between its ends, so a simple cycle of length $\ell$ yields $2^{L\ell}$ cycles. A Hamiltonian cycle then contributes $2^{Ln}$, more than all shorter cycles combined, so thresholding $\#\mathrm{CYCLE}$ decides Hamiltonicity, which is NP-complete.

## Depends on

- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [The complexity class P](../../complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Theorem 9.4.
