# Bin packing cannot be approximated within a factor below 3/2 unless P = NP

If for some fixed $\rho < 3/2$ a polynomial-time algorithm packs every list of positive integers, each at most a given bin capacity, into at most $\rho$ times the optimal number of bins of that capacity, then $\mathrm{P} = \mathrm{NP}$.

## Proof sketch

Given an instance of Partition with total $S$, answer directly if the list is empty, $S$ is odd, or some item exceeds $S/2$; otherwise ask the algorithm to pack it into bins of capacity $S/2$. If a partition exists the optimum is two bins and the algorithm uses at most $2\rho < 3$, i.e. two, which yields a partition; otherwise every packing uses at least three. Partition is NP-complete.

## Depends on

- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Sources

- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum, 1972.
