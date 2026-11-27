# Bin packing cannot be approximated within a factor below 3/2 unless P = NP

If a polynomial-time algorithm packs every list of positive integers into bins of a given capacity using fewer than $3/2$ times the optimal number of bins, then $\mathrm{P} = \mathrm{NP}$.

## Proof sketch

Given an instance of Partition with total $S$, ask the algorithm to pack it into bins of capacity $\lfloor S/2 \rfloor$. If a partition exists the optimum is two bins and the algorithm must use fewer than three, i.e. two, which yields a partition; otherwise it uses at least three. Partition is NP-complete.

## Depends on

- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Sources

- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum, 1972.
