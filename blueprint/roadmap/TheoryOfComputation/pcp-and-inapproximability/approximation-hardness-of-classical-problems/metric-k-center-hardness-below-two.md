# Metric k-center cannot be approximated within a factor below 2 unless P = NP

If a polynomial-time algorithm, given a finite metric space with integer distances and an integer $k$, always returns $k$ centers whose covering radius is less than $2$ times the optimal radius, then $\mathrm{P} = \mathrm{NP}$. The greedy farthest-point algorithm of Gonzalez achieves factor $2$, so the threshold is tight.

## Proof sketch

From a graph $G$ build the metric with distance $1$ between adjacent vertices and $2$ between nonadjacent distinct vertices. $G$ has a dominating set of size $k$ iff the optimal radius is $1$; then any radius below $2$ is $1$ and the returned centers form a dominating set. Dominating Set is NP-complete.

## Depends on

- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Sources

- W.-L. Hsu and G. L. Nemhauser, "Easy and Hard Bottleneck Location Problems", Discrete Applied Mathematics 1(3), 1979.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
