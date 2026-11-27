# Small partition gadgets exist

For every finite $\gamma$ and $t \ge 1$ there is a partition gadget over $\gamma$ separating up to $t$ labels with universe size at most $2^t \big(t \lceil \log_2(2|\gamma| + 1) \rceil + 1\big)$. The Boolean cube $U = \{0,1\}^\gamma$ with $S_b = \{u : u_b = 1\}$ separates every $t$ but has size $2^{|\gamma|}$.

## Proof sketch

Choose the points independently and uniformly from $\{0,1\}^\gamma$; a fixed pair $(P, Q)$ with $|P|+|Q| \le t$ is separated by a random point with probability at least $2^{-t}$, so the stated number of points separates all at most $(2|\gamma|+1)^t$ pairs simultaneously with positive probability by a union bound.

## Depends on

- [Partition gadget for Set Cover hardness](partition-gadget-for-set-cover.md)

## Sources

- C. Lund and M. Yannakakis, "On the Hardness of Approximating Minimization Problems", Journal of the ACM 41(5), 1994.
- U. Feige, "A Threshold of ln n for Approximating Set Cover", Journal of the ACM 45(4), 1998.
- N. Alon and J. H. Spencer, "The Probabilistic Method", 4th ed., Wiley, 2016.
