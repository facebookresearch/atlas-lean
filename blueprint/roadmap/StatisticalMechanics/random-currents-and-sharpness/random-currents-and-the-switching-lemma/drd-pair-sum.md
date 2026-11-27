# Sub-subset-weighted pair sum on a multigraph

Let $V$ be a finite set and $\iota$ a finite index set with an endpoint map $i \mapsto \mathrm{ends}(i)$ to unordered pairs of $V$ (a multigraph), $A \subseteq V$, $F$ a real function and $P$ a property of subsets of $\iota$. With $\partial m$ the set of vertices
of odd [degree](deg-k.md) in $m$, this is

$$\sum_{\substack{m \subseteq \iota \\ \partial m = A}} \#\{K \subseteq m : \partial K = A\} \cdot F(m)\, \mathbf 1_{P(m)}.$$
