# Sum over edge sets split into parts with sources $A$ and $B$

Let $V$ be a finite set and $\iota$ a finite index set with an endpoint map $i \mapsto \mathrm{ends}(i)$ to unordered pairs of $V$ (a multigraph), $A, B \subseteq V$ and $F$ a real function of subsets of $\iota$; write $\partial K$ for the set of vertices of odd [degree](deg-k.md) in $K$. This is

$$\sum_{\substack{m \subseteq \iota \\ \partial m = A \triangle B}} \#\{K \subseteq m : \partial K = A,\ \partial(m \setminus K) = B\} \cdot F(m).$$
