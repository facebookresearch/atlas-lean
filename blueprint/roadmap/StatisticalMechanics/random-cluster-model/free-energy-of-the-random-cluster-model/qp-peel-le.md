# Peeling bound for $-\log Z$ of a tagged graph

Let $K_0$ be a simple graph on a finite set $U$ and let $\tau : U \to T$ assign a tag to each vertex, and let $0 < p < 1$ and $q > 0$. For every finite set $S$ of tags there is $I \in \mathbb{N}$ with

$$-\log Z_{R_S}(p, q) \le \sum_{\theta \in S} -\log Z_{B_\theta}(p, q) + I\,\big(-\log(1 - p)\big) \quad\text{and}\quad I \le \sum_{\theta \in S} N_\theta,$$

where $R_S$ is the [graph induced on the vertices with tags in $S$](qp-rest-g.md), $B_\theta$ the [block](qp-blk-g.md) of $\theta$, $N_\theta$ the number of edges of $K_0$ straddling the set of vertices of tag $\theta$ (an edge straddles a set $A$ of vertices when exactly one of its endpoints lies in $A$), and $Z_G(p, q)$ denotes the [ambient random-cluster normalizer](../random-cluster-measures-on-finite-graphs/fk-z.md) $Z_G(p, q) = \sum_\omega p^{o(\omega)}(1 - p)^{c(\omega)} q^{k(\omega)}$ (sum over all assignments $\omega$ of open/closed states to the unordered pairs of vertices, loops and non-edges included; $o, c$ count open and closed edges, $k$ the open clusters).
