# Changing the flow on a unit arc of a fixed-value flow

For an $s$–$t$ flow of fixed value and an arc with bounds $[0,1]$, the flow on that arc can be switched to the other value, keeping the flow value, exactly when the residual graph has a path closing a cycle with the single residual copy of the arc; in particular an unused arc can be put to use iff its endpoints are strongly connected in the residual graph.

Let $G=(V,A)$ be a finite directed multigraph with distinct vertices $s,t$; arcs are tagged, so parallel and antiparallel arcs are allowed. Each arc $a$ has integers $0\le d(a)\le c(a)$ (demand and capacity). An **$s$–$t$ flow** is a function $f:A\to\mathbb Z$ with $d(a)\le f(a)\le c(a)$ for all $a$ and conservation (inflow equals outflow) at every vertex other than $s$ and $t$; its **value** is the net outflow of $s$. The **residual graph** $G_f$ has, for each arc $a$ from $u$ to $v$, a tagged forward arc $a^+$ from $u$ to $v$ if $f(a)<c(a)$ and a tagged backward arc $a^-$ from $v$ to $u$ if $f(a)>d(a)$.

**Theorem.** Let $f$ be an $s$–$t$ flow of value $\varphi$ and $a$ an arc from $u$ to $v$ with $d(a)=0$ and $c(a)=1$.

1. If $f(a)=0$, there is an $s$–$t$ flow $g$ of value $\varphi$ with $g(a)=1$ iff $u$ is reachable from $v$ in $G_f$, equivalently iff $u$ and $v$ lie in the same strongly connected component of $G_f$.
2. If $f(a)=1$, there is an $s$–$t$ flow $g$ of value $\varphi$ with $g(a)=0$ iff $v$ is reachable from $u$ in $G_f$, equivalently iff $u$ and $v$ lie in the same strongly connected component of $G_f$.

In each case $G_f$ contains exactly one residual copy of $a$ ($a^+$ in item 1, $a^-$ in item 2), so the cycle certifying the change passes through that copy and cannot cancel itself on $a$. For arcs that are only partly used the strongly-connected test is not valid: for a single arc $s\to t$ with bounds $[0,2]$ and the flow 1, both residual copies exist and form a cycle, yet every flow of value 1 uses the arc exactly once.

## Depends on

- [Strongly connected vertices](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/strongly-connected.md): mutual reachability in the residual graph.

## Proof depends on

None.

## Expansion

*Item 1.* Since $f(a)=0=d(a)$, the arc $a$ has the forward copy $a^+$ (from $u$ to $v$) and no backward copy. ($\Leftarrow$) A path from $v$ to $u$ in $G_f$ closes a directed cycle with $a^+$, and that path does not use a copy of $a$. Change $f$ by one unit along the cycle, adding 1 on arcs traversed forward and subtracting 1 on arcs traversed backward. Residual arcs have integer residual capacity at least 1, so the bounds hold; every vertex keeps its net inflow, so conservation and the value are unchanged; and $g(a)=1$. ($\Rightarrow$) Let $S$ be the set of vertices reachable from $v$ in $G_f$ and suppose $u\notin S$. No residual arc leaves $S$, so every arc from $S$ to $V\setminus S$ has $f=c$ and every arc from $V\setminus S$ to $S$ has $f=d$. A flow $g$ of the same value has the same net inflow as $f$ at every vertex ($\varphi$ out of $s$, $\varphi$ into $t$, zero elsewhere), hence the same net outflow from $S$, which $f$ already maximizes; so $g$ also has $g=d$ on every arc entering $S$. The arc $a$ enters $S$, so $g(a)=d(a)=0$. Finally, $a^+$ makes $v$ reachable from $u$, so reachability of $u$ from $v$ is the same as strong connectivity.

*Item 2* is symmetric: now $f(a)=1=c(a)$, only $a^-$ (from $v$ to $u$) exists, a path from $u$ to $v$ closes a cycle with it, and the cut argument uses the set of vertices reachable from $u$, which $a$ leaves.

Van Hoeve and Katriel state the rerouting theorem for an unused arc of a minimum-weight flow of fixed value (their Theorem 2): a cheapest directed circuit of $G_f$ through the arc gives the best flow of the same value using it, and if no such circuit exists no such flow exists; with all weights zero this is item 1. Maher, Narodytska, Quimper and Walsh state the unweighted test: with all costs zero, an extra unit can be pushed through an edge iff both ends of its residual copy are in the same strongly connected component of the residual graph, and removing a unit is checked similarly; they apply it to the unit arcs of their SEQUENCE network.

## Sources

- W.-J. van Hoeve and I. Katriel, "Global constraints", in F. Rossi, P. van Beek and T. Walsh (eds.), *Handbook of Constraint Programming*, Elsevier (2006), chapter 6, 169–208, doi:10.1016/S1574-6526(06)80010-6; author copy [https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf](https://www.andrew.cmu.edu/user/vanhoeve/papers/chapter.pdf). Flows with demands, the residual graph and Theorem 2 (an arc $a$ with $f(a)=0$) in §7.1.2; Theorem 9 and its use in §7.3.2 (section and theorem numbers of the author copy).
- M. J. Maher, N. Narodytska, C.-G. Quimper and T. Walsh, "Flow-based propagators for the SEQUENCE and related global constraints", *Principles and Practice of Constraint Programming – CP 2008*, Lecture Notes in Computer Science 5202 (2008), 159–174, doi:10.1007/978-3-540-85958-1_11. The residual graph and the strongly-connected-components test for pushing an extra unit of flow through an edge, and the remark that removing a unit is checked similarly, §2 of arXiv:0909.4452v1, [https://arxiv.org/abs/0909.4452v1](https://arxiv.org/abs/0909.4452v1).
