# Powering a constraint graph along killed random walks

Let $G$ be a $d$-regular constraint graph over $\Sigma$, with $d$ edges leaving each vertex in a fixed order and a constraint $c_e$ on each edge $e = (u, v)$, and let $t \ge 1$ be an integer; put $T^* = 5t$. The powered graph $G^t$ (Radhakrishnan–Sudan, Definition 5.13) has vertex set $V(G)$ and alphabet $\Sigma^{(d+1)^t}$: a value $A(v)$ is read as a partial assignment giving a value $A(v)[w] \in \Sigma$ (the *opinion* of $v$ about $w$) to every vertex $w$ within distance $t$ of $v$, and $A(v)[w]$ is null for every other $w$. Two partial assignments $A_1, A_2$ *pass the test at* an edge $e = (u, v)$ of $G$ when one of $A_1[u], A_1[v], A_2[u], A_2[v]$ is null, or $A_1$ and $A_2$ agree on $\{u, v\}$ and $c_e(A_1[u], A_2[v]) = 1$. For every vertex $a$ and every string $\tau = ((j_1, s_1), \dots, (j_{T^*}, s_{T^*})) \in ([d] \times [t])^{T^*}$, $G^t$ has one edge labelled $\tau$ with tail $a$. It follows the walk $a = v_0, v_1, \dots$ in which step $i$ takes the $j_i$-th edge $e_i$ leaving $v_{i-1}$ and the walk stops after that step, with $T = i$, if $s_i = 1$; for uniform $\tau$ this is a *killed* (lazy) walk that stops after each step with probability $1/t$, truncated at $T^*$ steps. If the walk has not stopped within $T^*$ steps, the edge is a self-loop at $a$ whose constraint is always satisfied. Otherwise the edge is $(a, b)$ with $b = v_T$, and values $A(a), A(b)$ satisfy it when $A(a)$ and $A(b)$ pass the test at every edge $e_1, \dots, e_T$ of the walk. Every vertex has $(dt)^{T^*}$ outgoing edges, so $G^t$ has exactly $|V(G)|\,(dt)^{5t}$ edges.

## Depends on

- [Spectral expander](../../../GraphTheory/graph-families-and-operations/expander-graphs/is-spectral-expander.md)

## Sources

- J. Radhakrishnan, "Gap Amplification in PCPs Using Lazy Random Walks", ICALP 2006, LNCS 4051.
- J. Radhakrishnan and M. Sudan, "On Dinur's Proof of the PCP Theorem", Bulletin of the AMS 44(1), 2007: Section 5.6 (the proof and the test), Section 5.8 (truncation at $T^* = 5t$, Lemma 5.12) and Definition 5.13.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007 (the fixed-length power that this construction modifies).
