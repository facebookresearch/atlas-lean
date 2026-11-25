# Dinur's amplification lemma for graph powering

Let $G = \langle (V, E), \Sigma, \mathcal{C}\rangle$ be a $d$-regular constraint graph and $t \ge 1$ an integer; a *$t$-step walk* is a sequence $(u_0, \dots, u_t)$ with $(u_i, u_{i+1}) \in E$. The
*powered* constraint graph $G^t$ has the same vertices; $u$ and $v$ are joined by $k$ parallel edges when $G$ has exactly $k$ $t$-step walks from $u$ to $v$; its
alphabet is $\Sigma^{d^{\lceil t/2\rceil}}$, a value at $u$ being read as an assignment to the vertices reachable from $u$ by walks of length $\lceil t/2 \rceil$; and the
constraint on an edge $(u, v)$ is satisfied by values $a, b$ when some assignment to those two neighborhoods agrees with $a$ and $b$ and satisfies every
constraint of $G$ between them. $\mathrm{UNSAT}$ is the least fraction of violated constraints over all assignments, and $\lambda(G)$ is the second largest
absolute eigenvalue of the adjacency matrix.

**Lemma (Dinur).** Let $0 < \lambda < d$ and $|\Sigma|$ be constants. There is a constant $\beta_2 = \beta_2(\lambda, d, |\Sigma|) > 0$ such that for every integer $t \ge 1$ and every
$d$-regular constraint graph $G$ with a self-loop on each vertex and $\lambda(G) \le \lambda$,

$$\mathrm{UNSAT}(G^t) \ge \beta_2 \sqrt t \cdot \min\Bigl(\mathrm{UNSAT}(G), \frac1t\Bigr).$$

Powering multiplies the number of edges by $d^{t-1}$, a linear blow-up for constant $t$, and $\mathrm{UNSAT}(G) = 0$ implies $\mathrm{UNSAT}(G^t) = 0$. The proof bounds how often a random walk in an expander passes through a fixed set of edges. The lemma is the main step in the proof of [Dinur's gap amplification](dinur-gap-amplification.md).

## Sources

- I. Dinur, "The PCP theorem by gap amplification", *Journal of the ACM* 54(3), 2007; ECCC TR05-046, <https://eccc.weizmann.ac.il/report/2005/046/>: Section 1.2, the definition of $G^t$, Lemma 1.6 (amplification lemma) and the remarks following it, and Proposition 2.5 (edges of random walks in expanders).
