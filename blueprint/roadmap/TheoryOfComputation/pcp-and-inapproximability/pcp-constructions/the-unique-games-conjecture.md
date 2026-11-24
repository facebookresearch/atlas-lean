# The Unique Games Conjecture

A *unique game* $\mathcal{U}(G(V, E), [n], \{\pi_e\})$ is a constraint satisfaction problem on a directed graph $G(V, E)$ whose vertices are variables taking labels in
$[n]$, with a bijection $\pi_e : [n] \to [n]$ on each edge $e = (v, w)$; a labelling $L : V \to [n]$ satisfies $e$ when $\pi_e(L(v)) = L(w)$. Its value $\mathrm{OPT}(\mathcal{U})$ is the
largest fraction of edges satisfied by a labelling.

**Conjecture (Khot, 2002).** For every $\varepsilon, \delta > 0$ there is $n = n(\varepsilon, \delta)$ such that, given a unique game with label set $[n]$, it is $\mathsf{NP}$-hard to
distinguish $\mathrm{OPT}(\mathcal{U}) \ge 1 - \varepsilon$ from $\mathrm{OPT}(\mathcal{U}) \le \delta$.

The conjecture fails for $\varepsilon = 0$, since a fully satisfiable unique game is found by propagating labels. A random labelling satisfies a $\frac1n$ fraction
of the constraints in expectation, so $n \ge \frac1\delta$ is necessary, and it is known that $n \ge 2^{\Omega(1/\varepsilon)}$ is necessary. The graph may be assumed regular
and undirected.

## Depends on

- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)

## Sources

- S. Khot, "On the Unique Games Conjecture", *Proceedings of the 25th IEEE Conference on Computational Complexity*, 2010, <https://cs.nyu.edu/~khot/papers/UGCSurvey.pdf>: Section 2.4 (Definition 2.4, the conjecture and the remarks following it).
