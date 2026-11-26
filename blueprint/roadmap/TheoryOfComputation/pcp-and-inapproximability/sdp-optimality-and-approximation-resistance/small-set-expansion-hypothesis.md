# The small-set expansion hypothesis

For a $d$-regular graph $G = (V, E)$ and $S \subseteq V$, the **edge expansion** is $\Phi_G(S) = |E(S, V \setminus S)| / (d|S|)$. The **small-set expansion problem** $\mathrm{SSE}(\eta, \delta)$ asks to distinguish graphs having a set $S$ of measure $|S|/|V| = \delta$ with $\Phi_G(S) \le \eta$ from graphs in which every set of measure $\delta$ has $\Phi_G(S) \ge 1 - \eta$. The **small-set expansion hypothesis** (Raghavendra-Steurer) asserts that for every $\eta > 0$ there is $\delta > 0$ such that $\mathrm{SSE}(\eta, \delta)$ is NP-hard.

## Depends on

- [Edge expansion of a vertex set](../../../GraphTheory/algebraic-graph-theory/part-01/grassmann-graphs/untitled.md)

## Sources

- P. Raghavendra, D. Steurer, "Graph expansion and the unique games conjecture", STOC (2010).
- P. Raghavendra, D. Steurer, M. Tulsiani, "Reductions between expansion problems", CCC (2012).
