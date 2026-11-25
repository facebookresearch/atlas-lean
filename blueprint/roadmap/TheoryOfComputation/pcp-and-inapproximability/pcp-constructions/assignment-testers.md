# Assignment testers

A *constraint graph* $G = \langle (V, E), \Sigma, \mathcal{C} \rangle$ has an undirected graph $(V, E)$ whose vertices are variables over the finite alphabet $\Sigma$, and a constraint
$c(e) \subseteq \Sigma \times \Sigma$ on each edge. For an assignment $\sigma : V \to \Sigma$, $\mathrm{UNSAT}_\sigma(G)$ is the fraction of edges $(u, v)$ with $(\sigma(u), \sigma(v)) \notin c(e)$. For an
assignment $a$ to Boolean variables $X$ and a set $S$ of such assignments, $\mathrm{rdist}(a, S)$ is the least fraction of variables on which $a$ differs from a member
of $S$, with the convention $\mathrm{rdist}(a, \emptyset) = 1$.

An *assignment tester* with alphabet $\Sigma_0$ and rejection probability $\varepsilon > 0$ is an algorithm $P$ that maps each Boolean circuit $\Phi$ over variables $X$ to a
constraint graph $G = \langle (V, E), \Sigma_0, \mathcal{C} \rangle$ with $V \supseteq X$, where $\Sigma_0$ contains the two Boolean values $0$ and $1$ so that $a \cup b$ is an assignment $V \to \Sigma_0$, such that, writing $V' = V \setminus X$ and $\mathrm{SAT}(\Phi)$ for the satisfying assignments, for every
$a : X \to \{0,1\}$:

- (completeness) if $a \in \mathrm{SAT}(\Phi)$, some $b : V' \to \Sigma_0$ has $\mathrm{UNSAT}_{a \cup b}(G) = 0$;
- (soundness) if $a \notin \mathrm{SAT}(\Phi)$, every $b : V' \to \Sigma_0$ has $\mathrm{UNSAT}_{a \cup b}(G) \ge \varepsilon \cdot \mathrm{rdist}(a, \mathrm{SAT}(\Phi))$.

No requirement is made on the running time of $P$. In Dinur's proof of the PCP theorem, an assignment tester applied to constant-size circuits
reduces the alphabet of a constraint graph by composition.

## Depends on

- [2CSP instances](../dinur-s-gap-amplification/cspinstance.md)
- [Evaluation of a flat Boolean circuit](../../complexity-classes/time-and-space-complexity-classes/circuit-eval.md)

## Sources

- I. Dinur, "The PCP theorem by gap amplification", *Journal of the ACM* 54(3), 2007; preprint ECCC TR05-046, copy at <https://www.cs.umd.edu/~gasarch/TOPICS/pcp/dinur.pdf>: Definition 1.2 (constraint graphs and UNSAT), Definition 2.2 (assignment tester) and Lemma 1.8 with Section 5 (composition).
