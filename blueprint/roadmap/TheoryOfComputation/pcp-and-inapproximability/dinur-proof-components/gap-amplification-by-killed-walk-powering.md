# Gap amplification by killed-walk powering

For every $d$, every $\lambda < d$ and every finite alphabet $\Sigma$ there is $c = c(d, \lambda, |\Sigma|) > 0$ such that for every $d$-regular constraint graph $G$ over $\Sigma$ with self-loops and second eigenvalue at most $\lambda$, and every $t \ge 1$, the killed-walk power satisfies: $G^t$ is satisfiable iff $G$ is, its size is $|V(G)| \cdot (dt)^{O(t)}$, and

$$\mathrm{UNSAT}(G^t) \ge c\, t \cdot \min\Big(\mathrm{UNSAT}(G), \frac{1}{t}\Big).$$

## Proof sketch

Fix a labelling of $G^t$ and define a labelling of $G$ by plurality of opinions. Fix a set $F$ of edges violated by the plurality labelling with $|F|/|E(G)| = \Theta(\min(\mathrm{UNSAT}(G), 1/t))$, and count the steps of a random walk that traverse an edge of $F$ with both endpoint opinions agreeing with the plurality ("hits"); its first moment is $\Omega(t\, |F|/|E(G)|)$ and, by expansion, its second moment is $O(t\, |F|/|E(G)|)$, so by the second-moment method a walk has at least one hit with probability $\Omega(t\, |F|/|E(G)|)$, which is the stated bound; truncating the walks at a fixed multiple of $t$ loses only a constant factor.

## Depends on

- [Powering a constraint graph along killed random walks](powering-along-killed-random-walks.md)

## Proof depends on

- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)
- [Hitting property of expander walks](../../../GraphTheory/graph-families-and-operations/expander-graphs/hitting-property-of-expander-walks.md)

## Sources

- J. Radhakrishnan, "Gap Amplification in PCPs Using Lazy Random Walks", ICALP 2006.
- J. Radhakrishnan and M. Sudan, "On Dinur's Proof of the PCP Theorem", Bulletin of the American Mathematical Society 44(1), 2007.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
