# Gap amplification by killed-walk powering

For every $d$, every $\lambda < d$ and every finite alphabet $\Sigma$ there is $c = c(d, \lambda, |\Sigma|) > 0$ such that for every $d$-regular constraint graph $G$ over $\Sigma$ with self-loops and second eigenvalue at most $\lambda$, and every $t \ge 1$, the killed-walk power satisfies: $G^t$ is satisfiable iff $G$ is, its size is $|V(G)| \cdot d^{O(t)}$, and

$$\mathrm{UNSAT}(G^t) \ge c \sqrt{t} \cdot \min\Big(\mathrm{UNSAT}(G), \frac{1}{t}\Big).$$

## Proof sketch

Fix a labelling of $G^t$ and define a labelling of $G$ by plurality of opinions. Count the expected number of steps of a random walk that traverse an edge violated by the plurality labelling with both endpoint opinions agreeing with the plurality ("hits"); its first moment is $\Omega(t \cdot \mathrm{UNSAT}(G))$ and, by expansion, its second moment is $O(t \cdot \mathrm{UNSAT}(G))$, so by the second-moment method a walk has at least one hit with probability $\Omega(t\, \mathrm{UNSAT}(G))$, which gives the stated bound after the truncation at $1/t$.

## Depends on

- [Powering a constraint graph along killed random walks](powering-along-killed-random-walks.md)

## Proof depends on

- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)
- [Hitting property of expander walks](../../../GraphTheory/graph-families-and-operations/expander-graphs/hitting-property-of-expander-walks.md)

## Sources

- J. Radhakrishnan, "Gap Amplification in PCPs Using Lazy Random Walks", ICALP 2006.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
