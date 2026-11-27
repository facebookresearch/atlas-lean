# Search problems relative to a random oracle

Let $H$ be a uniformly random function from $\{0,1\}^*$ to $\{0,1\}$ (a *random oracle*). A family of relations $R^H \subseteq \{0,1\}^* \times \{0,1\}^*$ is an *NP search problem relative to $H$* if membership $(x, w) \in R^H$ is decidable in deterministic polynomial time with oracle access to $H$ and $|w| \le \mathrm{poly}(|x|)$. It is *quantumly easy* if a quantum polynomial-time algorithm with superposition access to $H$ outputs a valid $w$ with probability $\ge 2/3$ for every $x$, and *classically hard* if every probabilistic algorithm making $\mathrm{poly}(|x|)$ classical queries to $H$ succeeds with probability $\mathrm{negl}(|x|)$, where both probabilities are also over $H$.

## Depends on

- [Search problems: FNP, FP and TFNP](../../../complexity-classes/total-search-problems/search-problems-fnp-fp-and-tfnp.md)
- [BQP](../../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Takashi Yamakawa, Mark Zhandry, "Verifiable quantum advantage without structure", FOCS (2022), Journal of the ACM 71(3) (2024); arXiv:2204.02063.
