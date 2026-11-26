# The random-edge verifier rejects with probability at least half the gap

Let $G$ be a constraint graph with $m \ge 1$ edges over an alphabet $\Sigma$, and consider the verifier that reads a proof assigning a label to every vertex, chooses an index $j$ uniformly from $\{0, \dots, 2^{\lceil \log_2 m \rceil} - 1\}$ using $\lceil \log_2 m \rceil$ fair bits, accepts if $j \ge m$, and otherwise reads the labels of the two endpoints of edge $j$ and accepts iff the constraint of edge $j$ holds. Then every proof is rejected with probability at least $\mathrm{UNSAT}(G)/2$, and the satisfying labellings of $G$ are accepted with probability $1$.

## Proof sketch

Each real edge is chosen with probability $2^{-\lceil\log_2 m\rceil} \ge 1/(2m)$; the rejected proportion of real edges is at least $\mathrm{UNSAT}(G)$, so the rejection probability is at least $\mathrm{UNSAT}(G)/2$.

## Depends on

- [Assignment testers](../pcp-constructions/assignment-testers.md)
- [Local test on a proof string](local-test-on-a-proof-string.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
