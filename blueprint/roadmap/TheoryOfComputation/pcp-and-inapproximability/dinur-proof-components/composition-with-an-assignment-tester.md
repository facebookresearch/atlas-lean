# Composition with an assignment tester reduces the alphabet

There are a fixed finite alphabet $\Sigma_0$ and an absolute constant $\beta > 0$ such that for every binary constraint graph $G$ over any finite alphabet $\alpha$ the composed graph $G \circ \mathcal{P}$, obtained by replacing every edge with the Hadamard assignment tester of its constraint (sharing the vertex tables), satisfies: $G \circ \mathcal{P}$ is over $\Sigma_0$; its size is $|E(G)| \cdot c(|\alpha|)$ for a function $c$ depending only on $|\alpha|$; it is satisfiable iff $G$ is; and

$$\mathrm{UNSAT}(G \circ \mathcal{P}) \ge \beta \cdot \mathrm{UNSAT}(G).$$

The essential feature is that $\beta$ and $\Sigma_0$ do not depend on $|\alpha|$, so composition can follow the alphabet blow-up of graph powering.

## Proof sketch

A labelling of the composed graph decodes each vertex table to the nearest long code (or an arbitrary label if none is within $1/4$). If an edge of $G$ is violated by the decoded labels, then either some table is far from all long codes or the tables are close to codes of a violating pair; in both cases the assignment tester of that edge rejects with probability at least $\varepsilon_0/4$, and averaging over edges gives the bound.

## Depends on

- [Alphabet reduction with given constants](../dinur-s-gap-amplification/alphabet-reduction.md)
- [Assignment testers](../pcp-constructions/assignment-testers.md)

## Proof depends on

- [The Hadamard assignment tester has constant queries and rejection rate](hadamard-assignment-tester.md)
- [Local tests as constraint graphs](../pcp-verifiers-and-local-tests/local-tests-as-constraint-graphs.md)

## Sources

- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
