# Preprocessing a constraint graph into a regular expander

Use constraint graphs and $\mathrm{UNSAT}(G) = \min_\sigma \mathrm{UNSAT}_\sigma(G)$ as in [assignment testers](assignment-testers.md); for a $d$-regular graph whose adjacency matrix has eigenvalues $d = \lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_n$, $\lambda(G) = \max_{i \ge 2} |\lambda_i|$ is the
largest absolute value of a nontrivial eigenvalue, as on [the amplification lemma for graph powering](../dinur-s-gap-amplification/dinur-s-amplification-lemma-for-graph-powering.md), and the size of $G$ is its number of vertices and edges.

**Lemma (Dinur).** There are constants $0 < \lambda < d$ and $\beta_1 > 0$ such that every constraint graph $G$ can be transformed in polynomial time into a
constraint graph $G' = \mathrm{prep}(G)$ with:

- $G'$ is $d$-regular with self-loops and $\lambda(G') \le \lambda < d$;
- $G'$ has the same alphabet as $G$ and $\mathrm{size}(G') = O(\mathrm{size}(G))$;
- $\beta_1 \cdot \mathrm{UNSAT}(G) \le \mathrm{UNSAT}(G') \le \mathrm{UNSAT}(G)$.

The construction first replaces each vertex by an expander cloud with equality constraints, making the graph regular of constant degree, and
then superimposes a constant-degree expander and self-loops carrying null constraints; each step changes the unsat value by at most a constant
factor.

## Depends on

- [Assignment testers](assignment-testers.md)

## Proof depends on

- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- I. Dinur, "The PCP theorem by gap amplification", *Journal of the ACM* 54(3), 2007; preprint ECCC TR05-046, copy at <https://www.cs.umd.edu/~gasarch/TOPICS/pcp/dinur.pdf>: Lemma 1.7 (Preprocessing Lemma), Section 2.1 (Lemma 2.1, Lemma 2.2, Theorem 2.3, Corollary 2.4) and Section 4 (Definitions 4.1–4.2, Lemmas 4.1–4.2, Corollary 4.3).
