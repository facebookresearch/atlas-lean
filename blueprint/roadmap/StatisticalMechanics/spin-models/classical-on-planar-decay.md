# Exponential decay for the planar classical O(n) model

Fix an integer $n\ge3$ and $\beta>0$. On a finite subgraph of the square lattice (any set of vertices and subset of unit horizontal or vertical edges, oriented in their positive directions to count each once), let $\sigma_x\in S^{n-1}$ have independent normalized rotation-invariant surface measures as reference. For couplings $0\le b_e\le\beta$ reweight the reference law by the density proportional to $\exp(\sum_e b_e\langle\sigma_{e_-},\sigma_{e_+}\rangle)$. No exterior spins are pinned. There exist real $A$ and $m>0$, depending only on $n,\beta$, such that all these graphs, couplings, and pairs of vertices $x,y$ satisfy

$$
0\le\mathbb E_b\langle\sigma_x,\sigma_y\rangle\le A e^{-m\|x-y\|_2}.
$$

**Conventions.** Use normalized sphere measure, its finite product, and the finite-edge Gibbs partition function; the distance is Euclidean on the lattice rather than graph distance in the subgraph.

## Depends on

- [The finite planar classical O(n) Gibbs law](classical-on-gibbs-law.md)

## Expansion

The finite-volume positivity argument and a uniform two-dimensional block comparison that bounds the correlation through successive separated blocks for each finite $\beta$.

Build the finite $O(n)$ Gibbs law as a normalized density and establish its nonnegative two-point correlation. Isolate the contraction per block and the iteration; quantify constants before the graph and all its local couplings. No infinite-volume assertion is required.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ClassicalON.lean#L53-L55)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/215.md)
- [Accompanying manuscript: Exponential decay in two-dimensional classical $O(n)$ models](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Exponential-decay-in-two-dimensional-classical-On-models-September-23-2026/paper.pdf)
