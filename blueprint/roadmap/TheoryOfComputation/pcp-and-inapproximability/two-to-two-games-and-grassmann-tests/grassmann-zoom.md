# Zoom-in and zoom-out subgraphs of the Grassmann graph

Let $\mathrm{Gr}(n, \ell)$ be the Grassmann graph on $\ell$-dimensional subspaces of $\mathbb{F}_2^n$, with $L \sim L'$ when $\dim(L \cap L') = \ell - 1$. For a subspace $Q$ of dimension $q < \ell$, the **zoom-in** on $Q$ is the induced subgraph on $\{L : Q \subseteq L\}$; for a subspace $W$ of codimension $w$, the **zoom-out** on $W$ is the induced subgraph on $\{L : L \subseteq W\}$. Both are isomorphic to Grassmann graphs of smaller order. A set $S$ of vertices of density $\mu(S)$ is **$(r, \varepsilon)$-pseudorandom** if for every $Q \subseteq W$ with $\dim Q + \operatorname{codim} W \le r$,

$$
\Pr_{L : Q \subseteq L \subseteq W}[L \in S] \le \varepsilon.
$$

## Depends on

- [Grassmann graph over $\mathbb{F}_2$](../../../GraphTheory/algebraic-graph-theory/part-01/grassmann-graphs/gr.md)

## Sources

- I. Dinur, S. Khot, G. Kindler, D. Minzer, M. Safra, "On non-optimally expanding sets in Grassmann graphs", STOC (2018); Israel Journal of Mathematics 243 (2021), ECCC TR17-094.
- S. Khot, D. Minzer, M. Safra, "Pseudorandom sets in Grassmann graph have near-perfect expansion", FOCS (2018); Annals of Mathematics 198 (2023), ECCC TR18-006.
