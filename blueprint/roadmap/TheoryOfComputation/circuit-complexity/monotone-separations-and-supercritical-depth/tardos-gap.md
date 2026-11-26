# Tardos: an exponential gap between monotone and non-monotone circuit complexity

There is a monotone graph property $T_n$ on $n$-vertex graphs that is computable in polynomial time, hence by Boolean circuits of polynomial size, but every monotone circuit computing $T_n$ has size

$$
\exp\Bigl(\Omega\bigl((n/\log n)^{1/3}\bigr)\Bigr).
$$

The function is a threshold of the Lovász theta function of the complement graph, which lies between the clique number and the chromatic number and is computable to high precision in polynomial time by the ellipsoid method.

## Proof sketch

Set $T_n(G) = 1$ iff $\vartheta(\overline{G}) \ge k$ for a suitable $k$. Since $\omega(G) \le \vartheta(\overline{G}) \le \chi(G)$, $T_n$ accepts every graph with a $k$-clique and rejects every complete $(k-1)$-partite graph, which are exactly the test distributions in the Alon-Boppana approximation method; their monotone lower bound for separating $k$-cliques from $(k-1)$-colourable graphs therefore applies to $T_n$. Monotonicity of $\vartheta(\overline{G})$ in $G$ follows from its SDP characterization.

## Depends on

- [Lovász theta function](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/lovasz-theta.md)

## Proof depends on

- [Alon–Boppana: monotone circuits for clique need exponential size](../monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md)
- [Razborov: monotone circuits for clique need superpolynomial size](../monotone-circuit-lower-bound-for-clique/razborov-monotone-clique.md)

## Sources

- É. Tardos, "The gap between monotone and non-monotone circuit complexity is exponential", Combinatorica 8 (1988) 141-142.
- N. Alon, R. B. Boppana, "The monotone circuit complexity of Boolean functions", Combinatorica 7 (1987) 1-22.
