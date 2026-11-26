# Unique disjointness

For a finite set $\alpha$, *unique disjointness* $\mathrm{UDISJ}_\alpha$ is the partial function on pairs of subsets $(S, T)$ of $\alpha$ defined by $\mathrm{UDISJ}(S, T) = 1$ if $S \cap T = \emptyset$, $\mathrm{UDISJ}(S, T) = 0$ if $|S \cap T| = 1$, and undefined (don't care) if $|S \cap T| \ge 2$. Its $1$-cover number governs the extension complexity of the correlation polytope, and it is the canonical hard function for randomized and nondeterministic communication.

## Depends on

- [Set intersection function](../randomized-communication-protocols/disj-fn.md)

## Sources

- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
