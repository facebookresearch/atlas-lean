# Pinned Ising conditionals and the contracted FK law

For a labelled finite loopless edge list, Gibbs weights are the exponentials of $\sum_e K_e\sigma_{e_-}\sigma_{e_+}+\sum_vh_v\sigma_v$. Condition by restricting the finite sum to the specified spin assignments and normalizing. For the two-terminal comparison, delete the commonly pinned sites and their incident edges, and contract each of the two disjoint terminal sets to its own vertex. A configuration of retained edges has weight $2^{k(\omega)}\prod_{e\in\omega}(1-e^{-2K_e})\prod_{e\notin\omega}e^{-2K_e}$, with all isolated vertices counted in the contracted component count. Normalize these weights and use the probability that the two terminals are connected. Parallel edges remain separate labels; this is not a model obtained by wiring the commonly pinned sites.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BufferedIsing.lean#L11-L90)
