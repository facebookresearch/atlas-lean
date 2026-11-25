# Subspace topology

Let $X$ be a topological space and let $A \subseteq X$ be a subset. The *subspace topology* on $A$ is the collection $\{U \cap A : U \text{ open in } X\}$. Equivalently, it is the topology induced on $A$ by the inclusion $\iota\colon A \to X$, whose open sets are the preimages $\iota^{-1}(U) = U \cap A$ of the open sets $U$ of $X$. So a subset of $A$ is open in $A$ exactly when it equals $U \cap A$ for some open set $U$ of $X$. The set $A$ with this topology is called a *subspace* of $X$.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the topology on a subset, given as the type of points satisfying a predicate, induced by the inclusion, whose open sets are the preimages of open sets: `instTopologicalSpaceSubtype` and `TopologicalSpace.induced`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Defs/Induced.lean#L60-L80.
