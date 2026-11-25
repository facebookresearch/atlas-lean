# Baire category theorem for completely pseudometrizable spaces

In a complete metric space, such as the real line, the intersection of countably many dense open sets is dense; in $\mathbb{R}$ it meets every nonempty open interval. Mathlib proves this for a wider class of spaces: the topology only has to be induced by some complete pseudometric. Let $X$ be a topological space that is completely pseudometrizable, meaning that some pseudometric on $X$ induces its topology and makes $X$ complete. If $U_1, U_2, \dots$ are open subsets of $X$, each dense in $X$, then $\bigcap_{n \ge 1} U_n$ is dense in $X$; in other words, $X$ is a Baire space. No separation axiom and no nonemptiness of $X$ is assumed, and completeness is required for one pseudometric inducing the topology, not for every such pseudometric. A complete metric space $(X, d)$, with the topology induced by $d$, is completely pseudometrizable, which gives the familiar statement.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for completely pseudometrizable spaces: `TopologicalSpace.IsCompletelyPseudoMetrizableSpace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L51-L57.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the Baire property: countable intersections of dense open sets are dense: `BaireSpace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Defs/Basic.lean#L240-L246.
