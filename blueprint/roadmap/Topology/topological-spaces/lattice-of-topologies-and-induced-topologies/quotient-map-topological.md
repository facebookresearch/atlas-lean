# Quotient map

Let $X$ and $Y$ be topological spaces. A function $q\colon X \to Y$ is a *quotient map* if $q$ is surjective and, for every subset $U \subseteq Y$, $U$ is open in $Y$ if and only if $q^{-1}(U)$ is open in $X$. Equivalently, $q$ is surjective and the topology of $Y$ is the topology coinduced by $q$, made of the subsets of $Y$ whose preimage under $q$ is open in $X$. The \"only if\" half of the condition says that $q$ is continuous.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for quotient maps as surjective maps whose codomain carries the topology coinduced by the map: `Topology.IsQuotientMap` and `Topology.IsCoinducing`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Defs/Induced.lean#L138-L144 and https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Defs/Induced.lean#L165-L170.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the coinduced topology, in which a set is open when its preimage is open: `TopologicalSpace.coinduced`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Defs/Induced.lean#L82-L91.
