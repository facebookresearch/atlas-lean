# Heine–Borel theorem: in a proper metric space, compact means closed and bounded

Let $X$ be a proper metric space: every closed ball $\{y \in X : d(x, y) \le r\}$ in $X$ is compact. Then a subset $A \subseteq X$ is compact if and only if $A$ is closed and bounded. Every finite-dimensional real normed space is proper, so in particular a subset of $\mathbb{R}^n$ with the Euclidean metric is compact if and only if it is closed and bounded.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for proper metric spaces: `ProperSpace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/MetricSpace/ProperSpace.lean#L37-L39.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the properness of finite-dimensional real normed spaces: `FiniteDimensional.proper_real`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Module/FiniteDimension.lean#L556-L559.
