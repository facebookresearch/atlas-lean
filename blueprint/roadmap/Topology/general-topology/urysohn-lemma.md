# Urysohn's lemma

Two disjoint closed subsets of a normal space can be separated by a continuous function with values in $[0, 1]$ that equals $0$ on one of them and $1$ on the other. Mathlib proves this under a weaker normality hypothesis than the textbook one, which also requires points to be closed: in Mathlib a topological space $X$ is *normal* when any two disjoint closed subsets of $X$ have disjoint open neighbourhoods, with no $T_1$ axiom. Let $X$ be normal in this sense and let $A, B \subseteq X$ be disjoint closed subsets, possibly empty. Then there is a continuous function $f \colon X \to \mathbb{R}$ with $f(x) = 0$ for all $x \in A$, $f(x) = 1$ for all $x \in B$, and $0 \le f(x) \le 1$ for all $x \in X$. Restricting the codomain to $[0, 1]$, with the subspace topology, gives a continuous function $X \to [0, 1]$ with the same values, which is the familiar statement.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for normal spaces, in which disjoint closed sets have disjoint open neighbourhoods and points need not be closed: `NormalSpace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Separation/Regular.lean#L509-L513.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the textbook normal spaces, which are also $T_1$: `T4Space`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Separation/Regular.lean#L626-L627.
