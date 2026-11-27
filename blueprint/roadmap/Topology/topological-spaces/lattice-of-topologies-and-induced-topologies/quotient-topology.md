# Coinduced topology and the quotient topology

Let $X$ be a topological space, let $Y$ be a set and let $f\colon X \to Y$ be a function. The topology on $Y$ *coinduced* by $f$ is the collection of all subsets $U \subseteq Y$ such that $f^{-1}(U)$ is open in $X$. It is a topology on $Y$, because preimages commute with unions and intersections and $f^{-1}(Y) = X$, and it is the finest topology on $Y$ for which $f$ is continuous. When $f$ is surjective, it is the *quotient topology* on $Y$ induced by $f$. Surjectivity is not required: a subset of $Y$ disjoint from the image of $f$ has empty preimage, so it is open.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the topology coinduced by an arbitrary function, in which a set is open when its preimage is open: `TopologicalSpace.coinduced`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Defs/Induced.lean#L82-L91.
