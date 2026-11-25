# In a pseudometrizable space, compact sets are exactly the sequentially compact sets

A metric space is compact if and only if it is sequentially compact: every sequence in it has a subsequence converging to a point of the space. Mathlib proves the same equivalence for every subset of a pseudometrizable space. Let $X$ be a topological space whose topology is induced by some pseudometric, and let $s \subseteq X$. Then $s$ is compact, meaning that every cover of $s$ by open subsets of $X$ has a finite subcover, if and only if $s$ is sequentially compact: for every sequence $(x_n)_{n \in \mathbb{N}}$ with all $x_n \in s$ there are a point $a \in s$ and a strictly increasing map $\varphi \colon \mathbb{N} \to \mathbb{N}$ with $x_{\varphi(n)} \to a$. The limit must lie in $s$ itself, not merely in its closure. Taking $s = X$ for a metric space $(X, d)$ with the topology induced by $d$ gives the familiar statement.

## Sources

- James R. Munkres, Topology, 2nd ed., Prentice Hall, 2000.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for sequentially compact sets, with the limit in the set: `IsSeqCompact`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Defs/Sequences.lean#L69-L72.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the pseudometrizability hypothesis: `TopologicalSpace.PseudoMetrizableSpace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Topology/Sequences.lean#L405.
