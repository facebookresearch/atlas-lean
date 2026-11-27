# EXPTIME-completeness of variable-dimension WL equivalence on connected subcubic graphs

Given binary $k\ge2$ and a pair of uncolored simple graphs encoded by their separately framed binary orders and row-major adjacency matrices, accept exactly when both have the same positive order, both are connected of maximum degree at most three, and their joint $k$-WL tuple histograms agree in all rounds. Joint refinement starts from all tuple equality and adjacency facts and at each update pairs the old color with the multiset of vectors of old colors for replacing each coordinate by the same vertex. This restricted language is complete for EXPTIME under polynomial-time many-one reductions on binary words. Deciders and reductions use the same [finite multitape machine and full-tape output convention](../time-and-space-classes-on-multi-tape-machines/finite-multitape-word-computations.md), with a separate budget of $2^{c(L+1)^d}$ for each decider and $c(L+1)^d$ for each reduction. Malformed words are not members.

## Depends on

- [Finite multitape computation and full-tape binary output](../time-and-space-classes-on-multi-tape-machines/finite-multitape-word-computations.md)
- For each graph, the order is encoded by as many $1$ bits as the numeral has bits, a $0$ delimiter, and the little-endian `Nat.bits` for its order; the full row-major binary matrix follows. The two encodings are concatenated, then the dimension is written using the same framing as the orders.
- Connected positive-order subcubic inputs and exact graph-code validity.

## Proof outline

Demonstrate that reductions produce the restricted class without changing acceptance, and that membership is decided on all encoded words. The unrestricted language alone cannot establish hardness under this promise.

- Hardness transformation with connectivity, subcubic degree and same-order guarantees, and the inherited exponential upper bound after checking those restrictions.

## Sources

- [Comparator statement: `OAI.VariableWL.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VariableWL.lean#L125-L127)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/133.md)
