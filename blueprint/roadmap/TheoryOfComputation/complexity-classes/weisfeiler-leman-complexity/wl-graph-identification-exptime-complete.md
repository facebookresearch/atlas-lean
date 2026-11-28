# EXPTIME-completeness of Weisfeiler–Leman identification dimension

For a simple uncolored graph $G$, say dimension $k>0$ identifies it if every finite simple graph with the same all-round WL histograms is isomorphic to $G$. At $k=1$, initialize vertex colors uniformly and update by the old color and multiset of neighbour colors. At $k>1$, initialize by the tuple equalities and adjacencies and use joint replacement vectors (one vector per replacement vertex), keeping each round's old color. Let $\dim_{WL}(G)$ be the natural infimum of its positive identifying dimensions. Encode a nonempty graph by a unary order header terminated by zero followed by its full row-major adjacency bits and then a positive binary $k$ most-significant bit first with initial bit one. The language of valid encodings with $\dim_{WL}(G)\le k$ is EXPTIME-complete. The comparator uses deterministic local one-tape machines with fixed finite alphabet and distinct accepting and rejecting states; the decider runs within $2^{C(L+1)^d}$ and hardness uses polynomial-time many-one word functions. Comparison graphs in the identifying predicate are unrestricted in order.

In this identification model there is one two-sided tape, initially with the input at origin onward, blank elsewhere and the head at origin. False/true/blank are 1/2/0. A local transition reads the state and symbol, writes one symbol, moves left/stay/right, and enters the next state. State 0 is initial, 1 accepts and 2 rejects, with both halts absorbing. The exponential-time decider must halt on every word and be in state 1 exactly on members. The reduction must halt in state 1 with its binary result starting at origin and a blank immediately after it, with no constraints on cells farther away. The result word preserves membership in both directions. Both use natural $C,d$ per machine in the exact budgets stated above (polynomial $C(L+1)^d$ for reductions).

## Depends on

- One-dimensional neighbor refinement and higher-dimensional joint refinement, infimum of identifying dimensions, binary coding, and local tape deciders and reducers.

## Proof outline

Check all-round and finite-round tests against the histogram definitions, and prove any monotonicity needed to replace the infimum comparison by identification at the input dimension. Separate the reduction and its correctness from the cost/encoding proof.

- Exponential upper decision bound, existence of a positive identifying dimension, and a reduction preserving identification against all comparison graphs.

## Sources

- [Comparator statement: `OAI.WLIdentification.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WLIdentification.lean#L140-L143)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/133.md)
- [One-tape dynamics, halting semantics and reducer output format](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WLIdentification.lean#L75-L137)
