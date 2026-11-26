# FPRAS for perfect matchings in finite simple graphs

There is one [eight-symbol fair-bit Post–Turing machine](eight-symbol-fair-bit-post-turing-machine.md) and fixed integers $C>0,d\ge0$. Input for a finite simple undirected graph with labelled vertices gives delimited natural vertex and edge counts, then successive increasing endpoint pairs sorted lexicographically, then reduced rational $0<\varepsilon<1$, $0<\delta<1/2$ in the model’s signed numerator/positive denominator format. Let $t=C(L+\lceil\varepsilon^{-1}\rceil+\lceil\log_2\lceil\delta^{-1}\rceil\rceil+1)^d$, where $L$ is that encoded length. Every length-$t$ prefix leaves the machine halted with the exact padded right-tape encoding of a nonnegative rational $q$. If $Z$ is the perfect-matching count, $Z=0$ forces the encoding of zero on every prefix. A uniform fraction at least $1-\delta$ of prefixes give $(1-\varepsilon)Z\le q\le(1+\varepsilon)Z$. The order-zero graph has one empty matching; other graphs may have none.

## Depends on

- [Correctness and resource conventions of the exact source machine](eight-symbol-fair-bit-post-turing-machine.md)
- Unweighted sparse simple-graph encoding, matching enumeration and bounded fair-bit tape semantics with absorbing halt.

## Proof outline

Separate the matching count estimator and concentration from the finite-alphabet implementation and encode/decode lemmas. Keep the single machine and explicit worst-case budget independent of the input and all tapes.

- Uniform approximation algorithm for general (not just bipartite) matchings with all-tape halt, zero count handling and relative-accuracy proof.

## Sources

- [Comparator statement: `OAI.MatchingFPRAS.thm_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatchingFPRAS.lean#L103-L107)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/113.md)
