# Arbitrary fixed gaps for directed feedback vertex set

For every real $A\ge 1$ and every binary language $L$ in NP, there is a deterministic polynomial-time reduction mapping every word $x$ to a finite loopless digraph $G_x$ with no repeated arcs and a positive integer $k_x$. Opposite arcs are allowed, hence directed cycles of length two count. Put $d(G)=\min |F|$ over sets of vertices $F$ meeting every directed cycle (a cyclic list of distinct vertices with all successive arcs, including the closing arc). If $x\in L$ then $d(G_x)\le k_x$; otherwise $A k_x<d(G_x)$, with the comparison in $\mathbb R$.

Here NP uses a polynomial bound in $|x|$ on a binary witness and a polynomial-time deterministic finite-stack verifier on the pair encoded as $1^{|x|}0\,x\,w$. The reduction uses a deterministic finite-stack machine with each stack alphabet finite. Its output explicitly lists the threshold, vertex count, all vertices including isolated ones, the arc count and the ordered endpoint pairs, with each natural $j$ written as $1^j0$.

## Depends on

- Finite loopless arc lists, the directed cyclic enumeration, and the finite-alphabet verifier and reduction model defined above.

## Proof depends on

- A verifier-to-gap construction preserving both strict soundness and polynomial bit time with the unary output format, not just unweighted directed feedback vertex set decision hardness.

## Expansion

Prove that directed-cycle hitting agrees with deletion to acyclicity, including opposite arcs and isolated vertices. Give a verifier/encoding bridge and split the quantitative reduction into a gap-preserving construction and its finite-alphabet implementation and output bound.

## Sources

- OpenAI, [DirectedFeedback.lean, definitions and `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectedFeedback.lean#L7-L99).
