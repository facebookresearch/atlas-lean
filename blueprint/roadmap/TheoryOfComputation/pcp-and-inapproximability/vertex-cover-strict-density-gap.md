# Strict vertex cover density gaps from binary 3SAT

For every integer $m\ge4$ there is one deterministic polynomial-time finite-stack machine with finite stack alphabets that maps every raw binary word $x$ to an explicit finite simple unweighted graph $G_x$. Edges are a list of distinct increasing endpoint pairs. The bit output is the framed binary vertex count, all vertex names, the edge count and all edge endpoints. Let $\tau(G)$ be the minimum cardinality of a vertex set meeting every edge, and let $n=|V(G_x)|$. On a satisfiable canonically encoded three-slot CNF the graph satisfies $\tau(G_x)<(1/2+1/m)n$; on every other word, including malformed encodings, $\tau(G_x)>(1-1/m)n$. Both inequalities are strict and are between real numbers after casting the natural cardinalities.

The input uses signed literals with self-delimiting canonical binary natural names and a continuation bit per three-literal clause. The time bound is polynomial in the original input bit length for fixed $m$.

## Depends on

- The cover predicate, minimum cover cardinality and explicit bit serialization above.

## Proof depends on

- A quantitative completeness/soundness reduction from binary 3SAT, including treatment of malformed inputs and a proof that the simple-graph serialization is polynomial time.

## Expansion

Separate coverage and optimum transport across graph encodings from the strict inequalities. Keep the vertex count explicit even on edgeless graphs; neither strict inequality allows a zero-vertex output in its respective case.

## Sources

- OpenAI, [formula, encoding, covering and gap](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VertexCover.lean#L5-L146).
