# Arbitrary fixed gaps for Min-Uncut

There is one deterministic finite-stack machine with finite stack alphabets computing a map $(K,\varphi)\mapsto (G,k)$ for every natural $K$ and every three-slot CNF formula $\varphi$. The variables have arbitrary natural names and literal repetitions are allowed. The output is a finite simple unweighted graph $G$ and an integer $k\ge1$. Let $u(G)$ be the minimum, over all Boolean vertex labelings, including constant labelings, of the number of edges with both endpoints on the same side, counting each unordered edge once. For $K\ge 2$, satisfiable formulas yield $u(G)\le k$ and unsatisfiable ones yield $Kk<u(G)$.

For each $K$, there are polynomials $p_K,q_K$ in the bit length of the formula alone bounding respectively the machine's runtime and the sum of the output vertex count and encoded output length. The machine gets $K$ in the input; this is not a claim that the bounds are polynomials in the joint input length. Use the syntax of a list of three-slot clauses, with a leading continuation bit per clause and a final zero; each literal is a sign followed by a framed canonical little-endian binary variable name. Framing a bit string replaces each bit $b$ by $1b$ and appends $0$. The input prepends framed $K$; the output is the framed vertex count, the full row-major Boolean adjacency table and the framed threshold. There is no guarantee stated for malformed words outside the typed input encoding.

## Depends on

- The simple graph and encoded three-slot CNF models above.

## Proof depends on

- A quantitative parity-constraint gadget reduction yielding arbitrary multiplicative gaps, and a uniform compiler with the two separate per-$K$ polynomial bounds.

## Expansion

Separate gap completeness and strict soundness on explicit simple graphs from exact transduction of the framed formula and adjacency table. Prove the bounds with $K$ fixed without assuming a polynomial bound uniform in its bit length.

## Related topics

- [The Max-Cut decision instance](../np-completeness/graph-coloring-and-partitioning/maximum-cut/max-cut-instance.md) uses a different graph representation and objective.

## Sources

- OpenAI, [MinUncut.lean, definitions and `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MinUncut.lean#L14-L126).
