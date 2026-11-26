# Binary 3SAT gap reduction to simple translation unique games

For each pair of reals $0<\varepsilon,\delta<1/2$, there exist a dimension $s\ge1$, an alphabet $[q]$ with $q\ge2$ identified by a fixed bijection with $\mathbb F_2^s$ (hence $q=2^s$), and a deterministic machine with finite control and finitely many finite-alphabet stacks. On every raw binary word it computes the explicit output in polynomial time in the input bit length. The output has a finite vertex set and a nonempty list of unweighted constraints, with a bipartition so each constraint goes from side zero to side one and no two occurrences have the same endpoints. A constraint has forward and inverse permutation tables, with forward map $z\mapsto z+b_e$ in the fixed coordinates. The serialized output gives the vertex count, alphabet size, and number of constraints followed by endpoints and forward tables, all as unary self-delimiting naturals.

For a satisfiable canonically encoded three-slot CNF, some vertex labeling satisfies at least the fraction $1-\varepsilon$ of the constraints; for every other word, every labeling satisfies at most the fraction $\delta$. A directed constraint is satisfied if its map sends the source label to the target label. Variable names in the input are binary naturals framed by leading $1$s per digit and a final $0$; each signed literal consists of the sign followed by its framed name. The clause list uses a leading $1$ for each clause and a final $0$, with no trailing bits. The dimension, identification, machine and time polynomial are independent of the input.

## Depends on

- The nonempty simple bipartite translation game and finite-alphabet machine reduction on framed three-slot inputs defined above.

## Proof depends on

- Completeness and soundness of a translation constraint reduction, preservation under making the bipartite output simple, and finite-alphabet bit-time realization for all inputs including malformed words.

## Expansion

Introduce a bit-coded reduction to finite nonempty games and a translation-only subtype. Isolate the tests for occurrence-wise simplicity, zero/one sides, and the per-edge affine translation law. Give a bridge from the framed three-slot input code to the native SAT language before drawing consequences for standard formulations.

## Related topics

- [The Unique Games Conjecture](the-unique-games-conjecture.md): with the usual NP-completeness bridge for the framed 3SAT language, a reduction as above yields the general unique-games hardness formulation. Translation tables are permutations, and errors outside the strict range can be handled by choosing smaller positive errors. The source endpoint supplies the specific reduction and does not use the conjecture as a hypothesis.

## Sources

- OpenAI, [UniqueGamesTheorem.lean, definitions and `theorem11`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniqueGamesTheorem.lean#L5-L235).
