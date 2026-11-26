# Perfect-completeness gap for two-to-one projection games

For each rational $0<\delta<1$ there is one deterministic polynomial-time finite-stack machine with finite stack alphabets, and a fixed integer $q\ge 2$. On every raw input word the machine outputs a finite bipartite game with a nonempty list of unweighted edge occurrences. Left labels form $[2q]$ and right labels $[q]$; each edge has a projection $[2q]\to[q]$ with exactly two preimages per image label. An edge is satisfied when the projection of the chosen left label equals the right label. The game value is the maximum satisfied fraction over all labelings, with multiplicity in the edge list. On a satisfiable binary 3CNF input the value is exactly $1$; on every other word it is at most the real cast of $\delta$.

Input decoding uses a list of three-slot clauses, a sign for each literal and canonically framed binary variable names, stopping at the list terminator and rejecting any trailing bits. The output consists of the two vertex counts, $q$, the edge count and, for each edge, both endpoints and its full projection table, written as unary self-delimiting naturals. The polynomial time bound is in the original input bit length; $q$ is fixed before that input is read.

## Depends on

- The exact two-to-one projection game, value and coded-input reduction model above.

## Proof depends on

- A perfect-completeness gap construction preserving exact two-to-one fibers and occurrence weights, with a finite-alphabet implementation for the framed SAT input and explicit projection tables.

## Expansion

Separate projections and game value from the gap-preserving construction; prove correctness for the raw bit language, including its malformed no-instances. Do not infer a simple-graph condition, use a real rather than rational input error, or replace value $1$ by a limit as the error tends to zero.

## Sources

- OpenAI, [source encodings, game and reduction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PerfectCompleteness.lean#L5-L181).
