# Undirected ST-connectivity is in L (Reingold)

The undirected $s$-$t$ connectivity
decision problem lies in the class $\mathsf{L}$ of decision problems decidable in deterministic
logarithmic space.

The vertex count $n$ is written in binary, so a single vertex name can be as long as the input, and
the graph on $\{0, \dots, n - 1\}$ can have exponentially many vertices in the input length. Only $s$,
$t$ and the endpoints of the listed edges with both endpoints below $n$ matter, at most
$2|E| + 2$ vertices. A logarithmic-space algorithm first checks that $s$ and $t$ are below $n$,
refers to each relevant vertex by the position of one of its occurrences in the input, and compares
two vertex names by rescanning the input bit by bit, never storing a name whole; this presents a
graph with $N \le 2|E| + 2$ vertices, linearly many in the input length, with the same
connectivity between $s$ and $t$.

On that graph, Reingold's algorithm first makes it regular of constant degree and non-bipartite (for
instance by adding self-loops), without changing its connected components, then raises it to a constant power and
reduces the degree back with a zig-zag product with a fixed small expander, $O(\log N)$ times; each
step increases the spectral gap of every connected component until it is a constant, so each
component has logarithmic diameter, and all of this is computed in logarithmic space through
rotation maps (Reingold; Salil P. Vadhan, *Pseudorandomness* (2012), Section 4.4, Theorem 4.46).

## Informally uses

- [Zig-zag theorem, spectral-gap form](../../../GraphTheory/graph-families-and-operations/zig-zag-product-and-explicit-expanders/zig-zag-theorem-gap-form.md):
  the zig-zag step keeps a constant fraction of the spectral gap while restoring constant degree
  (Reingold's Theorem 2.9 cites the zig-zag theorem of Reingold, Vadhan and Wigderson; Vadhan's
  proof uses his Theorem 4.35).
- [Squaring squares the spectral parameter](../../../GraphTheory/graph-families-and-operations/zig-zag-product-and-explicit-expanders/is-ndlambda-graph-square.md):
  powering (Reingold's Proposition 2.7) is what enlarges the spectral gap.
- [Spectral expanders have logarithmic diameter](../../../GraphTheory/graph-families-and-operations/expander-graphs/logarithmic-diameter.md):
  once every component is an expander, $s$ and $t$ are connected if and only if a walk of length
  $O(\log N)$ joins them (Reingold's Proposition 2.2).

## Sources

- Omer Reingold, "Undirected connectivity in log-space", Journal of the ACM 55 (2008), 1-24 (STOC 2005).
- Omer Reingold, "Undirected ST-connectivity in log-space", ECCC TR04-094 (preliminary version, 2004): the
  numbering of Proposition 2.2, Proposition 2.7 and Theorem 2.9 cited above is that of this version.
- Salil P. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7 (2012),
  Section 4.4 and Theorem 4.46.
