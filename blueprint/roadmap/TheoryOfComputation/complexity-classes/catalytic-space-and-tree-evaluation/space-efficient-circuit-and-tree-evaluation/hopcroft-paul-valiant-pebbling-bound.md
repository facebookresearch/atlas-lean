# Hopcroft–Paul–Valiant pebbling bound: bounded in-degree DAGs on N vertices need only O(N/log N) pebbles

In the black pebble game on a directed acyclic graph, a pebble may be placed on a vertex when all its predecessors carry pebbles (sources may always be pebbled) and may be removed at any time; a vertex is pebbled when a pebble is eventually placed on it. For every constant $d$, every DAG on $N$ vertices with in-degree at most $d$ has a pebbling strategy that places a pebble on any prescribed vertex while never using more than

$$
O\Bigl(\frac{N}{\log N}\Bigr)
$$

pebbles simultaneously.

## Proof sketch

The argument is a divide and conquer on the DAG measured by its number of edges, which is $O(N)$ for bounded in-degree. One splits the graph into a lower and an upper part; if few edges cross the cut, the crossing tails are pebbled recursively and kept while the upper part is handled, and otherwise the upper part is small enough to be pebbled naively. Solving the resulting recurrence for the maximal number of simultaneous pebbles gives $O(N/\log N)$.

## Proof depends on

- [Deterministic time classes on multi-tape machines](../../time-and-space-classes-on-multi-tape-machines/dtime.md)

## Sources

- John E. Hopcroft, Wolfgang J. Paul and Leslie G. Valiant, "On Time Versus Space", Journal of the ACM 24(2) (1977), 332-337.
