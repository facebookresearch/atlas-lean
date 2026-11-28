# Genome of an adjacency list

For an instance with $n$ genes and a list of pairs of natural numbers, the graph on the extremities $0, \dots, 2n - 1$ in which two distinct extremities are adjacent when the pair, in either order, is listed. The graph is built from any list. The [genome-list](genome-list.md) condition is **sufficient**, not necessary, for this graph to be a genome (each extremity in at most one adjacency): with one gene, the list $[(0, 1), (0, 1)]$ gives a single edge, hence a matching, although the list repeats a pair and fails the condition.
