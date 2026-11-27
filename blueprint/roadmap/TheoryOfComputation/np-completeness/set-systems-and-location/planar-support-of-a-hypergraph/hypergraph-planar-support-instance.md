# Instances of PLANAR SUPPORT OF A HYPERGRAPH (PLANAR VENN DIAGRAM)

An instance of PLANAR SUPPORT OF A HYPERGRAPH (PLANAR VENN DIAGRAM) consists of a natural number $n$ and a list of hyperedges, each a list of natural labels. The labels need not be below $n$: at $n = 1$ the list `[[1]]` is an instance, and its hyperedge projects to the empty vertex set of $\{0, \dots, n-1\}$. Each hyperedge keeps its position in the list. That every label is below $n$ is checked separately by [validation](well-formed.md).
